%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wYk4LvETPs

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 121 expanded)
%              Number of leaves         :   25 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :  431 ( 838 expanded)
%              Number of equality atoms :   62 ( 107 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('3',plain,(
    ! [X7: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X7 @ k1_xboole_0 ) )
      = X7 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('5',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X15 ) @ X17 )
      | ~ ( r2_hidden @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('8',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X6 @ X5 ) )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,
    ( ( ( k1_tarski @ ( sk_B @ k1_xboole_0 ) )
      = k1_xboole_0 )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X7: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X7 @ k1_xboole_0 ) )
      = X7 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('13',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X23 ) @ X24 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('14',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('15',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ X23 ) @ X24 ) )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['11','16'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('18',plain,(
    ! [X27: $i] :
      ( ~ ( v1_zfmisc_1 @ X27 )
      | ( X27
        = ( k6_domain_1 @ X27 @ ( sk_B_1 @ X27 ) ) )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('19',plain,(
    ! [X27: $i] :
      ( ~ ( v1_zfmisc_1 @ X27 )
      | ( m1_subset_1 @ ( sk_B_1 @ X27 ) @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('20',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ X25 )
      | ( ( k6_domain_1 @ X25 @ X26 )
        = ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X6 @ X5 ) )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('25',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_A @ sk_B_2 ) )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t44_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf('26',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( X20 = X21 )
      | ( ( k1_tarski @ X22 )
       != ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t44_zfmisc_1])).

thf('27',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('28',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( X20 = X21 )
      | ( ( k1_tarski @ X22 )
       != ( k3_tarski @ ( k2_tarski @ X20 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_2 )
      | ( sk_A = sk_B_2 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    sk_A != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_2 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
       != sk_B_2 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B_2 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','32'])).

thf('34',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 )
    | ~ ( v1_zfmisc_1 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    v1_zfmisc_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('simplify_reflect+',[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['11','16'])).

thf('40',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['17','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['0','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wYk4LvETPs
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:55:51 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.35  % Running portfolio for 600 s
% 0.21/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 194 iterations in 0.051s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.51  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.21/0.51  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.21/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.51  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.51  thf(t1_tex_2, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.21/0.51           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.21/0.51              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 0.21/0.51  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t1_boole, axiom,
% 0.21/0.51    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.51  thf('1', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.51  thf(l51_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i]:
% 0.21/0.51         ((k3_tarski @ (k2_tarski @ X18 @ X19)) = (k2_xboole_0 @ X18 @ X19))),
% 0.21/0.51      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X7 : $i]: ((k3_tarski @ (k2_tarski @ X7 @ k1_xboole_0)) = (X7))),
% 0.21/0.51      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf(d1_xboole_0, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.51  thf(l1_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X15 : $i, X17 : $i]:
% 0.21/0.51         ((r1_tarski @ (k1_tarski @ X15) @ X17) | ~ (r2_hidden @ X15 @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf(t12_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i]:
% 0.21/0.51         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i]:
% 0.21/0.51         ((k3_tarski @ (k2_tarski @ X18 @ X19)) = (k2_xboole_0 @ X18 @ X19))),
% 0.21/0.51      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i]:
% 0.21/0.51         (((k3_tarski @ (k2_tarski @ X6 @ X5)) = (X5))
% 0.21/0.51          | ~ (r1_tarski @ X6 @ X5))),
% 0.21/0.51      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ X0)
% 0.21/0.51          | ((k3_tarski @ (k2_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0)) = (X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['6', '9'])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      ((((k1_tarski @ (sk_B @ k1_xboole_0)) = (k1_xboole_0))
% 0.21/0.51        | (v1_xboole_0 @ k1_xboole_0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['3', '10'])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X7 : $i]: ((k3_tarski @ (k2_tarski @ X7 @ k1_xboole_0)) = (X7))),
% 0.21/0.51      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf(t49_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X23 : $i, X24 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ (k1_tarski @ X23) @ X24) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i]:
% 0.21/0.51         ((k3_tarski @ (k2_tarski @ X18 @ X19)) = (k2_xboole_0 @ X18 @ X19))),
% 0.21/0.51      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X23 : $i, X24 : $i]:
% 0.21/0.51         ((k3_tarski @ (k2_tarski @ (k1_tarski @ X23) @ X24)) != (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('16', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '15'])).
% 0.21/0.51  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['11', '16'])).
% 0.21/0.51  thf(d1_tex_2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.51       ( ( v1_zfmisc_1 @ A ) <=>
% 0.21/0.51         ( ?[B:$i]:
% 0.21/0.51           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X27 : $i]:
% 0.21/0.51         (~ (v1_zfmisc_1 @ X27)
% 0.21/0.51          | ((X27) = (k6_domain_1 @ X27 @ (sk_B_1 @ X27)))
% 0.21/0.51          | (v1_xboole_0 @ X27))),
% 0.21/0.51      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X27 : $i]:
% 0.21/0.51         (~ (v1_zfmisc_1 @ X27)
% 0.21/0.51          | (m1_subset_1 @ (sk_B_1 @ X27) @ X27)
% 0.21/0.51          | (v1_xboole_0 @ X27))),
% 0.21/0.51      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.21/0.51  thf(redefinition_k6_domain_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.51       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X25 : $i, X26 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ X25)
% 0.21/0.51          | ~ (m1_subset_1 @ X26 @ X25)
% 0.21/0.51          | ((k6_domain_1 @ X25 @ X26) = (k1_tarski @ X26)))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ X0)
% 0.21/0.51          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.51          | ((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.21/0.51          | (v1_xboole_0 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.21/0.51          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.51          | (v1_xboole_0 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.51  thf('23', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i]:
% 0.21/0.51         (((k3_tarski @ (k2_tarski @ X6 @ X5)) = (X5))
% 0.21/0.51          | ~ (r1_tarski @ X6 @ X5))),
% 0.21/0.51      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('25', plain, (((k3_tarski @ (k2_tarski @ sk_A @ sk_B_2)) = (sk_B_2))),
% 0.21/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.51  thf(t44_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.21/0.51          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.51          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.51         (((X20) = (k1_xboole_0))
% 0.21/0.51          | ((X21) = (k1_xboole_0))
% 0.21/0.51          | ((X20) = (X21))
% 0.21/0.51          | ((k1_tarski @ X22) != (k2_xboole_0 @ X20 @ X21)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t44_zfmisc_1])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i]:
% 0.21/0.51         ((k3_tarski @ (k2_tarski @ X18 @ X19)) = (k2_xboole_0 @ X18 @ X19))),
% 0.21/0.51      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.51         (((X20) = (k1_xboole_0))
% 0.21/0.51          | ((X21) = (k1_xboole_0))
% 0.21/0.51          | ((X20) = (X21))
% 0.21/0.51          | ((k1_tarski @ X22) != (k3_tarski @ (k2_tarski @ X20 @ X21))))),
% 0.21/0.51      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k1_tarski @ X0) != (sk_B_2))
% 0.21/0.51          | ((sk_A) = (sk_B_2))
% 0.21/0.51          | ((sk_B_2) = (k1_xboole_0))
% 0.21/0.51          | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['25', '28'])).
% 0.21/0.51  thf('30', plain, (((sk_A) != (sk_B_2))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k1_tarski @ X0) != (sk_B_2))
% 0.21/0.51          | ((sk_B_2) = (k1_xboole_0))
% 0.21/0.51          | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) != (sk_B_2))
% 0.21/0.51          | (v1_xboole_0 @ X0)
% 0.21/0.51          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.51          | ((sk_A) = (k1_xboole_0))
% 0.21/0.51          | ((sk_B_2) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['22', '31'])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((X0) != (sk_B_2))
% 0.21/0.51          | (v1_xboole_0 @ X0)
% 0.21/0.51          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.51          | ((sk_B_2) = (k1_xboole_0))
% 0.21/0.51          | ((sk_A) = (k1_xboole_0))
% 0.21/0.51          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.51          | (v1_xboole_0 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['18', '32'])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      ((((sk_A) = (k1_xboole_0))
% 0.21/0.51        | ((sk_B_2) = (k1_xboole_0))
% 0.21/0.51        | ~ (v1_zfmisc_1 @ sk_B_2)
% 0.21/0.51        | (v1_xboole_0 @ sk_B_2))),
% 0.21/0.51      inference('simplify', [status(thm)], ['33'])).
% 0.21/0.51  thf('35', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      ((((sk_A) = (k1_xboole_0))
% 0.21/0.51        | ((sk_B_2) = (k1_xboole_0))
% 0.21/0.51        | (v1_xboole_0 @ sk_B_2))),
% 0.21/0.51      inference('simplify_reflect+', [status(thm)], ['34', '35'])).
% 0.21/0.51  thf('37', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('38', plain, ((((sk_B_2) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.51      inference('clc', [status(thm)], ['36', '37'])).
% 0.21/0.51  thf('39', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['11', '16'])).
% 0.21/0.51  thf('40', plain, (((v1_xboole_0 @ sk_B_2) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['38', '39'])).
% 0.21/0.51  thf('41', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('42', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.51      inference('clc', [status(thm)], ['40', '41'])).
% 0.21/0.51  thf('43', plain, ((v1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['17', '42'])).
% 0.21/0.51  thf('44', plain, ($false), inference('demod', [status(thm)], ['0', '43'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
