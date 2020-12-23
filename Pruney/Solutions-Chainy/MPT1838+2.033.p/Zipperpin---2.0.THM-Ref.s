%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9SdhPKsVc4

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:19 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 115 expanded)
%              Number of leaves         :   26 (  46 expanded)
%              Depth                    :   16
%              Number of atoms          :  485 ( 795 expanded)
%              Number of equality atoms :   58 (  90 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

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
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X19 @ X20 ) )
      = ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('3',plain,(
    ! [X12: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X12 @ k1_xboole_0 ) )
      = X12 ) ),
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
    ! [X16: $i,X18: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X16 ) @ X18 )
      | ~ ( r2_hidden @ X16 @ X18 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('8',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X19 @ X20 ) )
      = ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X11 @ X10 ) )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
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
    ! [X12: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X12 @ k1_xboole_0 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('13',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X24 ) @ X25 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X19 @ X20 ) )
      = ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('15',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ X24 ) @ X25 ) )
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
    ! [X28: $i] :
      ( ~ ( v1_zfmisc_1 @ X28 )
      | ( X28
        = ( k6_domain_1 @ X28 @ ( sk_B_1 @ X28 ) ) )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('19',plain,(
    ! [X28: $i] :
      ( ~ ( v1_zfmisc_1 @ X28 )
      | ( m1_subset_1 @ ( sk_B_1 @ X28 ) @ X28 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('20',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ X26 )
      | ( ( k6_domain_1 @ X26 @ X27 )
        = ( k1_tarski @ X27 ) ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X11 @ X10 ) )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X21 = X22 )
      | ( ( k1_tarski @ X23 )
       != ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t44_zfmisc_1])).

thf('27',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X19 @ X20 ) )
      = ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('28',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X21 = X22 )
      | ( ( k1_tarski @ X23 )
       != ( k3_tarski @ ( k2_tarski @ X21 @ X22 ) ) ) ) ),
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
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('31',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('32',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ sk_B_2 ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X16 ) @ X18 )
      | ~ ( r2_hidden @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('38',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_B @ sk_A ) ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X11 @ X10 ) )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('40',plain,
    ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ ( sk_B @ sk_A ) ) @ sk_B_2 ) )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ X24 ) @ X25 ) )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('42',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    sk_A != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_2 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['29','42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
       != sk_B_2 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B_2 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','45'])).

thf('47',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v1_zfmisc_1 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    v1_zfmisc_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('simplify_reflect+',[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['17','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['0','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9SdhPKsVc4
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:56:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 364 iterations in 0.122s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.39/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.57  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.39/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.57  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.39/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.39/0.57  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.39/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.57  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.39/0.57  thf(t1_tex_2, conjecture,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.39/0.57           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i]:
% 0.39/0.57        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.57          ( ![B:$i]:
% 0.39/0.57            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.39/0.57              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 0.39/0.57  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(t1_boole, axiom,
% 0.39/0.57    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.57  thf('1', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.39/0.57      inference('cnf', [status(esa)], [t1_boole])).
% 0.39/0.57  thf(l51_zfmisc_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.57  thf('2', plain,
% 0.39/0.57      (![X19 : $i, X20 : $i]:
% 0.39/0.57         ((k3_tarski @ (k2_tarski @ X19 @ X20)) = (k2_xboole_0 @ X19 @ X20))),
% 0.39/0.57      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.39/0.57  thf('3', plain,
% 0.39/0.57      (![X12 : $i]: ((k3_tarski @ (k2_tarski @ X12 @ k1_xboole_0)) = (X12))),
% 0.39/0.57      inference('demod', [status(thm)], ['1', '2'])).
% 0.39/0.57  thf(d1_xboole_0, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.39/0.57  thf('4', plain,
% 0.39/0.57      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.39/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.57  thf(l1_zfmisc_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.39/0.57  thf('5', plain,
% 0.39/0.57      (![X16 : $i, X18 : $i]:
% 0.39/0.57         ((r1_tarski @ (k1_tarski @ X16) @ X18) | ~ (r2_hidden @ X16 @ X18))),
% 0.39/0.57      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.39/0.57  thf('6', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.39/0.57  thf(t12_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.39/0.57  thf('7', plain,
% 0.39/0.57      (![X10 : $i, X11 : $i]:
% 0.39/0.57         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.39/0.57      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.39/0.57  thf('8', plain,
% 0.39/0.57      (![X19 : $i, X20 : $i]:
% 0.39/0.57         ((k3_tarski @ (k2_tarski @ X19 @ X20)) = (k2_xboole_0 @ X19 @ X20))),
% 0.39/0.57      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.39/0.57  thf('9', plain,
% 0.39/0.57      (![X10 : $i, X11 : $i]:
% 0.39/0.57         (((k3_tarski @ (k2_tarski @ X11 @ X10)) = (X10))
% 0.39/0.57          | ~ (r1_tarski @ X11 @ X10))),
% 0.39/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.39/0.57  thf('10', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v1_xboole_0 @ X0)
% 0.39/0.57          | ((k3_tarski @ (k2_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0)) = (X0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['6', '9'])).
% 0.39/0.57  thf('11', plain,
% 0.39/0.57      ((((k1_tarski @ (sk_B @ k1_xboole_0)) = (k1_xboole_0))
% 0.39/0.57        | (v1_xboole_0 @ k1_xboole_0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['3', '10'])).
% 0.39/0.57  thf('12', plain,
% 0.39/0.57      (![X12 : $i]: ((k3_tarski @ (k2_tarski @ X12 @ k1_xboole_0)) = (X12))),
% 0.39/0.57      inference('demod', [status(thm)], ['1', '2'])).
% 0.39/0.57  thf(t49_zfmisc_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.39/0.57  thf('13', plain,
% 0.39/0.57      (![X24 : $i, X25 : $i]:
% 0.39/0.57         ((k2_xboole_0 @ (k1_tarski @ X24) @ X25) != (k1_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.39/0.57  thf('14', plain,
% 0.39/0.57      (![X19 : $i, X20 : $i]:
% 0.39/0.57         ((k3_tarski @ (k2_tarski @ X19 @ X20)) = (k2_xboole_0 @ X19 @ X20))),
% 0.39/0.57      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.39/0.57  thf('15', plain,
% 0.39/0.57      (![X24 : $i, X25 : $i]:
% 0.39/0.57         ((k3_tarski @ (k2_tarski @ (k1_tarski @ X24) @ X25)) != (k1_xboole_0))),
% 0.39/0.57      inference('demod', [status(thm)], ['13', '14'])).
% 0.39/0.57  thf('16', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['12', '15'])).
% 0.39/0.57  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['11', '16'])).
% 0.39/0.57  thf(d1_tex_2, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.57       ( ( v1_zfmisc_1 @ A ) <=>
% 0.39/0.57         ( ?[B:$i]:
% 0.39/0.57           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.39/0.57  thf('18', plain,
% 0.39/0.57      (![X28 : $i]:
% 0.39/0.57         (~ (v1_zfmisc_1 @ X28)
% 0.39/0.57          | ((X28) = (k6_domain_1 @ X28 @ (sk_B_1 @ X28)))
% 0.39/0.57          | (v1_xboole_0 @ X28))),
% 0.39/0.57      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.39/0.57  thf('19', plain,
% 0.39/0.57      (![X28 : $i]:
% 0.39/0.57         (~ (v1_zfmisc_1 @ X28)
% 0.39/0.57          | (m1_subset_1 @ (sk_B_1 @ X28) @ X28)
% 0.39/0.57          | (v1_xboole_0 @ X28))),
% 0.39/0.57      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.39/0.57  thf(redefinition_k6_domain_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.39/0.57       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.39/0.57  thf('20', plain,
% 0.39/0.57      (![X26 : $i, X27 : $i]:
% 0.39/0.57         ((v1_xboole_0 @ X26)
% 0.39/0.57          | ~ (m1_subset_1 @ X27 @ X26)
% 0.39/0.57          | ((k6_domain_1 @ X26 @ X27) = (k1_tarski @ X27)))),
% 0.39/0.57      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.39/0.57  thf('21', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v1_xboole_0 @ X0)
% 0.39/0.57          | ~ (v1_zfmisc_1 @ X0)
% 0.39/0.57          | ((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.39/0.57          | (v1_xboole_0 @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.39/0.57  thf('22', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.39/0.57          | ~ (v1_zfmisc_1 @ X0)
% 0.39/0.57          | (v1_xboole_0 @ X0))),
% 0.39/0.57      inference('simplify', [status(thm)], ['21'])).
% 0.39/0.57  thf('23', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('24', plain,
% 0.39/0.57      (![X10 : $i, X11 : $i]:
% 0.39/0.57         (((k3_tarski @ (k2_tarski @ X11 @ X10)) = (X10))
% 0.39/0.57          | ~ (r1_tarski @ X11 @ X10))),
% 0.39/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.39/0.57  thf('25', plain, (((k3_tarski @ (k2_tarski @ sk_A @ sk_B_2)) = (sk_B_2))),
% 0.39/0.57      inference('sup-', [status(thm)], ['23', '24'])).
% 0.39/0.57  thf(t44_zfmisc_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.39/0.57          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.39/0.57          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.39/0.57  thf('26', plain,
% 0.39/0.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.39/0.57         (((X21) = (k1_xboole_0))
% 0.39/0.57          | ((X22) = (k1_xboole_0))
% 0.39/0.57          | ((X21) = (X22))
% 0.39/0.57          | ((k1_tarski @ X23) != (k2_xboole_0 @ X21 @ X22)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t44_zfmisc_1])).
% 0.39/0.57  thf('27', plain,
% 0.39/0.57      (![X19 : $i, X20 : $i]:
% 0.39/0.57         ((k3_tarski @ (k2_tarski @ X19 @ X20)) = (k2_xboole_0 @ X19 @ X20))),
% 0.39/0.57      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.39/0.57  thf('28', plain,
% 0.39/0.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.39/0.57         (((X21) = (k1_xboole_0))
% 0.39/0.57          | ((X22) = (k1_xboole_0))
% 0.39/0.57          | ((X21) = (X22))
% 0.39/0.57          | ((k1_tarski @ X23) != (k3_tarski @ (k2_tarski @ X21 @ X22))))),
% 0.39/0.57      inference('demod', [status(thm)], ['26', '27'])).
% 0.39/0.57  thf('29', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (((k1_tarski @ X0) != (sk_B_2))
% 0.39/0.57          | ((sk_A) = (sk_B_2))
% 0.39/0.57          | ((sk_B_2) = (k1_xboole_0))
% 0.39/0.57          | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['25', '28'])).
% 0.39/0.57  thf('30', plain,
% 0.39/0.57      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.39/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.57  thf('31', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(d3_tarski, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.39/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.39/0.57  thf('32', plain,
% 0.39/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X3 @ X4)
% 0.39/0.57          | (r2_hidden @ X3 @ X5)
% 0.39/0.57          | ~ (r1_tarski @ X4 @ X5))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.57  thf('33', plain,
% 0.39/0.57      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_2) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['31', '32'])).
% 0.39/0.57  thf('34', plain,
% 0.39/0.57      (((v1_xboole_0 @ sk_A) | (r2_hidden @ (sk_B @ sk_A) @ sk_B_2))),
% 0.39/0.57      inference('sup-', [status(thm)], ['30', '33'])).
% 0.39/0.57  thf('35', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('36', plain, ((r2_hidden @ (sk_B @ sk_A) @ sk_B_2)),
% 0.39/0.57      inference('clc', [status(thm)], ['34', '35'])).
% 0.39/0.57  thf('37', plain,
% 0.39/0.57      (![X16 : $i, X18 : $i]:
% 0.39/0.57         ((r1_tarski @ (k1_tarski @ X16) @ X18) | ~ (r2_hidden @ X16 @ X18))),
% 0.39/0.57      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.39/0.57  thf('38', plain, ((r1_tarski @ (k1_tarski @ (sk_B @ sk_A)) @ sk_B_2)),
% 0.39/0.57      inference('sup-', [status(thm)], ['36', '37'])).
% 0.39/0.57  thf('39', plain,
% 0.39/0.57      (![X10 : $i, X11 : $i]:
% 0.39/0.57         (((k3_tarski @ (k2_tarski @ X11 @ X10)) = (X10))
% 0.39/0.57          | ~ (r1_tarski @ X11 @ X10))),
% 0.39/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.39/0.57  thf('40', plain,
% 0.39/0.57      (((k3_tarski @ (k2_tarski @ (k1_tarski @ (sk_B @ sk_A)) @ sk_B_2))
% 0.39/0.57         = (sk_B_2))),
% 0.39/0.57      inference('sup-', [status(thm)], ['38', '39'])).
% 0.39/0.57  thf('41', plain,
% 0.39/0.57      (![X24 : $i, X25 : $i]:
% 0.39/0.57         ((k3_tarski @ (k2_tarski @ (k1_tarski @ X24) @ X25)) != (k1_xboole_0))),
% 0.39/0.57      inference('demod', [status(thm)], ['13', '14'])).
% 0.39/0.57  thf('42', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.39/0.57  thf('43', plain, (((sk_A) != (sk_B_2))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('44', plain,
% 0.39/0.57      (![X0 : $i]: (((k1_tarski @ X0) != (sk_B_2)) | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['29', '42', '43'])).
% 0.39/0.57  thf('45', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) != (sk_B_2))
% 0.39/0.57          | (v1_xboole_0 @ X0)
% 0.39/0.57          | ~ (v1_zfmisc_1 @ X0)
% 0.39/0.57          | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['22', '44'])).
% 0.39/0.57  thf('46', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (((X0) != (sk_B_2))
% 0.39/0.57          | (v1_xboole_0 @ X0)
% 0.39/0.57          | ~ (v1_zfmisc_1 @ X0)
% 0.39/0.57          | ((sk_A) = (k1_xboole_0))
% 0.39/0.57          | ~ (v1_zfmisc_1 @ X0)
% 0.39/0.57          | (v1_xboole_0 @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['18', '45'])).
% 0.39/0.57  thf('47', plain,
% 0.39/0.57      ((((sk_A) = (k1_xboole_0))
% 0.39/0.57        | ~ (v1_zfmisc_1 @ sk_B_2)
% 0.39/0.57        | (v1_xboole_0 @ sk_B_2))),
% 0.39/0.57      inference('simplify', [status(thm)], ['46'])).
% 0.39/0.57  thf('48', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('49', plain, ((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_B_2))),
% 0.39/0.57      inference('simplify_reflect+', [status(thm)], ['47', '48'])).
% 0.39/0.57  thf('50', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('51', plain, (((sk_A) = (k1_xboole_0))),
% 0.39/0.57      inference('clc', [status(thm)], ['49', '50'])).
% 0.39/0.57  thf('52', plain, ((v1_xboole_0 @ sk_A)),
% 0.39/0.57      inference('demod', [status(thm)], ['17', '51'])).
% 0.39/0.57  thf('53', plain, ($false), inference('demod', [status(thm)], ['0', '52'])).
% 0.39/0.57  
% 0.39/0.57  % SZS output end Refutation
% 0.39/0.57  
% 0.39/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
