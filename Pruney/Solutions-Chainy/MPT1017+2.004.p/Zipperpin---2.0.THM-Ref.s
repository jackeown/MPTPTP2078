%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.klvCZLDvrC

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:56 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   56 (  74 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :  349 ( 997 expanded)
%              Number of equality atoms :   11 (  29 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(t83_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( ( v2_funct_1 @ B )
          & ( ( k2_relset_1 @ A @ A @ B )
            = A ) )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( v3_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( ( v2_funct_1 @ B )
            & ( ( k2_relset_1 @ A @ A @ B )
              = A ) )
         => ( ( v1_funct_1 @ B )
            & ( v1_funct_2 @ B @ A @ A )
            & ( v3_funct_2 @ B @ A @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t83_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v2_funct_2 @ X12 @ X13 )
      | ( v3_funct_2 @ X12 @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc3_funct_2])).

thf('2',plain,
    ( ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v2_funct_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('11',plain,(
    ~ ( v2_funct_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['5','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('14',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['14','15'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('17',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_relat_1 @ X16 )
       != X15 )
      | ( v2_funct_2 @ X16 @ X15 )
      | ~ ( v5_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('18',plain,(
    ! [X16: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v5_relat_1 @ X16 @ ( k2_relat_1 @ X16 ) )
      | ( v2_funct_2 @ X16 @ ( k2_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('21',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ( v5_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X16: $i] :
      ( ( v2_funct_2 @ X16 @ ( k2_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(clc,[status(thm)],['18','22'])).

thf('24',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('26',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['11','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.klvCZLDvrC
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:33:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 33 iterations in 0.017s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.46  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.19/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.46  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.19/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.46  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.46  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.19/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.46  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.46  thf(t83_funct_2, conjecture,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.19/0.46         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.19/0.46       ( ( ( v2_funct_1 @ B ) & ( ( k2_relset_1 @ A @ A @ B ) = ( A ) ) ) =>
% 0.19/0.46         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.19/0.46           ( v3_funct_2 @ B @ A @ A ) & 
% 0.19/0.46           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i,B:$i]:
% 0.19/0.46        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.19/0.46            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.19/0.46          ( ( ( v2_funct_1 @ B ) & ( ( k2_relset_1 @ A @ A @ B ) = ( A ) ) ) =>
% 0.19/0.46            ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.19/0.46              ( v3_funct_2 @ B @ A @ A ) & 
% 0.19/0.46              ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t83_funct_2])).
% 0.19/0.46  thf('0', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(cc3_funct_2, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.46       ( ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) =>
% 0.19/0.46         ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) ) ))).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.46         (~ (v1_funct_1 @ X12)
% 0.19/0.46          | ~ (v2_funct_1 @ X12)
% 0.19/0.46          | ~ (v2_funct_2 @ X12 @ X13)
% 0.19/0.46          | (v3_funct_2 @ X12 @ X14 @ X13)
% 0.19/0.46          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X13))))),
% 0.19/0.46      inference('cnf', [status(esa)], [cc3_funct_2])).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (((v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.19/0.46        | ~ (v2_funct_2 @ sk_B @ sk_A)
% 0.19/0.46        | ~ (v2_funct_1 @ sk_B)
% 0.19/0.46        | ~ (v1_funct_1 @ sk_B))),
% 0.19/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.46  thf('3', plain, ((v2_funct_1 @ sk_B)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('5', plain,
% 0.19/0.46      (((v3_funct_2 @ sk_B @ sk_A @ sk_A) | ~ (v2_funct_2 @ sk_B @ sk_A))),
% 0.19/0.46      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      ((~ (v1_funct_1 @ sk_B)
% 0.19/0.46        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.19/0.46        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.19/0.46        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('7', plain, ((v1_funct_1 @ sk_B)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('8', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('9', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('10', plain, (~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.19/0.46      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.19/0.46  thf('11', plain, (~ (v2_funct_2 @ sk_B @ sk_A)),
% 0.19/0.46      inference('clc', [status(thm)], ['5', '10'])).
% 0.19/0.46  thf('12', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(redefinition_k2_relset_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.46       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.19/0.46  thf('13', plain,
% 0.19/0.46      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.46         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.19/0.46          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.19/0.46      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.19/0.46  thf('14', plain,
% 0.19/0.46      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 0.19/0.46      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.46  thf('15', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('16', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.19/0.46      inference('sup+', [status(thm)], ['14', '15'])).
% 0.19/0.46  thf(d3_funct_2, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.19/0.46       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.19/0.46  thf('17', plain,
% 0.19/0.46      (![X15 : $i, X16 : $i]:
% 0.19/0.46         (((k2_relat_1 @ X16) != (X15))
% 0.19/0.46          | (v2_funct_2 @ X16 @ X15)
% 0.19/0.46          | ~ (v5_relat_1 @ X16 @ X15)
% 0.19/0.46          | ~ (v1_relat_1 @ X16))),
% 0.19/0.46      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.19/0.46  thf('18', plain,
% 0.19/0.46      (![X16 : $i]:
% 0.19/0.46         (~ (v1_relat_1 @ X16)
% 0.19/0.46          | ~ (v5_relat_1 @ X16 @ (k2_relat_1 @ X16))
% 0.19/0.46          | (v2_funct_2 @ X16 @ (k2_relat_1 @ X16)))),
% 0.19/0.46      inference('simplify', [status(thm)], ['17'])).
% 0.19/0.46  thf(d10_xboole_0, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.46  thf('19', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.19/0.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.46  thf('20', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.19/0.46      inference('simplify', [status(thm)], ['19'])).
% 0.19/0.46  thf(d19_relat_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ B ) =>
% 0.19/0.46       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.46  thf('21', plain,
% 0.19/0.46      (![X5 : $i, X6 : $i]:
% 0.19/0.46         (~ (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.19/0.46          | (v5_relat_1 @ X5 @ X6)
% 0.19/0.46          | ~ (v1_relat_1 @ X5))),
% 0.19/0.46      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.19/0.46  thf('22', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.46  thf('23', plain,
% 0.19/0.46      (![X16 : $i]:
% 0.19/0.46         ((v2_funct_2 @ X16 @ (k2_relat_1 @ X16)) | ~ (v1_relat_1 @ X16))),
% 0.19/0.46      inference('clc', [status(thm)], ['18', '22'])).
% 0.19/0.46  thf('24', plain, (((v2_funct_2 @ sk_B @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 0.19/0.46      inference('sup+', [status(thm)], ['16', '23'])).
% 0.19/0.46  thf('25', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(cc2_relat_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ A ) =>
% 0.19/0.46       ( ![B:$i]:
% 0.19/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.19/0.46  thf('26', plain,
% 0.19/0.46      (![X3 : $i, X4 : $i]:
% 0.19/0.46         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.19/0.46          | (v1_relat_1 @ X3)
% 0.19/0.46          | ~ (v1_relat_1 @ X4))),
% 0.19/0.46      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.19/0.46  thf('27', plain,
% 0.19/0.46      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.19/0.46      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.46  thf(fc6_relat_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.19/0.46  thf('28', plain,
% 0.19/0.46      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.19/0.46      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.19/0.46  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.46      inference('demod', [status(thm)], ['27', '28'])).
% 0.19/0.46  thf('30', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 0.19/0.46      inference('demod', [status(thm)], ['24', '29'])).
% 0.19/0.46  thf('31', plain, ($false), inference('demod', [status(thm)], ['11', '30'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
