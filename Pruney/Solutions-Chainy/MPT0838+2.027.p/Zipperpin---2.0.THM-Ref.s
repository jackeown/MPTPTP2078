%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hL5ddJZk0B

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:02 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   60 (  88 expanded)
%              Number of leaves         :   25 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  363 ( 886 expanded)
%              Number of equality atoms :   22 (  44 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t49_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
             => ~ ( ( ( k1_relset_1 @ A @ B @ C )
                   != k1_xboole_0 )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ B )
                     => ~ ( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
               => ~ ( ( ( k1_relset_1 @ A @ B @ C )
                     != k1_xboole_0 )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ B )
                       => ~ ( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_relset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X8 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('5',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(t10_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ~ ( ( B != k1_xboole_0 )
          & ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ~ ( r2_hidden @ C @ B ) ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X2 ) @ X1 )
      | ( X1 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('8',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X17: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X17 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('11',plain,(
    ! [X17: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X17 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('14',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X1 @ X2 ) @ X2 )
      | ( X1 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('15',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['12','15'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X4: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('18',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('19',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('20',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('21',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('22',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference(demod,[status(thm)],['18','19','22'])).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('24',plain,(
    ! [X3: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X3 ) )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('30',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('31',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['27','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hL5ddJZk0B
% 0.15/0.38  % Computer   : n011.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 20:06:57 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.25/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.46  % Solved by: fo/fo7.sh
% 0.25/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.46  % done 29 iterations in 0.011s
% 0.25/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.46  % SZS output start Refutation
% 0.25/0.46  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.25/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.25/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.25/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.25/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.25/0.46  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.25/0.46  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.25/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.25/0.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.25/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.25/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.25/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.25/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.25/0.46  thf(t49_relset_1, conjecture,
% 0.25/0.46    (![A:$i]:
% 0.25/0.46     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.25/0.46       ( ![B:$i]:
% 0.25/0.46         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.25/0.46           ( ![C:$i]:
% 0.25/0.46             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.25/0.46               ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.25/0.46                    ( ![D:$i]:
% 0.25/0.46                      ( ( m1_subset_1 @ D @ B ) =>
% 0.25/0.46                        ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.25/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.46    (~( ![A:$i]:
% 0.25/0.46        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.25/0.46          ( ![B:$i]:
% 0.25/0.46            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.25/0.46              ( ![C:$i]:
% 0.25/0.46                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.25/0.46                  ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.25/0.46                       ( ![D:$i]:
% 0.25/0.46                         ( ( m1_subset_1 @ D @ B ) =>
% 0.25/0.46                           ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.25/0.46    inference('cnf.neg', [status(esa)], [t49_relset_1])).
% 0.25/0.46  thf('0', plain,
% 0.25/0.46      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.25/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.46  thf(dt_k2_relset_1, axiom,
% 0.25/0.46    (![A:$i,B:$i,C:$i]:
% 0.25/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.25/0.46       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.25/0.46  thf('1', plain,
% 0.25/0.46      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.25/0.46         ((m1_subset_1 @ (k2_relset_1 @ X8 @ X9 @ X10) @ (k1_zfmisc_1 @ X9))
% 0.25/0.46          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.25/0.46      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.25/0.46  thf('2', plain,
% 0.25/0.46      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.25/0.46        (k1_zfmisc_1 @ sk_B))),
% 0.25/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.25/0.46  thf('3', plain,
% 0.25/0.46      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.25/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.46  thf(redefinition_k2_relset_1, axiom,
% 0.25/0.46    (![A:$i,B:$i,C:$i]:
% 0.25/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.25/0.46       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.25/0.46  thf('4', plain,
% 0.25/0.46      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.25/0.46         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.25/0.46          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.25/0.46      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.25/0.46  thf('5', plain,
% 0.25/0.46      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.25/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.25/0.46  thf('6', plain,
% 0.25/0.46      ((m1_subset_1 @ (k2_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.25/0.46      inference('demod', [status(thm)], ['2', '5'])).
% 0.25/0.46  thf(t10_subset_1, axiom,
% 0.25/0.46    (![A:$i,B:$i]:
% 0.25/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.25/0.46       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.25/0.46            ( ![C:$i]:
% 0.25/0.46              ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.25/0.46  thf('7', plain,
% 0.25/0.46      (![X1 : $i, X2 : $i]:
% 0.25/0.46         ((r2_hidden @ (sk_C @ X1 @ X2) @ X1)
% 0.25/0.46          | ((X1) = (k1_xboole_0))
% 0.25/0.46          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.25/0.46      inference('cnf', [status(esa)], [t10_subset_1])).
% 0.25/0.46  thf('8', plain,
% 0.25/0.46      ((((k2_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.25/0.46        | (r2_hidden @ (sk_C @ (k2_relat_1 @ sk_C_1) @ sk_B) @ 
% 0.25/0.46           (k2_relat_1 @ sk_C_1)))),
% 0.25/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.25/0.46  thf('9', plain,
% 0.25/0.46      (![X17 : $i]:
% 0.25/0.46         (~ (r2_hidden @ X17 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 0.25/0.46          | ~ (m1_subset_1 @ X17 @ sk_B))),
% 0.25/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.46  thf('10', plain,
% 0.25/0.46      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.25/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.25/0.46  thf('11', plain,
% 0.25/0.46      (![X17 : $i]:
% 0.25/0.46         (~ (r2_hidden @ X17 @ (k2_relat_1 @ sk_C_1))
% 0.25/0.46          | ~ (m1_subset_1 @ X17 @ sk_B))),
% 0.25/0.46      inference('demod', [status(thm)], ['9', '10'])).
% 0.25/0.46  thf('12', plain,
% 0.25/0.46      ((((k2_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.25/0.46        | ~ (m1_subset_1 @ (sk_C @ (k2_relat_1 @ sk_C_1) @ sk_B) @ sk_B))),
% 0.25/0.46      inference('sup-', [status(thm)], ['8', '11'])).
% 0.25/0.46  thf('13', plain,
% 0.25/0.46      ((m1_subset_1 @ (k2_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.25/0.46      inference('demod', [status(thm)], ['2', '5'])).
% 0.25/0.46  thf('14', plain,
% 0.25/0.46      (![X1 : $i, X2 : $i]:
% 0.25/0.46         ((m1_subset_1 @ (sk_C @ X1 @ X2) @ X2)
% 0.25/0.46          | ((X1) = (k1_xboole_0))
% 0.25/0.46          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.25/0.46      inference('cnf', [status(esa)], [t10_subset_1])).
% 0.25/0.46  thf('15', plain,
% 0.25/0.46      ((((k2_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.25/0.46        | (m1_subset_1 @ (sk_C @ (k2_relat_1 @ sk_C_1) @ sk_B) @ sk_B))),
% 0.25/0.46      inference('sup-', [status(thm)], ['13', '14'])).
% 0.25/0.46  thf('16', plain, (((k2_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.25/0.46      inference('clc', [status(thm)], ['12', '15'])).
% 0.25/0.46  thf(fc9_relat_1, axiom,
% 0.25/0.46    (![A:$i]:
% 0.25/0.46     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.25/0.46       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.25/0.46  thf('17', plain,
% 0.25/0.46      (![X4 : $i]:
% 0.25/0.46         (~ (v1_xboole_0 @ (k2_relat_1 @ X4))
% 0.25/0.46          | ~ (v1_relat_1 @ X4)
% 0.25/0.46          | (v1_xboole_0 @ X4))),
% 0.25/0.46      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.25/0.46  thf('18', plain,
% 0.25/0.46      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.25/0.46        | (v1_xboole_0 @ sk_C_1)
% 0.25/0.46        | ~ (v1_relat_1 @ sk_C_1))),
% 0.25/0.46      inference('sup-', [status(thm)], ['16', '17'])).
% 0.25/0.46  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.25/0.46  thf('19', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.25/0.46      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.25/0.46  thf('20', plain,
% 0.25/0.46      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.25/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.46  thf(cc1_relset_1, axiom,
% 0.25/0.46    (![A:$i,B:$i,C:$i]:
% 0.25/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.25/0.46       ( v1_relat_1 @ C ) ))).
% 0.25/0.46  thf('21', plain,
% 0.25/0.46      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.25/0.46         ((v1_relat_1 @ X5)
% 0.25/0.46          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.25/0.46      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.25/0.46  thf('22', plain, ((v1_relat_1 @ sk_C_1)),
% 0.25/0.46      inference('sup-', [status(thm)], ['20', '21'])).
% 0.25/0.46  thf('23', plain, ((v1_xboole_0 @ sk_C_1)),
% 0.25/0.46      inference('demod', [status(thm)], ['18', '19', '22'])).
% 0.25/0.46  thf(fc10_relat_1, axiom,
% 0.25/0.46    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 0.25/0.46  thf('24', plain,
% 0.25/0.46      (![X3 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X3)) | ~ (v1_xboole_0 @ X3))),
% 0.25/0.46      inference('cnf', [status(esa)], [fc10_relat_1])).
% 0.25/0.46  thf(l13_xboole_0, axiom,
% 0.25/0.46    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.25/0.46  thf('25', plain,
% 0.25/0.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.25/0.46      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.25/0.46  thf('26', plain,
% 0.25/0.46      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 0.25/0.46      inference('sup-', [status(thm)], ['24', '25'])).
% 0.25/0.46  thf('27', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.25/0.46      inference('sup-', [status(thm)], ['23', '26'])).
% 0.25/0.46  thf('28', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) != (k1_xboole_0))),
% 0.25/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.46  thf('29', plain,
% 0.25/0.46      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.25/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.46  thf(redefinition_k1_relset_1, axiom,
% 0.25/0.46    (![A:$i,B:$i,C:$i]:
% 0.25/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.25/0.46       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.25/0.46  thf('30', plain,
% 0.25/0.46      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.25/0.46         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 0.25/0.46          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.25/0.46      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.25/0.46  thf('31', plain,
% 0.25/0.46      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.25/0.46      inference('sup-', [status(thm)], ['29', '30'])).
% 0.25/0.46  thf('32', plain, (((k1_relat_1 @ sk_C_1) != (k1_xboole_0))),
% 0.25/0.46      inference('demod', [status(thm)], ['28', '31'])).
% 0.25/0.46  thf('33', plain, ($false),
% 0.25/0.46      inference('simplify_reflect-', [status(thm)], ['27', '32'])).
% 0.25/0.46  
% 0.25/0.46  % SZS output end Refutation
% 0.25/0.46  
% 0.25/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
