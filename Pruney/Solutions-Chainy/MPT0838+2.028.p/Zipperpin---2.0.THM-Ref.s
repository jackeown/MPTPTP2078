%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A9iz9kf7jp

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 (  84 expanded)
%              Number of leaves         :   23 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :  361 ( 884 expanded)
%              Number of equality atoms :   32 (  54 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('3',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X6 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('7',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('10',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','10'])).

thf(t10_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ~ ( ( B != k1_xboole_0 )
          & ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ~ ( r2_hidden @ C @ B ) ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('13',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X15: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X15 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('16',plain,(
    ! [X15: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X15 @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X0 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('20',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['17','20'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('22',plain,(
    ! [X2: $i] :
      ( ( ( k2_relat_1 @ X2 )
       != k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('23',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('25',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('26',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['27'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('29',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('30',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['4','28','29'])).

thf('31',plain,(
    $false ),
    inference(simplify,[status(thm)],['30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A9iz9kf7jp
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:07:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 26 iterations in 0.015s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.46  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.46  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.46  thf(t49_relset_1, conjecture,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.46       ( ![B:$i]:
% 0.21/0.46         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.46           ( ![C:$i]:
% 0.21/0.46             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.46               ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.46                    ( ![D:$i]:
% 0.21/0.46                      ( ( m1_subset_1 @ D @ B ) =>
% 0.21/0.46                        ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i]:
% 0.21/0.46        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.46          ( ![B:$i]:
% 0.21/0.46            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.46              ( ![C:$i]:
% 0.21/0.46                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.46                  ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.46                       ( ![D:$i]:
% 0.21/0.46                         ( ( m1_subset_1 @ D @ B ) =>
% 0.21/0.46                           ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t49_relset_1])).
% 0.21/0.46  thf('0', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) != (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.46       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.46         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.21/0.46          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.21/0.46      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.21/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.46  thf('4', plain, (((k1_relat_1 @ sk_C_1) != (k1_xboole_0))),
% 0.21/0.46      inference('demod', [status(thm)], ['0', '3'])).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(dt_k2_relset_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.46       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.46         ((m1_subset_1 @ (k2_relset_1 @ X6 @ X7 @ X8) @ (k1_zfmisc_1 @ X7))
% 0.21/0.46          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.21/0.46      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.21/0.46        (k1_zfmisc_1 @ sk_B))),
% 0.21/0.46      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.46  thf('8', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.46       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.46         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.21/0.46          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.21/0.46      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.21/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      ((m1_subset_1 @ (k2_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.21/0.46      inference('demod', [status(thm)], ['7', '10'])).
% 0.21/0.46  thf(t10_subset_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.46       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.46            ( ![C:$i]:
% 0.21/0.46              ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.46  thf('12', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         ((r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.21/0.46          | ((X0) = (k1_xboole_0))
% 0.21/0.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t10_subset_1])).
% 0.21/0.46  thf('13', plain,
% 0.21/0.46      ((((k2_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.21/0.46        | (r2_hidden @ (sk_C @ (k2_relat_1 @ sk_C_1) @ sk_B) @ 
% 0.21/0.46           (k2_relat_1 @ sk_C_1)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.46  thf('14', plain,
% 0.21/0.46      (![X15 : $i]:
% 0.21/0.46         (~ (r2_hidden @ X15 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 0.21/0.46          | ~ (m1_subset_1 @ X15 @ sk_B))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('15', plain,
% 0.21/0.46      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.21/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.46  thf('16', plain,
% 0.21/0.46      (![X15 : $i]:
% 0.21/0.46         (~ (r2_hidden @ X15 @ (k2_relat_1 @ sk_C_1))
% 0.21/0.46          | ~ (m1_subset_1 @ X15 @ sk_B))),
% 0.21/0.46      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.46  thf('17', plain,
% 0.21/0.46      ((((k2_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.21/0.46        | ~ (m1_subset_1 @ (sk_C @ (k2_relat_1 @ sk_C_1) @ sk_B) @ sk_B))),
% 0.21/0.46      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.46  thf('18', plain,
% 0.21/0.46      ((m1_subset_1 @ (k2_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.21/0.46      inference('demod', [status(thm)], ['7', '10'])).
% 0.21/0.46  thf('19', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         ((m1_subset_1 @ (sk_C @ X0 @ X1) @ X1)
% 0.21/0.46          | ((X0) = (k1_xboole_0))
% 0.21/0.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t10_subset_1])).
% 0.21/0.46  thf('20', plain,
% 0.21/0.46      ((((k2_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.21/0.46        | (m1_subset_1 @ (sk_C @ (k2_relat_1 @ sk_C_1) @ sk_B) @ sk_B))),
% 0.21/0.46      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.46  thf('21', plain, (((k2_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.21/0.46      inference('clc', [status(thm)], ['17', '20'])).
% 0.21/0.46  thf(t64_relat_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( v1_relat_1 @ A ) =>
% 0.21/0.46       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.46           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.46         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.46  thf('22', plain,
% 0.21/0.46      (![X2 : $i]:
% 0.21/0.46         (((k2_relat_1 @ X2) != (k1_xboole_0))
% 0.21/0.46          | ((X2) = (k1_xboole_0))
% 0.21/0.46          | ~ (v1_relat_1 @ X2))),
% 0.21/0.46      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.46  thf('23', plain,
% 0.21/0.46      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.46        | ~ (v1_relat_1 @ sk_C_1)
% 0.21/0.46        | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.46  thf('24', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(cc1_relset_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.46       ( v1_relat_1 @ C ) ))).
% 0.21/0.46  thf('25', plain,
% 0.21/0.46      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.46         ((v1_relat_1 @ X3)
% 0.21/0.46          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.21/0.46      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.46  thf('26', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.46      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.46  thf('27', plain,
% 0.21/0.46      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.46      inference('demod', [status(thm)], ['23', '26'])).
% 0.21/0.46  thf('28', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.21/0.46      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.46  thf(t60_relat_1, axiom,
% 0.21/0.46    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.46     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.46  thf('29', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.46  thf('30', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.46      inference('demod', [status(thm)], ['4', '28', '29'])).
% 0.21/0.46  thf('31', plain, ($false), inference('simplify', [status(thm)], ['30'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
