%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.430eDfN473

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 110 expanded)
%              Number of leaves         :   10 (  35 expanded)
%              Depth                    :   15
%              Number of atoms          :  390 (1631 expanded)
%              Number of equality atoms :   18 (  77 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t52_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ~ ( r2_hidden @ D @ B )
                <=> ( r2_hidden @ D @ C ) ) )
           => ( B
              = ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ! [D: $i] :
                  ( ( m1_subset_1 @ D @ A )
                 => ( ~ ( r2_hidden @ D @ B )
                  <=> ( r2_hidden @ D @ C ) ) )
             => ( B
                = ( k3_subset_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t51_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                <=> ~ ( r2_hidden @ D @ C ) ) )
           => ( B
              = ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( X2
        = ( k3_subset_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ X2 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t51_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D @ sk_C @ X0 @ sk_A ) @ sk_A )
      | ( X0
        = ( k3_subset_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_B
      = ( k3_subset_1 @ sk_A @ sk_C ) )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    sk_B
 != ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X3: $i] :
      ( ( r2_hidden @ X3 @ sk_B )
      | ( r2_hidden @ X3 @ sk_C )
      | ~ ( m1_subset_1 @ X3 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( X2
        = ( k3_subset_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t51_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_C @ X0 @ sk_A ) @ sk_C )
      | ( r2_hidden @ ( sk_D @ sk_C @ X0 @ sk_A ) @ X0 )
      | ( X0
        = ( k3_subset_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( sk_B
      = ( k3_subset_1 @ sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( sk_B
      = ( k3_subset_1 @ sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_B
      = ( k3_subset_1 @ sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    sk_B
 != ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( X2
        = ( k3_subset_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t51_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ sk_C @ X0 @ sk_A ) @ sk_C )
      | ~ ( r2_hidden @ ( sk_D @ sk_C @ X0 @ sk_A ) @ X0 )
      | ( X0
        = ( k3_subset_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B
      = ( k3_subset_1 @ sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( sk_B
      = ( k3_subset_1 @ sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    sk_B
 != ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X3: $i] :
      ( ~ ( r2_hidden @ X3 @ sk_C )
      | ~ ( r2_hidden @ X3 @ sk_B )
      | ~ ( m1_subset_1 @ X3 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('29',plain,(
    r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['27','28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.430eDfN473
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:45:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 31 iterations in 0.013s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.46  thf(t52_subset_1, conjecture,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.46       ( ![C:$i]:
% 0.21/0.46         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.46           ( ( ![D:$i]:
% 0.21/0.46               ( ( m1_subset_1 @ D @ A ) =>
% 0.21/0.46                 ( ( ~( r2_hidden @ D @ B ) ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.21/0.46             ( ( B ) = ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i]:
% 0.21/0.46        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.46          ( ![C:$i]:
% 0.21/0.46            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.46              ( ( ![D:$i]:
% 0.21/0.46                  ( ( m1_subset_1 @ D @ A ) =>
% 0.21/0.46                    ( ( ~( r2_hidden @ D @ B ) ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.21/0.46                ( ( B ) = ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t52_subset_1])).
% 0.21/0.46  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('1', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t51_subset_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.46       ( ![C:$i]:
% 0.21/0.46         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.46           ( ( ![D:$i]:
% 0.21/0.46               ( ( m1_subset_1 @ D @ A ) =>
% 0.21/0.46                 ( ( r2_hidden @ D @ B ) <=> ( ~( r2_hidden @ D @ C ) ) ) ) ) =>
% 0.21/0.46             ( ( B ) = ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.21/0.46          | ((X2) = (k3_subset_1 @ X1 @ X0))
% 0.21/0.46          | (m1_subset_1 @ (sk_D @ X0 @ X2 @ X1) @ X1)
% 0.21/0.46          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t51_subset_1])).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.46          | (m1_subset_1 @ (sk_D @ sk_C @ X0 @ sk_A) @ sk_A)
% 0.21/0.46          | ((X0) = (k3_subset_1 @ sk_A @ sk_C)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      ((((sk_B) = (k3_subset_1 @ sk_A @ sk_C))
% 0.21/0.46        | (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.46  thf('5', plain, (((sk_B) != (k3_subset_1 @ sk_A @ sk_C))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('6', plain, ((m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X3 : $i]:
% 0.21/0.46         ((r2_hidden @ X3 @ sk_B)
% 0.21/0.46          | (r2_hidden @ X3 @ sk_C)
% 0.21/0.46          | ~ (m1_subset_1 @ X3 @ sk_A))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('8', plain,
% 0.21/0.46      (((r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.21/0.46        | (r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.21/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf('9', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.21/0.46          | ((X2) = (k3_subset_1 @ X1 @ X0))
% 0.21/0.46          | (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X2)
% 0.21/0.46          | ~ (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X0)
% 0.21/0.46          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t51_subset_1])).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.46          | ~ (r2_hidden @ (sk_D @ sk_C @ X0 @ sk_A) @ sk_C)
% 0.21/0.46          | (r2_hidden @ (sk_D @ sk_C @ X0 @ sk_A) @ X0)
% 0.21/0.46          | ((X0) = (k3_subset_1 @ sk_A @ sk_C)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.46  thf('12', plain,
% 0.21/0.46      (((r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.21/0.46        | ((sk_B) = (k3_subset_1 @ sk_A @ sk_C))
% 0.21/0.46        | (r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.21/0.46        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['8', '11'])).
% 0.21/0.46  thf('13', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('14', plain,
% 0.21/0.46      (((r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.21/0.46        | ((sk_B) = (k3_subset_1 @ sk_A @ sk_C))
% 0.21/0.46        | (r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.21/0.46      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.46  thf('15', plain,
% 0.21/0.46      ((((sk_B) = (k3_subset_1 @ sk_A @ sk_C))
% 0.21/0.46        | (r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.21/0.46      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.46  thf('16', plain, (((sk_B) != (k3_subset_1 @ sk_A @ sk_C))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('17', plain, ((r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.21/0.46  thf('18', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('19', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.21/0.46          | ((X2) = (k3_subset_1 @ X1 @ X0))
% 0.21/0.46          | ~ (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X2)
% 0.21/0.46          | (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X0)
% 0.21/0.46          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t51_subset_1])).
% 0.21/0.46  thf('20', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.46          | (r2_hidden @ (sk_D @ sk_C @ X0 @ sk_A) @ sk_C)
% 0.21/0.46          | ~ (r2_hidden @ (sk_D @ sk_C @ X0 @ sk_A) @ X0)
% 0.21/0.46          | ((X0) = (k3_subset_1 @ sk_A @ sk_C)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.46  thf('21', plain,
% 0.21/0.46      ((((sk_B) = (k3_subset_1 @ sk_A @ sk_C))
% 0.21/0.46        | (r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.21/0.46        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['17', '20'])).
% 0.21/0.46  thf('22', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('23', plain,
% 0.21/0.46      ((((sk_B) = (k3_subset_1 @ sk_A @ sk_C))
% 0.21/0.46        | (r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_C))),
% 0.21/0.46      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.46  thf('24', plain, (((sk_B) != (k3_subset_1 @ sk_A @ sk_C))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('25', plain, ((r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.21/0.46  thf('26', plain,
% 0.21/0.46      (![X3 : $i]:
% 0.21/0.46         (~ (r2_hidden @ X3 @ sk_C)
% 0.21/0.46          | ~ (r2_hidden @ X3 @ sk_B)
% 0.21/0.46          | ~ (m1_subset_1 @ X3 @ sk_A))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('27', plain,
% 0.21/0.46      ((~ (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.21/0.46        | ~ (r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.21/0.46      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.46  thf('28', plain, ((m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.21/0.46  thf('29', plain, ((r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.21/0.46  thf('30', plain, ($false),
% 0.21/0.46      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
