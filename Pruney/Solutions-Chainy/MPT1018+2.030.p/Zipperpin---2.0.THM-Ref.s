%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pFFgtb17Hl

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   46 (  77 expanded)
%              Number of leaves         :   20 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :  291 (1103 expanded)
%              Number of equality atoms :   28 (  82 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t85_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v2_funct_1 @ B )
       => ! [C: $i,D: $i] :
            ( ( ( r2_hidden @ C @ A )
              & ( r2_hidden @ D @ A )
              & ( ( k1_funct_1 @ B @ C )
                = ( k1_funct_1 @ B @ D ) ) )
           => ( C = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( v2_funct_1 @ B )
         => ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A )
                & ( ( k1_funct_1 @ B @ C )
                  = ( k1_funct_1 @ B @ D ) ) )
             => ( C = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t85_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('2',plain,(
    ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ D )
          & ( r2_hidden @ C @ A ) )
       => ( ( B = k1_xboole_0 )
          | ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) )
            = C ) ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( X11 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ X12 ) @ ( k1_funct_1 @ X12 @ X9 ) )
        = X9 )
      | ~ ( v2_funct_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t32_funct_2])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ sk_B )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('11',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('14',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_D ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k1_funct_1 @ sk_B @ sk_C )
    = ( k1_funct_1 @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_C ) )
      = sk_D ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_C = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','16'])).

thf('18',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C = sk_D ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    sk_C != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['2','20','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pFFgtb17Hl
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:20:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 25 iterations in 0.015s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.48  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.22/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(t85_funct_2, conjecture,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.48         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.48       ( ( v2_funct_1 @ B ) =>
% 0.22/0.48         ( ![C:$i,D:$i]:
% 0.22/0.48           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.22/0.48               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.22/0.48             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i,B:$i]:
% 0.22/0.48        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.48            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.48          ( ( v2_funct_1 @ B ) =>
% 0.22/0.48            ( ![C:$i,D:$i]:
% 0.22/0.48              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.22/0.48                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.22/0.48                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t85_funct_2])).
% 0.22/0.48  thf('0', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t7_ordinal1, axiom,
% 0.22/0.48    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      (![X7 : $i, X8 : $i]: (~ (r2_hidden @ X7 @ X8) | ~ (r1_tarski @ X8 @ X7))),
% 0.22/0.48      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.22/0.48  thf('2', plain, (~ (r1_tarski @ sk_A @ sk_C)),
% 0.22/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.48  thf('3', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t32_funct_2, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.48     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.48         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.48       ( ( ( v2_funct_1 @ D ) & ( r2_hidden @ C @ A ) ) =>
% 0.22/0.48         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.22/0.48           ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) ) =
% 0.22/0.48             ( C ) ) ) ) ))).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X9 @ X10)
% 0.22/0.48          | ((X11) = (k1_xboole_0))
% 0.22/0.48          | ~ (v1_funct_1 @ X12)
% 0.22/0.48          | ~ (v1_funct_2 @ X12 @ X10 @ X11)
% 0.22/0.48          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.22/0.48          | ((k1_funct_1 @ (k2_funct_1 @ X12) @ (k1_funct_1 @ X12 @ X9)) = (X9))
% 0.22/0.48          | ~ (v2_funct_1 @ X12))),
% 0.22/0.48      inference('cnf', [status(esa)], [t32_funct_2])).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (v2_funct_1 @ sk_B)
% 0.22/0.48          | ((k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ X0))
% 0.22/0.48              = (X0))
% 0.22/0.48          | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.22/0.48          | ~ (v1_funct_1 @ sk_B)
% 0.22/0.48          | ((sk_A) = (k1_xboole_0))
% 0.22/0.48          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.48  thf('7', plain, ((v2_funct_1 @ sk_B)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('8', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('9', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (((k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ X0)) = (X0))
% 0.22/0.48          | ((sk_A) = (k1_xboole_0))
% 0.22/0.48          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      ((((sk_A) = (k1_xboole_0))
% 0.22/0.48        | ((k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_C))
% 0.22/0.48            = (sk_C)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['3', '10'])).
% 0.22/0.48  thf('12', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('13', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (((k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ X0)) = (X0))
% 0.22/0.48          | ((sk_A) = (k1_xboole_0))
% 0.22/0.48          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.22/0.48  thf('14', plain,
% 0.22/0.48      ((((sk_A) = (k1_xboole_0))
% 0.22/0.48        | ((k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_D))
% 0.22/0.48            = (sk_D)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.48  thf('15', plain, (((k1_funct_1 @ sk_B @ sk_C) = (k1_funct_1 @ sk_B @ sk_D))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('16', plain,
% 0.22/0.48      ((((sk_A) = (k1_xboole_0))
% 0.22/0.48        | ((k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_C))
% 0.22/0.48            = (sk_D)))),
% 0.22/0.48      inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.48  thf('17', plain,
% 0.22/0.48      ((((sk_C) = (sk_D)) | ((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.48      inference('sup+', [status(thm)], ['11', '16'])).
% 0.22/0.48  thf('18', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C) = (sk_D)))),
% 0.22/0.48      inference('simplify', [status(thm)], ['17'])).
% 0.22/0.48  thf('19', plain, (((sk_C) != (sk_D))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('20', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.48      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.22/0.48  thf(t4_subset_1, axiom,
% 0.22/0.48    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.48  thf('21', plain,
% 0.22/0.48      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.48      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.48  thf(t3_subset, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.48  thf('22', plain,
% 0.22/0.48      (![X1 : $i, X2 : $i]:
% 0.22/0.48         ((r1_tarski @ X1 @ X2) | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.48  thf('23', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.48  thf('24', plain, ($false),
% 0.22/0.48      inference('demod', [status(thm)], ['2', '20', '23'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
