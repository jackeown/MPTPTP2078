%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HcQ9jTjC0X

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 237 expanded)
%              Number of leaves         :   25 (  80 expanded)
%              Depth                    :   12
%              Number of atoms          :  359 (3582 expanded)
%              Number of equality atoms :   26 ( 232 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

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

thf('1',plain,
    ( ( k1_funct_1 @ sk_B @ sk_C )
    = ( k1_funct_1 @ sk_B @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ C @ A @ B )
        & ( v1_funct_1 @ C ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( v2_funct_1 @ C )
        <=> ! [D: $i,E: $i] :
              ( ( ( ( k1_funct_1 @ C @ D )
                  = ( k1_funct_1 @ C @ E ) )
                & ( r2_hidden @ E @ A )
                & ( r2_hidden @ D @ A ) )
             => ( D = E ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_1 @ E @ D @ C @ A )
    <=> ( ( r2_hidden @ D @ A )
        & ( r2_hidden @ E @ A )
        & ( ( k1_funct_1 @ C @ D )
          = ( k1_funct_1 @ C @ E ) ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X4: $i,X5: $i,X6: $i] :
      ( ( zip_tseitin_1 @ X4 @ X2 @ X5 @ X6 )
      | ( ( k1_funct_1 @ X5 @ X2 )
       != ( k1_funct_1 @ X5 @ X4 ) )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ sk_B @ sk_C )
       != ( k1_funct_1 @ sk_B @ X0 ) )
      | ~ ( r2_hidden @ sk_D_1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( zip_tseitin_1 @ X0 @ sk_D_1 @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_C @ sk_D_1 @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_C @ X0 )
      | ~ ( r2_hidden @ sk_D_1 @ X0 ) ) ),
    inference(eq_res,[status(thm)],['3'])).

thf('5',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ sk_A )
    | ( zip_tseitin_1 @ sk_C @ sk_D_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    r2_hidden @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    zip_tseitin_1 @ sk_C @ sk_D_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['5','6'])).

thf(zf_stmt_2,axiom,(
    ! [C: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ A )
     => ( ( v2_funct_1 @ C )
      <=> ! [D: $i,E: $i] :
            ( ( zip_tseitin_1 @ E @ D @ C @ A )
           => ( D = E ) ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( X10 = X9 )
      | ~ ( zip_tseitin_1 @ X9 @ X10 @ X8 @ X7 )
      | ~ ( zip_tseitin_2 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,
    ( ~ ( zip_tseitin_2 @ sk_B @ sk_A )
    | ( sk_D_1 = sk_C )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( zip_tseitin_2 @ sk_B @ sk_A )
    | ( sk_D_1 = sk_C ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    sk_C != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ~ ( zip_tseitin_2 @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf(zf_stmt_3,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_4,type,(
    zip_tseitin_2: $i > $i > $o )).

thf(zf_stmt_5,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( zip_tseitin_0 @ B @ A )
       => ( zip_tseitin_2 @ C @ A ) ) ) )).

thf('16',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( zip_tseitin_0 @ X11 @ X12 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_funct_2 @ X13 @ X12 @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X11 ) ) )
      | ( zip_tseitin_2 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('17',plain,
    ( ( zip_tseitin_2 @ sk_B @ sk_A )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( zip_tseitin_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    ~ ( zip_tseitin_2 @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('23',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( zip_tseitin_2 @ sk_B @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','23'])).

thf('25',plain,
    ( ( zip_tseitin_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('26',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('27',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('28',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('30',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    zip_tseitin_2 @ sk_B @ k1_xboole_0 ),
    inference(demod,[status(thm)],['25','26','27','28','30'])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['24','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HcQ9jTjC0X
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:20:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 37 iterations in 0.019s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $o).
% 0.21/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.48  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.48  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.48  thf(t85_funct_2, conjecture,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.48         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.48       ( ( v2_funct_1 @ B ) =>
% 0.21/0.48         ( ![C:$i,D:$i]:
% 0.21/0.48           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.21/0.48               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.21/0.48             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i]:
% 0.21/0.48        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.48            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.48          ( ( v2_funct_1 @ B ) =>
% 0.21/0.48            ( ![C:$i,D:$i]:
% 0.21/0.48              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.21/0.48                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.21/0.48                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t85_funct_2])).
% 0.21/0.48  thf('0', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (((k1_funct_1 @ sk_B @ sk_C) = (k1_funct_1 @ sk_B @ sk_D_1))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t25_funct_2, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.48         ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.48       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.48         ( ( v2_funct_1 @ C ) <=>
% 0.21/0.48           ( ![D:$i,E:$i]:
% 0.21/0.48             ( ( ( ( k1_funct_1 @ C @ D ) = ( k1_funct_1 @ C @ E ) ) & 
% 0.21/0.48                 ( r2_hidden @ E @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.21/0.48               ( ( D ) = ( E ) ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_1, axiom,
% 0.21/0.48    (![E:$i,D:$i,C:$i,A:$i]:
% 0.21/0.48     ( ( zip_tseitin_1 @ E @ D @ C @ A ) <=>
% 0.21/0.48       ( ( r2_hidden @ D @ A ) & ( r2_hidden @ E @ A ) & 
% 0.21/0.48         ( ( k1_funct_1 @ C @ D ) = ( k1_funct_1 @ C @ E ) ) ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X2 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.48         ((zip_tseitin_1 @ X4 @ X2 @ X5 @ X6)
% 0.21/0.48          | ((k1_funct_1 @ X5 @ X2) != (k1_funct_1 @ X5 @ X4))
% 0.21/0.48          | ~ (r2_hidden @ X4 @ X6)
% 0.21/0.48          | ~ (r2_hidden @ X2 @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((k1_funct_1 @ sk_B @ sk_C) != (k1_funct_1 @ sk_B @ X0))
% 0.21/0.48          | ~ (r2_hidden @ sk_D_1 @ X1)
% 0.21/0.48          | ~ (r2_hidden @ X0 @ X1)
% 0.21/0.48          | (zip_tseitin_1 @ X0 @ sk_D_1 @ sk_B @ X1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((zip_tseitin_1 @ sk_C @ sk_D_1 @ sk_B @ X0)
% 0.21/0.48          | ~ (r2_hidden @ sk_C @ X0)
% 0.21/0.48          | ~ (r2_hidden @ sk_D_1 @ X0))),
% 0.21/0.48      inference('eq_res', [status(thm)], ['3'])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      ((~ (r2_hidden @ sk_D_1 @ sk_A)
% 0.21/0.48        | (zip_tseitin_1 @ sk_C @ sk_D_1 @ sk_B @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '4'])).
% 0.21/0.48  thf('6', plain, ((r2_hidden @ sk_D_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('7', plain, ((zip_tseitin_1 @ sk_C @ sk_D_1 @ sk_B @ sk_A)),
% 0.21/0.48      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.48  thf(zf_stmt_2, axiom,
% 0.21/0.48    (![C:$i,A:$i]:
% 0.21/0.48     ( ( zip_tseitin_2 @ C @ A ) =>
% 0.21/0.48       ( ( v2_funct_1 @ C ) <=>
% 0.21/0.48         ( ![D:$i,E:$i]:
% 0.21/0.48           ( ( zip_tseitin_1 @ E @ D @ C @ A ) => ( ( D ) = ( E ) ) ) ) ) ))).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.48         (~ (v2_funct_1 @ X8)
% 0.21/0.48          | ((X10) = (X9))
% 0.21/0.48          | ~ (zip_tseitin_1 @ X9 @ X10 @ X8 @ X7)
% 0.21/0.48          | ~ (zip_tseitin_2 @ X8 @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      ((~ (zip_tseitin_2 @ sk_B @ sk_A)
% 0.21/0.48        | ((sk_D_1) = (sk_C))
% 0.21/0.48        | ~ (v2_funct_1 @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.48  thf('10', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('11', plain, ((~ (zip_tseitin_2 @ sk_B @ sk_A) | ((sk_D_1) = (sk_C)))),
% 0.21/0.48      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.48  thf('12', plain, (((sk_C) != (sk_D_1))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('13', plain, (~ (zip_tseitin_2 @ sk_B @ sk_A)),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.21/0.48  thf(zf_stmt_3, axiom,
% 0.21/0.48    (![B:$i,A:$i]:
% 0.21/0.48     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.48       ( zip_tseitin_0 @ B @ A ) ))).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((zip_tseitin_0 @ X0 @ X1) | ((X0) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(zf_stmt_4, type, zip_tseitin_2 : $i > $i > $o).
% 0.21/0.48  thf(zf_stmt_5, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.21/0.48  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $o).
% 0.21/0.48  thf(zf_stmt_7, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.48       ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_2 @ C @ A ) ) ))).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.48         (~ (zip_tseitin_0 @ X11 @ X12)
% 0.21/0.48          | ~ (v1_funct_1 @ X13)
% 0.21/0.48          | ~ (v1_funct_2 @ X13 @ X12 @ X11)
% 0.21/0.48          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X11)))
% 0.21/0.48          | (zip_tseitin_2 @ X13 @ X12))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (((zip_tseitin_2 @ sk_B @ sk_A)
% 0.21/0.48        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.48        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.48        | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.48  thf('18', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('19', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (((zip_tseitin_2 @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_2 @ sk_B @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['14', '20'])).
% 0.21/0.48  thf('22', plain, (~ (zip_tseitin_2 @ sk_B @ sk_A)),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.21/0.48  thf('23', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.48  thf('24', plain, (~ (zip_tseitin_2 @ sk_B @ k1_xboole_0)),
% 0.21/0.48      inference('demod', [status(thm)], ['13', '23'])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (((zip_tseitin_2 @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.21/0.48  thf('26', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.48  thf('27', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.48  thf('28', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((zip_tseitin_0 @ X0 @ X1) | ((X1) != (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.48  thf('30', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ k1_xboole_0)),
% 0.21/0.48      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.48  thf('31', plain, ((zip_tseitin_2 @ sk_B @ k1_xboole_0)),
% 0.21/0.48      inference('demod', [status(thm)], ['25', '26', '27', '28', '30'])).
% 0.21/0.48  thf('32', plain, ($false), inference('demod', [status(thm)], ['24', '31'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
