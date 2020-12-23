%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sQFozSpF0j

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 168 expanded)
%              Number of leaves         :   24 (  60 expanded)
%              Depth                    :   16
%              Number of atoms          :  464 (2676 expanded)
%              Number of equality atoms :   42 ( 197 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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

thf('0',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( X15 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ X16 ) @ ( k1_funct_1 @ X16 @ X13 ) )
        = X13 )
      | ~ ( v2_funct_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t32_funct_2])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6','7','8'])).

thf('10',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_1 ) )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6','7','8'])).

thf('13',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_D ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_1 ) )
      = sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_C_1 = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf('17',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    sk_C_1 != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf('20',plain,(
    r2_hidden @ sk_C_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['1','19'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('24',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_C_1 @ X0 ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf(d8_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
      <=> ! [B: $i,C: $i] :
            ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
              & ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
              & ( ( k1_funct_1 @ A @ B )
                = ( k1_funct_1 @ A @ C ) ) )
           => ( B = C ) ) ) ) )).

thf('27',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X7 ) )
      | ( ( k1_funct_1 @ X7 @ X8 )
       != ( k1_funct_1 @ X7 @ X9 ) )
      | ( X8 = X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( sk_C_1 = X1 )
      | ( ( k1_funct_1 @ X0 @ sk_C_1 )
       != ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
     != ( k1_funct_1 @ sk_B_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ sk_B_1 )
    | ~ ( r2_hidden @ sk_D @ ( k1_relat_1 @ sk_B_1 ) )
    | ( sk_C_1 = sk_D )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','28'])).

thf('30',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf('33',plain,(
    r2_hidden @ sk_D @ k1_xboole_0 ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_D @ X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('38',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('39',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
     != ( k1_funct_1 @ sk_B_1 @ sk_C_1 ) )
    | ( sk_C_1 = sk_D ) ),
    inference(demod,[status(thm)],['29','30','35','36','39'])).

thf('41',plain,(
    sk_C_1 = sk_D ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    sk_C_1 != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sQFozSpF0j
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:30:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 47 iterations in 0.021s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.49  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.49  thf(t85_funct_2, conjecture,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.49         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.49       ( ( v2_funct_1 @ B ) =>
% 0.21/0.49         ( ![C:$i,D:$i]:
% 0.21/0.49           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.21/0.49               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.21/0.49             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i]:
% 0.21/0.49        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.49            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.49          ( ( v2_funct_1 @ B ) =>
% 0.21/0.49            ( ![C:$i,D:$i]:
% 0.21/0.49              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.21/0.49                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.21/0.49                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t85_funct_2])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('2', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t32_funct_2, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.49       ( ( ( v2_funct_1 @ D ) & ( r2_hidden @ C @ A ) ) =>
% 0.21/0.49         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.49           ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) ) =
% 0.21/0.49             ( C ) ) ) ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X13 @ X14)
% 0.21/0.49          | ((X15) = (k1_xboole_0))
% 0.21/0.49          | ~ (v1_funct_1 @ X16)
% 0.21/0.49          | ~ (v1_funct_2 @ X16 @ X14 @ X15)
% 0.21/0.49          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.21/0.49          | ((k1_funct_1 @ (k2_funct_1 @ X16) @ (k1_funct_1 @ X16 @ X13))
% 0.21/0.49              = (X13))
% 0.21/0.49          | ~ (v2_funct_1 @ X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [t32_funct_2])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v2_funct_1 @ sk_B_1)
% 0.21/0.49          | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.21/0.49              = (X0))
% 0.21/0.49          | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.21/0.49          | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.49          | ((sk_A) = (k1_xboole_0))
% 0.21/0.49          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf('6', plain, ((v2_funct_1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('7', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('8', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.21/0.49            = (X0))
% 0.21/0.49          | ((sk_A) = (k1_xboole_0))
% 0.21/0.49          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['5', '6', '7', '8'])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      ((((sk_A) = (k1_xboole_0))
% 0.21/0.49        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_1))
% 0.21/0.49            = (sk_C_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '9'])).
% 0.21/0.49  thf('11', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.21/0.49            = (X0))
% 0.21/0.49          | ((sk_A) = (k1_xboole_0))
% 0.21/0.49          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['5', '6', '7', '8'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      ((((sk_A) = (k1_xboole_0))
% 0.21/0.49        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_D))
% 0.21/0.49            = (sk_D)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      ((((sk_A) = (k1_xboole_0))
% 0.21/0.49        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_1))
% 0.21/0.49            = (sk_D)))),
% 0.21/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      ((((sk_C_1) = (sk_D))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['10', '15'])).
% 0.21/0.49  thf('17', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C_1) = (sk_D)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.49  thf('18', plain, (((sk_C_1) != (sk_D))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('19', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.21/0.49  thf('20', plain, ((r2_hidden @ sk_C_1 @ k1_xboole_0)),
% 0.21/0.49      inference('demod', [status(thm)], ['1', '19'])).
% 0.21/0.49  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.49  thf('21', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.49      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.49  thf(t3_subset, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X4 : $i, X6 : $i]:
% 0.21/0.49         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.49  thf(l3_subset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X1 @ X2)
% 0.21/0.49          | (r2_hidden @ X1 @ X3)
% 0.21/0.49          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.21/0.49      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.49  thf('26', plain, (![X0 : $i]: (r2_hidden @ sk_C_1 @ X0)),
% 0.21/0.49      inference('sup-', [status(thm)], ['20', '25'])).
% 0.21/0.49  thf(d8_funct_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.49       ( ( v2_funct_1 @ A ) <=>
% 0.21/0.49         ( ![B:$i,C:$i]:
% 0.21/0.49           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.49               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.49               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.21/0.49             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         (~ (v2_funct_1 @ X7)
% 0.21/0.49          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ X7))
% 0.21/0.49          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ X7))
% 0.21/0.49          | ((k1_funct_1 @ X7 @ X8) != (k1_funct_1 @ X7 @ X9))
% 0.21/0.49          | ((X8) = (X9))
% 0.21/0.49          | ~ (v1_funct_1 @ X7)
% 0.21/0.49          | ~ (v1_relat_1 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ((sk_C_1) = (X1))
% 0.21/0.49          | ((k1_funct_1 @ X0 @ sk_C_1) != (k1_funct_1 @ X0 @ X1))
% 0.21/0.49          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.21/0.49          | ~ (v2_funct_1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) != (k1_funct_1 @ sk_B_1 @ sk_C_1))
% 0.21/0.49        | ~ (v2_funct_1 @ sk_B_1)
% 0.21/0.49        | ~ (r2_hidden @ sk_D @ (k1_relat_1 @ sk_B_1))
% 0.21/0.49        | ((sk_C_1) = (sk_D))
% 0.21/0.49        | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.49        | ~ (v1_relat_1 @ sk_B_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '28'])).
% 0.21/0.49  thf('30', plain, ((v2_funct_1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('31', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('32', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.21/0.49  thf('33', plain, ((r2_hidden @ sk_D @ k1_xboole_0)),
% 0.21/0.49      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.49  thf('35', plain, (![X0 : $i]: (r2_hidden @ sk_D @ X0)),
% 0.21/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.49  thf('36', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(cc1_relset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.49       ( v1_relat_1 @ C ) ))).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.49         ((v1_relat_1 @ X10)
% 0.21/0.49          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.21/0.49      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.49  thf('39', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.49      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) != (k1_funct_1 @ sk_B_1 @ sk_C_1))
% 0.21/0.49        | ((sk_C_1) = (sk_D)))),
% 0.21/0.49      inference('demod', [status(thm)], ['29', '30', '35', '36', '39'])).
% 0.21/0.49  thf('41', plain, (((sk_C_1) = (sk_D))),
% 0.21/0.49      inference('simplify', [status(thm)], ['40'])).
% 0.21/0.49  thf('42', plain, (((sk_C_1) != (sk_D))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('43', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
