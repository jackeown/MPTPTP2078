%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O6b54U1KHW

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:15 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 321 expanded)
%              Number of leaves         :   15 (  96 expanded)
%              Depth                    :   14
%              Number of atoms          :  502 (7334 expanded)
%              Number of equality atoms :   12 (  38 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(t152_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ! [D: $i] :
              ( ( ( v1_funct_1 @ D )
                & ( v1_funct_2 @ D @ A @ A )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
             => ( ( ( r1_partfun1 @ B @ D )
                  & ( r1_partfun1 @ C @ D ) )
               => ( r1_partfun1 @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ! [D: $i] :
                ( ( ( v1_funct_1 @ D )
                  & ( v1_funct_2 @ D @ A @ A )
                  & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
               => ( ( ( r1_partfun1 @ B @ D )
                    & ( r1_partfun1 @ C @ D ) )
                 => ( r1_partfun1 @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t152_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t158_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ! [E: $i] :
              ( ( ( v1_funct_1 @ E )
                & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
             => ( ( ( r1_partfun1 @ C @ E )
                  & ( r1_partfun1 @ D @ E )
                  & ( v1_partfun1 @ E @ A ) )
               => ( r1_partfun1 @ C @ D ) ) ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_funct_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ( r1_partfun1 @ X6 @ X3 )
      | ~ ( r1_partfun1 @ X6 @ X7 )
      | ~ ( r1_partfun1 @ X3 @ X7 )
      | ~ ( v1_partfun1 @ X7 @ X4 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t158_partfun1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_partfun1 @ X1 @ sk_A )
      | ~ ( r1_partfun1 @ sk_C @ X1 )
      | ~ ( r1_partfun1 @ X0 @ X1 )
      | ( r1_partfun1 @ X0 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_partfun1 @ X1 @ sk_A )
      | ~ ( r1_partfun1 @ sk_C @ X1 )
      | ~ ( r1_partfun1 @ X0 @ X1 )
      | ( r1_partfun1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_partfun1 @ sk_B @ sk_C )
      | ~ ( r1_partfun1 @ sk_B @ X0 )
      | ~ ( r1_partfun1 @ sk_C @ X0 )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_partfun1 @ sk_B @ sk_C )
      | ~ ( r1_partfun1 @ sk_B @ X0 )
      | ~ ( r1_partfun1 @ sk_C @ X0 )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_partfun1 @ sk_D @ sk_A )
    | ~ ( r1_partfun1 @ sk_C @ sk_D )
    | ~ ( r1_partfun1 @ sk_B @ sk_D )
    | ( r1_partfun1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r1_partfun1 @ sk_B @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( v1_partfun1 @ sk_D @ sk_A )
    | ( r1_partfun1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('15',plain,(
    ~ ( r1_partfun1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ~ ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t132_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( v1_partfun1 @ C @ A ) ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ( v1_partfun1 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X1 @ X2 @ X0 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_2 @ X1 @ X2 @ X0 )
      | ( v1_partfun1 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_partfun1 @ sk_D @ sk_A )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ~ ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('25',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( v1_partfun1 @ sk_D @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('29',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ( v1_partfun1 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X1 @ X2 @ X0 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_2 @ X1 @ k1_xboole_0 @ X0 )
      | ( v1_partfun1 @ X1 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( v1_partfun1 @ sk_D @ k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('37',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('38',plain,(
    v1_funct_2 @ sk_D @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    v1_partfun1 @ sk_D @ k1_xboole_0 ),
    inference(demod,[status(thm)],['33','34','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['26','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O6b54U1KHW
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:34:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 47 iterations in 0.030s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.19/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.48  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.19/0.48  thf(t152_funct_2, conjecture,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( v1_funct_1 @ B ) & 
% 0.19/0.48         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.19/0.48       ( ![C:$i]:
% 0.19/0.48         ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.48             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.19/0.48           ( ![D:$i]:
% 0.19/0.48             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ A ) & 
% 0.19/0.48                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.19/0.48               ( ( ( r1_partfun1 @ B @ D ) & ( r1_partfun1 @ C @ D ) ) =>
% 0.19/0.48                 ( r1_partfun1 @ B @ C ) ) ) ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i,B:$i]:
% 0.19/0.48        ( ( ( v1_funct_1 @ B ) & 
% 0.19/0.48            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.19/0.48          ( ![C:$i]:
% 0.19/0.48            ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.48                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.19/0.48              ( ![D:$i]:
% 0.19/0.48                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ A ) & 
% 0.19/0.48                    ( m1_subset_1 @
% 0.19/0.48                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.19/0.48                  ( ( ( r1_partfun1 @ B @ D ) & ( r1_partfun1 @ C @ D ) ) =>
% 0.19/0.48                    ( r1_partfun1 @ B @ C ) ) ) ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t152_funct_2])).
% 0.19/0.48  thf('0', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t158_partfun1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.48       ( ![D:$i]:
% 0.19/0.48         ( ( ( v1_funct_1 @ D ) & 
% 0.19/0.48             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.48           ( ![E:$i]:
% 0.19/0.48             ( ( ( v1_funct_1 @ E ) & 
% 0.19/0.48                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.48               ( ( ( r1_partfun1 @ C @ E ) & ( r1_partfun1 @ D @ E ) & 
% 0.19/0.48                   ( v1_partfun1 @ E @ A ) ) =>
% 0.19/0.48                 ( r1_partfun1 @ C @ D ) ) ) ) ) ) ))).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.19/0.48         (~ (v1_funct_1 @ X3)
% 0.19/0.48          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.19/0.48          | (r1_partfun1 @ X6 @ X3)
% 0.19/0.48          | ~ (r1_partfun1 @ X6 @ X7)
% 0.19/0.48          | ~ (r1_partfun1 @ X3 @ X7)
% 0.19/0.48          | ~ (v1_partfun1 @ X7 @ X4)
% 0.19/0.48          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.19/0.48          | ~ (v1_funct_1 @ X7)
% 0.19/0.48          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.19/0.48          | ~ (v1_funct_1 @ X6))),
% 0.19/0.48      inference('cnf', [status(esa)], [t158_partfun1])).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (v1_funct_1 @ X0)
% 0.19/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.19/0.48          | ~ (v1_funct_1 @ X1)
% 0.19/0.48          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.19/0.48          | ~ (v1_partfun1 @ X1 @ sk_A)
% 0.19/0.48          | ~ (r1_partfun1 @ sk_C @ X1)
% 0.19/0.48          | ~ (r1_partfun1 @ X0 @ X1)
% 0.19/0.48          | (r1_partfun1 @ X0 @ sk_C)
% 0.19/0.48          | ~ (v1_funct_1 @ sk_C))),
% 0.19/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.48  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (v1_funct_1 @ X0)
% 0.19/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.19/0.48          | ~ (v1_funct_1 @ X1)
% 0.19/0.48          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.19/0.48          | ~ (v1_partfun1 @ X1 @ sk_A)
% 0.19/0.48          | ~ (r1_partfun1 @ sk_C @ X1)
% 0.19/0.48          | ~ (r1_partfun1 @ X0 @ X1)
% 0.19/0.48          | (r1_partfun1 @ X0 @ sk_C))),
% 0.19/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((r1_partfun1 @ sk_B @ sk_C)
% 0.19/0.48          | ~ (r1_partfun1 @ sk_B @ X0)
% 0.19/0.48          | ~ (r1_partfun1 @ sk_C @ X0)
% 0.19/0.48          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.19/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.19/0.48          | ~ (v1_funct_1 @ X0)
% 0.19/0.48          | ~ (v1_funct_1 @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['1', '6'])).
% 0.19/0.48  thf('8', plain, ((v1_funct_1 @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((r1_partfun1 @ sk_B @ sk_C)
% 0.19/0.48          | ~ (r1_partfun1 @ sk_B @ X0)
% 0.19/0.48          | ~ (r1_partfun1 @ sk_C @ X0)
% 0.19/0.48          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.19/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.19/0.48          | ~ (v1_funct_1 @ X0))),
% 0.19/0.48      inference('demod', [status(thm)], ['7', '8'])).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      ((~ (v1_funct_1 @ sk_D)
% 0.19/0.48        | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.19/0.48        | ~ (r1_partfun1 @ sk_C @ sk_D)
% 0.19/0.48        | ~ (r1_partfun1 @ sk_B @ sk_D)
% 0.19/0.48        | (r1_partfun1 @ sk_B @ sk_C))),
% 0.19/0.48      inference('sup-', [status(thm)], ['0', '9'])).
% 0.19/0.48  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('12', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('13', plain, ((r1_partfun1 @ sk_B @ sk_D)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      ((~ (v1_partfun1 @ sk_D @ sk_A) | (r1_partfun1 @ sk_B @ sk_C))),
% 0.19/0.48      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.19/0.48  thf('15', plain, (~ (r1_partfun1 @ sk_B @ sk_C)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('16', plain, (~ (v1_partfun1 @ sk_D @ sk_A)),
% 0.19/0.48      inference('clc', [status(thm)], ['14', '15'])).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t132_funct_2, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.48       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.48           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.48         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.19/0.48           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.48         (((X0) = (k1_xboole_0))
% 0.19/0.48          | ~ (v1_funct_1 @ X1)
% 0.19/0.48          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.19/0.48          | (v1_partfun1 @ X1 @ X2)
% 0.19/0.48          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.19/0.48          | ~ (v1_funct_2 @ X1 @ X2 @ X0)
% 0.19/0.48          | ~ (v1_funct_1 @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.48         (~ (v1_funct_2 @ X1 @ X2 @ X0)
% 0.19/0.48          | (v1_partfun1 @ X1 @ X2)
% 0.19/0.48          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.19/0.48          | ~ (v1_funct_1 @ X1)
% 0.19/0.48          | ((X0) = (k1_xboole_0)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['18'])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      ((((sk_A) = (k1_xboole_0))
% 0.19/0.48        | ~ (v1_funct_1 @ sk_D)
% 0.19/0.48        | (v1_partfun1 @ sk_D @ sk_A)
% 0.19/0.48        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['17', '19'])).
% 0.19/0.48  thf('21', plain, ((v1_funct_1 @ sk_D)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('22', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('23', plain, ((((sk_A) = (k1_xboole_0)) | (v1_partfun1 @ sk_D @ sk_A))),
% 0.19/0.48      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.19/0.48  thf('24', plain, (~ (v1_partfun1 @ sk_D @ sk_A)),
% 0.19/0.48      inference('clc', [status(thm)], ['14', '15'])).
% 0.19/0.48  thf('25', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.48  thf('26', plain, (~ (v1_partfun1 @ sk_D @ k1_xboole_0)),
% 0.19/0.48      inference('demod', [status(thm)], ['16', '25'])).
% 0.19/0.48  thf('27', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('28', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.48  thf('29', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.48  thf('30', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_D @ 
% 0.19/0.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.19/0.48  thf('31', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.48         (((X2) != (k1_xboole_0))
% 0.19/0.48          | ~ (v1_funct_1 @ X1)
% 0.19/0.48          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.19/0.48          | (v1_partfun1 @ X1 @ X2)
% 0.19/0.48          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.19/0.48          | ~ (v1_funct_2 @ X1 @ X2 @ X0)
% 0.19/0.48          | ~ (v1_funct_1 @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.19/0.48  thf('32', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (v1_funct_2 @ X1 @ k1_xboole_0 @ X0)
% 0.19/0.48          | (v1_partfun1 @ X1 @ k1_xboole_0)
% 0.19/0.48          | ~ (m1_subset_1 @ X1 @ 
% 0.19/0.48               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)))
% 0.19/0.48          | ~ (v1_funct_1 @ X1))),
% 0.19/0.48      inference('simplify', [status(thm)], ['31'])).
% 0.19/0.48  thf('33', plain,
% 0.19/0.48      ((~ (v1_funct_1 @ sk_D)
% 0.19/0.48        | (v1_partfun1 @ sk_D @ k1_xboole_0)
% 0.19/0.48        | ~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ k1_xboole_0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['30', '32'])).
% 0.19/0.48  thf('34', plain, ((v1_funct_1 @ sk_D)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('35', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('36', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.48  thf('37', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.48  thf('38', plain, ((v1_funct_2 @ sk_D @ k1_xboole_0 @ k1_xboole_0)),
% 0.19/0.48      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.19/0.48  thf('39', plain, ((v1_partfun1 @ sk_D @ k1_xboole_0)),
% 0.19/0.48      inference('demod', [status(thm)], ['33', '34', '38'])).
% 0.19/0.48  thf('40', plain, ($false), inference('demod', [status(thm)], ['26', '39'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
