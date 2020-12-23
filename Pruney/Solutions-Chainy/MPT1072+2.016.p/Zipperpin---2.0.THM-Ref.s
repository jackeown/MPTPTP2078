%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.81ku4TAKNN

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 (  71 expanded)
%              Number of leaves         :   20 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :  348 ( 986 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t189_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ A @ B )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
                 => ( r2_hidden @ ( k3_funct_2 @ A @ B @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ A )
               => ! [D: $i] :
                    ( ( ( v1_funct_1 @ D )
                      & ( v1_funct_2 @ D @ A @ B )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
                   => ( r2_hidden @ ( k3_funct_2 @ A @ B @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t189_funct_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(clc,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( X8 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X9 @ X6 ) @ ( k2_relset_1 @ X7 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_D )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    ~ ( r2_hidden @ ( k3_funct_2 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X3 @ X4 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X5 @ X3 )
      | ( ( k3_funct_2 @ X3 @ X4 @ X2 @ X5 )
        = ( k1_funct_1 @ X2 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k3_funct_2 @ sk_A @ sk_B @ sk_D @ sk_C )
    = ( k1_funct_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf('24',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['13','23'])).

thf('25',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['12','24'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['0','25','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.81ku4TAKNN
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:08:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 17 iterations in 0.013s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.48  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(t189_funct_2, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( m1_subset_1 @ C @ A ) =>
% 0.20/0.48               ( ![D:$i]:
% 0.20/0.48                 ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.48                     ( m1_subset_1 @
% 0.20/0.48                       D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.48                   ( r2_hidden @
% 0.20/0.48                     ( k3_funct_2 @ A @ B @ D @ C ) @ 
% 0.20/0.48                     ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.48              ( ![C:$i]:
% 0.20/0.48                ( ( m1_subset_1 @ C @ A ) =>
% 0.20/0.48                  ( ![D:$i]:
% 0.20/0.48                    ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.48                        ( m1_subset_1 @
% 0.20/0.48                          D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.48                      ( r2_hidden @
% 0.20/0.48                        ( k3_funct_2 @ A @ B @ D @ C ) @ 
% 0.20/0.48                        ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t189_funct_2])).
% 0.20/0.48  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t2_subset, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.48       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((r2_hidden @ X0 @ X1)
% 0.20/0.48          | (v1_xboole_0 @ X1)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.48  thf('3', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_C @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf('4', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('5', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['3', '4'])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t6_funct_2, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.48         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.48       ( ( r2_hidden @ C @ A ) =>
% 0.20/0.48         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.48           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X6 @ X7)
% 0.20/0.48          | ((X8) = (k1_xboole_0))
% 0.20/0.48          | ~ (v1_funct_1 @ X9)
% 0.20/0.48          | ~ (v1_funct_2 @ X9 @ X7 @ X8)
% 0.20/0.48          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.20/0.48          | (r2_hidden @ (k1_funct_1 @ X9 @ X6) @ (k2_relset_1 @ X7 @ X8 @ X9)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ 
% 0.20/0.48           (k2_relset_1 @ sk_A @ sk_B @ sk_D))
% 0.20/0.48          | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B)
% 0.20/0.48          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.48          | ((sk_B) = (k1_xboole_0))
% 0.20/0.48          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf('9', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ 
% 0.20/0.48           (k2_relset_1 @ sk_A @ sk_B @ sk_D))
% 0.20/0.48          | ((sk_B) = (k1_xboole_0))
% 0.20/0.48          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      ((((sk_B) = (k1_xboole_0))
% 0.20/0.48        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ 
% 0.20/0.48           (k2_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['5', '11'])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (~ (r2_hidden @ (k3_funct_2 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.20/0.48          (k2_relset_1 @ sk_A @ sk_B @ sk_D))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('14', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(redefinition_k3_funct_2, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.48         ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.48         ( m1_subset_1 @ D @ A ) ) =>
% 0.20/0.48       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4)))
% 0.20/0.48          | ~ (v1_funct_2 @ X2 @ X3 @ X4)
% 0.20/0.48          | ~ (v1_funct_1 @ X2)
% 0.20/0.48          | (v1_xboole_0 @ X3)
% 0.20/0.48          | ~ (m1_subset_1 @ X5 @ X3)
% 0.20/0.48          | ((k3_funct_2 @ X3 @ X4 @ X2 @ X5) = (k1_funct_1 @ X2 @ X5)))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k3_funct_2 @ sk_A @ sk_B @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.48          | (v1_xboole_0 @ sk_A)
% 0.20/0.48          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.48          | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('19', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k3_funct_2 @ sk_A @ sk_B @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.48          | (v1_xboole_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.20/0.48  thf('21', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.48          | ((k3_funct_2 @ sk_A @ sk_B @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0)))),
% 0.20/0.48      inference('clc', [status(thm)], ['20', '21'])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (((k3_funct_2 @ sk_A @ sk_B @ sk_D @ sk_C) = (k1_funct_1 @ sk_D @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['14', '22'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (~ (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ 
% 0.20/0.48          (k2_relset_1 @ sk_A @ sk_B @ sk_D))),
% 0.20/0.48      inference('demod', [status(thm)], ['13', '23'])).
% 0.20/0.48  thf('25', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.48      inference('clc', [status(thm)], ['12', '24'])).
% 0.20/0.48  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.48  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.48  thf('27', plain, ($false),
% 0.20/0.48      inference('demod', [status(thm)], ['0', '25', '26'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
