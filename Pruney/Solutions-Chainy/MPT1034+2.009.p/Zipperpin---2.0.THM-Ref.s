%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fmr50PUcnB

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:12 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 358 expanded)
%              Number of leaves         :   13 ( 110 expanded)
%              Depth                    :   13
%              Number of atoms          :  466 (7710 expanded)
%              Number of equality atoms :   18 (  83 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t143_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( r1_partfun1 @ B @ C )
           => ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( r1_partfun1 @ B @ C )
             => ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t143_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t142_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( r1_partfun1 @ C @ D )
           => ( ( ( B = k1_xboole_0 )
                & ( A != k1_xboole_0 ) )
              | ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( r2_relset_1 @ X1 @ X2 @ X3 @ X0 )
      | ~ ( r1_partfun1 @ X3 @ X0 )
      | ( X2 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_2 @ X3 @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t142_funct_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r1_partfun1 @ X0 @ sk_C )
      | ( r2_relset_1 @ sk_A @ sk_A @ X0 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r1_partfun1 @ X0 @ sk_C )
      | ( r2_relset_1 @ sk_A @ sk_A @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_partfun1 @ sk_B @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    r1_partfun1 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9','10','11'])).

thf('13',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['12','13'])).

thf('16',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['12','13'])).

thf('19',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['12','13'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['12','13'])).

thf('23',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['12','13'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( r2_relset_1 @ X1 @ X2 @ X3 @ X0 )
      | ~ ( r1_partfun1 @ X3 @ X0 )
      | ( X1 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_2 @ X3 @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t142_funct_2])).

thf('26',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ k1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X2 ) ) )
      | ~ ( r1_partfun1 @ X3 @ X0 )
      | ( r2_relset_1 @ k1_xboole_0 @ X2 @ X3 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X2 ) ) )
      | ~ ( v1_funct_2 @ X0 @ k1_xboole_0 @ X2 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) )
      | ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ X0 )
      | ~ ( r1_partfun1 @ sk_B @ X0 )
      | ~ ( v1_funct_2 @ sk_B @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['12','13'])).

thf('30',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['12','13'])).

thf('31',plain,(
    v1_funct_2 @ sk_B @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) )
      | ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ X0 )
      | ~ ( r1_partfun1 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['27','31','32'])).

thf('34',plain,
    ( ~ ( r1_partfun1 @ sk_B @ sk_C )
    | ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','33'])).

thf('35',plain,(
    r1_partfun1 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['12','13'])).

thf('38',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['12','13'])).

thf('39',plain,(
    v1_funct_2 @ sk_C @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['34','35','39','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['16','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fmr50PUcnB
% 0.12/0.32  % Computer   : n005.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 10:29:33 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running portfolio for 600 s
% 0.12/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.32  % Number of cores: 8
% 0.12/0.32  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.18/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.46  % Solved by: fo/fo7.sh
% 0.18/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.46  % done 22 iterations in 0.025s
% 0.18/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.46  % SZS output start Refutation
% 0.18/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.18/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.18/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.18/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.18/0.46  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.18/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.46  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.18/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.18/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.18/0.46  thf(t143_funct_2, conjecture,
% 0.18/0.46    (![A:$i,B:$i]:
% 0.18/0.46     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.18/0.46         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.18/0.46       ( ![C:$i]:
% 0.18/0.46         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.18/0.46             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.18/0.46           ( ( r1_partfun1 @ B @ C ) => ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) ))).
% 0.18/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.46    (~( ![A:$i,B:$i]:
% 0.18/0.46        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.18/0.46            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.18/0.46          ( ![C:$i]:
% 0.18/0.46            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.18/0.46                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.18/0.46              ( ( r1_partfun1 @ B @ C ) => ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) ) )),
% 0.18/0.46    inference('cnf.neg', [status(esa)], [t143_funct_2])).
% 0.18/0.46  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('1', plain,
% 0.18/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('2', plain,
% 0.18/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf(t142_funct_2, axiom,
% 0.18/0.46    (![A:$i,B:$i,C:$i]:
% 0.18/0.46     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.18/0.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.18/0.46       ( ![D:$i]:
% 0.18/0.46         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.18/0.46             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.18/0.46           ( ( r1_partfun1 @ C @ D ) =>
% 0.18/0.46             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.18/0.46               ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.18/0.46  thf('3', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.18/0.46         (~ (v1_funct_1 @ X0)
% 0.18/0.46          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.18/0.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.18/0.46          | (r2_relset_1 @ X1 @ X2 @ X3 @ X0)
% 0.18/0.46          | ~ (r1_partfun1 @ X3 @ X0)
% 0.18/0.46          | ((X2) = (k1_xboole_0))
% 0.18/0.46          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.18/0.46          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 0.18/0.46          | ~ (v1_funct_1 @ X3))),
% 0.18/0.46      inference('cnf', [status(esa)], [t142_funct_2])).
% 0.18/0.46  thf('4', plain,
% 0.18/0.46      (![X0 : $i]:
% 0.18/0.46         (~ (v1_funct_1 @ X0)
% 0.18/0.46          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.18/0.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.18/0.46          | ((sk_A) = (k1_xboole_0))
% 0.18/0.46          | ~ (r1_partfun1 @ X0 @ sk_C)
% 0.18/0.46          | (r2_relset_1 @ sk_A @ sk_A @ X0 @ sk_C)
% 0.18/0.46          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.18/0.46          | ~ (v1_funct_1 @ sk_C))),
% 0.18/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.18/0.46  thf('5', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('7', plain,
% 0.18/0.46      (![X0 : $i]:
% 0.18/0.46         (~ (v1_funct_1 @ X0)
% 0.18/0.46          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.18/0.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.18/0.46          | ((sk_A) = (k1_xboole_0))
% 0.18/0.46          | ~ (r1_partfun1 @ X0 @ sk_C)
% 0.18/0.46          | (r2_relset_1 @ sk_A @ sk_A @ X0 @ sk_C))),
% 0.18/0.46      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.18/0.46  thf('8', plain,
% 0.18/0.46      (((r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.18/0.46        | ~ (r1_partfun1 @ sk_B @ sk_C)
% 0.18/0.46        | ((sk_A) = (k1_xboole_0))
% 0.18/0.46        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.18/0.46        | ~ (v1_funct_1 @ sk_B))),
% 0.18/0.46      inference('sup-', [status(thm)], ['1', '7'])).
% 0.18/0.46  thf('9', plain, ((r1_partfun1 @ sk_B @ sk_C)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('10', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('11', plain, ((v1_funct_1 @ sk_B)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('12', plain,
% 0.18/0.46      (((r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.18/0.46      inference('demod', [status(thm)], ['8', '9', '10', '11'])).
% 0.18/0.46  thf('13', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('14', plain, (((sk_A) = (k1_xboole_0))),
% 0.18/0.46      inference('clc', [status(thm)], ['12', '13'])).
% 0.18/0.46  thf('15', plain, (((sk_A) = (k1_xboole_0))),
% 0.18/0.46      inference('clc', [status(thm)], ['12', '13'])).
% 0.18/0.46  thf('16', plain, (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_C)),
% 0.18/0.46      inference('demod', [status(thm)], ['0', '14', '15'])).
% 0.18/0.46  thf('17', plain,
% 0.18/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('18', plain, (((sk_A) = (k1_xboole_0))),
% 0.18/0.46      inference('clc', [status(thm)], ['12', '13'])).
% 0.18/0.46  thf('19', plain, (((sk_A) = (k1_xboole_0))),
% 0.18/0.46      inference('clc', [status(thm)], ['12', '13'])).
% 0.18/0.46  thf('20', plain,
% 0.18/0.46      ((m1_subset_1 @ sk_C @ 
% 0.18/0.46        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.18/0.46      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.18/0.46  thf('21', plain,
% 0.18/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('22', plain, (((sk_A) = (k1_xboole_0))),
% 0.18/0.46      inference('clc', [status(thm)], ['12', '13'])).
% 0.18/0.46  thf('23', plain, (((sk_A) = (k1_xboole_0))),
% 0.18/0.46      inference('clc', [status(thm)], ['12', '13'])).
% 0.18/0.46  thf('24', plain,
% 0.18/0.46      ((m1_subset_1 @ sk_B @ 
% 0.18/0.46        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.18/0.46      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.18/0.46  thf('25', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.18/0.46         (~ (v1_funct_1 @ X0)
% 0.18/0.46          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.18/0.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.18/0.46          | (r2_relset_1 @ X1 @ X2 @ X3 @ X0)
% 0.18/0.46          | ~ (r1_partfun1 @ X3 @ X0)
% 0.18/0.46          | ((X1) != (k1_xboole_0))
% 0.18/0.46          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.18/0.46          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 0.18/0.46          | ~ (v1_funct_1 @ X3))),
% 0.18/0.46      inference('cnf', [status(esa)], [t142_funct_2])).
% 0.18/0.46  thf('26', plain,
% 0.18/0.46      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.18/0.46         (~ (v1_funct_1 @ X3)
% 0.18/0.46          | ~ (v1_funct_2 @ X3 @ k1_xboole_0 @ X2)
% 0.18/0.46          | ~ (m1_subset_1 @ X3 @ 
% 0.18/0.46               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X2)))
% 0.18/0.46          | ~ (r1_partfun1 @ X3 @ X0)
% 0.18/0.46          | (r2_relset_1 @ k1_xboole_0 @ X2 @ X3 @ X0)
% 0.18/0.46          | ~ (m1_subset_1 @ X0 @ 
% 0.18/0.46               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X2)))
% 0.18/0.46          | ~ (v1_funct_2 @ X0 @ k1_xboole_0 @ X2)
% 0.18/0.46          | ~ (v1_funct_1 @ X0))),
% 0.18/0.46      inference('simplify', [status(thm)], ['25'])).
% 0.18/0.46  thf('27', plain,
% 0.18/0.46      (![X0 : $i]:
% 0.18/0.46         (~ (v1_funct_1 @ X0)
% 0.18/0.46          | ~ (v1_funct_2 @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 0.18/0.46          | ~ (m1_subset_1 @ X0 @ 
% 0.18/0.46               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))
% 0.18/0.46          | (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ X0)
% 0.18/0.46          | ~ (r1_partfun1 @ sk_B @ X0)
% 0.18/0.46          | ~ (v1_funct_2 @ sk_B @ k1_xboole_0 @ k1_xboole_0)
% 0.18/0.46          | ~ (v1_funct_1 @ sk_B))),
% 0.18/0.46      inference('sup-', [status(thm)], ['24', '26'])).
% 0.18/0.46  thf('28', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('29', plain, (((sk_A) = (k1_xboole_0))),
% 0.18/0.46      inference('clc', [status(thm)], ['12', '13'])).
% 0.18/0.46  thf('30', plain, (((sk_A) = (k1_xboole_0))),
% 0.18/0.46      inference('clc', [status(thm)], ['12', '13'])).
% 0.18/0.46  thf('31', plain, ((v1_funct_2 @ sk_B @ k1_xboole_0 @ k1_xboole_0)),
% 0.18/0.46      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.18/0.46  thf('32', plain, ((v1_funct_1 @ sk_B)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('33', plain,
% 0.18/0.46      (![X0 : $i]:
% 0.18/0.46         (~ (v1_funct_1 @ X0)
% 0.18/0.46          | ~ (v1_funct_2 @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 0.18/0.46          | ~ (m1_subset_1 @ X0 @ 
% 0.18/0.46               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))
% 0.18/0.46          | (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ X0)
% 0.18/0.46          | ~ (r1_partfun1 @ sk_B @ X0))),
% 0.18/0.46      inference('demod', [status(thm)], ['27', '31', '32'])).
% 0.18/0.46  thf('34', plain,
% 0.18/0.46      ((~ (r1_partfun1 @ sk_B @ sk_C)
% 0.18/0.46        | (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_C)
% 0.18/0.46        | ~ (v1_funct_2 @ sk_C @ k1_xboole_0 @ k1_xboole_0)
% 0.18/0.46        | ~ (v1_funct_1 @ sk_C))),
% 0.18/0.46      inference('sup-', [status(thm)], ['20', '33'])).
% 0.18/0.46  thf('35', plain, ((r1_partfun1 @ sk_B @ sk_C)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('36', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('37', plain, (((sk_A) = (k1_xboole_0))),
% 0.18/0.46      inference('clc', [status(thm)], ['12', '13'])).
% 0.18/0.46  thf('38', plain, (((sk_A) = (k1_xboole_0))),
% 0.18/0.46      inference('clc', [status(thm)], ['12', '13'])).
% 0.18/0.46  thf('39', plain, ((v1_funct_2 @ sk_C @ k1_xboole_0 @ k1_xboole_0)),
% 0.18/0.46      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.18/0.46  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('41', plain, ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_C)),
% 0.18/0.46      inference('demod', [status(thm)], ['34', '35', '39', '40'])).
% 0.18/0.46  thf('42', plain, ($false), inference('demod', [status(thm)], ['16', '41'])).
% 0.18/0.46  
% 0.18/0.46  % SZS output end Refutation
% 0.18/0.46  
% 0.33/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
