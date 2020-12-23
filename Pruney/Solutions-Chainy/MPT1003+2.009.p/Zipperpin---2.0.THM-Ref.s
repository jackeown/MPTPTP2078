%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.okk875znbX

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:03 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 151 expanded)
%              Number of leaves         :   17 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  689 (2483 expanded)
%              Number of equality atoms :   79 ( 272 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(t51_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k8_relset_1 @ A @ B @ C @ ( k7_relset_1 @ A @ B @ C @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( k8_relset_1 @ A @ B @ C @ ( k7_relset_1 @ A @ B @ C @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t51_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k8_relset_1 @ A @ B @ C @ B )
          = A ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_funct_2 @ X7 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X8 ) ) )
      | ( ( k8_relset_1 @ X6 @ X8 @ X7 @ X8 )
        = X6 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_2])).

thf('2',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
      = sk_A )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relset_1 @ X0 @ X1 @ X2 @ X1 )
        = ( k1_relset_1 @ X0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('5',plain,
    ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
    = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
      = sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','5','6','7'])).

thf('9',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t39_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) )
          = ( k2_relset_1 @ B @ A @ C ) )
        & ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) )
          = ( k1_relset_1 @ B @ A @ C ) ) ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k8_relset_1 @ X3 @ X4 @ X5 @ ( k7_relset_1 @ X3 @ X4 @ X5 @ X3 ) )
        = ( k1_relset_1 @ X3 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[t39_relset_1])).

thf('15',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ ( k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ k1_xboole_0 ) )
      = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relset_1 @ X0 @ X1 @ X2 @ X0 )
        = ( k2_relset_1 @ X0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('18',plain,
    ( ( ( k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ k1_xboole_0 )
      = ( k2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relset_1 @ X0 @ X1 @ X2 @ X1 )
        = ( k1_relset_1 @ X0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('21',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_B )
      = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('23',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X6 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_funct_2 @ X7 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X8 ) ) )
      | ( ( k8_relset_1 @ X6 @ X8 @ X7 @ X8 )
        = X6 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_2])).

thf('24',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k8_relset_1 @ k1_xboole_0 @ X8 @ X7 @ X8 )
        = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X8 ) ) )
      | ~ ( v1_funct_2 @ X7 @ k1_xboole_0 @ X8 )
      | ~ ( v1_funct_1 @ X7 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B )
      | ( ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_B )
        = k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('28',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_B )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26','29'])).

thf('31',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','30'])).

thf('32',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ ( k2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C ) )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','18','31'])).

thf('33',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('34',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relset_1 @ X0 @ X1 @ X2 @ X0 )
        = ( k2_relset_1 @ X0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('37',plain,
    ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
 != sk_A ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
     != sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('41',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('42',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ ( k2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    sk_A != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['32','42'])).

thf('44',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('45',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['43','44'])).

thf('46',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['10','45'])).

thf('47',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
 != sk_A ),
    inference(demod,[status(thm)],['34','37'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k8_relset_1 @ X3 @ X4 @ X5 @ ( k7_relset_1 @ X3 @ X4 @ X5 @ X3 ) )
        = ( k1_relset_1 @ X3 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[t39_relset_1])).

thf('50',plain,
    ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('52',plain,
    ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
    = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
 != sk_A ),
    inference(demod,[status(thm)],['47','52'])).

thf('54',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['8','46','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.okk875znbX
% 0.14/0.33  % Computer   : n014.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 15:42:07 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  % Running portfolio for 600 s
% 0.14/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.33  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 37 iterations in 0.016s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.46  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.19/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.46  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.46  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.46  thf(t51_funct_2, conjecture,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.46       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.19/0.46         ( ( k8_relset_1 @ A @ B @ C @ ( k7_relset_1 @ A @ B @ C @ A ) ) =
% 0.19/0.46           ( A ) ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.46        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.46            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.46          ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.19/0.46            ( ( k8_relset_1 @ A @ B @ C @ ( k7_relset_1 @ A @ B @ C @ A ) ) =
% 0.19/0.46              ( A ) ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t51_funct_2])).
% 0.19/0.46  thf('0', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(t48_funct_2, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.46       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.19/0.46         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ))).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.46         (((X8) = (k1_xboole_0))
% 0.19/0.46          | ~ (v1_funct_1 @ X7)
% 0.19/0.46          | ~ (v1_funct_2 @ X7 @ X6 @ X8)
% 0.19/0.46          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X8)))
% 0.19/0.46          | ((k8_relset_1 @ X6 @ X8 @ X7 @ X8) = (X6)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t48_funct_2])).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) = (sk_A))
% 0.19/0.46        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.19/0.46        | ~ (v1_funct_1 @ sk_C)
% 0.19/0.46        | ((sk_B) = (k1_xboole_0)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(t38_relset_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.46       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.19/0.46         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.19/0.46  thf('4', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         (((k8_relset_1 @ X0 @ X1 @ X2 @ X1) = (k1_relset_1 @ X0 @ X1 @ X2))
% 0.19/0.46          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 0.19/0.46      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.19/0.46  thf('5', plain,
% 0.19/0.46      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.19/0.46         = (k1_relset_1 @ sk_A @ sk_B @ sk_C))),
% 0.19/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.46  thf('6', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('8', plain,
% 0.19/0.46      ((((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_A))
% 0.19/0.46        | ((sk_B) = (k1_xboole_0)))),
% 0.19/0.46      inference('demod', [status(thm)], ['2', '5', '6', '7'])).
% 0.19/0.46  thf('9', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) != (k1_xboole_0)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('10', plain,
% 0.19/0.46      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.19/0.46      inference('split', [status(esa)], ['9'])).
% 0.19/0.46  thf('11', plain,
% 0.19/0.46      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.46      inference('split', [status(esa)], ['9'])).
% 0.19/0.46  thf('12', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('13', plain,
% 0.19/0.46      (((m1_subset_1 @ sk_C @ 
% 0.19/0.46         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.19/0.46         <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.46      inference('sup+', [status(thm)], ['11', '12'])).
% 0.19/0.46  thf(t39_relset_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.19/0.46       ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.19/0.46           ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.19/0.46         ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.19/0.46           ( k1_relset_1 @ B @ A @ C ) ) ) ))).
% 0.19/0.46  thf('14', plain,
% 0.19/0.46      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.46         (((k8_relset_1 @ X3 @ X4 @ X5 @ (k7_relset_1 @ X3 @ X4 @ X5 @ X3))
% 0.19/0.46            = (k1_relset_1 @ X3 @ X4 @ X5))
% 0.19/0.46          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.19/0.46      inference('cnf', [status(esa)], [t39_relset_1])).
% 0.19/0.46  thf('15', plain,
% 0.19/0.46      ((((k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ 
% 0.19/0.46          (k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ k1_xboole_0))
% 0.19/0.46          = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C)))
% 0.19/0.46         <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.46      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.46  thf('16', plain,
% 0.19/0.46      (((m1_subset_1 @ sk_C @ 
% 0.19/0.46         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.19/0.46         <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.46      inference('sup+', [status(thm)], ['11', '12'])).
% 0.19/0.46  thf('17', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         (((k7_relset_1 @ X0 @ X1 @ X2 @ X0) = (k2_relset_1 @ X0 @ X1 @ X2))
% 0.19/0.46          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 0.19/0.46      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.19/0.46  thf('18', plain,
% 0.19/0.46      ((((k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ k1_xboole_0)
% 0.19/0.46          = (k2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C)))
% 0.19/0.46         <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.46      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.46  thf('19', plain,
% 0.19/0.46      (((m1_subset_1 @ sk_C @ 
% 0.19/0.46         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.19/0.46         <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.46      inference('sup+', [status(thm)], ['11', '12'])).
% 0.19/0.46  thf('20', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         (((k8_relset_1 @ X0 @ X1 @ X2 @ X1) = (k1_relset_1 @ X0 @ X1 @ X2))
% 0.19/0.46          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 0.19/0.46      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.19/0.46  thf('21', plain,
% 0.19/0.46      ((((k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_B)
% 0.19/0.46          = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C)))
% 0.19/0.46         <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.46      inference('sup-', [status(thm)], ['19', '20'])).
% 0.19/0.46  thf('22', plain,
% 0.19/0.46      (((m1_subset_1 @ sk_C @ 
% 0.19/0.46         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.19/0.46         <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.46      inference('sup+', [status(thm)], ['11', '12'])).
% 0.19/0.46  thf('23', plain,
% 0.19/0.46      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.46         (((X6) != (k1_xboole_0))
% 0.19/0.46          | ~ (v1_funct_1 @ X7)
% 0.19/0.46          | ~ (v1_funct_2 @ X7 @ X6 @ X8)
% 0.19/0.46          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X8)))
% 0.19/0.46          | ((k8_relset_1 @ X6 @ X8 @ X7 @ X8) = (X6)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t48_funct_2])).
% 0.19/0.46  thf('24', plain,
% 0.19/0.46      (![X7 : $i, X8 : $i]:
% 0.19/0.46         (((k8_relset_1 @ k1_xboole_0 @ X8 @ X7 @ X8) = (k1_xboole_0))
% 0.19/0.46          | ~ (m1_subset_1 @ X7 @ 
% 0.19/0.46               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X8)))
% 0.19/0.46          | ~ (v1_funct_2 @ X7 @ k1_xboole_0 @ X8)
% 0.19/0.46          | ~ (v1_funct_1 @ X7))),
% 0.19/0.46      inference('simplify', [status(thm)], ['23'])).
% 0.19/0.46  thf('25', plain,
% 0.19/0.46      (((~ (v1_funct_1 @ sk_C)
% 0.19/0.46         | ~ (v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B)
% 0.19/0.46         | ((k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_B) = (k1_xboole_0))))
% 0.19/0.46         <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.46      inference('sup-', [status(thm)], ['22', '24'])).
% 0.19/0.46  thf('26', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('27', plain,
% 0.19/0.46      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.46      inference('split', [status(esa)], ['9'])).
% 0.19/0.46  thf('28', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('29', plain,
% 0.19/0.46      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B))
% 0.19/0.46         <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.46      inference('sup+', [status(thm)], ['27', '28'])).
% 0.19/0.46  thf('30', plain,
% 0.19/0.46      ((((k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_B) = (k1_xboole_0)))
% 0.19/0.46         <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.46      inference('demod', [status(thm)], ['25', '26', '29'])).
% 0.19/0.46  thf('31', plain,
% 0.19/0.46      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0)))
% 0.19/0.46         <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.46      inference('sup+', [status(thm)], ['21', '30'])).
% 0.19/0.46  thf('32', plain,
% 0.19/0.46      ((((k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ 
% 0.19/0.46          (k2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0)))
% 0.19/0.46         <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.46      inference('demod', [status(thm)], ['15', '18', '31'])).
% 0.19/0.46  thf('33', plain,
% 0.19/0.46      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.46      inference('split', [status(esa)], ['9'])).
% 0.19/0.46  thf('34', plain,
% 0.19/0.46      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ 
% 0.19/0.46         (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)) != (sk_A))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('35', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('36', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         (((k7_relset_1 @ X0 @ X1 @ X2 @ X0) = (k2_relset_1 @ X0 @ X1 @ X2))
% 0.19/0.46          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 0.19/0.46      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.19/0.46  thf('37', plain,
% 0.19/0.46      (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.19/0.46         = (k2_relset_1 @ sk_A @ sk_B @ sk_C))),
% 0.19/0.46      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.46  thf('38', plain,
% 0.19/0.46      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.19/0.46         != (sk_A))),
% 0.19/0.46      inference('demod', [status(thm)], ['34', '37'])).
% 0.19/0.46  thf('39', plain,
% 0.19/0.46      ((((k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ 
% 0.19/0.46          (k2_relset_1 @ sk_A @ sk_B @ sk_C)) != (sk_A)))
% 0.19/0.46         <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.46      inference('sup-', [status(thm)], ['33', '38'])).
% 0.19/0.46  thf('40', plain,
% 0.19/0.46      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.46      inference('split', [status(esa)], ['9'])).
% 0.19/0.46  thf('41', plain,
% 0.19/0.46      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.46      inference('split', [status(esa)], ['9'])).
% 0.19/0.46  thf('42', plain,
% 0.19/0.46      ((((k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ 
% 0.19/0.46          (k2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C)) != (k1_xboole_0)))
% 0.19/0.46         <= ((((sk_A) = (k1_xboole_0))))),
% 0.19/0.46      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.19/0.46  thf('43', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.19/0.46      inference('simplify_reflect-', [status(thm)], ['32', '42'])).
% 0.19/0.46  thf('44', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.19/0.46      inference('split', [status(esa)], ['9'])).
% 0.19/0.46  thf('45', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.19/0.46      inference('sat_resolution*', [status(thm)], ['43', '44'])).
% 0.19/0.46  thf('46', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.46      inference('simpl_trail', [status(thm)], ['10', '45'])).
% 0.19/0.46  thf('47', plain,
% 0.19/0.46      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.19/0.46         != (sk_A))),
% 0.19/0.46      inference('demod', [status(thm)], ['34', '37'])).
% 0.19/0.46  thf('48', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('49', plain,
% 0.19/0.46      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.46         (((k8_relset_1 @ X3 @ X4 @ X5 @ (k7_relset_1 @ X3 @ X4 @ X5 @ X3))
% 0.19/0.46            = (k1_relset_1 @ X3 @ X4 @ X5))
% 0.19/0.46          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.19/0.46      inference('cnf', [status(esa)], [t39_relset_1])).
% 0.19/0.46  thf('50', plain,
% 0.19/0.46      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ 
% 0.19/0.46         (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 0.19/0.46         = (k1_relset_1 @ sk_A @ sk_B @ sk_C))),
% 0.19/0.46      inference('sup-', [status(thm)], ['48', '49'])).
% 0.19/0.46  thf('51', plain,
% 0.19/0.46      (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.19/0.46         = (k2_relset_1 @ sk_A @ sk_B @ sk_C))),
% 0.19/0.46      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.46  thf('52', plain,
% 0.19/0.46      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.19/0.46         = (k1_relset_1 @ sk_A @ sk_B @ sk_C))),
% 0.19/0.46      inference('demod', [status(thm)], ['50', '51'])).
% 0.19/0.46  thf('53', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_A))),
% 0.19/0.46      inference('demod', [status(thm)], ['47', '52'])).
% 0.19/0.46  thf('54', plain, ($false),
% 0.19/0.46      inference('simplify_reflect-', [status(thm)], ['8', '46', '53'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
