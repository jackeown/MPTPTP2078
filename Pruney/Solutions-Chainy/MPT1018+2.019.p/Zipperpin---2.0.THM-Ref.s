%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NXDJlZ3Goc

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:58 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 353 expanded)
%              Number of leaves         :   23 ( 114 expanded)
%              Depth                    :   17
%              Number of atoms          :  509 (5003 expanded)
%              Number of equality atoms :   57 ( 396 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('1',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ( X1 = X2 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( m1_subset_1 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ X0 )
      | ~ ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ( X24 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ X25 ) @ ( k1_funct_1 @ X25 @ X22 ) )
        = X22 )
      | ~ ( v2_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t32_funct_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ sk_B )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('20',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_D ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k1_funct_1 @ sk_B @ sk_C )
    = ( k1_funct_1 @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_C ) )
      = sk_D ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_C = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf('24',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C = sk_D ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    sk_C != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_C @ X0 ) ),
    inference(demod,[status(thm)],['8','26','27'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('29',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('30',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('31',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X21 ) ) )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('32',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('34',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    v1_xboole_0 @ sk_C ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ X0 )
      | ~ ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_D @ X0 ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X21 ) ) )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('43',plain,(
    ! [X1: $i] :
      ( ( v1_xboole_0 @ sk_D )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('45',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    v1_xboole_0 @ sk_C ),
    inference('sup-',[status(thm)],['28','34'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('52',plain,(
    k1_xboole_0 = sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    k1_xboole_0 = sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = sk_C )
      | ( X1 = sk_C )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['49','52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = sk_C ) ) ),
    inference(condensation,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_D = sk_C ) ) ),
    inference('sup-',[status(thm)],['43','55'])).

thf('57',plain,(
    sk_C != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference('sup-',[status(thm)],['35','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NXDJlZ3Goc
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:08:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.57  % Solved by: fo/fo7.sh
% 0.37/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.57  % done 211 iterations in 0.116s
% 0.37/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.57  % SZS output start Refutation
% 0.37/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.57  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.37/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.37/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.57  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.37/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.57  thf(t85_funct_2, conjecture,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.37/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.37/0.57       ( ( v2_funct_1 @ B ) =>
% 0.37/0.57         ( ![C:$i,D:$i]:
% 0.37/0.57           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.37/0.57               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.37/0.57             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.37/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.57    (~( ![A:$i,B:$i]:
% 0.37/0.57        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.37/0.57            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.37/0.57          ( ( v2_funct_1 @ B ) =>
% 0.37/0.57            ( ![C:$i,D:$i]:
% 0.37/0.57              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.37/0.57                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.37/0.57                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.37/0.57    inference('cnf.neg', [status(esa)], [t85_funct_2])).
% 0.37/0.57  thf('0', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.37/0.57  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.57  thf(t8_boole, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.37/0.57  thf('2', plain,
% 0.37/0.57      (![X1 : $i, X2 : $i]:
% 0.37/0.57         (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X2) | ((X1) = (X2)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t8_boole])).
% 0.37/0.57  thf('3', plain,
% 0.37/0.57      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.57  thf(t4_subset_1, axiom,
% 0.37/0.57    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.37/0.57  thf('4', plain,
% 0.37/0.57      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.37/0.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.37/0.57  thf('5', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['3', '4'])).
% 0.37/0.57  thf(t4_subset, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.37/0.58       ( m1_subset_1 @ A @ C ) ))).
% 0.37/0.58  thf('6', plain,
% 0.37/0.58      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X7 @ X8)
% 0.37/0.58          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.37/0.58          | (m1_subset_1 @ X7 @ X9))),
% 0.37/0.58      inference('cnf', [status(esa)], [t4_subset])).
% 0.37/0.58  thf('7', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.58         (~ (v1_xboole_0 @ X1)
% 0.37/0.58          | (m1_subset_1 @ X2 @ X0)
% 0.37/0.58          | ~ (r2_hidden @ X2 @ X1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.58  thf('8', plain,
% 0.37/0.58      (![X0 : $i]: ((m1_subset_1 @ sk_C @ X0) | ~ (v1_xboole_0 @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['0', '7'])).
% 0.37/0.58  thf('9', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('10', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(t32_funct_2, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.58     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.37/0.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.58       ( ( ( v2_funct_1 @ D ) & ( r2_hidden @ C @ A ) ) =>
% 0.37/0.58         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.37/0.58           ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) ) =
% 0.37/0.58             ( C ) ) ) ) ))).
% 0.37/0.58  thf('11', plain,
% 0.37/0.58      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X22 @ X23)
% 0.37/0.58          | ((X24) = (k1_xboole_0))
% 0.37/0.58          | ~ (v1_funct_1 @ X25)
% 0.37/0.58          | ~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.37/0.58          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.37/0.58          | ((k1_funct_1 @ (k2_funct_1 @ X25) @ (k1_funct_1 @ X25 @ X22))
% 0.37/0.58              = (X22))
% 0.37/0.58          | ~ (v2_funct_1 @ X25))),
% 0.37/0.58      inference('cnf', [status(esa)], [t32_funct_2])).
% 0.37/0.58  thf('12', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (~ (v2_funct_1 @ sk_B)
% 0.37/0.58          | ((k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ X0))
% 0.37/0.58              = (X0))
% 0.37/0.58          | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.37/0.58          | ~ (v1_funct_1 @ sk_B)
% 0.37/0.58          | ((sk_A) = (k1_xboole_0))
% 0.37/0.58          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.58  thf('13', plain, ((v2_funct_1 @ sk_B)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('14', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('15', plain, ((v1_funct_1 @ sk_B)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('16', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (((k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ X0)) = (X0))
% 0.37/0.58          | ((sk_A) = (k1_xboole_0))
% 0.37/0.58          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.37/0.58      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.37/0.58  thf('17', plain,
% 0.37/0.58      ((((sk_A) = (k1_xboole_0))
% 0.37/0.58        | ((k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_C))
% 0.37/0.58            = (sk_C)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['9', '16'])).
% 0.37/0.58  thf('18', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('19', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (((k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ X0)) = (X0))
% 0.37/0.58          | ((sk_A) = (k1_xboole_0))
% 0.37/0.58          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.37/0.58      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.37/0.58  thf('20', plain,
% 0.37/0.58      ((((sk_A) = (k1_xboole_0))
% 0.37/0.58        | ((k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_D))
% 0.37/0.58            = (sk_D)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.58  thf('21', plain, (((k1_funct_1 @ sk_B @ sk_C) = (k1_funct_1 @ sk_B @ sk_D))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('22', plain,
% 0.37/0.58      ((((sk_A) = (k1_xboole_0))
% 0.37/0.58        | ((k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_C))
% 0.37/0.58            = (sk_D)))),
% 0.37/0.58      inference('demod', [status(thm)], ['20', '21'])).
% 0.37/0.58  thf('23', plain,
% 0.37/0.58      ((((sk_C) = (sk_D)) | ((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.58      inference('sup+', [status(thm)], ['17', '22'])).
% 0.37/0.58  thf('24', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C) = (sk_D)))),
% 0.37/0.58      inference('simplify', [status(thm)], ['23'])).
% 0.37/0.58  thf('25', plain, (((sk_C) != (sk_D))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('26', plain, (((sk_A) = (k1_xboole_0))),
% 0.37/0.58      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.37/0.58  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.58  thf('28', plain, (![X0 : $i]: (m1_subset_1 @ sk_C @ X0)),
% 0.37/0.58      inference('demod', [status(thm)], ['8', '26', '27'])).
% 0.37/0.58  thf(t113_zfmisc_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.37/0.58       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.37/0.58  thf('29', plain,
% 0.37/0.58      (![X4 : $i, X5 : $i]:
% 0.37/0.58         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.37/0.58  thf('30', plain,
% 0.37/0.58      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.37/0.58      inference('simplify', [status(thm)], ['29'])).
% 0.37/0.58  thf(cc3_relset_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( v1_xboole_0 @ A ) =>
% 0.37/0.58       ( ![C:$i]:
% 0.37/0.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.58           ( v1_xboole_0 @ C ) ) ) ))).
% 0.37/0.58  thf('31', plain,
% 0.37/0.58      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.58         (~ (v1_xboole_0 @ X19)
% 0.37/0.58          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X21)))
% 0.37/0.58          | (v1_xboole_0 @ X20))),
% 0.37/0.58      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.37/0.58  thf('32', plain,
% 0.37/0.58      (![X1 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.37/0.58          | (v1_xboole_0 @ X1)
% 0.37/0.58          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['30', '31'])).
% 0.37/0.58  thf('33', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.58  thf('34', plain,
% 0.37/0.58      (![X1 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.37/0.58          | (v1_xboole_0 @ X1))),
% 0.37/0.58      inference('demod', [status(thm)], ['32', '33'])).
% 0.37/0.58  thf('35', plain, ((v1_xboole_0 @ sk_C)),
% 0.37/0.58      inference('sup-', [status(thm)], ['28', '34'])).
% 0.37/0.58  thf('36', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('37', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.58         (~ (v1_xboole_0 @ X1)
% 0.37/0.58          | (m1_subset_1 @ X2 @ X0)
% 0.37/0.58          | ~ (r2_hidden @ X2 @ X1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.58  thf('38', plain,
% 0.37/0.58      (![X0 : $i]: ((m1_subset_1 @ sk_D @ X0) | ~ (v1_xboole_0 @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.58  thf('39', plain, (((sk_A) = (k1_xboole_0))),
% 0.37/0.58      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.37/0.58  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.58  thf('41', plain, (![X0 : $i]: (m1_subset_1 @ sk_D @ X0)),
% 0.37/0.58      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.37/0.58  thf('42', plain,
% 0.37/0.58      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.58         (~ (v1_xboole_0 @ X19)
% 0.37/0.58          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X21)))
% 0.37/0.58          | (v1_xboole_0 @ X20))),
% 0.37/0.58      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.37/0.58  thf('43', plain, (![X1 : $i]: ((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ X1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['41', '42'])).
% 0.37/0.58  thf('44', plain,
% 0.37/0.58      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.58  thf('45', plain,
% 0.37/0.58      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.37/0.58      inference('simplify', [status(thm)], ['29'])).
% 0.37/0.58  thf('46', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.58      inference('sup+', [status(thm)], ['44', '45'])).
% 0.37/0.58  thf('47', plain,
% 0.37/0.58      (![X3 : $i, X4 : $i]:
% 0.37/0.58         (((X3) = (k1_xboole_0))
% 0.37/0.58          | ((X4) = (k1_xboole_0))
% 0.37/0.58          | ((k2_zfmisc_1 @ X4 @ X3) != (k1_xboole_0)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.37/0.58  thf('48', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (((k1_xboole_0) != (k1_xboole_0))
% 0.37/0.58          | ~ (v1_xboole_0 @ X1)
% 0.37/0.58          | ((X1) = (k1_xboole_0))
% 0.37/0.58          | ((X0) = (k1_xboole_0)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['46', '47'])).
% 0.37/0.58  thf('49', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (((X0) = (k1_xboole_0))
% 0.37/0.58          | ((X1) = (k1_xboole_0))
% 0.37/0.58          | ~ (v1_xboole_0 @ X1))),
% 0.37/0.58      inference('simplify', [status(thm)], ['48'])).
% 0.37/0.58  thf('50', plain, ((v1_xboole_0 @ sk_C)),
% 0.37/0.58      inference('sup-', [status(thm)], ['28', '34'])).
% 0.37/0.58  thf('51', plain,
% 0.37/0.58      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.58  thf('52', plain, (((k1_xboole_0) = (sk_C))),
% 0.37/0.58      inference('sup-', [status(thm)], ['50', '51'])).
% 0.37/0.58  thf('53', plain, (((k1_xboole_0) = (sk_C))),
% 0.37/0.58      inference('sup-', [status(thm)], ['50', '51'])).
% 0.37/0.58  thf('54', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (((X0) = (sk_C)) | ((X1) = (sk_C)) | ~ (v1_xboole_0 @ X1))),
% 0.37/0.58      inference('demod', [status(thm)], ['49', '52', '53'])).
% 0.37/0.58  thf('55', plain, (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (sk_C)))),
% 0.37/0.58      inference('condensation', [status(thm)], ['54'])).
% 0.37/0.58  thf('56', plain, (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((sk_D) = (sk_C)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['43', '55'])).
% 0.37/0.58  thf('57', plain, (((sk_C) != (sk_D))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('58', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 0.37/0.58      inference('simplify_reflect-', [status(thm)], ['56', '57'])).
% 0.37/0.58  thf('59', plain, ($false), inference('sup-', [status(thm)], ['35', '58'])).
% 0.37/0.58  
% 0.37/0.58  % SZS output end Refutation
% 0.37/0.58  
% 0.37/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
