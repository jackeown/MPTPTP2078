%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TS7a592M2o

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:05 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   49 (  86 expanded)
%              Number of leaves         :   19 (  34 expanded)
%              Depth                    :   13
%              Number of atoms          :  254 ( 563 expanded)
%              Number of equality atoms :   27 (  64 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t59_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ k1_xboole_0 @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) )
     => ( ( k7_relset_1 @ k1_xboole_0 @ A @ C @ B )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ k1_xboole_0 @ A )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) )
       => ( ( k7_relset_1 @ k1_xboole_0 @ A @ C @ B )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t59_funct_2])).

thf('0',plain,(
    ( k7_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('2',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('6',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','7'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X5 ) ) )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('12',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('13',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('14',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('16',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ( k7_relset_1 @ k1_xboole_0 @ sk_A @ k1_xboole_0 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','6'])).

thf('19',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('20',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('22',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( ( k7_relset_1 @ X9 @ X10 @ X8 @ X11 )
        = ( k9_relat_1 @ X8 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k7_relset_1 @ k1_xboole_0 @ X0 @ X1 @ X2 )
        = ( k9_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relset_1 @ k1_xboole_0 @ X1 @ k1_xboole_0 @ X0 )
      = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('25',plain,(
    ! [X4: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relset_1 @ k1_xboole_0 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['17','26'])).

thf('28',plain,(
    $false ),
    inference(simplify,[status(thm)],['27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TS7a592M2o
% 0.17/0.35  % Computer   : n022.cluster.edu
% 0.17/0.35  % Model      : x86_64 x86_64
% 0.17/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.35  % Memory     : 8042.1875MB
% 0.17/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.35  % CPULimit   : 60
% 0.17/0.35  % DateTime   : Tue Dec  1 15:49:11 EST 2020
% 0.17/0.35  % CPUTime    : 
% 0.17/0.35  % Running portfolio for 600 s
% 0.17/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.35  % Number of cores: 8
% 0.17/0.36  % Python version: Python 3.6.8
% 0.17/0.36  % Running in FO mode
% 0.43/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.59  % Solved by: fo/fo7.sh
% 0.43/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.59  % done 194 iterations in 0.132s
% 0.43/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.59  % SZS output start Refutation
% 0.43/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.43/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.43/0.59  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.43/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.59  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.43/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.43/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.43/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.43/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.43/0.59  thf(t59_funct_2, conjecture,
% 0.43/0.59    (![A:$i,B:$i,C:$i]:
% 0.43/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.43/0.59         ( m1_subset_1 @
% 0.43/0.59           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.43/0.59       ( ( k7_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ))).
% 0.43/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.43/0.59        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.43/0.59            ( m1_subset_1 @
% 0.43/0.59              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.43/0.59          ( ( k7_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.43/0.59    inference('cnf.neg', [status(esa)], [t59_funct_2])).
% 0.43/0.59  thf('0', plain,
% 0.43/0.59      (((k7_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ sk_B) != (k1_xboole_0))),
% 0.43/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.59  thf(t113_zfmisc_1, axiom,
% 0.43/0.59    (![A:$i,B:$i]:
% 0.43/0.59     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.43/0.59       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.43/0.59  thf('1', plain,
% 0.43/0.59      (![X2 : $i, X3 : $i]:
% 0.43/0.59         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.43/0.59      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.43/0.59  thf('2', plain,
% 0.43/0.59      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.59      inference('simplify', [status(thm)], ['1'])).
% 0.43/0.59  thf(l13_xboole_0, axiom,
% 0.43/0.59    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.43/0.59  thf('3', plain,
% 0.43/0.59      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.43/0.59      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.43/0.59  thf('4', plain,
% 0.43/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A)))),
% 0.43/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.59  thf('5', plain,
% 0.43/0.59      (![X2 : $i, X3 : $i]:
% 0.43/0.59         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.43/0.59      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.43/0.59  thf('6', plain,
% 0.43/0.59      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.43/0.59      inference('simplify', [status(thm)], ['5'])).
% 0.43/0.59  thf('7', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.43/0.59      inference('demod', [status(thm)], ['4', '6'])).
% 0.43/0.59  thf('8', plain,
% 0.43/0.59      (![X0 : $i]:
% 0.43/0.59         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.43/0.59      inference('sup+', [status(thm)], ['3', '7'])).
% 0.43/0.59  thf(cc4_relset_1, axiom,
% 0.43/0.59    (![A:$i,B:$i]:
% 0.43/0.59     ( ( v1_xboole_0 @ A ) =>
% 0.43/0.59       ( ![C:$i]:
% 0.43/0.59         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.43/0.59           ( v1_xboole_0 @ C ) ) ) ))).
% 0.43/0.59  thf('9', plain,
% 0.43/0.59      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.43/0.59         (~ (v1_xboole_0 @ X5)
% 0.43/0.59          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X5)))
% 0.43/0.59          | (v1_xboole_0 @ X6))),
% 0.43/0.59      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.43/0.59  thf('10', plain,
% 0.43/0.59      (![X0 : $i, X1 : $i]:
% 0.43/0.59         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.43/0.59          | (v1_xboole_0 @ sk_C)
% 0.43/0.59          | ~ (v1_xboole_0 @ X0))),
% 0.43/0.59      inference('sup-', [status(thm)], ['8', '9'])).
% 0.43/0.59  thf('11', plain,
% 0.43/0.59      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.43/0.59        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.43/0.59        | (v1_xboole_0 @ sk_C))),
% 0.43/0.59      inference('sup-', [status(thm)], ['2', '10'])).
% 0.43/0.59  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.43/0.59  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.43/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.43/0.59  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.43/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.43/0.59  thf('14', plain, ((v1_xboole_0 @ sk_C)),
% 0.43/0.59      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.43/0.59  thf('15', plain,
% 0.43/0.59      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.43/0.59      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.43/0.59  thf('16', plain, (((sk_C) = (k1_xboole_0))),
% 0.43/0.59      inference('sup-', [status(thm)], ['14', '15'])).
% 0.43/0.59  thf('17', plain,
% 0.43/0.59      (((k7_relset_1 @ k1_xboole_0 @ sk_A @ k1_xboole_0 @ sk_B)
% 0.43/0.59         != (k1_xboole_0))),
% 0.43/0.59      inference('demod', [status(thm)], ['0', '16'])).
% 0.43/0.59  thf('18', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.43/0.59      inference('demod', [status(thm)], ['4', '6'])).
% 0.43/0.59  thf('19', plain, (((sk_C) = (k1_xboole_0))),
% 0.43/0.59      inference('sup-', [status(thm)], ['14', '15'])).
% 0.43/0.59  thf('20', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.43/0.59      inference('demod', [status(thm)], ['18', '19'])).
% 0.43/0.59  thf('21', plain,
% 0.43/0.59      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.43/0.59      inference('simplify', [status(thm)], ['5'])).
% 0.43/0.59  thf(redefinition_k7_relset_1, axiom,
% 0.43/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.59       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.43/0.59  thf('22', plain,
% 0.43/0.59      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.43/0.59         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.43/0.59          | ((k7_relset_1 @ X9 @ X10 @ X8 @ X11) = (k9_relat_1 @ X8 @ X11)))),
% 0.43/0.59      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.43/0.59  thf('23', plain,
% 0.43/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.59         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.43/0.59          | ((k7_relset_1 @ k1_xboole_0 @ X0 @ X1 @ X2)
% 0.43/0.59              = (k9_relat_1 @ X1 @ X2)))),
% 0.43/0.59      inference('sup-', [status(thm)], ['21', '22'])).
% 0.43/0.59  thf('24', plain,
% 0.43/0.59      (![X0 : $i, X1 : $i]:
% 0.43/0.59         ((k7_relset_1 @ k1_xboole_0 @ X1 @ k1_xboole_0 @ X0)
% 0.43/0.59           = (k9_relat_1 @ k1_xboole_0 @ X0))),
% 0.43/0.59      inference('sup-', [status(thm)], ['20', '23'])).
% 0.43/0.59  thf(t150_relat_1, axiom,
% 0.43/0.59    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.43/0.59  thf('25', plain,
% 0.43/0.59      (![X4 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 0.43/0.59      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.43/0.59  thf('26', plain,
% 0.43/0.59      (![X0 : $i, X1 : $i]:
% 0.43/0.59         ((k7_relset_1 @ k1_xboole_0 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.43/0.59      inference('demod', [status(thm)], ['24', '25'])).
% 0.43/0.59  thf('27', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.43/0.59      inference('demod', [status(thm)], ['17', '26'])).
% 0.43/0.59  thf('28', plain, ($false), inference('simplify', [status(thm)], ['27'])).
% 0.43/0.59  
% 0.43/0.59  % SZS output end Refutation
% 0.43/0.59  
% 0.43/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
