%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3P1v7RQPm8

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:08 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   52 (  93 expanded)
%              Number of leaves         :   20 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :  252 ( 537 expanded)
%              Number of equality atoms :   27 (  60 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(t60_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ k1_xboole_0 @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) )
     => ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ k1_xboole_0 @ A )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) )
       => ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t60_funct_2])).

thf('0',plain,(
    ( k8_relset_1 @ k1_xboole_0 @ sk_A_1 @ sk_C @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('3',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['1','3'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('6',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('7',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('8',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('10',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('14',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ( k8_relset_1 @ k1_xboole_0 @ sk_A_1 @ k1_xboole_0 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','14'])).

thf('16',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['1','3'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('22',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ( ( k8_relset_1 @ X8 @ X9 @ X7 @ X10 )
        = ( k10_relat_1 @ X7 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = ( k10_relat_1 @ k1_xboole_0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t172_relat_1,axiom,(
    ! [A: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('24',plain,(
    ! [X6: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t172_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k8_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','25'])).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['7','10'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['15','28'])).

thf('30',plain,(
    $false ),
    inference(simplify,[status(thm)],['29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3P1v7RQPm8
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:33:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 107 iterations in 0.085s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.54  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.54  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.36/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.54  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.36/0.54  thf(t60_funct_2, conjecture,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.36/0.54         ( m1_subset_1 @
% 0.36/0.54           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.36/0.54       ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.54        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.36/0.54            ( m1_subset_1 @
% 0.36/0.54              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.36/0.54          ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t60_funct_2])).
% 0.36/0.54  thf('0', plain,
% 0.36/0.54      (((k8_relset_1 @ k1_xboole_0 @ sk_A_1 @ sk_C @ sk_B) != (k1_xboole_0))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('1', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_C @ 
% 0.36/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A_1)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t113_zfmisc_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.36/0.54       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.36/0.54  thf('2', plain,
% 0.36/0.54      (![X2 : $i, X3 : $i]:
% 0.36/0.54         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.36/0.54  thf('3', plain,
% 0.36/0.54      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.36/0.54      inference('simplify', [status(thm)], ['2'])).
% 0.36/0.54  thf('4', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.36/0.54      inference('demod', [status(thm)], ['1', '3'])).
% 0.36/0.54  thf(cc1_subset_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( v1_xboole_0 @ A ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.36/0.54  thf('5', plain,
% 0.36/0.54      (![X4 : $i, X5 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.36/0.54          | (v1_xboole_0 @ X4)
% 0.36/0.54          | ~ (v1_xboole_0 @ X5))),
% 0.36/0.54      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.36/0.54  thf('6', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_C))),
% 0.36/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.54  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.36/0.54  thf('7', plain, ((v1_xboole_0 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.36/0.54  thf('8', plain, ((v1_xboole_0 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.36/0.54  thf(l13_xboole_0, axiom,
% 0.36/0.54    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.54  thf('9', plain,
% 0.36/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.36/0.54  thf('10', plain, (((sk_A) = (k1_xboole_0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.54  thf('11', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.54      inference('demod', [status(thm)], ['7', '10'])).
% 0.36/0.54  thf('12', plain, ((v1_xboole_0 @ sk_C)),
% 0.36/0.54      inference('demod', [status(thm)], ['6', '11'])).
% 0.36/0.54  thf('13', plain,
% 0.36/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.36/0.54  thf('14', plain, (((sk_C) = (k1_xboole_0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.36/0.54  thf('15', plain,
% 0.36/0.54      (((k8_relset_1 @ k1_xboole_0 @ sk_A_1 @ k1_xboole_0 @ sk_B)
% 0.36/0.54         != (k1_xboole_0))),
% 0.36/0.54      inference('demod', [status(thm)], ['0', '14'])).
% 0.36/0.54  thf('16', plain,
% 0.36/0.54      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.36/0.54      inference('simplify', [status(thm)], ['2'])).
% 0.36/0.54  thf('17', plain,
% 0.36/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.36/0.54  thf('18', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.36/0.54      inference('demod', [status(thm)], ['1', '3'])).
% 0.36/0.54  thf('19', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.54      inference('sup+', [status(thm)], ['17', '18'])).
% 0.36/0.54  thf('20', plain, (((sk_C) = (k1_xboole_0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.36/0.54  thf('21', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.36/0.54          | ~ (v1_xboole_0 @ X0))),
% 0.36/0.54      inference('demod', [status(thm)], ['19', '20'])).
% 0.36/0.54  thf(redefinition_k8_relset_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.54       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.36/0.54  thf('22', plain,
% 0.36/0.54      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.36/0.54          | ((k8_relset_1 @ X8 @ X9 @ X7 @ X10) = (k10_relat_1 @ X7 @ X10)))),
% 0.36/0.54      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.36/0.54  thf('23', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.54         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.36/0.54          | ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 0.36/0.54              = (k10_relat_1 @ k1_xboole_0 @ X2)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['21', '22'])).
% 0.36/0.54  thf(t172_relat_1, axiom,
% 0.36/0.54    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.36/0.54  thf('24', plain,
% 0.36/0.54      (![X6 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.36/0.54      inference('cnf', [status(esa)], [t172_relat_1])).
% 0.36/0.54  thf('25', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.54         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.36/0.54          | ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0)))),
% 0.36/0.54      inference('demod', [status(thm)], ['23', '24'])).
% 0.36/0.54  thf('26', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.36/0.54          | ((k8_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 @ X1)
% 0.36/0.54              = (k1_xboole_0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['16', '25'])).
% 0.36/0.54  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.54      inference('demod', [status(thm)], ['7', '10'])).
% 0.36/0.54  thf('28', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((k8_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 @ X1) = (k1_xboole_0))),
% 0.36/0.54      inference('demod', [status(thm)], ['26', '27'])).
% 0.36/0.54  thf('29', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.36/0.54      inference('demod', [status(thm)], ['15', '28'])).
% 0.36/0.54  thf('30', plain, ($false), inference('simplify', [status(thm)], ['29'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.36/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
