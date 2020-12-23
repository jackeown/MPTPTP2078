%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gnL5LbzHcN

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:09 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   53 (  73 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  276 ( 478 expanded)
%              Number of equality atoms :   18 (  28 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X9 ) ) )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('3',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('4',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('5',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['3','4'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('7',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ( k8_relset_1 @ k1_xboole_0 @ sk_A @ k1_xboole_0 @ sk_B_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','7'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('9',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( ( k8_relset_1 @ X11 @ X12 @ X10 @ X13 )
        = ( k10_relat_1 @ X10 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k10_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ( k10_relat_1 @ k1_xboole_0 @ sk_B_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t47_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r1_tarski @ ( k8_relset_1 @ A @ B @ D @ C ) @ A ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k8_relset_1 @ X20 @ X21 @ X22 @ X23 ) @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t47_funct_2])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('18',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k10_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('20',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ ( k10_relat_1 @ k1_xboole_0 @ X2 ) @ X1 ) ),
    inference(demod,[status(thm)],['15','18','19'])).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('21',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('22',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['12','24'])).

thf('26',plain,(
    $false ),
    inference(simplify,[status(thm)],['25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gnL5LbzHcN
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:05:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.34/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.34/0.55  % Solved by: fo/fo7.sh
% 0.34/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.55  % done 76 iterations in 0.069s
% 0.34/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.34/0.55  % SZS output start Refutation
% 0.34/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.34/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.34/0.55  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.34/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.34/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.34/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.34/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.34/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.34/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.34/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.34/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.55  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.34/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.34/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.55  thf(t60_funct_2, conjecture,
% 0.34/0.55    (![A:$i,B:$i,C:$i]:
% 0.34/0.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.34/0.55         ( m1_subset_1 @
% 0.34/0.55           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.34/0.55       ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ))).
% 0.34/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.34/0.55        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.34/0.55            ( m1_subset_1 @
% 0.34/0.55              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.34/0.55          ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.34/0.55    inference('cnf.neg', [status(esa)], [t60_funct_2])).
% 0.34/0.55  thf('0', plain,
% 0.34/0.55      (((k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ sk_B_1) != (k1_xboole_0))),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf('1', plain,
% 0.34/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A)))),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf(cc3_relset_1, axiom,
% 0.34/0.55    (![A:$i,B:$i]:
% 0.34/0.55     ( ( v1_xboole_0 @ A ) =>
% 0.34/0.55       ( ![C:$i]:
% 0.34/0.55         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.55           ( v1_xboole_0 @ C ) ) ) ))).
% 0.34/0.55  thf('2', plain,
% 0.34/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.34/0.55         (~ (v1_xboole_0 @ X7)
% 0.34/0.55          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X9)))
% 0.34/0.55          | (v1_xboole_0 @ X8))),
% 0.34/0.55      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.34/0.55  thf('3', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.34/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.34/0.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.34/0.55  thf('4', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.34/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.34/0.55  thf('5', plain, ((v1_xboole_0 @ sk_C)),
% 0.34/0.55      inference('demod', [status(thm)], ['3', '4'])).
% 0.34/0.55  thf(l13_xboole_0, axiom,
% 0.34/0.55    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.34/0.55  thf('6', plain,
% 0.34/0.55      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.34/0.55      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.34/0.55  thf('7', plain, (((sk_C) = (k1_xboole_0))),
% 0.34/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.34/0.55  thf('8', plain,
% 0.34/0.55      (((k8_relset_1 @ k1_xboole_0 @ sk_A @ k1_xboole_0 @ sk_B_1)
% 0.34/0.55         != (k1_xboole_0))),
% 0.34/0.55      inference('demod', [status(thm)], ['0', '7'])).
% 0.34/0.55  thf(t4_subset_1, axiom,
% 0.34/0.55    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.34/0.55  thf('9', plain,
% 0.34/0.55      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.34/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.34/0.55  thf(redefinition_k8_relset_1, axiom,
% 0.34/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.34/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.55       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.34/0.55  thf('10', plain,
% 0.34/0.55      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.34/0.55         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.34/0.55          | ((k8_relset_1 @ X11 @ X12 @ X10 @ X13) = (k10_relat_1 @ X10 @ X13)))),
% 0.34/0.55      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.34/0.55  thf('11', plain,
% 0.34/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.55         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 0.34/0.55           = (k10_relat_1 @ k1_xboole_0 @ X2))),
% 0.34/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.34/0.55  thf('12', plain, (((k10_relat_1 @ k1_xboole_0 @ sk_B_1) != (k1_xboole_0))),
% 0.34/0.55      inference('demod', [status(thm)], ['8', '11'])).
% 0.34/0.55  thf('13', plain,
% 0.34/0.55      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.34/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.34/0.55  thf(t47_funct_2, axiom,
% 0.34/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.34/0.55     ( ( ( v1_funct_1 @ D ) & 
% 0.34/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.34/0.55       ( r1_tarski @ ( k8_relset_1 @ A @ B @ D @ C ) @ A ) ))).
% 0.34/0.55  thf('14', plain,
% 0.34/0.55      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.34/0.55         ((r1_tarski @ (k8_relset_1 @ X20 @ X21 @ X22 @ X23) @ X20)
% 0.34/0.55          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.34/0.55          | ~ (v1_funct_1 @ X22))),
% 0.34/0.55      inference('cnf', [status(esa)], [t47_funct_2])).
% 0.34/0.55  thf('15', plain,
% 0.34/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.55         (~ (v1_funct_1 @ k1_xboole_0)
% 0.34/0.55          | (r1_tarski @ (k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2) @ X1))),
% 0.34/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.34/0.55  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf('17', plain, (((sk_C) = (k1_xboole_0))),
% 0.34/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.34/0.55  thf('18', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.34/0.55      inference('demod', [status(thm)], ['16', '17'])).
% 0.34/0.55  thf('19', plain,
% 0.34/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.55         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 0.34/0.55           = (k10_relat_1 @ k1_xboole_0 @ X2))),
% 0.34/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.34/0.55  thf('20', plain,
% 0.34/0.55      (![X1 : $i, X2 : $i]: (r1_tarski @ (k10_relat_1 @ k1_xboole_0 @ X2) @ X1)),
% 0.34/0.55      inference('demod', [status(thm)], ['15', '18', '19'])).
% 0.34/0.55  thf(t6_mcart_1, axiom,
% 0.34/0.55    (![A:$i]:
% 0.34/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.34/0.55          ( ![B:$i]:
% 0.34/0.55            ( ~( ( r2_hidden @ B @ A ) & 
% 0.34/0.55                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.34/0.55                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.34/0.55                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.34/0.55                       ( r2_hidden @ G @ B ) ) =>
% 0.34/0.55                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.34/0.55  thf('21', plain,
% 0.34/0.55      (![X14 : $i]:
% 0.34/0.55         (((X14) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 0.34/0.55      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.34/0.55  thf(t7_ordinal1, axiom,
% 0.34/0.55    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.34/0.55  thf('22', plain,
% 0.34/0.55      (![X5 : $i, X6 : $i]: (~ (r2_hidden @ X5 @ X6) | ~ (r1_tarski @ X6 @ X5))),
% 0.34/0.55      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.34/0.55  thf('23', plain,
% 0.34/0.55      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.34/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.34/0.55  thf('24', plain,
% 0.34/0.55      (![X0 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.34/0.55      inference('sup-', [status(thm)], ['20', '23'])).
% 0.34/0.55  thf('25', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.34/0.55      inference('demod', [status(thm)], ['12', '24'])).
% 0.34/0.55  thf('26', plain, ($false), inference('simplify', [status(thm)], ['25'])).
% 0.34/0.55  
% 0.34/0.55  % SZS output end Refutation
% 0.34/0.55  
% 0.38/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
