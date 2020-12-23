%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oHa2FWmUaJ

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   49 (  52 expanded)
%              Number of leaves         :   24 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  251 ( 300 expanded)
%              Number of equality atoms :   24 (  29 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C_1 @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('1',plain,(
    ! [X21: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X21 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('4',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','4'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    r1_tarski @ sk_C_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('11',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ~ ( r2_hidden @ X7 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['9','13'])).

thf('15',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','14'])).

thf('16',plain,(
    ( k8_relset_1 @ k1_xboole_0 @ sk_A @ k1_xboole_0 @ sk_B_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','15'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('17',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( ( k8_relset_1 @ X18 @ X19 @ X17 @ X20 )
        = ( k10_relat_1 @ X17 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k10_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t172_relat_1,axiom,(
    ! [A: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('20',plain,(
    ! [X16: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t172_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['16','21'])).

thf('23',plain,(
    $false ),
    inference(simplify,[status(thm)],['22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oHa2FWmUaJ
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:54:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 42 iterations in 0.019s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.49  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.49  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.22/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(t60_funct_2, conjecture,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.22/0.49         ( m1_subset_1 @
% 0.22/0.49           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.22/0.49       ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.49        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.22/0.49            ( m1_subset_1 @
% 0.22/0.49              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.22/0.49          ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t60_funct_2])).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      (((k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C_1 @ sk_B_1) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t9_mcart_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49          ( ![B:$i]:
% 0.22/0.49            ( ~( ( r2_hidden @ B @ A ) & 
% 0.22/0.49                 ( ![C:$i,D:$i]:
% 0.22/0.49                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.22/0.49                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X21 : $i]:
% 0.22/0.49         (((X21) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X21) @ X21))),
% 0.22/0.49      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_C_1 @ 
% 0.22/0.49        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t113_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.49       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i]:
% 0.22/0.49         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.22/0.49      inference('simplify', [status(thm)], ['3'])).
% 0.22/0.49  thf('5', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.22/0.49      inference('demod', [status(thm)], ['2', '4'])).
% 0.22/0.49  thf(t3_subset, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i]:
% 0.22/0.49         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.49  thf('7', plain, ((r1_tarski @ sk_C_1 @ k1_xboole_0)),
% 0.22/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.49  thf(d3_tarski, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.49          | (r2_hidden @ X0 @ X2)
% 0.22/0.49          | ~ (r1_tarski @ X1 @ X2))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i]:
% 0.22/0.49         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.49      inference('simplify', [status(thm)], ['10'])).
% 0.22/0.49  thf(t152_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X7 : $i, X8 : $i]: ~ (r2_hidden @ X7 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.22/0.49      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.22/0.49  thf('13', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf('14', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C_1)),
% 0.22/0.49      inference('clc', [status(thm)], ['9', '13'])).
% 0.22/0.49  thf('15', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['1', '14'])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (((k8_relset_1 @ k1_xboole_0 @ sk_A @ k1_xboole_0 @ sk_B_1)
% 0.22/0.49         != (k1_xboole_0))),
% 0.22/0.49      inference('demod', [status(thm)], ['0', '15'])).
% 0.22/0.49  thf(t4_subset_1, axiom,
% 0.22/0.49    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.22/0.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.49  thf(redefinition_k8_relset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.49       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.22/0.49          | ((k8_relset_1 @ X18 @ X19 @ X17 @ X20) = (k10_relat_1 @ X17 @ X20)))),
% 0.22/0.49      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 0.22/0.49           = (k10_relat_1 @ k1_xboole_0 @ X2))),
% 0.22/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.49  thf(t172_relat_1, axiom,
% 0.22/0.49    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (![X16 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [t172_relat_1])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.22/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.22/0.49  thf('22', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.49      inference('demod', [status(thm)], ['16', '21'])).
% 0.22/0.49  thf('23', plain, ($false), inference('simplify', [status(thm)], ['22'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
