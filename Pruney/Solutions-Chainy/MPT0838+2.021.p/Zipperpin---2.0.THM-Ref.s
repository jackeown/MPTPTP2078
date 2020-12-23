%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mIYa359BZp

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:01 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   76 (  95 expanded)
%              Number of leaves         :   31 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  430 ( 708 expanded)
%              Number of equality atoms :   22 (  36 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X10 ) )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ( X1 = X2 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t49_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
             => ~ ( ( ( k1_relset_1 @ A @ B @ C )
                   != k1_xboole_0 )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ B )
                     => ~ ( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
               => ~ ( ( ( k1_relset_1 @ A @ B @ C )
                     != k1_xboole_0 )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ B )
                       => ~ ( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_relset_1])).

thf('3',plain,(
    ( k1_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('6',plain,
    ( ( k1_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ( k1_relat_1 @ sk_C )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('10',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('11',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('13',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('simplify_reflect+',[status(thm)],['9','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('18',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('19',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ ( sk_B @ X6 ) @ X6 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X17 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('24',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( m1_subset_1 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X26: $i] :
      ( ~ ( r2_hidden @ X26 @ ( k2_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C ) )
      | ~ ( m1_subset_1 @ X26 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    v1_xboole_0 @ ( k2_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['21','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('31',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['18','31'])).

thf(t126_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A )
        = A ) ) )).

thf('33',plain,(
    ! [X13: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X13 ) @ X13 )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf(fc18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_xboole_0 @ B ) )
     => ( ( v1_xboole_0 @ ( k8_relat_1 @ B @ A ) )
        & ( v1_relat_1 @ ( k8_relat_1 @ B @ A ) ) ) ) )).

thf('34',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ( v1_xboole_0 @ ( k8_relat_1 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[fc18_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['10','13'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('40',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['37','38','41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['15','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mIYa359BZp
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:16:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 117 iterations in 0.165s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.65  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.46/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.65  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.46/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.65  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.65  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.46/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.65  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.65  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(fc10_relat_1, axiom,
% 0.46/0.65    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 0.46/0.65  thf('0', plain,
% 0.46/0.65      (![X10 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ (k1_relat_1 @ X10)) | ~ (v1_xboole_0 @ X10))),
% 0.46/0.65      inference('cnf', [status(esa)], [fc10_relat_1])).
% 0.46/0.65  thf(t8_boole, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.46/0.65  thf('1', plain,
% 0.46/0.65      (![X1 : $i, X2 : $i]:
% 0.46/0.65         (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X2) | ((X1) = (X2)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t8_boole])).
% 0.46/0.65  thf('2', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (v1_xboole_0 @ X0)
% 0.46/0.65          | ((k1_relat_1 @ X0) = (X1))
% 0.46/0.65          | ~ (v1_xboole_0 @ X1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.65  thf(t49_relset_1, conjecture,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.46/0.65           ( ![C:$i]:
% 0.46/0.65             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.65               ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.46/0.65                    ( ![D:$i]:
% 0.46/0.65                      ( ( m1_subset_1 @ D @ B ) =>
% 0.46/0.65                        ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i]:
% 0.46/0.65        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.65          ( ![B:$i]:
% 0.46/0.65            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.46/0.65              ( ![C:$i]:
% 0.46/0.65                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.65                  ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.46/0.65                       ( ![D:$i]:
% 0.46/0.65                         ( ( m1_subset_1 @ D @ B ) =>
% 0.46/0.65                           ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t49_relset_1])).
% 0.46/0.65  thf('3', plain, (((k1_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C) != (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('4', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(redefinition_k1_relset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.65       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.46/0.65  thf('5', plain,
% 0.46/0.65      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.65         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.46/0.65          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.46/0.65      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.65  thf('6', plain,
% 0.46/0.65      (((k1_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.46/0.65      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.65  thf('7', plain, (((k1_relat_1 @ sk_C) != (k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['3', '6'])).
% 0.46/0.65  thf('8', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((X0) != (k1_xboole_0))
% 0.46/0.65          | ~ (v1_xboole_0 @ X0)
% 0.46/0.65          | ~ (v1_xboole_0 @ sk_C))),
% 0.46/0.65      inference('sup-', [status(thm)], ['2', '7'])).
% 0.46/0.65  thf('9', plain, ((~ (v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['8'])).
% 0.46/0.65  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.46/0.65  thf('10', plain, ((v1_xboole_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.46/0.65  thf('11', plain, ((v1_xboole_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.46/0.65  thf(l13_xboole_0, axiom,
% 0.46/0.65    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.65  thf('12', plain,
% 0.46/0.65      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.65      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.46/0.65  thf('13', plain, (((sk_A) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.65  thf('14', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.65      inference('demod', [status(thm)], ['10', '13'])).
% 0.46/0.65  thf('15', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.46/0.65      inference('simplify_reflect+', [status(thm)], ['9', '14'])).
% 0.46/0.65  thf('16', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(redefinition_k2_relset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.65       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.46/0.65  thf('17', plain,
% 0.46/0.65      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.46/0.65         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 0.46/0.65          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.46/0.65      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      (((k2_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.46/0.65      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.65  thf(existence_m1_subset_1, axiom,
% 0.46/0.65    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.46/0.65  thf('19', plain, (![X6 : $i]: (m1_subset_1 @ (sk_B @ X6) @ X6)),
% 0.46/0.65      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.46/0.65  thf(d2_subset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( v1_xboole_0 @ A ) =>
% 0.46/0.65         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.46/0.65       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.65         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.46/0.65  thf('20', plain,
% 0.46/0.65      (![X3 : $i, X4 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X3 @ X4)
% 0.46/0.65          | (r2_hidden @ X3 @ X4)
% 0.46/0.65          | (v1_xboole_0 @ X4))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.46/0.65  thf('21', plain,
% 0.46/0.65      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.65  thf('22', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(dt_k2_relset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.65       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.46/0.65  thf('23', plain,
% 0.46/0.65      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.65         ((m1_subset_1 @ (k2_relset_1 @ X17 @ X18 @ X19) @ (k1_zfmisc_1 @ X18))
% 0.46/0.65          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      ((m1_subset_1 @ (k2_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C) @ 
% 0.46/0.65        (k1_zfmisc_1 @ sk_B_1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.65  thf(t4_subset, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.46/0.65       ( m1_subset_1 @ A @ C ) ))).
% 0.46/0.65  thf('25', plain,
% 0.46/0.65      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X7 @ X8)
% 0.46/0.65          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.46/0.65          | (m1_subset_1 @ X7 @ X9))),
% 0.46/0.65      inference('cnf', [status(esa)], [t4_subset])).
% 0.46/0.65  thf('26', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((m1_subset_1 @ X0 @ sk_B_1)
% 0.46/0.65          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.65  thf('27', plain,
% 0.46/0.65      (![X26 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X26 @ (k2_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C))
% 0.46/0.65          | ~ (m1_subset_1 @ X26 @ sk_B_1))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('28', plain,
% 0.46/0.65      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C))),
% 0.46/0.65      inference('clc', [status(thm)], ['26', '27'])).
% 0.46/0.65  thf('29', plain, ((v1_xboole_0 @ (k2_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C))),
% 0.46/0.65      inference('sup-', [status(thm)], ['21', '28'])).
% 0.46/0.65  thf('30', plain,
% 0.46/0.65      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.65      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.46/0.65  thf('31', plain, (((k2_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.65  thf('32', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['18', '31'])).
% 0.46/0.65  thf(t126_relat_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( v1_relat_1 @ A ) =>
% 0.46/0.65       ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A ) = ( A ) ) ))).
% 0.46/0.65  thf('33', plain,
% 0.46/0.65      (![X13 : $i]:
% 0.46/0.65         (((k8_relat_1 @ (k2_relat_1 @ X13) @ X13) = (X13))
% 0.46/0.65          | ~ (v1_relat_1 @ X13))),
% 0.46/0.65      inference('cnf', [status(esa)], [t126_relat_1])).
% 0.46/0.65  thf(fc18_relat_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_xboole_0 @ B ) ) =>
% 0.46/0.65       ( ( v1_xboole_0 @ ( k8_relat_1 @ B @ A ) ) & 
% 0.46/0.65         ( v1_relat_1 @ ( k8_relat_1 @ B @ A ) ) ) ))).
% 0.46/0.65  thf('34', plain,
% 0.46/0.65      (![X11 : $i, X12 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X11)
% 0.46/0.65          | ~ (v1_xboole_0 @ X12)
% 0.46/0.65          | (v1_xboole_0 @ (k8_relat_1 @ X12 @ X11)))),
% 0.46/0.65      inference('cnf', [status(esa)], [fc18_relat_1])).
% 0.46/0.65  thf('35', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.46/0.65          | ~ (v1_relat_1 @ X0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['33', '34'])).
% 0.46/0.65  thf('36', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | (v1_xboole_0 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['35'])).
% 0.46/0.65  thf('37', plain,
% 0.46/0.65      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | ~ (v1_relat_1 @ sk_C))),
% 0.46/0.65      inference('sup-', [status(thm)], ['32', '36'])).
% 0.46/0.65  thf('38', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.65      inference('demod', [status(thm)], ['10', '13'])).
% 0.46/0.65  thf('39', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(cc1_relset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.65       ( v1_relat_1 @ C ) ))).
% 0.46/0.65  thf('40', plain,
% 0.46/0.65      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.65         ((v1_relat_1 @ X14)
% 0.46/0.65          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.46/0.65      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.65  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.65      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.65  thf('42', plain, ((v1_xboole_0 @ sk_C)),
% 0.46/0.65      inference('demod', [status(thm)], ['37', '38', '41'])).
% 0.46/0.65  thf('43', plain, ($false), inference('demod', [status(thm)], ['15', '42'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
