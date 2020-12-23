%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.42nDBelBvQ

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   74 (  93 expanded)
%              Number of leaves         :   32 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :  393 ( 731 expanded)
%              Number of equality atoms :   17 (  29 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X13: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
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
    ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
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

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('10',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('11',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('simplify_reflect+',[status(thm)],['9','10'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('13',plain,(
    ! [X26: $i] :
      ( ~ ( r2_hidden @ X26 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C ) )
      | ~ ( m1_subset_1 @ X26 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('16',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X26: $i] :
      ( ~ ( r2_hidden @ X26 @ ( k2_relat_1 @ sk_C ) )
      | ~ ( m1_subset_1 @ X26 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('20',plain,(
    v5_relat_1 @ sk_C @ sk_B_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v5_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('24',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('26',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ),
    inference(demod,[status(thm)],['22','27'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('31',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( m1_subset_1 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X26: $i] :
      ~ ( r2_hidden @ X26 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['17','32'])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','33'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('35',plain,(
    ! [X16: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('36',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['25','26'])).

thf('39',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['11','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.42nDBelBvQ
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:25:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.57  % Solved by: fo/fo7.sh
% 0.22/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.57  % done 99 iterations in 0.100s
% 0.22/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.57  % SZS output start Refutation
% 0.22/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.57  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.22/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.57  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.57  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.57  thf(fc10_relat_1, axiom,
% 0.22/0.57    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 0.22/0.57  thf('0', plain,
% 0.22/0.57      (![X13 : $i]:
% 0.22/0.57         ((v1_xboole_0 @ (k1_relat_1 @ X13)) | ~ (v1_xboole_0 @ X13))),
% 0.22/0.57      inference('cnf', [status(esa)], [fc10_relat_1])).
% 0.22/0.57  thf(t8_boole, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.22/0.57  thf('1', plain,
% 0.22/0.57      (![X1 : $i, X2 : $i]:
% 0.22/0.57         (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X2) | ((X1) = (X2)))),
% 0.22/0.57      inference('cnf', [status(esa)], [t8_boole])).
% 0.22/0.57  thf('2', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (~ (v1_xboole_0 @ X0)
% 0.22/0.57          | ((k1_relat_1 @ X0) = (X1))
% 0.22/0.57          | ~ (v1_xboole_0 @ X1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.57  thf(t49_relset_1, conjecture,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.57       ( ![B:$i]:
% 0.22/0.57         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.57           ( ![C:$i]:
% 0.22/0.57             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.57               ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.22/0.57                    ( ![D:$i]:
% 0.22/0.57                      ( ( m1_subset_1 @ D @ B ) =>
% 0.22/0.57                        ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.57    (~( ![A:$i]:
% 0.22/0.57        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.57          ( ![B:$i]:
% 0.22/0.57            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.57              ( ![C:$i]:
% 0.22/0.57                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.57                  ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.22/0.57                       ( ![D:$i]:
% 0.22/0.57                         ( ( m1_subset_1 @ D @ B ) =>
% 0.22/0.57                           ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.57    inference('cnf.neg', [status(esa)], [t49_relset_1])).
% 0.22/0.57  thf('3', plain, (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) != (k1_xboole_0))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('4', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(redefinition_k1_relset_1, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.57       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.22/0.57  thf('5', plain,
% 0.22/0.57      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.57         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.22/0.57          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.22/0.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.22/0.57  thf('6', plain,
% 0.22/0.57      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.22/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.57  thf('7', plain, (((k1_relat_1 @ sk_C) != (k1_xboole_0))),
% 0.22/0.57      inference('demod', [status(thm)], ['3', '6'])).
% 0.22/0.57  thf('8', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (((X0) != (k1_xboole_0))
% 0.22/0.57          | ~ (v1_xboole_0 @ X0)
% 0.22/0.57          | ~ (v1_xboole_0 @ sk_C))),
% 0.22/0.57      inference('sup-', [status(thm)], ['2', '7'])).
% 0.22/0.57  thf('9', plain, ((~ (v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.22/0.57      inference('simplify', [status(thm)], ['8'])).
% 0.22/0.57  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.57  thf('10', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.57  thf('11', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.22/0.57      inference('simplify_reflect+', [status(thm)], ['9', '10'])).
% 0.22/0.57  thf(t7_xboole_0, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.57          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.57  thf('12', plain,
% 0.22/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.22/0.57      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.57  thf('13', plain,
% 0.22/0.57      (![X26 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X26 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.22/0.57          | ~ (m1_subset_1 @ X26 @ sk_B_1))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('14', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(redefinition_k2_relset_1, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.57       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.22/0.57  thf('15', plain,
% 0.22/0.57      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.57         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 0.22/0.57          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.22/0.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.22/0.57  thf('16', plain,
% 0.22/0.57      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.22/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.57  thf('17', plain,
% 0.22/0.57      (![X26 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X26 @ (k2_relat_1 @ sk_C))
% 0.22/0.57          | ~ (m1_subset_1 @ X26 @ sk_B_1))),
% 0.22/0.57      inference('demod', [status(thm)], ['13', '16'])).
% 0.22/0.57  thf('18', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(cc2_relset_1, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.57       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.57  thf('19', plain,
% 0.22/0.57      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.57         ((v5_relat_1 @ X17 @ X19)
% 0.22/0.57          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.22/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.57  thf('20', plain, ((v5_relat_1 @ sk_C @ sk_B_1)),
% 0.22/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.57  thf(d19_relat_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( v1_relat_1 @ B ) =>
% 0.22/0.57       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.57  thf('21', plain,
% 0.22/0.57      (![X11 : $i, X12 : $i]:
% 0.22/0.57         (~ (v5_relat_1 @ X11 @ X12)
% 0.22/0.57          | (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 0.22/0.57          | ~ (v1_relat_1 @ X11))),
% 0.22/0.57      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.22/0.57  thf('22', plain,
% 0.22/0.57      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.57  thf('23', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(cc2_relat_1, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( v1_relat_1 @ A ) =>
% 0.22/0.57       ( ![B:$i]:
% 0.22/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.22/0.57  thf('24', plain,
% 0.22/0.57      (![X9 : $i, X10 : $i]:
% 0.22/0.57         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.22/0.57          | (v1_relat_1 @ X9)
% 0.22/0.57          | ~ (v1_relat_1 @ X10))),
% 0.22/0.57      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.57  thf('25', plain,
% 0.22/0.57      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C))),
% 0.22/0.57      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.57  thf(fc6_relat_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.57  thf('26', plain,
% 0.22/0.57      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 0.22/0.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.57  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.57      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.57  thf('28', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)),
% 0.22/0.57      inference('demod', [status(thm)], ['22', '27'])).
% 0.22/0.57  thf(t3_subset, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.57  thf('29', plain,
% 0.22/0.57      (![X3 : $i, X5 : $i]:
% 0.22/0.57         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.22/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.57  thf('30', plain,
% 0.22/0.57      ((m1_subset_1 @ (k2_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.57  thf(t4_subset, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.22/0.57       ( m1_subset_1 @ A @ C ) ))).
% 0.22/0.57  thf('31', plain,
% 0.22/0.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X6 @ X7)
% 0.22/0.57          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.22/0.57          | (m1_subset_1 @ X6 @ X8))),
% 0.22/0.57      inference('cnf', [status(esa)], [t4_subset])).
% 0.22/0.57  thf('32', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         ((m1_subset_1 @ X0 @ sk_B_1)
% 0.22/0.57          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.57  thf('33', plain, (![X26 : $i]: ~ (r2_hidden @ X26 @ (k2_relat_1 @ sk_C))),
% 0.22/0.57      inference('clc', [status(thm)], ['17', '32'])).
% 0.22/0.57  thf('34', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['12', '33'])).
% 0.22/0.57  thf(fc9_relat_1, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.22/0.57       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.22/0.57  thf('35', plain,
% 0.22/0.57      (![X16 : $i]:
% 0.22/0.57         (~ (v1_xboole_0 @ (k2_relat_1 @ X16))
% 0.22/0.57          | ~ (v1_relat_1 @ X16)
% 0.22/0.57          | (v1_xboole_0 @ X16))),
% 0.22/0.57      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.22/0.57  thf('36', plain,
% 0.22/0.57      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.57        | (v1_xboole_0 @ sk_C)
% 0.22/0.57        | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.57      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.57  thf('37', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.57  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.57      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.57  thf('39', plain, ((v1_xboole_0 @ sk_C)),
% 0.22/0.57      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.22/0.57  thf('40', plain, ($false), inference('demod', [status(thm)], ['11', '39'])).
% 0.22/0.57  
% 0.22/0.57  % SZS output end Refutation
% 0.22/0.57  
% 0.22/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
