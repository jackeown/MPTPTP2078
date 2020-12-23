%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IxhuJpsZZX

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   68 (  83 expanded)
%              Number of leaves         :   30 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :  400 ( 722 expanded)
%              Number of equality atoms :   29 (  41 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('2',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ~ ( r2_hidden @ X5 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

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

thf('6',plain,(
    ! [X28: $i] :
      ( ~ ( r2_hidden @ X28 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X28 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('9',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X28: $i] :
      ( ~ ( r2_hidden @ X28 @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X28 @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('13',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v5_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('18',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['15','18'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('22',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( m1_subset_1 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X28: $i] :
      ~ ( r2_hidden @ X28 @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['10','23'])).

thf('25',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','24'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('26',plain,(
    ! [X15: $i] :
      ( ( ( k2_relat_1 @ X15 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X15 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('27',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('29',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('33',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('34',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['30','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IxhuJpsZZX
% 0.14/0.36  % Computer   : n024.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 16:14:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 59 iterations in 0.032s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.51  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.51  thf(t2_tarski, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.22/0.51       ( ( A ) = ( B ) ) ))).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (((X1) = (X0))
% 0.22/0.51          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.22/0.51          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.22/0.51      inference('cnf', [status(esa)], [t2_tarski])).
% 0.22/0.51  thf(t113_zfmisc_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.51       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      (![X3 : $i, X4 : $i]:
% 0.22/0.51         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.51      inference('simplify', [status(thm)], ['1'])).
% 0.22/0.51  thf(t152_zfmisc_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      (![X5 : $i, X6 : $i]: ~ (r2_hidden @ X5 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.22/0.51      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.22/0.51  thf('4', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.22/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0) | ((k1_xboole_0) = (X0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['0', '4'])).
% 0.22/0.51  thf(t49_relset_1, conjecture,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.51               ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.22/0.51                    ( ![D:$i]:
% 0.22/0.51                      ( ( m1_subset_1 @ D @ B ) =>
% 0.22/0.51                        ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i]:
% 0.22/0.51        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.51          ( ![B:$i]:
% 0.22/0.51            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.51              ( ![C:$i]:
% 0.22/0.51                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.51                  ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.22/0.51                       ( ![D:$i]:
% 0.22/0.51                         ( ( m1_subset_1 @ D @ B ) =>
% 0.22/0.51                           ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t49_relset_1])).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      (![X28 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X28 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 0.22/0.51          | ~ (m1_subset_1 @ X28 @ sk_B))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(redefinition_k2_relset_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.51       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.22/0.51         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 0.22/0.51          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.22/0.51      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.22/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (![X28 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X28 @ (k2_relat_1 @ sk_C_1))
% 0.22/0.51          | ~ (m1_subset_1 @ X28 @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['6', '9'])).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(cc2_relset_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.51         ((v5_relat_1 @ X19 @ X21)
% 0.22/0.51          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.22/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.51  thf('13', plain, ((v5_relat_1 @ sk_C_1 @ sk_B)),
% 0.22/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.51  thf(d19_relat_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ B ) =>
% 0.22/0.51       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      (![X13 : $i, X14 : $i]:
% 0.22/0.51         (~ (v5_relat_1 @ X13 @ X14)
% 0.22/0.51          | (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 0.22/0.51          | ~ (v1_relat_1 @ X13))),
% 0.22/0.51      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(cc1_relset_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.51       ( v1_relat_1 @ C ) ))).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.51         ((v1_relat_1 @ X16)
% 0.22/0.51          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.22/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.51  thf('18', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.51  thf('19', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)),
% 0.22/0.51      inference('demod', [status(thm)], ['15', '18'])).
% 0.22/0.51  thf(t3_subset, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      (![X7 : $i, X9 : $i]:
% 0.22/0.51         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.22/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      ((m1_subset_1 @ (k2_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.51  thf(t4_subset, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.22/0.51       ( m1_subset_1 @ A @ C ) ))).
% 0.22/0.51  thf('22', plain,
% 0.22/0.51      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X10 @ X11)
% 0.22/0.51          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.22/0.51          | (m1_subset_1 @ X10 @ X12))),
% 0.22/0.51      inference('cnf', [status(esa)], [t4_subset])).
% 0.22/0.51  thf('23', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((m1_subset_1 @ X0 @ sk_B)
% 0.22/0.51          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.51  thf('24', plain, (![X28 : $i]: ~ (r2_hidden @ X28 @ (k2_relat_1 @ sk_C_1))),
% 0.22/0.51      inference('clc', [status(thm)], ['10', '23'])).
% 0.22/0.51  thf('25', plain, (((k1_xboole_0) = (k2_relat_1 @ sk_C_1))),
% 0.22/0.51      inference('sup-', [status(thm)], ['5', '24'])).
% 0.22/0.51  thf(t65_relat_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ A ) =>
% 0.22/0.51       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.51         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.51  thf('26', plain,
% 0.22/0.51      (![X15 : $i]:
% 0.22/0.51         (((k2_relat_1 @ X15) != (k1_xboole_0))
% 0.22/0.51          | ((k1_relat_1 @ X15) = (k1_xboole_0))
% 0.22/0.51          | ~ (v1_relat_1 @ X15))),
% 0.22/0.51      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.22/0.51  thf('27', plain,
% 0.22/0.51      ((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.51        | ~ (v1_relat_1 @ sk_C_1)
% 0.22/0.51        | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.51  thf('28', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.51  thf('29', plain,
% 0.22/0.51      ((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.51        | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.22/0.51      inference('demod', [status(thm)], ['27', '28'])).
% 0.22/0.51  thf('30', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.22/0.51      inference('simplify', [status(thm)], ['29'])).
% 0.22/0.51  thf('31', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) != (k1_xboole_0))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('32', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(redefinition_k1_relset_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.51       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.22/0.51  thf('33', plain,
% 0.22/0.51      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.22/0.51         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 0.22/0.51          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.22/0.51      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.22/0.51  thf('34', plain,
% 0.22/0.51      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.22/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.51  thf('35', plain, (((k1_relat_1 @ sk_C_1) != (k1_xboole_0))),
% 0.22/0.51      inference('demod', [status(thm)], ['31', '34'])).
% 0.22/0.51  thf('36', plain, ($false),
% 0.22/0.51      inference('simplify_reflect-', [status(thm)], ['30', '35'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
