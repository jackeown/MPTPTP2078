%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1QdL6Icuen

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:26 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   65 (  75 expanded)
%              Number of leaves         :   29 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :  407 ( 587 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relset_1_type,type,(
    k5_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t34_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ( r1_tarski @ B @ C )
       => ( r2_relset_1 @ B @ A @ ( k5_relset_1 @ B @ A @ D @ C ) @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
       => ( ( r1_tarski @ B @ C )
         => ( r2_relset_1 @ B @ A @ ( k5_relset_1 @ B @ A @ D @ C ) @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_relset_1])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_B @ sk_A @ ( k5_relset_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k5_relset_1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( ( k5_relset_1 @ X24 @ X25 @ X23 @ X26 )
        = ( k7_relat_1 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_B @ sk_A @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( r2_hidden @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('7',plain,(
    ! [X9: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('8',plain,(
    r2_hidden @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X4 @ X6 ) @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X7 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r2_hidden @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('20',plain,(
    v4_relat_1 @ sk_D @ sk_C_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18
        = ( k7_relat_1 @ X18 @ X19 ) )
      | ~ ( v4_relat_1 @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('24',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('26',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('27',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['22','27'])).

thf('29',plain,(
    ~ ( r2_relset_1 @ sk_B @ sk_A @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['0','3','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('31',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( r2_relset_1 @ X27 @ X28 @ X29 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['31'])).

thf('33',plain,(
    r2_relset_1 @ sk_B @ sk_A @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['29','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1QdL6Icuen
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:13:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.52  % Solved by: fo/fo7.sh
% 0.36/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.52  % done 107 iterations in 0.067s
% 0.36/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.52  % SZS output start Refutation
% 0.36/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.52  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.36/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.36/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.36/0.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.36/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.52  thf(k5_relset_1_type, type, k5_relset_1: $i > $i > $i > $i > $i).
% 0.36/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.52  thf(t34_relset_1, conjecture,
% 0.36/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.52     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.36/0.52       ( ( r1_tarski @ B @ C ) =>
% 0.36/0.52         ( r2_relset_1 @ B @ A @ ( k5_relset_1 @ B @ A @ D @ C ) @ D ) ) ))).
% 0.36/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.52    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.52        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.36/0.52          ( ( r1_tarski @ B @ C ) =>
% 0.36/0.52            ( r2_relset_1 @ B @ A @ ( k5_relset_1 @ B @ A @ D @ C ) @ D ) ) ) )),
% 0.36/0.52    inference('cnf.neg', [status(esa)], [t34_relset_1])).
% 0.36/0.52  thf('0', plain,
% 0.36/0.52      (~ (r2_relset_1 @ sk_B @ sk_A @ 
% 0.36/0.52          (k5_relset_1 @ sk_B @ sk_A @ sk_D @ sk_C_1) @ sk_D)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('1', plain,
% 0.36/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf(redefinition_k5_relset_1, axiom,
% 0.36/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.52       ( ( k5_relset_1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.36/0.52  thf('2', plain,
% 0.36/0.52      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.36/0.52         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.36/0.52          | ((k5_relset_1 @ X24 @ X25 @ X23 @ X26) = (k7_relat_1 @ X23 @ X26)))),
% 0.36/0.52      inference('cnf', [status(esa)], [redefinition_k5_relset_1])).
% 0.36/0.52  thf('3', plain,
% 0.36/0.52      (![X0 : $i]:
% 0.36/0.52         ((k5_relset_1 @ sk_B @ sk_A @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.36/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.52  thf('4', plain,
% 0.36/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf(t2_subset, axiom,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ( m1_subset_1 @ A @ B ) =>
% 0.36/0.52       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.36/0.52  thf('5', plain,
% 0.36/0.52      (![X12 : $i, X13 : $i]:
% 0.36/0.52         ((r2_hidden @ X12 @ X13)
% 0.36/0.52          | (v1_xboole_0 @ X13)
% 0.36/0.52          | ~ (m1_subset_1 @ X12 @ X13))),
% 0.36/0.52      inference('cnf', [status(esa)], [t2_subset])).
% 0.36/0.52  thf('6', plain,
% 0.36/0.52      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.36/0.52        | (r2_hidden @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.36/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.52  thf(fc1_subset_1, axiom,
% 0.36/0.52    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.36/0.52  thf('7', plain, (![X9 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.36/0.52      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.36/0.52  thf('8', plain,
% 0.36/0.52      ((r2_hidden @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.36/0.52      inference('clc', [status(thm)], ['6', '7'])).
% 0.36/0.52  thf('9', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf(t118_zfmisc_1, axiom,
% 0.36/0.52    (![A:$i,B:$i,C:$i]:
% 0.36/0.52     ( ( r1_tarski @ A @ B ) =>
% 0.36/0.52       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.36/0.52         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 0.36/0.52  thf('10', plain,
% 0.36/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.52         (~ (r1_tarski @ X4 @ X5)
% 0.36/0.52          | (r1_tarski @ (k2_zfmisc_1 @ X4 @ X6) @ (k2_zfmisc_1 @ X5 @ X6)))),
% 0.36/0.52      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.36/0.52  thf('11', plain,
% 0.36/0.52      (![X0 : $i]:
% 0.36/0.52         (r1_tarski @ (k2_zfmisc_1 @ sk_B @ X0) @ (k2_zfmisc_1 @ sk_C_1 @ X0))),
% 0.36/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.36/0.52  thf(t79_zfmisc_1, axiom,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ( r1_tarski @ A @ B ) =>
% 0.36/0.52       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.36/0.52  thf('12', plain,
% 0.36/0.52      (![X7 : $i, X8 : $i]:
% 0.36/0.52         ((r1_tarski @ (k1_zfmisc_1 @ X7) @ (k1_zfmisc_1 @ X8))
% 0.36/0.52          | ~ (r1_tarski @ X7 @ X8))),
% 0.36/0.52      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.36/0.52  thf('13', plain,
% 0.36/0.52      (![X0 : $i]:
% 0.36/0.52         (r1_tarski @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)) @ 
% 0.36/0.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X0)))),
% 0.36/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.52  thf(d3_tarski, axiom,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ( r1_tarski @ A @ B ) <=>
% 0.36/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.36/0.52  thf('14', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.36/0.52          | (r2_hidden @ X0 @ X2)
% 0.36/0.52          | ~ (r1_tarski @ X1 @ X2))),
% 0.36/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.52  thf('15', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i]:
% 0.36/0.52         ((r2_hidden @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X0)))
% 0.36/0.52          | ~ (r2_hidden @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0))))),
% 0.36/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.36/0.52  thf('16', plain,
% 0.36/0.52      ((r2_hidden @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.36/0.52      inference('sup-', [status(thm)], ['8', '15'])).
% 0.36/0.52  thf(t1_subset, axiom,
% 0.36/0.52    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.36/0.52  thf('17', plain,
% 0.36/0.52      (![X10 : $i, X11 : $i]:
% 0.36/0.52         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.36/0.52      inference('cnf', [status(esa)], [t1_subset])).
% 0.36/0.52  thf('18', plain,
% 0.36/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.36/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.52  thf(cc2_relset_1, axiom,
% 0.36/0.52    (![A:$i,B:$i,C:$i]:
% 0.36/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.36/0.52  thf('19', plain,
% 0.36/0.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.36/0.52         ((v4_relat_1 @ X20 @ X21)
% 0.36/0.52          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.36/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.36/0.52  thf('20', plain, ((v4_relat_1 @ sk_D @ sk_C_1)),
% 0.36/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.52  thf(t209_relat_1, axiom,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.36/0.52       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.36/0.52  thf('21', plain,
% 0.36/0.52      (![X18 : $i, X19 : $i]:
% 0.36/0.52         (((X18) = (k7_relat_1 @ X18 @ X19))
% 0.36/0.52          | ~ (v4_relat_1 @ X18 @ X19)
% 0.36/0.52          | ~ (v1_relat_1 @ X18))),
% 0.36/0.52      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.36/0.52  thf('22', plain,
% 0.36/0.52      ((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_C_1)))),
% 0.36/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.36/0.52  thf('23', plain,
% 0.36/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf(cc2_relat_1, axiom,
% 0.36/0.52    (![A:$i]:
% 0.36/0.52     ( ( v1_relat_1 @ A ) =>
% 0.36/0.52       ( ![B:$i]:
% 0.36/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.36/0.52  thf('24', plain,
% 0.36/0.52      (![X14 : $i, X15 : $i]:
% 0.36/0.52         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.36/0.52          | (v1_relat_1 @ X14)
% 0.36/0.52          | ~ (v1_relat_1 @ X15))),
% 0.36/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.36/0.52  thf('25', plain,
% 0.36/0.52      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.36/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.36/0.52  thf(fc6_relat_1, axiom,
% 0.36/0.52    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.36/0.52  thf('26', plain,
% 0.36/0.52      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 0.36/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.36/0.52  thf('27', plain, ((v1_relat_1 @ sk_D)),
% 0.36/0.52      inference('demod', [status(thm)], ['25', '26'])).
% 0.36/0.52  thf('28', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_C_1))),
% 0.36/0.52      inference('demod', [status(thm)], ['22', '27'])).
% 0.36/0.52  thf('29', plain, (~ (r2_relset_1 @ sk_B @ sk_A @ sk_D @ sk_D)),
% 0.36/0.52      inference('demod', [status(thm)], ['0', '3', '28'])).
% 0.36/0.52  thf('30', plain,
% 0.36/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf(reflexivity_r2_relset_1, axiom,
% 0.36/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.52     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.36/0.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.52       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.36/0.52  thf('31', plain,
% 0.36/0.52      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.36/0.52         ((r2_relset_1 @ X27 @ X28 @ X29 @ X29)
% 0.36/0.52          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.36/0.52          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.36/0.52      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.36/0.52  thf('32', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.52         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.36/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.36/0.52      inference('condensation', [status(thm)], ['31'])).
% 0.36/0.52  thf('33', plain, ((r2_relset_1 @ sk_B @ sk_A @ sk_D @ sk_D)),
% 0.36/0.52      inference('sup-', [status(thm)], ['30', '32'])).
% 0.36/0.52  thf('34', plain, ($false), inference('demod', [status(thm)], ['29', '33'])).
% 0.36/0.52  
% 0.36/0.52  % SZS output end Refutation
% 0.36/0.52  
% 0.36/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
