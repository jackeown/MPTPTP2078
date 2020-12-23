%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sb4YzRjkjy

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   66 (  78 expanded)
%              Number of leaves         :   28 (  35 expanded)
%              Depth                    :   13
%              Number of atoms          :  424 ( 622 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_relset_1_type,type,(
    k5_relset_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k5_relset_1 @ X25 @ X26 @ X24 @ X27 )
        = ( k7_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_B @ sk_A @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( r2_hidden @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('7',plain,(
    ! [X12: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
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

thf('17',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( m1_subset_1 @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X12: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('22',plain,(
    v4_relat_1 @ sk_D @ sk_C_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19
        = ( k7_relat_1 @ X19 @ X20 ) )
      | ~ ( v4_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('26',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('28',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('29',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,(
    ~ ( r2_relset_1 @ sk_B @ sk_A @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['0','3','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('33',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( r2_relset_1 @ X28 @ X29 @ X30 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['33'])).

thf('35',plain,(
    r2_relset_1 @ sk_B @ sk_A @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['31','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sb4YzRjkjy
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 15:20:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.53  % Solved by: fo/fo7.sh
% 0.22/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.53  % done 107 iterations in 0.065s
% 0.22/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.53  % SZS output start Refutation
% 0.22/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.53  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.22/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.53  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.53  thf(k5_relset_1_type, type, k5_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.53  thf(t34_relset_1, conjecture,
% 0.22/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.53     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.22/0.53       ( ( r1_tarski @ B @ C ) =>
% 0.22/0.53         ( r2_relset_1 @ B @ A @ ( k5_relset_1 @ B @ A @ D @ C ) @ D ) ) ))).
% 0.22/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.53    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.53        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.22/0.53          ( ( r1_tarski @ B @ C ) =>
% 0.22/0.53            ( r2_relset_1 @ B @ A @ ( k5_relset_1 @ B @ A @ D @ C ) @ D ) ) ) )),
% 0.22/0.53    inference('cnf.neg', [status(esa)], [t34_relset_1])).
% 0.22/0.53  thf('0', plain,
% 0.22/0.53      (~ (r2_relset_1 @ sk_B @ sk_A @ 
% 0.22/0.53          (k5_relset_1 @ sk_B @ sk_A @ sk_D @ sk_C_1) @ sk_D)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('1', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(redefinition_k5_relset_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.53       ( ( k5_relset_1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.22/0.53  thf('2', plain,
% 0.22/0.53      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.22/0.53          | ((k5_relset_1 @ X25 @ X26 @ X24 @ X27) = (k7_relat_1 @ X24 @ X27)))),
% 0.22/0.53      inference('cnf', [status(esa)], [redefinition_k5_relset_1])).
% 0.22/0.53  thf('3', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((k5_relset_1 @ sk_B @ sk_A @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.53  thf('4', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(d2_subset_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( ( v1_xboole_0 @ A ) =>
% 0.22/0.53         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.22/0.53       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.53         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.53  thf('5', plain,
% 0.22/0.53      (![X9 : $i, X10 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X9 @ X10)
% 0.22/0.53          | (r2_hidden @ X9 @ X10)
% 0.22/0.53          | (v1_xboole_0 @ X10))),
% 0.22/0.53      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.22/0.53  thf('6', plain,
% 0.22/0.53      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.22/0.53        | (r2_hidden @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.53  thf(fc1_subset_1, axiom,
% 0.22/0.53    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.53  thf('7', plain, (![X12 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.22/0.53      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.22/0.53  thf('8', plain,
% 0.22/0.53      ((r2_hidden @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.53      inference('clc', [status(thm)], ['6', '7'])).
% 0.22/0.53  thf('9', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(t118_zfmisc_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( r1_tarski @ A @ B ) =>
% 0.22/0.53       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.22/0.53         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 0.22/0.53  thf('10', plain,
% 0.22/0.53      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.53         (~ (r1_tarski @ X4 @ X5)
% 0.22/0.53          | (r1_tarski @ (k2_zfmisc_1 @ X4 @ X6) @ (k2_zfmisc_1 @ X5 @ X6)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.22/0.53  thf('11', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (r1_tarski @ (k2_zfmisc_1 @ sk_B @ X0) @ (k2_zfmisc_1 @ sk_C_1 @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.53  thf(t79_zfmisc_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( r1_tarski @ A @ B ) =>
% 0.22/0.53       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.22/0.53  thf('12', plain,
% 0.22/0.53      (![X7 : $i, X8 : $i]:
% 0.22/0.53         ((r1_tarski @ (k1_zfmisc_1 @ X7) @ (k1_zfmisc_1 @ X8))
% 0.22/0.53          | ~ (r1_tarski @ X7 @ X8))),
% 0.22/0.53      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.22/0.53  thf('13', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (r1_tarski @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)) @ 
% 0.22/0.53          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X0)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.53  thf(d3_tarski, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.53  thf('14', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.53          | (r2_hidden @ X0 @ X2)
% 0.22/0.53          | ~ (r1_tarski @ X1 @ X2))),
% 0.22/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.53  thf('15', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((r2_hidden @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X0)))
% 0.22/0.53          | ~ (r2_hidden @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.53  thf('16', plain,
% 0.22/0.53      ((r2_hidden @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['8', '15'])).
% 0.22/0.53  thf('17', plain,
% 0.22/0.53      (![X9 : $i, X10 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X9 @ X10)
% 0.22/0.53          | (m1_subset_1 @ X9 @ X10)
% 0.22/0.53          | (v1_xboole_0 @ X10))),
% 0.22/0.53      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.22/0.53  thf('18', plain,
% 0.22/0.53      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))
% 0.22/0.53        | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.53  thf('19', plain, (![X12 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.22/0.53      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.22/0.53  thf('20', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.22/0.53      inference('clc', [status(thm)], ['18', '19'])).
% 0.22/0.53  thf(cc2_relset_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.53  thf('21', plain,
% 0.22/0.53      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.22/0.53         ((v4_relat_1 @ X21 @ X22)
% 0.22/0.53          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.22/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.53  thf('22', plain, ((v4_relat_1 @ sk_D @ sk_C_1)),
% 0.22/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.53  thf(t209_relat_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.22/0.53       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.22/0.53  thf('23', plain,
% 0.22/0.53      (![X19 : $i, X20 : $i]:
% 0.22/0.53         (((X19) = (k7_relat_1 @ X19 @ X20))
% 0.22/0.53          | ~ (v4_relat_1 @ X19 @ X20)
% 0.22/0.53          | ~ (v1_relat_1 @ X19))),
% 0.22/0.53      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.22/0.53  thf('24', plain,
% 0.22/0.53      ((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_C_1)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.53  thf('25', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(cc2_relat_1, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( v1_relat_1 @ A ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.22/0.53  thf('26', plain,
% 0.22/0.53      (![X15 : $i, X16 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.22/0.53          | (v1_relat_1 @ X15)
% 0.22/0.53          | ~ (v1_relat_1 @ X16))),
% 0.22/0.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.53  thf('27', plain,
% 0.22/0.53      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.22/0.53      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.53  thf(fc6_relat_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.53  thf('28', plain,
% 0.22/0.53      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 0.22/0.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.53  thf('29', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.22/0.53  thf('30', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_C_1))),
% 0.22/0.53      inference('demod', [status(thm)], ['24', '29'])).
% 0.22/0.53  thf('31', plain, (~ (r2_relset_1 @ sk_B @ sk_A @ sk_D @ sk_D)),
% 0.22/0.53      inference('demod', [status(thm)], ['0', '3', '30'])).
% 0.22/0.53  thf('32', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(reflexivity_r2_relset_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.53     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.22/0.53         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.53       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.22/0.53  thf('33', plain,
% 0.22/0.53      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.22/0.53         ((r2_relset_1 @ X28 @ X29 @ X30 @ X30)
% 0.22/0.53          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.22/0.53          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.22/0.53      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.22/0.53  thf('34', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.22/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.22/0.53      inference('condensation', [status(thm)], ['33'])).
% 0.22/0.53  thf('35', plain, ((r2_relset_1 @ sk_B @ sk_A @ sk_D @ sk_D)),
% 0.22/0.53      inference('sup-', [status(thm)], ['32', '34'])).
% 0.22/0.53  thf('36', plain, ($false), inference('demod', [status(thm)], ['31', '35'])).
% 0.22/0.53  
% 0.22/0.53  % SZS output end Refutation
% 0.22/0.53  
% 0.22/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
