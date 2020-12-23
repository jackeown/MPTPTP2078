%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.51etjITU1L

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   63 (  77 expanded)
%              Number of leaves         :   26 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  409 ( 560 expanded)
%              Number of equality atoms :   14 (  17 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t19_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t19_relset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X35 @ X36 ) )
      = ( k2_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k3_tarski @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X40: $i] :
      ( ( ( k3_relat_1 @ X40 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X40 ) @ ( k2_relat_1 @ X40 ) ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('4',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X35 @ X36 ) )
      = ( k2_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('5',plain,(
    ! [X40: $i] :
      ( ( ( k3_relat_1 @ X40 )
        = ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ X40 ) @ ( k2_relat_1 @ X40 ) ) ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('7',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X47 @ X48 @ X49 ) @ ( k1_zfmisc_1 @ X48 ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('8',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('10',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( ( k2_relset_1 @ X54 @ X55 @ X53 )
        = ( k2_relat_1 @ X53 ) )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('11',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['8','11'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X37: $i,X38: $i] :
      ( ( r1_tarski @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X44 @ X45 @ X46 ) @ ( k1_zfmisc_1 @ X44 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('17',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('19',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( ( k1_relset_1 @ X51 @ X52 @ X50 )
        = ( k1_relat_1 @ X50 ) )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('20',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X37: $i,X38: $i] :
      ( ( r1_tarski @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t13_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ D ) ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ ( k2_xboole_0 @ X2 @ X4 ) @ ( k2_xboole_0 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t13_xboole_1])).

thf('25',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X35 @ X36 ) )
      = ( k2_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('26',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X35 @ X36 ) )
      = ( k2_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('27',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X2 @ X4 ) ) @ ( k3_tarski @ ( k2_tarski @ X3 @ X5 ) ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ sk_C ) @ X1 ) ) @ ( k3_tarski @ ( k2_tarski @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,(
    r1_tarski @ ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) @ ( k3_tarski @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','28'])).

thf('30',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k3_tarski @ ( k2_tarski @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['5','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('32',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( v1_relat_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k3_tarski @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['2','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.51etjITU1L
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:38:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 45 iterations in 0.025s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.22/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.49  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(t19_relset_1, conjecture,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.49       ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.49        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.49          ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t19_relset_1])).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      (~ (r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(l51_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X35 : $i, X36 : $i]:
% 0.22/0.49         ((k3_tarski @ (k2_tarski @ X35 @ X36)) = (k2_xboole_0 @ X35 @ X36))),
% 0.22/0.49      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (~ (r1_tarski @ (k3_relat_1 @ sk_C) @ 
% 0.22/0.49          (k3_tarski @ (k2_tarski @ sk_A @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf(d6_relat_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ A ) =>
% 0.22/0.49       ( ( k3_relat_1 @ A ) =
% 0.22/0.49         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X40 : $i]:
% 0.22/0.49         (((k3_relat_1 @ X40)
% 0.22/0.49            = (k2_xboole_0 @ (k1_relat_1 @ X40) @ (k2_relat_1 @ X40)))
% 0.22/0.49          | ~ (v1_relat_1 @ X40))),
% 0.22/0.49      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X35 : $i, X36 : $i]:
% 0.22/0.49         ((k3_tarski @ (k2_tarski @ X35 @ X36)) = (k2_xboole_0 @ X35 @ X36))),
% 0.22/0.49      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X40 : $i]:
% 0.22/0.49         (((k3_relat_1 @ X40)
% 0.22/0.49            = (k3_tarski @ 
% 0.22/0.49               (k2_tarski @ (k1_relat_1 @ X40) @ (k2_relat_1 @ X40))))
% 0.22/0.49          | ~ (v1_relat_1 @ X40))),
% 0.22/0.49      inference('demod', [status(thm)], ['3', '4'])).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(dt_k2_relset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.49       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.22/0.49         ((m1_subset_1 @ (k2_relset_1 @ X47 @ X48 @ X49) @ (k1_zfmisc_1 @ X48))
% 0.22/0.49          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48))))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(redefinition_k2_relset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.49       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.22/0.49         (((k2_relset_1 @ X54 @ X55 @ X53) = (k2_relat_1 @ X53))
% 0.22/0.49          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55))))),
% 0.22/0.49      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      ((m1_subset_1 @ (k2_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 0.22/0.49      inference('demod', [status(thm)], ['8', '11'])).
% 0.22/0.49  thf(t3_subset, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (![X37 : $i, X38 : $i]:
% 0.22/0.49         ((r1_tarski @ X37 @ X38) | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.49  thf('14', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.22/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(dt_k1_relset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.49       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.22/0.49         ((m1_subset_1 @ (k1_relset_1 @ X44 @ X45 @ X46) @ (k1_zfmisc_1 @ X44))
% 0.22/0.49          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45))))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      ((m1_subset_1 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(redefinition_k1_relset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.49       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.22/0.49         (((k1_relset_1 @ X51 @ X52 @ X50) = (k1_relat_1 @ X50))
% 0.22/0.49          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52))))),
% 0.22/0.49      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      ((m1_subset_1 @ (k1_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['17', '20'])).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (![X37 : $i, X38 : $i]:
% 0.22/0.49         ((r1_tarski @ X37 @ X38) | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.49  thf('23', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.22/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.49  thf(t13_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.49     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.22/0.49       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ D ) ) ))).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.49         (~ (r1_tarski @ X2 @ X3)
% 0.22/0.49          | ~ (r1_tarski @ X4 @ X5)
% 0.22/0.49          | (r1_tarski @ (k2_xboole_0 @ X2 @ X4) @ (k2_xboole_0 @ X3 @ X5)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t13_xboole_1])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      (![X35 : $i, X36 : $i]:
% 0.22/0.49         ((k3_tarski @ (k2_tarski @ X35 @ X36)) = (k2_xboole_0 @ X35 @ X36))),
% 0.22/0.49      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.49  thf('26', plain,
% 0.22/0.49      (![X35 : $i, X36 : $i]:
% 0.22/0.49         ((k3_tarski @ (k2_tarski @ X35 @ X36)) = (k2_xboole_0 @ X35 @ X36))),
% 0.22/0.49      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.49         (~ (r1_tarski @ X2 @ X3)
% 0.22/0.49          | ~ (r1_tarski @ X4 @ X5)
% 0.22/0.49          | (r1_tarski @ (k3_tarski @ (k2_tarski @ X2 @ X4)) @ 
% 0.22/0.49             (k3_tarski @ (k2_tarski @ X3 @ X5))))),
% 0.22/0.49      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((r1_tarski @ (k3_tarski @ (k2_tarski @ (k1_relat_1 @ sk_C) @ X1)) @ 
% 0.22/0.49           (k3_tarski @ (k2_tarski @ sk_A @ X0)))
% 0.22/0.49          | ~ (r1_tarski @ X1 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['23', '27'])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      ((r1_tarski @ 
% 0.22/0.49        (k3_tarski @ (k2_tarski @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))) @ 
% 0.22/0.49        (k3_tarski @ (k2_tarski @ sk_A @ sk_B)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['14', '28'])).
% 0.22/0.49  thf('30', plain,
% 0.22/0.49      (((r1_tarski @ (k3_relat_1 @ sk_C) @ 
% 0.22/0.49         (k3_tarski @ (k2_tarski @ sk_A @ sk_B)))
% 0.22/0.49        | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.49      inference('sup+', [status(thm)], ['5', '29'])).
% 0.22/0.49  thf('31', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(cc1_relset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.49       ( v1_relat_1 @ C ) ))).
% 0.22/0.49  thf('32', plain,
% 0.22/0.49      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.22/0.49         ((v1_relat_1 @ X41)
% 0.22/0.49          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43))))),
% 0.22/0.49      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.49  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.49      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.49  thf('34', plain,
% 0.22/0.49      ((r1_tarski @ (k3_relat_1 @ sk_C) @ 
% 0.22/0.49        (k3_tarski @ (k2_tarski @ sk_A @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['30', '33'])).
% 0.22/0.49  thf('35', plain, ($false), inference('demod', [status(thm)], ['2', '34'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
