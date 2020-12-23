%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sTMBGxImSW

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:52 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   72 (  96 expanded)
%              Number of leaves         :   29 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :  414 ( 625 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_C_1 ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X31: $i] :
      ( ( ( k3_relat_1 @ X31 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X31 ) @ ( k2_relat_1 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v5_relat_1 @ X34 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('4',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('5',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v5_relat_1 @ X29 @ X30 )
      | ( r1_tarski @ ( k2_relat_1 @ X29 ) @ X30 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( v1_relat_1 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X32: $i,X33: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('11',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['6','11'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v4_relat_1 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('17',plain,(
    v4_relat_1 @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v4_relat_1 @ X27 @ X28 )
      | ( r1_tarski @ ( k1_relat_1 @ X27 ) @ X28 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('21',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['19','20'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('22',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r2_hidden @ X10 @ X12 )
      | ( X12
       != ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('23',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    r2_hidden @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('26',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X17 ) @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X19: $i,X21: $i] :
      ( ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('30',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( m1_subset_1 @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf('33',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('35',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X7 @ X6 )
      | ( r1_tarski @ ( k2_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ X1 ) @ ( k2_xboole_0 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','36'])).

thf('38',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_C_1 ) @ ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['1','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('40',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C_1 ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['0','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sTMBGxImSW
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:55:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.58/1.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.58/1.78  % Solved by: fo/fo7.sh
% 1.58/1.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.58/1.78  % done 2187 iterations in 1.319s
% 1.58/1.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.58/1.78  % SZS output start Refutation
% 1.58/1.78  thf(sk_B_type, type, sk_B: $i).
% 1.58/1.78  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.58/1.78  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.58/1.78  thf(sk_A_type, type, sk_A: $i).
% 1.58/1.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.58/1.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.58/1.78  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.58/1.78  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 1.58/1.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.58/1.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.58/1.78  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.58/1.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.58/1.78  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.58/1.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.58/1.78  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.58/1.78  thf(t19_relset_1, conjecture,
% 1.58/1.78    (![A:$i,B:$i,C:$i]:
% 1.58/1.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.58/1.78       ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.58/1.78  thf(zf_stmt_0, negated_conjecture,
% 1.58/1.78    (~( ![A:$i,B:$i,C:$i]:
% 1.58/1.78        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.58/1.78          ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 1.58/1.78    inference('cnf.neg', [status(esa)], [t19_relset_1])).
% 1.58/1.78  thf('0', plain,
% 1.58/1.78      (~ (r1_tarski @ (k3_relat_1 @ sk_C_1) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 1.58/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.78  thf(d6_relat_1, axiom,
% 1.58/1.78    (![A:$i]:
% 1.58/1.78     ( ( v1_relat_1 @ A ) =>
% 1.58/1.78       ( ( k3_relat_1 @ A ) =
% 1.58/1.78         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 1.58/1.78  thf('1', plain,
% 1.58/1.78      (![X31 : $i]:
% 1.58/1.78         (((k3_relat_1 @ X31)
% 1.58/1.78            = (k2_xboole_0 @ (k1_relat_1 @ X31) @ (k2_relat_1 @ X31)))
% 1.58/1.78          | ~ (v1_relat_1 @ X31))),
% 1.58/1.78      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.58/1.78  thf('2', plain,
% 1.58/1.78      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.58/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.78  thf(cc2_relset_1, axiom,
% 1.58/1.78    (![A:$i,B:$i,C:$i]:
% 1.58/1.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.58/1.78       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.58/1.78  thf('3', plain,
% 1.58/1.78      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.58/1.78         ((v5_relat_1 @ X34 @ X36)
% 1.58/1.78          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 1.58/1.78      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.58/1.78  thf('4', plain, ((v5_relat_1 @ sk_C_1 @ sk_B)),
% 1.58/1.78      inference('sup-', [status(thm)], ['2', '3'])).
% 1.58/1.78  thf(d19_relat_1, axiom,
% 1.58/1.78    (![A:$i,B:$i]:
% 1.58/1.78     ( ( v1_relat_1 @ B ) =>
% 1.58/1.78       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.58/1.78  thf('5', plain,
% 1.58/1.78      (![X29 : $i, X30 : $i]:
% 1.58/1.78         (~ (v5_relat_1 @ X29 @ X30)
% 1.58/1.78          | (r1_tarski @ (k2_relat_1 @ X29) @ X30)
% 1.58/1.78          | ~ (v1_relat_1 @ X29))),
% 1.58/1.78      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.58/1.78  thf('6', plain,
% 1.58/1.78      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B))),
% 1.58/1.78      inference('sup-', [status(thm)], ['4', '5'])).
% 1.58/1.78  thf('7', plain,
% 1.58/1.78      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.58/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.78  thf(cc2_relat_1, axiom,
% 1.58/1.78    (![A:$i]:
% 1.58/1.78     ( ( v1_relat_1 @ A ) =>
% 1.58/1.78       ( ![B:$i]:
% 1.58/1.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.58/1.78  thf('8', plain,
% 1.58/1.78      (![X25 : $i, X26 : $i]:
% 1.58/1.78         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 1.58/1.78          | (v1_relat_1 @ X25)
% 1.58/1.78          | ~ (v1_relat_1 @ X26))),
% 1.58/1.78      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.58/1.78  thf('9', plain,
% 1.58/1.78      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_1))),
% 1.58/1.78      inference('sup-', [status(thm)], ['7', '8'])).
% 1.58/1.78  thf(fc6_relat_1, axiom,
% 1.58/1.78    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.58/1.78  thf('10', plain,
% 1.58/1.78      (![X32 : $i, X33 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X32 @ X33))),
% 1.58/1.78      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.58/1.78  thf('11', plain, ((v1_relat_1 @ sk_C_1)),
% 1.58/1.78      inference('demod', [status(thm)], ['9', '10'])).
% 1.58/1.78  thf('12', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)),
% 1.58/1.78      inference('demod', [status(thm)], ['6', '11'])).
% 1.58/1.78  thf(t10_xboole_1, axiom,
% 1.58/1.78    (![A:$i,B:$i,C:$i]:
% 1.58/1.78     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 1.58/1.78  thf('13', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.58/1.78         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 1.58/1.78      inference('cnf', [status(esa)], [t10_xboole_1])).
% 1.58/1.78  thf('14', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         (r1_tarski @ (k2_relat_1 @ sk_C_1) @ (k2_xboole_0 @ X0 @ sk_B))),
% 1.58/1.78      inference('sup-', [status(thm)], ['12', '13'])).
% 1.58/1.78  thf('15', plain,
% 1.58/1.78      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.58/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.78  thf('16', plain,
% 1.58/1.78      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.58/1.78         ((v4_relat_1 @ X34 @ X35)
% 1.58/1.78          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 1.58/1.78      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.58/1.78  thf('17', plain, ((v4_relat_1 @ sk_C_1 @ sk_A)),
% 1.58/1.78      inference('sup-', [status(thm)], ['15', '16'])).
% 1.58/1.78  thf(d18_relat_1, axiom,
% 1.58/1.78    (![A:$i,B:$i]:
% 1.58/1.78     ( ( v1_relat_1 @ B ) =>
% 1.58/1.78       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.58/1.78  thf('18', plain,
% 1.58/1.78      (![X27 : $i, X28 : $i]:
% 1.58/1.78         (~ (v4_relat_1 @ X27 @ X28)
% 1.58/1.78          | (r1_tarski @ (k1_relat_1 @ X27) @ X28)
% 1.58/1.78          | ~ (v1_relat_1 @ X27))),
% 1.58/1.78      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.58/1.78  thf('19', plain,
% 1.58/1.78      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A))),
% 1.58/1.78      inference('sup-', [status(thm)], ['17', '18'])).
% 1.58/1.78  thf('20', plain, ((v1_relat_1 @ sk_C_1)),
% 1.58/1.78      inference('demod', [status(thm)], ['9', '10'])).
% 1.58/1.78  thf('21', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 1.58/1.78      inference('demod', [status(thm)], ['19', '20'])).
% 1.58/1.78  thf(d1_zfmisc_1, axiom,
% 1.58/1.78    (![A:$i,B:$i]:
% 1.58/1.78     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.58/1.78       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.58/1.78  thf('22', plain,
% 1.58/1.78      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.58/1.78         (~ (r1_tarski @ X10 @ X11)
% 1.58/1.78          | (r2_hidden @ X10 @ X12)
% 1.58/1.78          | ((X12) != (k1_zfmisc_1 @ X11)))),
% 1.58/1.78      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.58/1.78  thf('23', plain,
% 1.58/1.78      (![X10 : $i, X11 : $i]:
% 1.58/1.78         ((r2_hidden @ X10 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X10 @ X11))),
% 1.58/1.78      inference('simplify', [status(thm)], ['22'])).
% 1.58/1.78  thf('24', plain,
% 1.58/1.78      ((r2_hidden @ (k1_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 1.58/1.78      inference('sup-', [status(thm)], ['21', '23'])).
% 1.58/1.78  thf(t7_xboole_1, axiom,
% 1.58/1.78    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.58/1.78  thf('25', plain,
% 1.58/1.78      (![X3 : $i, X4 : $i]: (r1_tarski @ X3 @ (k2_xboole_0 @ X3 @ X4))),
% 1.58/1.78      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.58/1.78  thf(t79_zfmisc_1, axiom,
% 1.58/1.78    (![A:$i,B:$i]:
% 1.58/1.78     ( ( r1_tarski @ A @ B ) =>
% 1.58/1.78       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.58/1.78  thf('26', plain,
% 1.58/1.78      (![X17 : $i, X18 : $i]:
% 1.58/1.78         ((r1_tarski @ (k1_zfmisc_1 @ X17) @ (k1_zfmisc_1 @ X18))
% 1.58/1.78          | ~ (r1_tarski @ X17 @ X18))),
% 1.58/1.78      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 1.58/1.78  thf('27', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         (r1_tarski @ (k1_zfmisc_1 @ X1) @ 
% 1.58/1.78          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['25', '26'])).
% 1.58/1.78  thf(t3_subset, axiom,
% 1.58/1.78    (![A:$i,B:$i]:
% 1.58/1.78     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.58/1.78  thf('28', plain,
% 1.58/1.78      (![X19 : $i, X21 : $i]:
% 1.58/1.78         ((m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X21)) | ~ (r1_tarski @ X19 @ X21))),
% 1.58/1.78      inference('cnf', [status(esa)], [t3_subset])).
% 1.58/1.78  thf('29', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         (m1_subset_1 @ (k1_zfmisc_1 @ X1) @ 
% 1.58/1.78          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0))))),
% 1.58/1.78      inference('sup-', [status(thm)], ['27', '28'])).
% 1.58/1.78  thf(t4_subset, axiom,
% 1.58/1.78    (![A:$i,B:$i,C:$i]:
% 1.58/1.78     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 1.58/1.78       ( m1_subset_1 @ A @ C ) ))).
% 1.58/1.78  thf('30', plain,
% 1.58/1.78      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.58/1.78         (~ (r2_hidden @ X22 @ X23)
% 1.58/1.78          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 1.58/1.78          | (m1_subset_1 @ X22 @ X24))),
% 1.58/1.78      inference('cnf', [status(esa)], [t4_subset])).
% 1.58/1.78  thf('31', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.58/1.78         ((m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 1.58/1.78          | ~ (r2_hidden @ X2 @ (k1_zfmisc_1 @ X1)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['29', '30'])).
% 1.58/1.78  thf('32', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         (m1_subset_1 @ (k1_relat_1 @ sk_C_1) @ 
% 1.58/1.78          (k1_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['24', '31'])).
% 1.58/1.78  thf('33', plain,
% 1.58/1.78      (![X19 : $i, X20 : $i]:
% 1.58/1.78         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 1.58/1.78      inference('cnf', [status(esa)], [t3_subset])).
% 1.58/1.78  thf('34', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         (r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k2_xboole_0 @ sk_A @ X0))),
% 1.58/1.78      inference('sup-', [status(thm)], ['32', '33'])).
% 1.58/1.78  thf(t8_xboole_1, axiom,
% 1.58/1.78    (![A:$i,B:$i,C:$i]:
% 1.58/1.78     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.58/1.78       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.58/1.78  thf('35', plain,
% 1.58/1.78      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.58/1.78         (~ (r1_tarski @ X5 @ X6)
% 1.58/1.78          | ~ (r1_tarski @ X7 @ X6)
% 1.58/1.78          | (r1_tarski @ (k2_xboole_0 @ X5 @ X7) @ X6))),
% 1.58/1.78      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.58/1.78  thf('36', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_C_1) @ X1) @ 
% 1.58/1.78           (k2_xboole_0 @ sk_A @ X0))
% 1.58/1.78          | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ sk_A @ X0)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['34', '35'])).
% 1.58/1.78  thf('37', plain,
% 1.58/1.78      ((r1_tarski @ 
% 1.58/1.78        (k2_xboole_0 @ (k1_relat_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1)) @ 
% 1.58/1.78        (k2_xboole_0 @ sk_A @ sk_B))),
% 1.58/1.78      inference('sup-', [status(thm)], ['14', '36'])).
% 1.58/1.78  thf('38', plain,
% 1.58/1.78      (((r1_tarski @ (k3_relat_1 @ sk_C_1) @ (k2_xboole_0 @ sk_A @ sk_B))
% 1.58/1.78        | ~ (v1_relat_1 @ sk_C_1))),
% 1.58/1.78      inference('sup+', [status(thm)], ['1', '37'])).
% 1.58/1.78  thf('39', plain, ((v1_relat_1 @ sk_C_1)),
% 1.58/1.78      inference('demod', [status(thm)], ['9', '10'])).
% 1.58/1.78  thf('40', plain,
% 1.58/1.78      ((r1_tarski @ (k3_relat_1 @ sk_C_1) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 1.58/1.78      inference('demod', [status(thm)], ['38', '39'])).
% 1.58/1.78  thf('41', plain, ($false), inference('demod', [status(thm)], ['0', '40'])).
% 1.58/1.78  
% 1.58/1.78  % SZS output end Refutation
% 1.58/1.78  
% 1.59/1.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
