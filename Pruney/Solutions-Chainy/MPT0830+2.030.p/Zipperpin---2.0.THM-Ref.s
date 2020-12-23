%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vMctMOmmrd

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 137 expanded)
%              Number of leaves         :   26 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :  470 (1156 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k5_relset_1_type,type,(
    k5_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t33_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( m1_subset_1 @ ( k5_relset_1 @ A @ C @ D @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
       => ( m1_subset_1 @ ( k5_relset_1 @ A @ C @ D @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_relset_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k5_relset_1 @ sk_A @ sk_C @ sk_D @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k5_relset_1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( ( k5_relset_1 @ X17 @ X18 @ X16 @ X19 )
        = ( k7_relat_1 @ X16 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_A @ sk_C @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X11 @ X12 ) @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
     => ( ( r1_tarski @ A @ D )
       => ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('7',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( r1_tarski @ X23 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t4_relset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_D )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('14',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v5_relat_1 @ X4 @ X5 )
      | ( r1_tarski @ ( k2_relat_1 @ X4 ) @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('22',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc23_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v4_relat_1 @ C @ B ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) )
        & ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A )
        & ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) )
      | ~ ( v4_relat_1 @ X6 @ X8 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc23_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('26',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['19','26'])).

thf('28',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('29',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) @ X7 )
      | ~ ( v4_relat_1 @ X6 @ X8 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc23_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('32',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v4_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('37',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X22 )
      | ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['27','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['4','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vMctMOmmrd
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:03:30 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 63 iterations in 0.035s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.48  thf(k5_relset_1_type, type, k5_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.48  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(t33_relset_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.20/0.48       ( m1_subset_1 @
% 0.20/0.48         ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 0.20/0.48         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.20/0.48          ( m1_subset_1 @
% 0.20/0.48            ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 0.20/0.48            ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t33_relset_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (~ (m1_subset_1 @ (k5_relset_1 @ sk_A @ sk_C @ sk_D @ sk_B) @ 
% 0.20/0.48          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(redefinition_k5_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( ( k5_relset_1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.20/0.48          | ((k5_relset_1 @ X17 @ X18 @ X16 @ X19) = (k7_relat_1 @ X16 @ X19)))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k5_relset_1])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((k5_relset_1 @ sk_A @ sk_C @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_B) @ 
% 0.20/0.48          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.20/0.48      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.48  thf(t88_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i]:
% 0.20/0.48         ((r1_tarski @ (k7_relat_1 @ X11 @ X12) @ X11) | ~ (v1_relat_1 @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t4_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.20/0.48       ( ( r1_tarski @ A @ D ) =>
% 0.20/0.48         ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.48         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.20/0.48          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.20/0.48          | ~ (r1_tarski @ X23 @ X26))),
% 0.20/0.48      inference('cnf', [status(esa)], [t4_relset_1])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (r1_tarski @ X0 @ sk_D)
% 0.20/0.48          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ sk_D)
% 0.20/0.48          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.20/0.48             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(cc2_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.20/0.48          | (v1_relat_1 @ X0)
% 0.20/0.48          | ~ (v1_relat_1 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)) | (v1_relat_1 @ sk_D))),
% 0.20/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.48  thf(fc6_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.48  thf('14', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.48      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.20/0.48          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.20/0.48      inference('demod', [status(thm)], ['9', '14'])).
% 0.20/0.48  thf(cc2_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.48         ((v5_relat_1 @ X13 @ X15)
% 0.20/0.48          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_C)),
% 0.20/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf(d19_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i]:
% 0.20/0.48         (~ (v5_relat_1 @ X4 @ X5)
% 0.20/0.48          | (r1_tarski @ (k2_relat_1 @ X4) @ X5)
% 0.20/0.48          | ~ (v1_relat_1 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 0.20/0.49          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.49         ((v4_relat_1 @ X13 @ X14)
% 0.20/0.49          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.49  thf('22', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 0.20/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.49  thf(fc23_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ B ) ) =>
% 0.20/0.49       ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) ) & 
% 0.20/0.49         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A ) & 
% 0.20/0.49         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ))).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.49         ((v1_relat_1 @ (k7_relat_1 @ X6 @ X7))
% 0.20/0.49          | ~ (v4_relat_1 @ X6 @ X8)
% 0.20/0.49          | ~ (v1_relat_1 @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc23_relat_1])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ sk_D) | (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.49  thf('25', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.49  thf('26', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_C)),
% 0.20/0.49      inference('demod', [status(thm)], ['19', '26'])).
% 0.20/0.49  thf('28', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 0.20/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.49         ((v4_relat_1 @ (k7_relat_1 @ X6 @ X7) @ X7)
% 0.20/0.49          | ~ (v4_relat_1 @ X6 @ X8)
% 0.20/0.49          | ~ (v1_relat_1 @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc23_relat_1])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ sk_D) | (v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.49  thf('31', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.49  thf('32', plain, (![X0 : $i]: (v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X0)),
% 0.20/0.49      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.49  thf(d18_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (![X2 : $i, X3 : $i]:
% 0.20/0.49         (~ (v4_relat_1 @ X2 @ X3)
% 0.20/0.49          | (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 0.20/0.49          | ~ (v1_relat_1 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 0.20/0.49          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.49  thf('35', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X0)),
% 0.20/0.49      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.49  thf(t11_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ C ) =>
% 0.20/0.49       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.20/0.49           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.20/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.49         (~ (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.20/0.49          | ~ (r1_tarski @ (k2_relat_1 @ X20) @ X22)
% 0.20/0.49          | (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.20/0.49          | ~ (v1_relat_1 @ X20))),
% 0.20/0.49      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 0.20/0.49          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.20/0.49             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.20/0.49          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.49  thf('39', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.20/0.49           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.20/0.49          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X1))),
% 0.20/0.49      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.20/0.49          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['27', '40'])).
% 0.20/0.49  thf('42', plain, ($false), inference('demod', [status(thm)], ['4', '41'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
