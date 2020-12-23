%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.G13QWmrNHH

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:13 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 150 expanded)
%              Number of leaves         :   27 (  58 expanded)
%              Depth                    :   15
%              Number of atoms          :  476 (1280 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_relset_1_type,type,(
    k5_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

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
    ~ ( m1_subset_1 @ ( k5_relset_1 @ sk_A @ sk_C_1 @ sk_D @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k5_relset_1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( ( k5_relset_1 @ X22 @ X23 @ X21 @ X24 )
        = ( k7_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_A @ sk_C_1 @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X13 @ X14 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('17',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('18',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('27',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v5_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('30',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['28','31'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('33',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('34',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X25 ) @ X26 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X25 ) @ X27 )
      | ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C_1 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('38',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['16','17'])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['4','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.G13QWmrNHH
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:18:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.37/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.58  % Solved by: fo/fo7.sh
% 0.37/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.58  % done 221 iterations in 0.131s
% 0.37/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.58  % SZS output start Refutation
% 0.37/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.58  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.37/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.58  thf(k5_relset_1_type, type, k5_relset_1: $i > $i > $i > $i > $i).
% 0.37/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.58  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.37/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.58  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.37/0.58  thf(t33_relset_1, conjecture,
% 0.37/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.58     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.37/0.58       ( m1_subset_1 @
% 0.37/0.58         ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 0.37/0.58         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.37/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.58    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.58        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.37/0.58          ( m1_subset_1 @
% 0.37/0.58            ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 0.37/0.58            ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )),
% 0.37/0.58    inference('cnf.neg', [status(esa)], [t33_relset_1])).
% 0.37/0.58  thf('0', plain,
% 0.37/0.58      (~ (m1_subset_1 @ (k5_relset_1 @ sk_A @ sk_C_1 @ sk_D @ sk_B) @ 
% 0.37/0.58          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('1', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(redefinition_k5_relset_1, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.58       ( ( k5_relset_1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.37/0.58  thf('2', plain,
% 0.37/0.58      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.37/0.58          | ((k5_relset_1 @ X22 @ X23 @ X21 @ X24) = (k7_relat_1 @ X21 @ X24)))),
% 0.37/0.58      inference('cnf', [status(esa)], [redefinition_k5_relset_1])).
% 0.37/0.58  thf('3', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((k5_relset_1 @ sk_A @ sk_C_1 @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.58  thf('4', plain,
% 0.37/0.58      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_B) @ 
% 0.37/0.58          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.37/0.58      inference('demod', [status(thm)], ['0', '3'])).
% 0.37/0.58  thf(d3_tarski, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( r1_tarski @ A @ B ) <=>
% 0.37/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.37/0.58  thf('5', plain,
% 0.37/0.58      (![X1 : $i, X3 : $i]:
% 0.37/0.58         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.37/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.58  thf(t88_relat_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.37/0.58  thf('6', plain,
% 0.37/0.58      (![X13 : $i, X14 : $i]:
% 0.37/0.58         ((r1_tarski @ (k7_relat_1 @ X13 @ X14) @ X13) | ~ (v1_relat_1 @ X13))),
% 0.37/0.58      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.37/0.58  thf('7', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X0 @ X1)
% 0.37/0.58          | (r2_hidden @ X0 @ X2)
% 0.37/0.58          | ~ (r1_tarski @ X1 @ X2))),
% 0.37/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.58  thf('8', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ X0)
% 0.37/0.58          | (r2_hidden @ X2 @ X0)
% 0.37/0.58          | ~ (r2_hidden @ X2 @ (k7_relat_1 @ X0 @ X1)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.58  thf('9', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.58         ((r1_tarski @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.37/0.58          | (r2_hidden @ (sk_C @ X2 @ (k7_relat_1 @ X1 @ X0)) @ X1)
% 0.37/0.58          | ~ (v1_relat_1 @ X1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['5', '8'])).
% 0.37/0.58  thf('10', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(t3_subset, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.58  thf('11', plain,
% 0.37/0.58      (![X4 : $i, X5 : $i]:
% 0.37/0.58         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.58  thf('12', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_C_1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.58  thf('13', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X0 @ X1)
% 0.37/0.58          | (r2_hidden @ X0 @ X2)
% 0.37/0.58          | ~ (r1_tarski @ X1 @ X2))),
% 0.37/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.58  thf('14', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))
% 0.37/0.58          | ~ (r2_hidden @ X0 @ sk_D))),
% 0.37/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.58  thf('15', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ sk_D)
% 0.37/0.58          | (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ X1)
% 0.37/0.58          | (r2_hidden @ (sk_C @ X1 @ (k7_relat_1 @ sk_D @ X0)) @ 
% 0.37/0.58             (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['9', '14'])).
% 0.37/0.58  thf('16', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(cc1_relset_1, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i]:
% 0.37/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.58       ( v1_relat_1 @ C ) ))).
% 0.37/0.58  thf('17', plain,
% 0.37/0.58      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.37/0.58         ((v1_relat_1 @ X15)
% 0.37/0.58          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.37/0.58      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.37/0.58  thf('18', plain, ((v1_relat_1 @ sk_D)),
% 0.37/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.58  thf('19', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ X1)
% 0.37/0.58          | (r2_hidden @ (sk_C @ X1 @ (k7_relat_1 @ sk_D @ X0)) @ 
% 0.37/0.58             (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.37/0.58      inference('demod', [status(thm)], ['15', '18'])).
% 0.37/0.58  thf('20', plain,
% 0.37/0.58      (![X1 : $i, X3 : $i]:
% 0.37/0.58         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.37/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.58  thf('21', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_C_1))
% 0.37/0.58          | (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.37/0.58             (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.58  thf('22', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_C_1))),
% 0.37/0.58      inference('simplify', [status(thm)], ['21'])).
% 0.37/0.58  thf('23', plain,
% 0.37/0.58      (![X4 : $i, X6 : $i]:
% 0.37/0.58         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.37/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.58  thf('24', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.37/0.58          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.37/0.58  thf(cc2_relset_1, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i]:
% 0.37/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.58       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.37/0.58  thf('25', plain,
% 0.37/0.58      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.37/0.58         ((v5_relat_1 @ X18 @ X20)
% 0.37/0.58          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.37/0.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.37/0.58  thf('26', plain,
% 0.37/0.58      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_C_1)),
% 0.37/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.37/0.58  thf(d19_relat_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( v1_relat_1 @ B ) =>
% 0.37/0.58       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.37/0.58  thf('27', plain,
% 0.37/0.58      (![X9 : $i, X10 : $i]:
% 0.37/0.58         (~ (v5_relat_1 @ X9 @ X10)
% 0.37/0.58          | (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 0.37/0.58          | ~ (v1_relat_1 @ X9))),
% 0.37/0.58      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.37/0.58  thf('28', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 0.37/0.58          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_C_1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['26', '27'])).
% 0.37/0.58  thf('29', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.37/0.58          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.37/0.58  thf('30', plain,
% 0.37/0.58      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.37/0.58         ((v1_relat_1 @ X15)
% 0.37/0.58          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.37/0.58      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.37/0.58  thf('31', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['29', '30'])).
% 0.37/0.58  thf('32', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_C_1)),
% 0.37/0.58      inference('demod', [status(thm)], ['28', '31'])).
% 0.37/0.58  thf(t87_relat_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( v1_relat_1 @ B ) =>
% 0.37/0.58       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.37/0.58  thf('33', plain,
% 0.37/0.58      (![X11 : $i, X12 : $i]:
% 0.37/0.58         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X11 @ X12)) @ X12)
% 0.37/0.58          | ~ (v1_relat_1 @ X11))),
% 0.37/0.58      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.37/0.58  thf(t11_relset_1, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i]:
% 0.37/0.58     ( ( v1_relat_1 @ C ) =>
% 0.37/0.58       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.37/0.58           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.37/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.37/0.58  thf('34', plain,
% 0.37/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.37/0.58         (~ (r1_tarski @ (k1_relat_1 @ X25) @ X26)
% 0.37/0.58          | ~ (r1_tarski @ (k2_relat_1 @ X25) @ X27)
% 0.37/0.58          | (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.37/0.58          | ~ (v1_relat_1 @ X25))),
% 0.37/0.58      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.37/0.58  thf('35', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ X1)
% 0.37/0.58          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.37/0.58          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.37/0.58             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 0.37/0.58          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))),
% 0.37/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.58  thf('36', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.37/0.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C_1)))
% 0.37/0.58          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 0.37/0.58          | ~ (v1_relat_1 @ sk_D))),
% 0.37/0.58      inference('sup-', [status(thm)], ['32', '35'])).
% 0.37/0.58  thf('37', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['29', '30'])).
% 0.37/0.58  thf('38', plain, ((v1_relat_1 @ sk_D)),
% 0.37/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.58  thf('39', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.37/0.58          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C_1)))),
% 0.37/0.58      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.37/0.58  thf('40', plain, ($false), inference('demod', [status(thm)], ['4', '39'])).
% 0.37/0.58  
% 0.37/0.58  % SZS output end Refutation
% 0.37/0.58  
% 0.37/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
