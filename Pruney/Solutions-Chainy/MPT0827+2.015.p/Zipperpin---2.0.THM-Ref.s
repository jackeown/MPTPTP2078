%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gRHlJrvr49

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 133 expanded)
%              Number of leaves         :   29 (  51 expanded)
%              Depth                    :   13
%              Number of atoms          :  517 (1153 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(t30_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D )
       => ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) )
          & ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D )
         => ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) )
            & ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t30_relset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) )
    | ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) )
   <= ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('4',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('6',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_D ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ( v4_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_C ) @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    m1_subset_1 @ ( k6_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(cc5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) )
         => ( v4_relat_1 @ C @ A ) ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v4_relat_1 @ X8 @ X10 )
      | ~ ( v4_relat_1 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc5_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v4_relat_1 @ sk_D @ X0 )
      | ( v4_relat_1 @ ( k6_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('19',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('20',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ sk_D @ X0 )
      | ( v4_relat_1 @ ( k6_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( v4_relat_1 @ ( k6_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['18','19'])).

thf('24',plain,(
    v4_relat_1 @ ( k6_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v4_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('27',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('28',plain,(
    ! [X21: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('29',plain,(
    r1_tarski @ sk_C @ ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['6','29'])).

thf('31',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,(
    ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sat_resolution*',[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['1','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('35',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('36',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('38',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X16 ) @ X17 )
      | ( v5_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ ( k6_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(cc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) )
         => ( v5_relat_1 @ C @ A ) ) ) )).

thf('41',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v5_relat_1 @ X11 @ X13 )
      | ~ ( v5_relat_1 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc6_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v5_relat_1 @ sk_D @ X0 )
      | ( v5_relat_1 @ ( k6_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['18','19'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_D @ X0 )
      | ( v5_relat_1 @ ( k6_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( v5_relat_1 @ ( k6_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['18','19'])).

thf('47',plain,(
    v5_relat_1 @ ( k6_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v5_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k2_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('51',plain,(
    ! [X22: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('52',plain,(
    r1_tarski @ sk_C @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['33','36','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gRHlJrvr49
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:01:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 107 iterations in 0.042s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.49  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.49  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.49  thf(t30_relset_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D ) =>
% 0.20/0.49         ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) ) & 
% 0.20/0.49           ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49          ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D ) =>
% 0.20/0.49            ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) ) & 
% 0.20/0.49              ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t30_relset_1])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      ((~ (r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D))
% 0.20/0.49        | ~ (r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      ((~ (r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D)))
% 0.20/0.49         <= (~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.49         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 0.20/0.49          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.49  thf('4', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      ((~ (r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D)))
% 0.20/0.49         <= (~ ((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_D)))
% 0.20/0.49         <= (~ ((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf(d10_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.49  thf('8', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.49      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.49  thf(d18_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i]:
% 0.20/0.49         (~ (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 0.20/0.49          | (v4_relat_1 @ X14 @ X15)
% 0.20/0.49          | ~ (v1_relat_1 @ X14))),
% 0.20/0.49      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf('11', plain, ((r1_tarski @ (k6_relat_1 @ sk_C) @ sk_D)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t3_subset, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X3 : $i, X5 : $i]:
% 0.20/0.49         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      ((m1_subset_1 @ (k6_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf(cc5_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) ) => ( v4_relat_1 @ C @ A ) ) ) ))).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.20/0.49          | (v4_relat_1 @ X8 @ X10)
% 0.20/0.49          | ~ (v4_relat_1 @ X9 @ X10)
% 0.20/0.49          | ~ (v1_relat_1 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc5_relat_1])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ sk_D)
% 0.20/0.49          | ~ (v4_relat_1 @ sk_D @ X0)
% 0.20/0.49          | (v4_relat_1 @ (k6_relat_1 @ sk_C) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(cc2_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.20/0.49          | (v1_relat_1 @ X6)
% 0.20/0.49          | ~ (v1_relat_1 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf(fc6_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.49  thf('20', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.49      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v4_relat_1 @ sk_D @ X0) | (v4_relat_1 @ (k6_relat_1 @ sk_C) @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['15', '20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ sk_D)
% 0.20/0.49        | (v4_relat_1 @ (k6_relat_1 @ sk_C) @ (k1_relat_1 @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['10', '21'])).
% 0.20/0.49  thf('23', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.49      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.49  thf('24', plain, ((v4_relat_1 @ (k6_relat_1 @ sk_C) @ (k1_relat_1 @ sk_D))),
% 0.20/0.49      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i]:
% 0.20/0.49         (~ (v4_relat_1 @ X14 @ X15)
% 0.20/0.49          | (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 0.20/0.49          | ~ (v1_relat_1 @ X14))),
% 0.20/0.49      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_C))
% 0.20/0.49        | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ sk_C)) @ (k1_relat_1 @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.20/0.49  thf('27', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.49  thf(t71_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.20/0.49       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.49  thf('28', plain, (![X21 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 0.20/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.49  thf('29', plain, ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_D))),
% 0.20/0.49      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.20/0.49  thf('30', plain, (((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.20/0.49      inference('demod', [status(thm)], ['6', '29'])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D))) | 
% 0.20/0.49       ~ ((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['30', '31'])).
% 0.20/0.49  thf('33', plain, (~ (r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['1', '32'])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.49         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 0.20/0.49          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.49  thf('37', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.49      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.49  thf(d19_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X16 : $i, X17 : $i]:
% 0.20/0.49         (~ (r1_tarski @ (k2_relat_1 @ X16) @ X17)
% 0.20/0.49          | (v5_relat_1 @ X16 @ X17)
% 0.20/0.49          | ~ (v1_relat_1 @ X16))),
% 0.20/0.49      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      ((m1_subset_1 @ (k6_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf(cc6_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) ) => ( v5_relat_1 @ C @ A ) ) ) ))).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.20/0.49          | (v5_relat_1 @ X11 @ X13)
% 0.20/0.49          | ~ (v5_relat_1 @ X12 @ X13)
% 0.20/0.49          | ~ (v1_relat_1 @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc6_relat_1])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ sk_D)
% 0.20/0.49          | ~ (v5_relat_1 @ sk_D @ X0)
% 0.20/0.49          | (v5_relat_1 @ (k6_relat_1 @ sk_C) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.49  thf('43', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.49      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v5_relat_1 @ sk_D @ X0) | (v5_relat_1 @ (k6_relat_1 @ sk_C) @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ sk_D)
% 0.20/0.49        | (v5_relat_1 @ (k6_relat_1 @ sk_C) @ (k2_relat_1 @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['39', '44'])).
% 0.20/0.49  thf('46', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.49      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.49  thf('47', plain, ((v5_relat_1 @ (k6_relat_1 @ sk_C) @ (k2_relat_1 @ sk_D))),
% 0.20/0.49      inference('demod', [status(thm)], ['45', '46'])).
% 0.20/0.49  thf('48', plain,
% 0.20/0.49      (![X16 : $i, X17 : $i]:
% 0.20/0.49         (~ (v5_relat_1 @ X16 @ X17)
% 0.20/0.49          | (r1_tarski @ (k2_relat_1 @ X16) @ X17)
% 0.20/0.49          | ~ (v1_relat_1 @ X16))),
% 0.20/0.49      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.20/0.49  thf('49', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_C))
% 0.20/0.49        | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ sk_C)) @ (k2_relat_1 @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.49  thf('50', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.49  thf('51', plain, (![X22 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 0.20/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.49  thf('52', plain, ((r1_tarski @ sk_C @ (k2_relat_1 @ sk_D))),
% 0.20/0.49      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.20/0.49  thf('53', plain, ($false),
% 0.20/0.49      inference('demod', [status(thm)], ['33', '36', '52'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
