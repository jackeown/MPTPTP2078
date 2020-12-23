%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DfWQkteOyj

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:04 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 141 expanded)
%              Number of leaves         :   28 (  52 expanded)
%              Depth                    :   16
%              Number of atoms          :  588 (1318 expanded)
%              Number of equality atoms :   25 (  56 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(t31_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C )
       => ( ( B
            = ( k1_relset_1 @ B @ A @ C ) )
          & ( r1_tarski @ B @ ( k2_relset_1 @ B @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
       => ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C )
         => ( ( B
              = ( k1_relset_1 @ B @ A @ C ) )
            & ( r1_tarski @ B @ ( k2_relset_1 @ B @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_relset_1])).

thf('0',plain,
    ( ( sk_B
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ~ ( r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ~ ( r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('4',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('7',plain,(
    v4_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v4_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['9','12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_C ) )
    | ( sk_B
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( v4_relat_1 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    m1_subset_1 @ ( k6_relat_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(cc5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) )
         => ( v4_relat_1 @ C @ A ) ) ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v4_relat_1 @ X6 @ X8 )
      | ~ ( v4_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc5_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v4_relat_1 @ sk_C @ X0 )
      | ( v4_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['10','11'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ sk_C @ X0 )
      | ( v4_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( v4_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['10','11'])).

thf('29',plain,(
    v4_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v4_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(fc24_relat_1,axiom,(
    ! [A: $i] :
      ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('32',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('33',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('34',plain,(
    r1_tarski @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['15','34'])).

thf('36',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['4','35'])).

thf('37',plain,
    ( ( sk_B
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( sk_B
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ( sk_B != sk_B )
   <= ( sk_B
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( sk_B
    = ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( sk_B
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['1','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('44',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X32 @ X30 )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('45',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('47',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ( v5_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ ( k6_relat_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(cc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) )
         => ( v5_relat_1 @ C @ A ) ) ) )).

thf('50',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v5_relat_1 @ X9 @ X11 )
      | ~ ( v5_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc6_relat_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v5_relat_1 @ sk_C @ X0 )
      | ( v5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['10','11'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_C @ X0 )
      | ( v5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( v5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['10','11'])).

thf('56',plain,(
    v5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v5_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('60',plain,(
    ! [X17: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('61',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['42','45','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DfWQkteOyj
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:22:55 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.34/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.34/0.53  % Solved by: fo/fo7.sh
% 0.34/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.53  % done 152 iterations in 0.080s
% 0.34/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.34/0.53  % SZS output start Refutation
% 0.34/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.34/0.53  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.34/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.34/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.34/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.34/0.53  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.34/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.34/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.34/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.53  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.34/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.34/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.34/0.53  thf(t31_relset_1, conjecture,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.34/0.53       ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C ) =>
% 0.34/0.53         ( ( ( B ) = ( k1_relset_1 @ B @ A @ C ) ) & 
% 0.34/0.53           ( r1_tarski @ B @ ( k2_relset_1 @ B @ A @ C ) ) ) ) ))).
% 0.34/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.34/0.53        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.34/0.53          ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C ) =>
% 0.34/0.53            ( ( ( B ) = ( k1_relset_1 @ B @ A @ C ) ) & 
% 0.34/0.53              ( r1_tarski @ B @ ( k2_relset_1 @ B @ A @ C ) ) ) ) ) )),
% 0.34/0.53    inference('cnf.neg', [status(esa)], [t31_relset_1])).
% 0.34/0.53  thf('0', plain,
% 0.34/0.53      ((((sk_B) != (k1_relset_1 @ sk_B @ sk_A @ sk_C))
% 0.34/0.53        | ~ (r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('1', plain,
% 0.34/0.53      ((~ (r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.34/0.53         <= (~ ((r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.34/0.53      inference('split', [status(esa)], ['0'])).
% 0.34/0.53  thf('2', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(redefinition_k1_relset_1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.53       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.34/0.53  thf('3', plain,
% 0.34/0.53      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.34/0.53         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 0.34/0.53          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.34/0.53      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.34/0.53  thf('4', plain, (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.34/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.34/0.53  thf('5', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(cc2_relset_1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.34/0.53  thf('6', plain,
% 0.34/0.53      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.34/0.53         ((v4_relat_1 @ X24 @ X25)
% 0.34/0.53          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.34/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.34/0.53  thf('7', plain, ((v4_relat_1 @ sk_C @ sk_B)),
% 0.34/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.34/0.53  thf(d18_relat_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( v1_relat_1 @ B ) =>
% 0.34/0.53       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.34/0.53  thf('8', plain,
% 0.34/0.53      (![X12 : $i, X13 : $i]:
% 0.34/0.53         (~ (v4_relat_1 @ X12 @ X13)
% 0.34/0.53          | (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.34/0.53          | ~ (v1_relat_1 @ X12))),
% 0.34/0.53      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.34/0.53  thf('9', plain,
% 0.34/0.53      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_B))),
% 0.34/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.34/0.53  thf('10', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(cc1_relset_1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.53       ( v1_relat_1 @ C ) ))).
% 0.34/0.53  thf('11', plain,
% 0.34/0.53      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.34/0.53         ((v1_relat_1 @ X21)
% 0.34/0.53          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.34/0.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.34/0.53  thf('12', plain, ((v1_relat_1 @ sk_C)),
% 0.34/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.34/0.53  thf('13', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_B)),
% 0.34/0.53      inference('demod', [status(thm)], ['9', '12'])).
% 0.34/0.53  thf(d10_xboole_0, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.34/0.53  thf('14', plain,
% 0.34/0.53      (![X0 : $i, X2 : $i]:
% 0.34/0.53         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.34/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.34/0.53  thf('15', plain,
% 0.34/0.53      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ sk_C))
% 0.34/0.53        | ((sk_B) = (k1_relat_1 @ sk_C)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.34/0.53  thf('16', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.34/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.34/0.53  thf('17', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.34/0.53      inference('simplify', [status(thm)], ['16'])).
% 0.34/0.53  thf('18', plain,
% 0.34/0.53      (![X12 : $i, X13 : $i]:
% 0.34/0.53         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.34/0.53          | (v4_relat_1 @ X12 @ X13)
% 0.34/0.53          | ~ (v1_relat_1 @ X12))),
% 0.34/0.53      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.34/0.53  thf('19', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.34/0.53  thf('20', plain, ((r1_tarski @ (k6_relat_1 @ sk_B) @ sk_C)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(t3_subset, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.34/0.53  thf('21', plain,
% 0.34/0.53      (![X3 : $i, X5 : $i]:
% 0.34/0.53         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.34/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.34/0.53  thf('22', plain,
% 0.34/0.53      ((m1_subset_1 @ (k6_relat_1 @ sk_B) @ (k1_zfmisc_1 @ sk_C))),
% 0.34/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.34/0.53  thf(cc5_relat_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.34/0.53       ( ![C:$i]:
% 0.34/0.53         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) ) => ( v4_relat_1 @ C @ A ) ) ) ))).
% 0.34/0.53  thf('23', plain,
% 0.34/0.53      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.34/0.53         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.34/0.53          | (v4_relat_1 @ X6 @ X8)
% 0.34/0.53          | ~ (v4_relat_1 @ X7 @ X8)
% 0.34/0.53          | ~ (v1_relat_1 @ X7))),
% 0.34/0.53      inference('cnf', [status(esa)], [cc5_relat_1])).
% 0.34/0.53  thf('24', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (~ (v1_relat_1 @ sk_C)
% 0.34/0.53          | ~ (v4_relat_1 @ sk_C @ X0)
% 0.34/0.53          | (v4_relat_1 @ (k6_relat_1 @ sk_B) @ X0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.34/0.53  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.34/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.34/0.53  thf('26', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (~ (v4_relat_1 @ sk_C @ X0) | (v4_relat_1 @ (k6_relat_1 @ sk_B) @ X0))),
% 0.34/0.53      inference('demod', [status(thm)], ['24', '25'])).
% 0.34/0.53  thf('27', plain,
% 0.34/0.53      ((~ (v1_relat_1 @ sk_C)
% 0.34/0.53        | (v4_relat_1 @ (k6_relat_1 @ sk_B) @ (k1_relat_1 @ sk_C)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['19', '26'])).
% 0.34/0.53  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 0.34/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.34/0.53  thf('29', plain, ((v4_relat_1 @ (k6_relat_1 @ sk_B) @ (k1_relat_1 @ sk_C))),
% 0.34/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.34/0.53  thf('30', plain,
% 0.34/0.53      (![X12 : $i, X13 : $i]:
% 0.34/0.53         (~ (v4_relat_1 @ X12 @ X13)
% 0.34/0.53          | (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.34/0.53          | ~ (v1_relat_1 @ X12))),
% 0.34/0.53      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.34/0.53  thf('31', plain,
% 0.34/0.53      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.34/0.53        | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ sk_B)) @ (k1_relat_1 @ sk_C)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.34/0.53  thf(fc24_relat_1, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.34/0.53       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.34/0.53       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.34/0.53  thf('32', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 0.34/0.53      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.34/0.53  thf(t71_relat_1, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.34/0.53       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.34/0.53  thf('33', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.34/0.53      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.34/0.53  thf('34', plain, ((r1_tarski @ sk_B @ (k1_relat_1 @ sk_C))),
% 0.34/0.53      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.34/0.53  thf('35', plain, (((sk_B) = (k1_relat_1 @ sk_C))),
% 0.34/0.53      inference('demod', [status(thm)], ['15', '34'])).
% 0.34/0.53  thf('36', plain, (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (sk_B))),
% 0.34/0.53      inference('demod', [status(thm)], ['4', '35'])).
% 0.34/0.53  thf('37', plain,
% 0.34/0.53      ((((sk_B) != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.34/0.53         <= (~ (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.34/0.53      inference('split', [status(esa)], ['0'])).
% 0.34/0.53  thf('38', plain,
% 0.34/0.53      ((((sk_B) != (sk_B)))
% 0.34/0.53         <= (~ (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.34/0.53  thf('39', plain, ((((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.34/0.53      inference('simplify', [status(thm)], ['38'])).
% 0.34/0.53  thf('40', plain,
% 0.34/0.53      (~ ((r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))) | 
% 0.34/0.53       ~ (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.34/0.53      inference('split', [status(esa)], ['0'])).
% 0.34/0.53  thf('41', plain,
% 0.34/0.53      (~ ((r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.34/0.53      inference('sat_resolution*', [status(thm)], ['39', '40'])).
% 0.34/0.53  thf('42', plain, (~ (r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))),
% 0.34/0.53      inference('simpl_trail', [status(thm)], ['1', '41'])).
% 0.34/0.53  thf('43', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(redefinition_k2_relset_1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.53       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.34/0.53  thf('44', plain,
% 0.34/0.53      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.34/0.53         (((k2_relset_1 @ X31 @ X32 @ X30) = (k2_relat_1 @ X30))
% 0.34/0.53          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.34/0.53      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.34/0.53  thf('45', plain,
% 0.34/0.53      (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.34/0.53      inference('sup-', [status(thm)], ['43', '44'])).
% 0.34/0.53  thf('46', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.34/0.53      inference('simplify', [status(thm)], ['16'])).
% 0.34/0.53  thf(d19_relat_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( v1_relat_1 @ B ) =>
% 0.34/0.53       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.34/0.53  thf('47', plain,
% 0.34/0.53      (![X14 : $i, X15 : $i]:
% 0.34/0.53         (~ (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 0.34/0.53          | (v5_relat_1 @ X14 @ X15)
% 0.34/0.53          | ~ (v1_relat_1 @ X14))),
% 0.34/0.53      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.34/0.53  thf('48', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['46', '47'])).
% 0.34/0.53  thf('49', plain,
% 0.34/0.53      ((m1_subset_1 @ (k6_relat_1 @ sk_B) @ (k1_zfmisc_1 @ sk_C))),
% 0.34/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.34/0.53  thf(cc6_relat_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.34/0.53       ( ![C:$i]:
% 0.34/0.53         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) ) => ( v5_relat_1 @ C @ A ) ) ) ))).
% 0.34/0.53  thf('50', plain,
% 0.34/0.53      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.34/0.53         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.34/0.53          | (v5_relat_1 @ X9 @ X11)
% 0.34/0.53          | ~ (v5_relat_1 @ X10 @ X11)
% 0.34/0.53          | ~ (v1_relat_1 @ X10))),
% 0.34/0.53      inference('cnf', [status(esa)], [cc6_relat_1])).
% 0.34/0.53  thf('51', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (~ (v1_relat_1 @ sk_C)
% 0.34/0.53          | ~ (v5_relat_1 @ sk_C @ X0)
% 0.34/0.53          | (v5_relat_1 @ (k6_relat_1 @ sk_B) @ X0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['49', '50'])).
% 0.34/0.53  thf('52', plain, ((v1_relat_1 @ sk_C)),
% 0.34/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.34/0.53  thf('53', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (~ (v5_relat_1 @ sk_C @ X0) | (v5_relat_1 @ (k6_relat_1 @ sk_B) @ X0))),
% 0.34/0.53      inference('demod', [status(thm)], ['51', '52'])).
% 0.34/0.53  thf('54', plain,
% 0.34/0.53      ((~ (v1_relat_1 @ sk_C)
% 0.34/0.53        | (v5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_relat_1 @ sk_C)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['48', '53'])).
% 0.34/0.53  thf('55', plain, ((v1_relat_1 @ sk_C)),
% 0.34/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.34/0.53  thf('56', plain, ((v5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_relat_1 @ sk_C))),
% 0.34/0.53      inference('demod', [status(thm)], ['54', '55'])).
% 0.34/0.53  thf('57', plain,
% 0.34/0.53      (![X14 : $i, X15 : $i]:
% 0.34/0.53         (~ (v5_relat_1 @ X14 @ X15)
% 0.34/0.53          | (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 0.34/0.53          | ~ (v1_relat_1 @ X14))),
% 0.34/0.53      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.34/0.53  thf('58', plain,
% 0.34/0.53      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.34/0.53        | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ sk_B)) @ (k2_relat_1 @ sk_C)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['56', '57'])).
% 0.34/0.53  thf('59', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 0.34/0.53      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.34/0.53  thf('60', plain, (![X17 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 0.34/0.53      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.34/0.53  thf('61', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))),
% 0.34/0.53      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.34/0.53  thf('62', plain, ($false),
% 0.34/0.53      inference('demod', [status(thm)], ['42', '45', '61'])).
% 0.34/0.53  
% 0.34/0.53  % SZS output end Refutation
% 0.34/0.53  
% 0.34/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
