%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ipCMjqcvzY

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:04 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 120 expanded)
%              Number of leaves         :   32 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :  496 (1037 expanded)
%              Number of equality atoms :   13 (  18 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('4',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_relat_1 @ sk_D ) )
   <= ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X18: $i] :
      ( ( r1_tarski @ X18 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X18 ) @ ( k2_relat_1 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('7',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_C ) @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('9',plain,
    ( ( k2_xboole_0 @ ( k6_relat_1 @ sk_C ) @ sk_D )
    = sk_D ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_D @ X0 )
      | ( r1_tarski @ ( k6_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k6_relat_1 @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['12','17'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    m1_subset_1 @ ( k6_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('22',plain,(
    v4_relat_1 @ ( k6_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('23',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v4_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('25',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('26',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('27',plain,(
    r1_tarski @ sk_C @ ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('30',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_D ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,(
    ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sat_resolution*',[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( r1_tarski @ sk_C @ ( k2_relat_1 @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['5','35'])).

thf('37',plain,(
    m1_subset_1 @ ( k6_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('38',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v5_relat_1 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('39',plain,(
    v5_relat_1 @ ( k6_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('40',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v5_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('43',plain,(
    ! [X20: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('44',plain,(
    r1_tarski @ sk_C @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['36','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ipCMjqcvzY
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:22:23 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.76/0.98  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/0.98  % Solved by: fo/fo7.sh
% 0.76/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.98  % done 791 iterations in 0.514s
% 0.76/0.98  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/0.98  % SZS output start Refutation
% 0.76/0.98  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.76/0.98  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.76/0.98  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.76/0.98  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.76/0.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.98  thf(sk_C_type, type, sk_C: $i).
% 0.76/0.98  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.98  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.76/0.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.76/0.98  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.76/0.98  thf(sk_D_type, type, sk_D: $i).
% 0.76/0.98  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.76/0.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.98  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.76/0.98  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.76/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/0.98  thf(t30_relset_1, conjecture,
% 0.76/0.98    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.98     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.98       ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D ) =>
% 0.76/0.98         ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) ) & 
% 0.76/0.98           ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.76/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.98    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.98        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.98          ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D ) =>
% 0.76/0.98            ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) ) & 
% 0.76/0.98              ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )),
% 0.76/0.98    inference('cnf.neg', [status(esa)], [t30_relset_1])).
% 0.76/0.98  thf('0', plain,
% 0.76/0.98      ((~ (r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D))
% 0.76/0.98        | ~ (r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('1', plain,
% 0.76/0.98      ((~ (r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D)))
% 0.76/0.98         <= (~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 0.76/0.98      inference('split', [status(esa)], ['0'])).
% 0.76/0.98  thf('2', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(redefinition_k2_relset_1, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.98       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.76/0.98  thf('3', plain,
% 0.76/0.98      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.76/0.98         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 0.76/0.98          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.76/0.98      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.76/0.98  thf('4', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.76/0.98      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.98  thf('5', plain,
% 0.76/0.98      ((~ (r1_tarski @ sk_C @ (k2_relat_1 @ sk_D)))
% 0.76/0.98         <= (~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 0.76/0.98      inference('demod', [status(thm)], ['1', '4'])).
% 0.76/0.98  thf(t21_relat_1, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( v1_relat_1 @ A ) =>
% 0.76/0.98       ( r1_tarski @
% 0.76/0.98         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.76/0.98  thf('6', plain,
% 0.76/0.98      (![X18 : $i]:
% 0.76/0.98         ((r1_tarski @ X18 @ 
% 0.76/0.98           (k2_zfmisc_1 @ (k1_relat_1 @ X18) @ (k2_relat_1 @ X18)))
% 0.76/0.98          | ~ (v1_relat_1 @ X18))),
% 0.76/0.98      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.76/0.98  thf('7', plain, ((r1_tarski @ (k6_relat_1 @ sk_C) @ sk_D)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(t12_xboole_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.76/0.98  thf('8', plain,
% 0.76/0.98      (![X3 : $i, X4 : $i]:
% 0.76/0.98         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.76/0.98      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.76/0.98  thf('9', plain, (((k2_xboole_0 @ (k6_relat_1 @ sk_C) @ sk_D) = (sk_D))),
% 0.76/0.98      inference('sup-', [status(thm)], ['7', '8'])).
% 0.76/0.98  thf(t11_xboole_1, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.76/0.98  thf('10', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.98         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.76/0.98      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.76/0.98  thf('11', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (~ (r1_tarski @ sk_D @ X0) | (r1_tarski @ (k6_relat_1 @ sk_C) @ X0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['9', '10'])).
% 0.76/0.98  thf('12', plain,
% 0.76/0.98      ((~ (v1_relat_1 @ sk_D)
% 0.76/0.98        | (r1_tarski @ (k6_relat_1 @ sk_C) @ 
% 0.76/0.98           (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['6', '11'])).
% 0.76/0.98  thf('13', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(cc2_relat_1, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( v1_relat_1 @ A ) =>
% 0.76/0.98       ( ![B:$i]:
% 0.76/0.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.76/0.98  thf('14', plain,
% 0.76/0.98      (![X10 : $i, X11 : $i]:
% 0.76/0.98         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.76/0.98          | (v1_relat_1 @ X10)
% 0.76/0.98          | ~ (v1_relat_1 @ X11))),
% 0.76/0.98      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.76/0.98  thf('15', plain,
% 0.76/0.98      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.76/0.98      inference('sup-', [status(thm)], ['13', '14'])).
% 0.76/0.98  thf(fc6_relat_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.76/0.98  thf('16', plain,
% 0.76/0.98      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 0.76/0.98      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.76/0.98  thf('17', plain, ((v1_relat_1 @ sk_D)),
% 0.76/0.98      inference('demod', [status(thm)], ['15', '16'])).
% 0.76/0.98  thf('18', plain,
% 0.76/0.98      ((r1_tarski @ (k6_relat_1 @ sk_C) @ 
% 0.76/0.98        (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D)))),
% 0.76/0.98      inference('demod', [status(thm)], ['12', '17'])).
% 0.76/0.98  thf(t3_subset, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.76/0.98  thf('19', plain,
% 0.76/0.98      (![X7 : $i, X9 : $i]:
% 0.76/0.98         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.76/0.98      inference('cnf', [status(esa)], [t3_subset])).
% 0.76/0.98  thf('20', plain,
% 0.76/0.98      ((m1_subset_1 @ (k6_relat_1 @ sk_C) @ 
% 0.76/0.98        (k1_zfmisc_1 @ 
% 0.76/0.98         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['18', '19'])).
% 0.76/0.98  thf(cc2_relset_1, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.98       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.76/0.98  thf('21', plain,
% 0.76/0.98      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.76/0.98         ((v4_relat_1 @ X23 @ X24)
% 0.76/0.98          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.76/0.98      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.76/0.98  thf('22', plain, ((v4_relat_1 @ (k6_relat_1 @ sk_C) @ (k1_relat_1 @ sk_D))),
% 0.76/0.98      inference('sup-', [status(thm)], ['20', '21'])).
% 0.76/0.98  thf(d18_relat_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( v1_relat_1 @ B ) =>
% 0.76/0.98       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.76/0.98  thf('23', plain,
% 0.76/0.98      (![X12 : $i, X13 : $i]:
% 0.76/0.98         (~ (v4_relat_1 @ X12 @ X13)
% 0.76/0.98          | (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.76/0.98          | ~ (v1_relat_1 @ X12))),
% 0.76/0.98      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.76/0.98  thf('24', plain,
% 0.76/0.98      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_C))
% 0.76/0.98        | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ sk_C)) @ (k1_relat_1 @ sk_D)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['22', '23'])).
% 0.76/0.98  thf(fc3_funct_1, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.76/0.98       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.76/0.98  thf('25', plain, (![X21 : $i]: (v1_relat_1 @ (k6_relat_1 @ X21))),
% 0.76/0.98      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.76/0.98  thf(t71_relat_1, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.76/0.98       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.76/0.98  thf('26', plain, (![X19 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 0.76/0.98      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.76/0.98  thf('27', plain, ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_D))),
% 0.76/0.98      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.76/0.98  thf('28', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(redefinition_k1_relset_1, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.98       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.76/0.98  thf('29', plain,
% 0.76/0.98      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.76/0.98         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 0.76/0.98          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.76/0.98      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.76/0.98  thf('30', plain,
% 0.76/0.98      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.76/0.98      inference('sup-', [status(thm)], ['28', '29'])).
% 0.76/0.98  thf('31', plain,
% 0.76/0.98      ((~ (r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D)))
% 0.76/0.98         <= (~ ((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 0.76/0.98      inference('split', [status(esa)], ['0'])).
% 0.76/0.98  thf('32', plain,
% 0.76/0.98      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_D)))
% 0.76/0.98         <= (~ ((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['30', '31'])).
% 0.76/0.98  thf('33', plain, (((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['27', '32'])).
% 0.76/0.98  thf('34', plain,
% 0.76/0.98      (~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D))) | 
% 0.76/0.98       ~ ((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.76/0.98      inference('split', [status(esa)], ['0'])).
% 0.76/0.98  thf('35', plain,
% 0.76/0.98      (~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.76/0.98      inference('sat_resolution*', [status(thm)], ['33', '34'])).
% 0.76/0.98  thf('36', plain, (~ (r1_tarski @ sk_C @ (k2_relat_1 @ sk_D))),
% 0.76/0.98      inference('simpl_trail', [status(thm)], ['5', '35'])).
% 0.76/0.98  thf('37', plain,
% 0.76/0.98      ((m1_subset_1 @ (k6_relat_1 @ sk_C) @ 
% 0.76/0.98        (k1_zfmisc_1 @ 
% 0.76/0.98         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['18', '19'])).
% 0.76/0.98  thf('38', plain,
% 0.76/0.98      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.76/0.98         ((v5_relat_1 @ X23 @ X25)
% 0.76/0.98          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.76/0.98      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.76/0.98  thf('39', plain, ((v5_relat_1 @ (k6_relat_1 @ sk_C) @ (k2_relat_1 @ sk_D))),
% 0.76/0.98      inference('sup-', [status(thm)], ['37', '38'])).
% 0.76/0.98  thf(d19_relat_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( v1_relat_1 @ B ) =>
% 0.76/0.98       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.76/0.98  thf('40', plain,
% 0.76/0.98      (![X14 : $i, X15 : $i]:
% 0.76/0.98         (~ (v5_relat_1 @ X14 @ X15)
% 0.76/0.98          | (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 0.76/0.98          | ~ (v1_relat_1 @ X14))),
% 0.76/0.98      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.76/0.98  thf('41', plain,
% 0.76/0.98      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_C))
% 0.76/0.98        | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ sk_C)) @ (k2_relat_1 @ sk_D)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['39', '40'])).
% 0.76/0.98  thf('42', plain, (![X21 : $i]: (v1_relat_1 @ (k6_relat_1 @ X21))),
% 0.76/0.98      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.76/0.98  thf('43', plain, (![X20 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 0.76/0.98      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.76/0.98  thf('44', plain, ((r1_tarski @ sk_C @ (k2_relat_1 @ sk_D))),
% 0.76/0.98      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.76/0.98  thf('45', plain, ($false), inference('demod', [status(thm)], ['36', '44'])).
% 0.76/0.98  
% 0.76/0.98  % SZS output end Refutation
% 0.76/0.98  
% 0.76/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
