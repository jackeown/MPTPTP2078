%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YNDG3GKgP3

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:03 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 126 expanded)
%              Number of leaves         :   33 (  51 expanded)
%              Depth                    :   14
%              Number of atoms          :  524 (1093 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_xboole_0 @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('10',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_C ) @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X4 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_relat_1 @ sk_C ) @ ( k2_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_D @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( m1_subset_1 @ ( k6_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['8','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('20',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('21',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ ( k6_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['16','21'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('24',plain,(
    v4_relat_1 @ ( k6_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v4_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('27',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('28',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('29',plain,(
    r1_tarski @ sk_C @ ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('31',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('32',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_D ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,(
    ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sat_resolution*',[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( r1_tarski @ sk_C @ ( k2_relat_1 @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['5','37'])).

thf('39',plain,(
    m1_subset_1 @ ( k6_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['16','21'])).

thf('40',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v5_relat_1 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('41',plain,(
    v5_relat_1 @ ( k6_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('42',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v5_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('45',plain,(
    ! [X20: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('46',plain,(
    r1_tarski @ sk_C @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['38','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YNDG3GKgP3
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:29:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.66/1.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.66/1.90  % Solved by: fo/fo7.sh
% 1.66/1.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.66/1.90  % done 5026 iterations in 1.442s
% 1.66/1.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.66/1.90  % SZS output start Refutation
% 1.66/1.90  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.66/1.90  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.66/1.90  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.66/1.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.66/1.90  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.66/1.90  thf(sk_C_type, type, sk_C: $i).
% 1.66/1.90  thf(sk_B_type, type, sk_B: $i).
% 1.66/1.90  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.66/1.90  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.66/1.90  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.66/1.90  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.66/1.90  thf(sk_D_type, type, sk_D: $i).
% 1.66/1.90  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.66/1.90  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.66/1.90  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.66/1.90  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.66/1.90  thf(sk_A_type, type, sk_A: $i).
% 1.66/1.90  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.66/1.90  thf(t30_relset_1, conjecture,
% 1.66/1.90    (![A:$i,B:$i,C:$i,D:$i]:
% 1.66/1.90     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.66/1.90       ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D ) =>
% 1.66/1.90         ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) ) & 
% 1.66/1.90           ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 1.66/1.90  thf(zf_stmt_0, negated_conjecture,
% 1.66/1.90    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.66/1.90        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.66/1.90          ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D ) =>
% 1.66/1.90            ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) ) & 
% 1.66/1.90              ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )),
% 1.66/1.90    inference('cnf.neg', [status(esa)], [t30_relset_1])).
% 1.66/1.90  thf('0', plain,
% 1.66/1.90      ((~ (r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D))
% 1.66/1.90        | ~ (r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 1.66/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.90  thf('1', plain,
% 1.66/1.90      ((~ (r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D)))
% 1.66/1.90         <= (~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 1.66/1.90      inference('split', [status(esa)], ['0'])).
% 1.66/1.90  thf('2', plain,
% 1.66/1.90      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.66/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.90  thf(redefinition_k2_relset_1, axiom,
% 1.66/1.90    (![A:$i,B:$i,C:$i]:
% 1.66/1.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.66/1.90       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.66/1.90  thf('3', plain,
% 1.66/1.90      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.66/1.90         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 1.66/1.90          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 1.66/1.90      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.66/1.90  thf('4', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.66/1.90      inference('sup-', [status(thm)], ['2', '3'])).
% 1.66/1.90  thf('5', plain,
% 1.66/1.90      ((~ (r1_tarski @ sk_C @ (k2_relat_1 @ sk_D)))
% 1.66/1.90         <= (~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 1.66/1.90      inference('demod', [status(thm)], ['1', '4'])).
% 1.66/1.90  thf(t21_relat_1, axiom,
% 1.66/1.90    (![A:$i]:
% 1.66/1.90     ( ( v1_relat_1 @ A ) =>
% 1.66/1.90       ( r1_tarski @
% 1.66/1.90         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 1.66/1.90  thf('6', plain,
% 1.66/1.90      (![X18 : $i]:
% 1.66/1.90         ((r1_tarski @ X18 @ 
% 1.66/1.90           (k2_zfmisc_1 @ (k1_relat_1 @ X18) @ (k2_relat_1 @ X18)))
% 1.66/1.90          | ~ (v1_relat_1 @ X18))),
% 1.66/1.90      inference('cnf', [status(esa)], [t21_relat_1])).
% 1.66/1.90  thf(t12_xboole_1, axiom,
% 1.66/1.90    (![A:$i,B:$i]:
% 1.66/1.90     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.66/1.90  thf('7', plain,
% 1.66/1.90      (![X5 : $i, X6 : $i]:
% 1.66/1.90         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 1.66/1.90      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.66/1.90  thf('8', plain,
% 1.66/1.90      (![X0 : $i]:
% 1.66/1.90         (~ (v1_relat_1 @ X0)
% 1.66/1.90          | ((k2_xboole_0 @ X0 @ 
% 1.66/1.90              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 1.66/1.90              = (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 1.66/1.90      inference('sup-', [status(thm)], ['6', '7'])).
% 1.66/1.90  thf(commutativity_k2_xboole_0, axiom,
% 1.66/1.90    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.66/1.90  thf('9', plain,
% 1.66/1.90      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.66/1.90      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.66/1.90  thf('10', plain, ((r1_tarski @ (k6_relat_1 @ sk_C) @ sk_D)),
% 1.66/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.90  thf(t10_xboole_1, axiom,
% 1.66/1.90    (![A:$i,B:$i,C:$i]:
% 1.66/1.90     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 1.66/1.90  thf('11', plain,
% 1.66/1.90      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.66/1.90         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ X2 @ (k2_xboole_0 @ X4 @ X3)))),
% 1.66/1.90      inference('cnf', [status(esa)], [t10_xboole_1])).
% 1.66/1.90  thf('12', plain,
% 1.66/1.90      (![X0 : $i]:
% 1.66/1.90         (r1_tarski @ (k6_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_D))),
% 1.66/1.90      inference('sup-', [status(thm)], ['10', '11'])).
% 1.66/1.90  thf('13', plain,
% 1.66/1.90      (![X0 : $i]:
% 1.66/1.90         (r1_tarski @ (k6_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_D @ X0))),
% 1.66/1.90      inference('sup+', [status(thm)], ['9', '12'])).
% 1.66/1.90  thf(t3_subset, axiom,
% 1.66/1.90    (![A:$i,B:$i]:
% 1.66/1.90     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.66/1.90  thf('14', plain,
% 1.66/1.90      (![X7 : $i, X9 : $i]:
% 1.66/1.90         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 1.66/1.90      inference('cnf', [status(esa)], [t3_subset])).
% 1.66/1.90  thf('15', plain,
% 1.66/1.90      (![X0 : $i]:
% 1.66/1.90         (m1_subset_1 @ (k6_relat_1 @ sk_C) @ 
% 1.66/1.90          (k1_zfmisc_1 @ (k2_xboole_0 @ sk_D @ X0)))),
% 1.66/1.90      inference('sup-', [status(thm)], ['13', '14'])).
% 1.66/1.90  thf('16', plain,
% 1.66/1.90      (((m1_subset_1 @ (k6_relat_1 @ sk_C) @ 
% 1.66/1.90         (k1_zfmisc_1 @ 
% 1.66/1.90          (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D))))
% 1.66/1.90        | ~ (v1_relat_1 @ sk_D))),
% 1.66/1.90      inference('sup+', [status(thm)], ['8', '15'])).
% 1.66/1.90  thf('17', plain,
% 1.66/1.90      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.66/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.90  thf(cc2_relat_1, axiom,
% 1.66/1.90    (![A:$i]:
% 1.66/1.90     ( ( v1_relat_1 @ A ) =>
% 1.66/1.90       ( ![B:$i]:
% 1.66/1.90         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.66/1.90  thf('18', plain,
% 1.66/1.90      (![X10 : $i, X11 : $i]:
% 1.66/1.90         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 1.66/1.90          | (v1_relat_1 @ X10)
% 1.66/1.90          | ~ (v1_relat_1 @ X11))),
% 1.66/1.90      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.66/1.90  thf('19', plain,
% 1.66/1.90      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 1.66/1.90      inference('sup-', [status(thm)], ['17', '18'])).
% 1.66/1.90  thf(fc6_relat_1, axiom,
% 1.66/1.90    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.66/1.90  thf('20', plain,
% 1.66/1.90      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 1.66/1.90      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.66/1.90  thf('21', plain, ((v1_relat_1 @ sk_D)),
% 1.66/1.90      inference('demod', [status(thm)], ['19', '20'])).
% 1.66/1.90  thf('22', plain,
% 1.66/1.90      ((m1_subset_1 @ (k6_relat_1 @ sk_C) @ 
% 1.66/1.90        (k1_zfmisc_1 @ 
% 1.66/1.90         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D))))),
% 1.66/1.90      inference('demod', [status(thm)], ['16', '21'])).
% 1.66/1.90  thf(cc2_relset_1, axiom,
% 1.66/1.90    (![A:$i,B:$i,C:$i]:
% 1.66/1.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.66/1.90       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.66/1.90  thf('23', plain,
% 1.66/1.90      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.66/1.90         ((v4_relat_1 @ X23 @ X24)
% 1.66/1.90          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.66/1.90      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.66/1.90  thf('24', plain, ((v4_relat_1 @ (k6_relat_1 @ sk_C) @ (k1_relat_1 @ sk_D))),
% 1.66/1.90      inference('sup-', [status(thm)], ['22', '23'])).
% 1.66/1.90  thf(d18_relat_1, axiom,
% 1.66/1.90    (![A:$i,B:$i]:
% 1.66/1.90     ( ( v1_relat_1 @ B ) =>
% 1.66/1.90       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.66/1.90  thf('25', plain,
% 1.66/1.90      (![X12 : $i, X13 : $i]:
% 1.66/1.90         (~ (v4_relat_1 @ X12 @ X13)
% 1.66/1.90          | (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 1.66/1.90          | ~ (v1_relat_1 @ X12))),
% 1.66/1.90      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.66/1.90  thf('26', plain,
% 1.66/1.90      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_C))
% 1.66/1.90        | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ sk_C)) @ (k1_relat_1 @ sk_D)))),
% 1.66/1.90      inference('sup-', [status(thm)], ['24', '25'])).
% 1.66/1.90  thf(fc3_funct_1, axiom,
% 1.66/1.90    (![A:$i]:
% 1.66/1.90     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.66/1.90       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.66/1.90  thf('27', plain, (![X21 : $i]: (v1_relat_1 @ (k6_relat_1 @ X21))),
% 1.66/1.90      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.66/1.90  thf(t71_relat_1, axiom,
% 1.66/1.90    (![A:$i]:
% 1.66/1.90     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.66/1.90       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.66/1.90  thf('28', plain, (![X19 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 1.66/1.90      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.66/1.90  thf('29', plain, ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_D))),
% 1.66/1.90      inference('demod', [status(thm)], ['26', '27', '28'])).
% 1.66/1.90  thf('30', plain,
% 1.66/1.90      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.66/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.90  thf(redefinition_k1_relset_1, axiom,
% 1.66/1.90    (![A:$i,B:$i,C:$i]:
% 1.66/1.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.66/1.90       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.66/1.90  thf('31', plain,
% 1.66/1.90      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.66/1.90         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 1.66/1.90          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 1.66/1.90      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.66/1.90  thf('32', plain,
% 1.66/1.90      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.66/1.90      inference('sup-', [status(thm)], ['30', '31'])).
% 1.66/1.90  thf('33', plain,
% 1.66/1.90      ((~ (r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D)))
% 1.66/1.90         <= (~ ((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 1.66/1.90      inference('split', [status(esa)], ['0'])).
% 1.66/1.90  thf('34', plain,
% 1.66/1.90      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_D)))
% 1.66/1.90         <= (~ ((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 1.66/1.90      inference('sup-', [status(thm)], ['32', '33'])).
% 1.66/1.90  thf('35', plain, (((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 1.66/1.90      inference('sup-', [status(thm)], ['29', '34'])).
% 1.66/1.90  thf('36', plain,
% 1.66/1.90      (~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D))) | 
% 1.66/1.90       ~ ((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 1.66/1.90      inference('split', [status(esa)], ['0'])).
% 1.66/1.90  thf('37', plain,
% 1.66/1.90      (~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 1.66/1.90      inference('sat_resolution*', [status(thm)], ['35', '36'])).
% 1.66/1.90  thf('38', plain, (~ (r1_tarski @ sk_C @ (k2_relat_1 @ sk_D))),
% 1.66/1.90      inference('simpl_trail', [status(thm)], ['5', '37'])).
% 1.66/1.90  thf('39', plain,
% 1.66/1.90      ((m1_subset_1 @ (k6_relat_1 @ sk_C) @ 
% 1.66/1.90        (k1_zfmisc_1 @ 
% 1.66/1.90         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D))))),
% 1.66/1.90      inference('demod', [status(thm)], ['16', '21'])).
% 1.66/1.90  thf('40', plain,
% 1.66/1.90      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.66/1.90         ((v5_relat_1 @ X23 @ X25)
% 1.66/1.90          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.66/1.90      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.66/1.90  thf('41', plain, ((v5_relat_1 @ (k6_relat_1 @ sk_C) @ (k2_relat_1 @ sk_D))),
% 1.66/1.90      inference('sup-', [status(thm)], ['39', '40'])).
% 1.66/1.90  thf(d19_relat_1, axiom,
% 1.66/1.90    (![A:$i,B:$i]:
% 1.66/1.90     ( ( v1_relat_1 @ B ) =>
% 1.66/1.90       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.66/1.90  thf('42', plain,
% 1.66/1.90      (![X14 : $i, X15 : $i]:
% 1.66/1.90         (~ (v5_relat_1 @ X14 @ X15)
% 1.66/1.90          | (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 1.66/1.90          | ~ (v1_relat_1 @ X14))),
% 1.66/1.90      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.66/1.90  thf('43', plain,
% 1.66/1.90      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_C))
% 1.66/1.90        | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ sk_C)) @ (k2_relat_1 @ sk_D)))),
% 1.66/1.90      inference('sup-', [status(thm)], ['41', '42'])).
% 1.66/1.90  thf('44', plain, (![X21 : $i]: (v1_relat_1 @ (k6_relat_1 @ X21))),
% 1.66/1.90      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.66/1.90  thf('45', plain, (![X20 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 1.66/1.90      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.66/1.90  thf('46', plain, ((r1_tarski @ sk_C @ (k2_relat_1 @ sk_D))),
% 1.66/1.90      inference('demod', [status(thm)], ['43', '44', '45'])).
% 1.66/1.90  thf('47', plain, ($false), inference('demod', [status(thm)], ['38', '46'])).
% 1.66/1.90  
% 1.66/1.90  % SZS output end Refutation
% 1.66/1.90  
% 1.66/1.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
