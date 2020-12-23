%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3KHSO5eVCQ

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 148 expanded)
%              Number of leaves         :   31 (  63 expanded)
%              Depth                    :   10
%              Number of atoms          :  523 ( 938 expanded)
%              Number of equality atoms :   45 (  97 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(t171_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t171_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('2',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('3',plain,(
    ! [X18: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('5',plain,(
    ! [X18: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X18 ) )
      = X18 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X21 @ ( k2_relat_1 @ X22 ) )
      | ( ( k9_relat_1 @ X22 @ ( k10_relat_1 @ X22 @ X21 ) )
        = X21 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('9',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('10',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X20: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('12',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('13',plain,(
    ! [X20: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X20 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['7','10','13'])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X26 ) @ ( k6_relat_1 @ X25 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('16',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('17',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('18',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('19',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X26 ) @ ( k6_partfun1 @ X25 ) )
      = ( k6_partfun1 @ ( k3_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('20',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('21',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('22',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('23',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) )
        = ( k10_relat_1 @ X16 @ ( k1_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k6_partfun1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('29',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['14','30'])).

thf('32',plain,
    ( ( k9_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['2','31'])).

thf('33',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('35',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t162_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
        = B ) ) )).

thf('40',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X24 ) @ X23 )
        = X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t162_funct_1])).

thf('41',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('42',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k9_relat_1 @ ( k6_partfun1 @ X24 ) @ X23 )
        = X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['32','43'])).

thf('45',plain,(
    ( k8_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('46',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('47',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k8_relset_1 @ X28 @ X29 @ X27 @ X30 )
        = ( k10_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ( k3_xboole_0 @ sk_B @ sk_A )
 != sk_B ),
    inference(demod,[status(thm)],['45','50'])).

thf('52',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['44','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3KHSO5eVCQ
% 0.15/0.36  % Computer   : n003.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 19:45:12 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 77 iterations in 0.036s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.50  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.22/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.50  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.22/0.50  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.50  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.22/0.50  thf(t171_funct_2, conjecture,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.50       ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i]:
% 0.22/0.50        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.50          ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t171_funct_2])).
% 0.22/0.50  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t3_subset, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X12 : $i, X13 : $i]:
% 0.22/0.50         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.50  thf('2', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.22/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.50  thf(t71_relat_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.22/0.50       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.50  thf('3', plain, (![X18 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 0.22/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.50  thf(redefinition_k6_partfun1, axiom,
% 0.22/0.50    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.22/0.50  thf('4', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.22/0.50  thf('5', plain, (![X18 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X18)) = (X18))),
% 0.22/0.50      inference('demod', [status(thm)], ['3', '4'])).
% 0.22/0.50  thf(t147_funct_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.50       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.22/0.50         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X21 : $i, X22 : $i]:
% 0.22/0.50         (~ (r1_tarski @ X21 @ (k2_relat_1 @ X22))
% 0.22/0.50          | ((k9_relat_1 @ X22 @ (k10_relat_1 @ X22 @ X21)) = (X21))
% 0.22/0.50          | ~ (v1_funct_1 @ X22)
% 0.22/0.50          | ~ (v1_relat_1 @ X22))),
% 0.22/0.50      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (r1_tarski @ X1 @ X0)
% 0.22/0.50          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.22/0.50          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.22/0.50          | ((k9_relat_1 @ (k6_partfun1 @ X0) @ 
% 0.22/0.50              (k10_relat_1 @ (k6_partfun1 @ X0) @ X1)) = (X1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf(fc3_funct_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.22/0.50       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.22/0.50  thf('8', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.22/0.50  thf('9', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.22/0.50  thf('10', plain, (![X19 : $i]: (v1_relat_1 @ (k6_partfun1 @ X19))),
% 0.22/0.50      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.50  thf('11', plain, (![X20 : $i]: (v1_funct_1 @ (k6_relat_1 @ X20))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.22/0.50  thf('12', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.22/0.50  thf('13', plain, (![X20 : $i]: (v1_funct_1 @ (k6_partfun1 @ X20))),
% 0.22/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (r1_tarski @ X1 @ X0)
% 0.22/0.50          | ((k9_relat_1 @ (k6_partfun1 @ X0) @ 
% 0.22/0.50              (k10_relat_1 @ (k6_partfun1 @ X0) @ X1)) = (X1)))),
% 0.22/0.50      inference('demod', [status(thm)], ['7', '10', '13'])).
% 0.22/0.50  thf(t43_funct_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.22/0.50       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (![X25 : $i, X26 : $i]:
% 0.22/0.50         ((k5_relat_1 @ (k6_relat_1 @ X26) @ (k6_relat_1 @ X25))
% 0.22/0.50           = (k6_relat_1 @ (k3_xboole_0 @ X25 @ X26)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.22/0.50  thf('16', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.22/0.50  thf('17', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.22/0.50  thf('18', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (![X25 : $i, X26 : $i]:
% 0.22/0.50         ((k5_relat_1 @ (k6_partfun1 @ X26) @ (k6_partfun1 @ X25))
% 0.22/0.50           = (k6_partfun1 @ (k3_xboole_0 @ X25 @ X26)))),
% 0.22/0.50      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 0.22/0.50  thf('20', plain, (![X17 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 0.22/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.50  thf('21', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.22/0.50  thf('22', plain, (![X17 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 0.22/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.22/0.50  thf(t182_relat_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( v1_relat_1 @ B ) =>
% 0.22/0.50           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.22/0.50             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      (![X15 : $i, X16 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X15)
% 0.22/0.50          | ((k1_relat_1 @ (k5_relat_1 @ X16 @ X15))
% 0.22/0.50              = (k10_relat_1 @ X16 @ (k1_relat_1 @ X15)))
% 0.22/0.50          | ~ (v1_relat_1 @ X16))),
% 0.22/0.50      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 0.22/0.50            = (k10_relat_1 @ X1 @ X0))
% 0.22/0.50          | ~ (v1_relat_1 @ X1)
% 0.22/0.50          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['22', '23'])).
% 0.22/0.50  thf('25', plain, (![X19 : $i]: (v1_relat_1 @ (k6_partfun1 @ X19))),
% 0.22/0.50      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 0.22/0.50            = (k10_relat_1 @ X1 @ X0))
% 0.22/0.50          | ~ (v1_relat_1 @ X1))),
% 0.22/0.50      inference('demod', [status(thm)], ['24', '25'])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (((k1_relat_1 @ (k6_partfun1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.22/0.50            = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 0.22/0.50          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['19', '26'])).
% 0.22/0.50  thf('28', plain, (![X17 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 0.22/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.22/0.50  thf('29', plain, (![X19 : $i]: (v1_relat_1 @ (k6_partfun1 @ X19))),
% 0.22/0.50      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((k3_xboole_0 @ X1 @ X0) = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.22/0.50      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (r1_tarski @ X1 @ X0)
% 0.22/0.50          | ((k9_relat_1 @ (k6_partfun1 @ X0) @ (k3_xboole_0 @ X1 @ X0)) = (X1)))),
% 0.22/0.50      inference('demod', [status(thm)], ['14', '30'])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      (((k9_relat_1 @ (k6_partfun1 @ sk_A) @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.22/0.50         = (sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '31'])).
% 0.22/0.50  thf('33', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.22/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.50  thf(t17_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.22/0.50  thf('34', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.22/0.50      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.22/0.50  thf(t1_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.22/0.50       ( r1_tarski @ A @ C ) ))).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.50         (~ (r1_tarski @ X2 @ X3)
% 0.22/0.50          | ~ (r1_tarski @ X3 @ X4)
% 0.22/0.50          | (r1_tarski @ X2 @ X4))),
% 0.22/0.50      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.22/0.50  thf('36', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.50  thf('37', plain,
% 0.22/0.50      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)),
% 0.22/0.50      inference('sup-', [status(thm)], ['33', '36'])).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      (![X12 : $i, X14 : $i]:
% 0.22/0.50         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.22/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.50  thf('39', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.50  thf(t162_funct_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.50       ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ))).
% 0.22/0.50  thf('40', plain,
% 0.22/0.50      (![X23 : $i, X24 : $i]:
% 0.22/0.50         (((k9_relat_1 @ (k6_relat_1 @ X24) @ X23) = (X23))
% 0.22/0.50          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t162_funct_1])).
% 0.22/0.50  thf('41', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.22/0.50  thf('42', plain,
% 0.22/0.50      (![X23 : $i, X24 : $i]:
% 0.22/0.50         (((k9_relat_1 @ (k6_partfun1 @ X24) @ X23) = (X23))
% 0.22/0.50          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.22/0.50      inference('demod', [status(thm)], ['40', '41'])).
% 0.22/0.50  thf('43', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((k9_relat_1 @ (k6_partfun1 @ sk_A) @ (k3_xboole_0 @ sk_B @ X0))
% 0.22/0.50           = (k3_xboole_0 @ sk_B @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['39', '42'])).
% 0.22/0.50  thf('44', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['32', '43'])).
% 0.22/0.50  thf('45', plain,
% 0.22/0.50      (((k8_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ sk_B) != (sk_B))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(dt_k6_partfun1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( m1_subset_1 @
% 0.22/0.50         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.22/0.50       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.22/0.50  thf('46', plain,
% 0.22/0.50      (![X32 : $i]:
% 0.22/0.50         (m1_subset_1 @ (k6_partfun1 @ X32) @ 
% 0.22/0.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.22/0.50  thf(redefinition_k8_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.22/0.50  thf('47', plain,
% 0.22/0.50      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.22/0.50          | ((k8_relset_1 @ X28 @ X29 @ X27 @ X30) = (k10_relat_1 @ X27 @ X30)))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.22/0.50  thf('48', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 0.22/0.50           = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.50  thf('49', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((k3_xboole_0 @ X1 @ X0) = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.22/0.50      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.22/0.50  thf('50', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 0.22/0.50           = (k3_xboole_0 @ X1 @ X0))),
% 0.22/0.50      inference('demod', [status(thm)], ['48', '49'])).
% 0.22/0.50  thf('51', plain, (((k3_xboole_0 @ sk_B @ sk_A) != (sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['45', '50'])).
% 0.22/0.50  thf('52', plain, ($false),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['44', '51'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
