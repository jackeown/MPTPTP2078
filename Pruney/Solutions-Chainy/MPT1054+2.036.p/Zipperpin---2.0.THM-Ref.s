%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n7SnCk3oUb

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 149 expanded)
%              Number of leaves         :   30 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :  522 ( 932 expanded)
%              Number of equality atoms :   47 ( 101 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
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
    ! [X10: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X24: $i] :
      ( ( k6_partfun1 @ X24 )
      = ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('5',plain,(
    ! [X10: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X10 ) )
      = X10 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X13 @ ( k2_relat_1 @ X14 ) )
      | ( ( k9_relat_1 @ X14 @ ( k10_relat_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('8',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('9',plain,(
    ! [X24: $i] :
      ( ( k6_partfun1 @ X24 )
      = ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('10',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X6 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('12',plain,(
    ! [X24: $i] :
      ( ( k6_partfun1 @ X24 )
      = ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('13',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X12 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X18 ) @ ( k6_relat_1 @ X17 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('16',plain,(
    ! [X24: $i] :
      ( ( k6_partfun1 @ X24 )
      = ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('17',plain,(
    ! [X24: $i] :
      ( ( k6_partfun1 @ X24 )
      = ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('18',plain,(
    ! [X24: $i] :
      ( ( k6_partfun1 @ X24 )
      = ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('19',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X18 ) @ ( k6_partfun1 @ X17 ) )
      = ( k6_partfun1 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('20',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('21',plain,(
    ! [X24: $i] :
      ( ( k6_partfun1 @ X24 )
      = ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('22',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X9 ) )
      = X9 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X9 ) )
      = X9 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) )
        = ( k10_relat_1 @ X8 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X6 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X6 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['14','31'])).

thf('33',plain,
    ( ( k9_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['2','32'])).

thf('34',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t162_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
        = B ) ) )).

thf('39',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X16 ) @ X15 )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t162_funct_1])).

thf('40',plain,(
    ! [X24: $i] :
      ( ( k6_partfun1 @ X24 )
      = ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('41',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k9_relat_1 @ ( k6_partfun1 @ X16 ) @ X15 )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['33','42'])).

thf('44',plain,(
    ( k8_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('45',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('46',plain,(
    ! [X24: $i] :
      ( ( k6_partfun1 @ X24 )
      = ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('47',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('48',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( ( k8_relset_1 @ X20 @ X21 @ X19 @ X22 )
        = ( k10_relat_1 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ( k3_xboole_0 @ sk_B @ sk_A )
 != sk_B ),
    inference(demod,[status(thm)],['44','51'])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['43','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n7SnCk3oUb
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:16:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 58 iterations in 0.030s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.49  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.21/0.49  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(t171_funct_2, conjecture,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49       ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i]:
% 0.21/0.49        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49          ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t171_funct_2])).
% 0.21/0.49  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t3_subset, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i]:
% 0.21/0.49         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.49  thf('2', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf(t71_relat_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.49       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.49  thf('3', plain, (![X10 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.49  thf(redefinition_k6_partfun1, axiom,
% 0.21/0.49    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.21/0.49  thf('4', plain, (![X24 : $i]: ((k6_partfun1 @ X24) = (k6_relat_1 @ X24))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.49  thf('5', plain, (![X10 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X10)) = (X10))),
% 0.21/0.49      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf(t147_funct_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.49       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.21/0.49         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i]:
% 0.21/0.49         (~ (r1_tarski @ X13 @ (k2_relat_1 @ X14))
% 0.21/0.49          | ((k9_relat_1 @ X14 @ (k10_relat_1 @ X14 @ X13)) = (X13))
% 0.21/0.49          | ~ (v1_funct_1 @ X14)
% 0.21/0.49          | ~ (v1_relat_1 @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r1_tarski @ X1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.21/0.49          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.21/0.49          | ((k9_relat_1 @ (k6_partfun1 @ X0) @ 
% 0.21/0.49              (k10_relat_1 @ (k6_partfun1 @ X0) @ X1)) = (X1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.21/0.49  thf('8', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.49  thf('9', plain, (![X24 : $i]: ((k6_partfun1 @ X24) = (k6_relat_1 @ X24))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.49  thf('10', plain, (![X6 : $i]: (v1_relat_1 @ (k6_partfun1 @ X6))),
% 0.21/0.49      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf(fc3_funct_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.49       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.49  thf('11', plain, (![X12 : $i]: (v1_funct_1 @ (k6_relat_1 @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.49  thf('12', plain, (![X24 : $i]: ((k6_partfun1 @ X24) = (k6_relat_1 @ X24))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.49  thf('13', plain, (![X12 : $i]: (v1_funct_1 @ (k6_partfun1 @ X12))),
% 0.21/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r1_tarski @ X1 @ X0)
% 0.21/0.49          | ((k9_relat_1 @ (k6_partfun1 @ X0) @ 
% 0.21/0.49              (k10_relat_1 @ (k6_partfun1 @ X0) @ X1)) = (X1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['7', '10', '13'])).
% 0.21/0.49  thf(t43_funct_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.21/0.49       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X17 : $i, X18 : $i]:
% 0.21/0.49         ((k5_relat_1 @ (k6_relat_1 @ X18) @ (k6_relat_1 @ X17))
% 0.21/0.49           = (k6_relat_1 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.21/0.49  thf('16', plain, (![X24 : $i]: ((k6_partfun1 @ X24) = (k6_relat_1 @ X24))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.49  thf('17', plain, (![X24 : $i]: ((k6_partfun1 @ X24) = (k6_relat_1 @ X24))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.49  thf('18', plain, (![X24 : $i]: ((k6_partfun1 @ X24) = (k6_relat_1 @ X24))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X17 : $i, X18 : $i]:
% 0.21/0.49         ((k5_relat_1 @ (k6_partfun1 @ X18) @ (k6_partfun1 @ X17))
% 0.21/0.49           = (k6_partfun1 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.21/0.49      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 0.21/0.49  thf('20', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.49  thf('21', plain, (![X24 : $i]: ((k6_partfun1 @ X24) = (k6_relat_1 @ X24))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.49  thf('22', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X9)) = (X9))),
% 0.21/0.49      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((k1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X1) @ (k6_partfun1 @ X0)))
% 0.21/0.49           = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.49      inference('sup+', [status(thm)], ['19', '22'])).
% 0.21/0.49  thf('24', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X9)) = (X9))),
% 0.21/0.49      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf(t182_relat_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( v1_relat_1 @ B ) =>
% 0.21/0.49           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.21/0.49             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X7)
% 0.21/0.49          | ((k1_relat_1 @ (k5_relat_1 @ X8 @ X7))
% 0.21/0.49              = (k10_relat_1 @ X8 @ (k1_relat_1 @ X7)))
% 0.21/0.49          | ~ (v1_relat_1 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 0.21/0.49            = (k10_relat_1 @ X1 @ X0))
% 0.21/0.49          | ~ (v1_relat_1 @ X1)
% 0.21/0.49          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['24', '25'])).
% 0.21/0.49  thf('27', plain, (![X6 : $i]: (v1_relat_1 @ (k6_partfun1 @ X6))),
% 0.21/0.49      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 0.21/0.49            = (k10_relat_1 @ X1 @ X0))
% 0.21/0.49          | ~ (v1_relat_1 @ X1))),
% 0.21/0.49      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (((k3_xboole_0 @ X1 @ X0) = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 0.21/0.49          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['23', '28'])).
% 0.21/0.49  thf('30', plain, (![X6 : $i]: (v1_relat_1 @ (k6_partfun1 @ X6))),
% 0.21/0.49      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((k3_xboole_0 @ X1 @ X0) = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.21/0.49      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r1_tarski @ X1 @ X0)
% 0.21/0.49          | ((k9_relat_1 @ (k6_partfun1 @ X0) @ (k3_xboole_0 @ X1 @ X0)) = (X1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['14', '31'])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (((k9_relat_1 @ (k6_partfun1 @ sk_A) @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.21/0.49         = (sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '32'])).
% 0.21/0.49  thf('34', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf(t108_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k3_xboole_0 @ X0 @ X2) @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [t108_xboole_1])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)),
% 0.21/0.49      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      (![X3 : $i, X5 : $i]:
% 0.21/0.49         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.49  thf(t162_funct_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49       ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ))).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i]:
% 0.21/0.49         (((k9_relat_1 @ (k6_relat_1 @ X16) @ X15) = (X15))
% 0.21/0.49          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t162_funct_1])).
% 0.21/0.49  thf('40', plain, (![X24 : $i]: ((k6_partfun1 @ X24) = (k6_relat_1 @ X24))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i]:
% 0.21/0.49         (((k9_relat_1 @ (k6_partfun1 @ X16) @ X15) = (X15))
% 0.21/0.49          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.21/0.49      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((k9_relat_1 @ (k6_partfun1 @ sk_A) @ (k3_xboole_0 @ sk_B @ X0))
% 0.21/0.49           = (k3_xboole_0 @ sk_B @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['38', '41'])).
% 0.21/0.49  thf('43', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['33', '42'])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      (((k8_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ sk_B) != (sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t29_relset_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( m1_subset_1 @
% 0.21/0.49       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (![X23 : $i]:
% 0.21/0.49         (m1_subset_1 @ (k6_relat_1 @ X23) @ 
% 0.21/0.49          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.21/0.49  thf('46', plain, (![X24 : $i]: ((k6_partfun1 @ X24) = (k6_relat_1 @ X24))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.49  thf('47', plain,
% 0.21/0.49      (![X23 : $i]:
% 0.21/0.49         (m1_subset_1 @ (k6_partfun1 @ X23) @ 
% 0.21/0.49          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 0.21/0.49      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.49  thf(redefinition_k8_relset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.49       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.21/0.49          | ((k8_relset_1 @ X20 @ X21 @ X19 @ X22) = (k10_relat_1 @ X19 @ X22)))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 0.21/0.49           = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.49  thf('50', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((k3_xboole_0 @ X1 @ X0) = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.21/0.49      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.49  thf('51', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 0.21/0.49           = (k3_xboole_0 @ X1 @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.49  thf('52', plain, (((k3_xboole_0 @ sk_B @ sk_A) != (sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['44', '51'])).
% 0.21/0.49  thf('53', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['43', '52'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
