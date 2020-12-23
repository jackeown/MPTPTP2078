%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qKFMZndtQM

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 397 expanded)
%              Number of leaves         :   34 ( 132 expanded)
%              Depth                    :   16
%              Number of atoms          :  912 (4757 expanded)
%              Number of equality atoms :   74 ( 312 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t38_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( ( ( k7_relset_1 @ A @ B @ C @ A )
            = ( k2_relset_1 @ A @ B @ C ) )
          & ( ( k8_relset_1 @ A @ B @ C @ B )
            = ( k1_relset_1 @ A @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_relset_1])).

thf('0',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('4',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('7',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k7_relset_1 @ X32 @ X33 @ X31 @ X34 )
        = ( k9_relat_1 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ( ( k9_relat_1 @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X19 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('13',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('15',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ( ( k7_relat_1 @ X14 @ X15 )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k7_relat_1 @ sk_C @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k7_relat_1 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['19','22'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('25',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('27',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('30',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['10','27','30'])).

thf('32',plain,
    ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
 != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['32','33'])).

thf('35',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['5','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('37',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( ( k8_relset_1 @ X36 @ X37 @ X35 @ X38 )
        = ( k10_relat_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('40',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X22 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('41',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('43',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('47',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('48',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ( ( k8_relat_1 @ X8 @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 )
      | ( ( k8_relat_1 @ X0 @ ( k7_relat_1 @ sk_C @ sk_A ) )
        = ( k7_relat_1 @ sk_C @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,
    ( ( k7_relat_1 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['19','22'])).

thf('52',plain,
    ( ( k7_relat_1 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['19','22'])).

thf('53',plain,
    ( ( k7_relat_1 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['19','22'])).

thf('54',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('55',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 )
      | ( ( k8_relat_1 @ X0 @ sk_C )
        = sk_C ) ) ),
    inference(demod,[status(thm)],['50','51','52','53','54','55'])).

thf('57',plain,
    ( ( k8_relat_1 @ sk_B @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['45','56'])).

thf(t119_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('58',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X6 @ X5 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X5 ) @ X6 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('59',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k10_relat_1 @ X11 @ X12 )
        = ( k10_relat_1 @ X11 @ ( k3_xboole_0 @ ( k2_relat_1 @ X11 ) @ X12 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X0 @ X1 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ X1 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['57','61'])).

thf('63',plain,
    ( ( k7_relat_1 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['19','22'])).

thf('64',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('65',plain,(
    ! [X13: $i] :
      ( ( ( k10_relat_1 @ X13 @ ( k2_relat_1 @ X13 ) )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('69',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('70',plain,
    ( ( k7_relat_1 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['19','22'])).

thf('71',plain,
    ( ( k7_relat_1 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['19','22'])).

thf('72',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68','69','70','71'])).

thf('73',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('74',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('76',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['62','74','75'])).

thf('77',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['35','38','76'])).

thf('78',plain,(
    $false ),
    inference(simplify,[status(thm)],['77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qKFMZndtQM
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:37:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 80 iterations in 0.058s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.51  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.51  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.20/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(t38_relset_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.20/0.51         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.51        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51          ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.20/0.51            ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t38_relset_1])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.51          != (k2_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.51        | ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.20/0.51            != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.20/0.51          != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.51         <= (~
% 0.20/0.51             (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.20/0.51                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.51         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 0.20/0.51          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.51  thf('4', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) != (k1_relat_1 @ sk_C)))
% 0.20/0.51         <= (~
% 0.20/0.51             (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.20/0.51                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.51      inference('demod', [status(thm)], ['1', '4'])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(redefinition_k7_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.20/0.51          | ((k7_relset_1 @ X32 @ X33 @ X31 @ X34) = (k9_relat_1 @ X31 @ X34)))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.51          != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.51         <= (~
% 0.20/0.51             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.51                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      ((((k9_relat_1 @ sk_C @ sk_A) != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.51         <= (~
% 0.20/0.51             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.51                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(dt_k1_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.51         ((m1_subset_1 @ (k1_relset_1 @ X19 @ X20 @ X21) @ (k1_zfmisc_1 @ X19))
% 0.20/0.51          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      ((m1_subset_1 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      ((m1_subset_1 @ (k1_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.51  thf(t3_subset, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X2 : $i, X3 : $i]:
% 0.20/0.51         ((r1_tarski @ X2 @ X3) | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.51  thf('17', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.51  thf(t97_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ B ) =>
% 0.20/0.51       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.20/0.51         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i]:
% 0.20/0.51         (~ (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 0.20/0.51          | ((k7_relat_1 @ X14 @ X15) = (X14))
% 0.20/0.51          | ~ (v1_relat_1 @ X14))),
% 0.20/0.51      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ sk_C) | ((k7_relat_1 @ sk_C @ sk_A) = (sk_C)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(cc1_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( v1_relat_1 @ C ) ))).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.51         ((v1_relat_1 @ X16)
% 0.20/0.51          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.51  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.51  thf('23', plain, (((k7_relat_1 @ sk_C @ sk_A) = (sk_C))),
% 0.20/0.51      inference('demod', [status(thm)], ['19', '22'])).
% 0.20/0.51  thf(t148_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ B ) =>
% 0.20/0.51       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i]:
% 0.20/0.51         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.20/0.51          | ~ (v1_relat_1 @ X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 0.20/0.51        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.51      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.51  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.51  thf('27', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.51         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 0.20/0.51          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.20/0.51         <= (~
% 0.20/0.51             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.51                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.51      inference('demod', [status(thm)], ['10', '27', '30'])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.51          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (~
% 0.20/0.51       (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.20/0.51          = (k1_relset_1 @ sk_A @ sk_B @ sk_C))) | 
% 0.20/0.51       ~
% 0.20/0.51       (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.51          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      (~
% 0.20/0.51       (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.20/0.51          = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['32', '33'])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) != (k1_relat_1 @ sk_C))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['5', '34'])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(redefinition_k8_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.20/0.51          | ((k8_relset_1 @ X36 @ X37 @ X35 @ X38) = (k10_relat_1 @ X35 @ X38)))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(dt_k2_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.51         ((m1_subset_1 @ (k2_relset_1 @ X22 @ X23 @ X24) @ (k1_zfmisc_1 @ X23))
% 0.20/0.51          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      ((m1_subset_1 @ (k2_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      (![X2 : $i, X3 : $i]:
% 0.20/0.51         ((r1_tarski @ X2 @ X3) | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.51  thf('45', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.20/0.51      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.51  thf('46', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i]:
% 0.20/0.51         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.20/0.51          | ~ (v1_relat_1 @ X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.51  thf(t125_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ B ) =>
% 0.20/0.51       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.20/0.51         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      (![X7 : $i, X8 : $i]:
% 0.20/0.51         (~ (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 0.20/0.51          | ((k8_relat_1 @ X8 @ X7) = (X7))
% 0.20/0.51          | ~ (v1_relat_1 @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.20/0.51          | ~ (v1_relat_1 @ X1)
% 0.20/0.51          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.20/0.51          | ((k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0))
% 0.20/0.51              = (k7_relat_1 @ X1 @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r1_tarski @ (k2_relat_1 @ sk_C) @ X0)
% 0.20/0.51          | ((k8_relat_1 @ X0 @ (k7_relat_1 @ sk_C @ sk_A))
% 0.20/0.51              = (k7_relat_1 @ sk_C @ sk_A))
% 0.20/0.51          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A))
% 0.20/0.51          | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['46', '49'])).
% 0.20/0.51  thf('51', plain, (((k7_relat_1 @ sk_C @ sk_A) = (sk_C))),
% 0.20/0.51      inference('demod', [status(thm)], ['19', '22'])).
% 0.20/0.51  thf('52', plain, (((k7_relat_1 @ sk_C @ sk_A) = (sk_C))),
% 0.20/0.51      inference('demod', [status(thm)], ['19', '22'])).
% 0.20/0.51  thf('53', plain, (((k7_relat_1 @ sk_C @ sk_A) = (sk_C))),
% 0.20/0.51      inference('demod', [status(thm)], ['19', '22'])).
% 0.20/0.51  thf('54', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.51  thf('55', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.51  thf('56', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r1_tarski @ (k2_relat_1 @ sk_C) @ X0)
% 0.20/0.51          | ((k8_relat_1 @ X0 @ sk_C) = (sk_C)))),
% 0.20/0.51      inference('demod', [status(thm)], ['50', '51', '52', '53', '54', '55'])).
% 0.20/0.51  thf('57', plain, (((k8_relat_1 @ sk_B @ sk_C) = (sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['45', '56'])).
% 0.20/0.51  thf(t119_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ B ) =>
% 0.20/0.51       ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) =
% 0.20/0.51         ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.51  thf('58', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i]:
% 0.20/0.51         (((k2_relat_1 @ (k8_relat_1 @ X6 @ X5))
% 0.20/0.51            = (k3_xboole_0 @ (k2_relat_1 @ X5) @ X6))
% 0.20/0.51          | ~ (v1_relat_1 @ X5))),
% 0.20/0.51      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.20/0.51  thf(t168_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ B ) =>
% 0.20/0.51       ( ( k10_relat_1 @ B @ A ) =
% 0.20/0.51         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 0.20/0.51  thf('59', plain,
% 0.20/0.51      (![X11 : $i, X12 : $i]:
% 0.20/0.51         (((k10_relat_1 @ X11 @ X12)
% 0.20/0.51            = (k10_relat_1 @ X11 @ (k3_xboole_0 @ (k2_relat_1 @ X11) @ X12)))
% 0.20/0.51          | ~ (v1_relat_1 @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.20/0.51  thf('60', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((k10_relat_1 @ X0 @ X1)
% 0.20/0.51            = (k10_relat_1 @ X0 @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0))))
% 0.20/0.51          | ~ (v1_relat_1 @ X0)
% 0.20/0.51          | ~ (v1_relat_1 @ X0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['58', '59'])).
% 0.20/0.51  thf('61', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X0)
% 0.20/0.51          | ((k10_relat_1 @ X0 @ X1)
% 0.20/0.51              = (k10_relat_1 @ X0 @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['60'])).
% 0.20/0.51  thf('62', plain,
% 0.20/0.51      ((((k10_relat_1 @ sk_C @ sk_B)
% 0.20/0.51          = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.20/0.51        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.51      inference('sup+', [status(thm)], ['57', '61'])).
% 0.20/0.51  thf('63', plain, (((k7_relat_1 @ sk_C @ sk_A) = (sk_C))),
% 0.20/0.51      inference('demod', [status(thm)], ['19', '22'])).
% 0.20/0.51  thf('64', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i]:
% 0.20/0.51         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.20/0.51          | ~ (v1_relat_1 @ X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.51  thf(t169_relat_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.20/0.51  thf('65', plain,
% 0.20/0.51      (![X13 : $i]:
% 0.20/0.51         (((k10_relat_1 @ X13 @ (k2_relat_1 @ X13)) = (k1_relat_1 @ X13))
% 0.20/0.51          | ~ (v1_relat_1 @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.20/0.51  thf('66', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.20/0.51            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.20/0.51          | ~ (v1_relat_1 @ X1)
% 0.20/0.51          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['64', '65'])).
% 0.20/0.51  thf('67', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.51        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.51        | ((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ 
% 0.20/0.51            (k9_relat_1 @ sk_C @ sk_A))
% 0.20/0.51            = (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['63', '66'])).
% 0.20/0.51  thf('68', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.51  thf('69', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.51  thf('70', plain, (((k7_relat_1 @ sk_C @ sk_A) = (sk_C))),
% 0.20/0.51      inference('demod', [status(thm)], ['19', '22'])).
% 0.20/0.51  thf('71', plain, (((k7_relat_1 @ sk_C @ sk_A) = (sk_C))),
% 0.20/0.51      inference('demod', [status(thm)], ['19', '22'])).
% 0.20/0.51  thf('72', plain,
% 0.20/0.51      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) = (k1_relat_1 @ sk_C))),
% 0.20/0.51      inference('demod', [status(thm)], ['67', '68', '69', '70', '71'])).
% 0.20/0.51  thf('73', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.51  thf('74', plain,
% 0.20/0.51      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.20/0.51      inference('demod', [status(thm)], ['72', '73'])).
% 0.20/0.51  thf('75', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.51  thf('76', plain, (((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))),
% 0.20/0.51      inference('demod', [status(thm)], ['62', '74', '75'])).
% 0.20/0.51  thf('77', plain, (((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))),
% 0.20/0.51      inference('demod', [status(thm)], ['35', '38', '76'])).
% 0.20/0.51  thf('78', plain, ($false), inference('simplify', [status(thm)], ['77'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
