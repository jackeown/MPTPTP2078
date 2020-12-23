%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BzBaRwsqUo

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 650 expanded)
%              Number of leaves         :   35 ( 206 expanded)
%              Depth                    :   20
%              Number of atoms          : 1424 (8896 expanded)
%              Number of equality atoms :   97 ( 507 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k6_relset_1_type,type,(
    k6_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k5_relset_1_type,type,(
    k5_relset_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t39_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) )
          = ( k2_relset_1 @ B @ A @ C ) )
        & ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) )
          = ( k1_relset_1 @ B @ A @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
       => ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) )
            = ( k2_relset_1 @ B @ A @ C ) )
          & ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) )
            = ( k1_relset_1 @ B @ A @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_relset_1])).

thf('0',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k7_relset_1 @ X26 @ X27 @ X25 @ X28 )
        = ( k9_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('6',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( ( k7_relset_1 @ X41 @ X42 @ X43 @ X41 )
        = ( k2_relset_1 @ X41 @ X42 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('7',plain,
    ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B )
    = ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('10',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('13',plain,
    ( ( k9_relat_1 @ sk_C @ sk_B )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('15',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k8_relset_1 @ X30 @ X31 @ X29 @ X32 )
        = ( k10_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X9 ) @ X10 )
      | ( ( k7_relat_1 @ X9 @ X10 )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t33_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( m1_subset_1 @ ( k5_relset_1 @ A @ C @ D @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('24',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( m1_subset_1 @ ( k5_relset_1 @ X33 @ X34 @ X35 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[t33_relset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k5_relset_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k5_relset_1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('27',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( ( k5_relset_1 @ X18 @ X19 @ X17 @ X20 )
        = ( k7_relat_1 @ X17 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_relset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k7_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_relset_1 @ X0 @ sk_A @ ( k7_relat_1 @ sk_C @ X0 ) )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_A @ sk_C )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['22','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('34',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('35',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('37',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('39',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('40',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('43',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('45',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['32','43','44'])).

thf('46',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('47',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ( ( k8_relat_1 @ X8 @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k8_relat_1 @ ( k2_relat_1 @ sk_C ) @ ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
      = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k5_relset_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('51',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) )
      | ( v1_relat_1 @ ( k5_relset_1 @ sk_B @ sk_A @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k5_relset_1 @ sk_B @ sk_A @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k7_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('56',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k8_relat_1 @ ( k2_relat_1 @ sk_C ) @ ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['49','56'])).

thf('58',plain,
    ( ( ( k8_relat_1 @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['21','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('60',plain,
    ( ( k8_relat_1 @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k8_relat_1 @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['20','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('63',plain,
    ( ( k8_relat_1 @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( m1_subset_1 @ ( k6_relset_1 @ C @ A @ B @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('65',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( m1_subset_1 @ ( k6_relset_1 @ X37 @ X38 @ X39 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X39 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[t35_relset_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k6_relset_1 @ sk_B @ sk_A @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k6_relset_1 @ A @ B @ C @ D )
        = ( k8_relat_1 @ C @ D ) ) ) )).

thf('68',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( ( k6_relset_1 @ X23 @ X24 @ X21 @ X22 )
        = ( k8_relat_1 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_relset_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k6_relset_1 @ sk_B @ sk_A @ X0 @ sk_C )
      = ( k8_relat_1 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['63','70'])).

thf('72',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( ( k8_relset_1 @ X41 @ X42 @ X43 @ X42 )
        = ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('73',plain,
    ( ( k8_relset_1 @ sk_B @ ( k2_relat_1 @ sk_C ) @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relset_1 @ sk_B @ ( k2_relat_1 @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['63','70'])).

thf('75',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k8_relset_1 @ X30 @ X31 @ X29 @ X32 )
        = ( k10_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ ( k2_relat_1 @ sk_C ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['63','70'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('78',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('79',plain,
    ( ( k1_relset_1 @ sk_B @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['73','76','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('83',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['1','4','13','16','80','83'])).

thf('85',plain,
    ( $false
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( ( k8_relset_1 @ X41 @ X42 @ X43 @ X42 )
        = ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('88',plain,
    ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A )
    = ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('90',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('91',plain,
    ( ( k10_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('94',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('95',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('97',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['92','97'])).

thf('99',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['91','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('101',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( ( k7_relset_1 @ X41 @ X42 @ X43 @ X41 )
        = ( k2_relset_1 @ X41 @ X42 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('102',plain,
    ( ( k7_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_A @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('104',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k7_relset_1 @ X26 @ X27 @ X25 @ X28 )
        = ( k9_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('107',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','105','106'])).

thf('108',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['99','107'])).

thf('109',plain,
    ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
    = ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('111',plain,(
    ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
 != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['109','110'])).

thf('112',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['85','111'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BzBaRwsqUo
% 0.13/0.36  % Computer   : n008.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 12:05:30 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 110 iterations in 0.052s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.50  thf(k6_relset_1_type, type, k6_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.22/0.50  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.50  thf(k5_relset_1_type, type, k5_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.50  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.50  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.50  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.22/0.50  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.22/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.50  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.50  thf(t39_relset_1, conjecture,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.22/0.50       ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.22/0.50           ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.22/0.50         ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.22/0.50           ( k1_relset_1 @ B @ A @ C ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.50        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.22/0.50          ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.22/0.50              ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.22/0.50            ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.22/0.50              ( k1_relset_1 @ B @ A @ C ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t39_relset_1])).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.50          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.22/0.50          != (k2_relset_1 @ sk_B @ sk_A @ sk_C))
% 0.22/0.50        | ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.50            (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.22/0.50            != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.50          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.22/0.50          != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.22/0.50         <= (~
% 0.22/0.50             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.50                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.22/0.50                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(redefinition_k7_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.22/0.50          | ((k7_relset_1 @ X26 @ X27 @ X25 @ X28) = (k9_relat_1 @ X25 @ X28)))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t38_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.22/0.50         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.22/0.50         (((k7_relset_1 @ X41 @ X42 @ X43 @ X41)
% 0.22/0.50            = (k2_relset_1 @ X41 @ X42 @ X43))
% 0.22/0.50          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 0.22/0.50      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B)
% 0.22/0.50         = (k2_relset_1 @ sk_B @ sk_A @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(redefinition_k2_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.50         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.22/0.50          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k2_relat_1 @ sk_C))),
% 0.22/0.50      inference('demod', [status(thm)], ['7', '10'])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.50  thf('13', plain, (((k9_relat_1 @ sk_C @ sk_B) = (k2_relat_1 @ sk_C))),
% 0.22/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(redefinition_k8_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.22/0.50          | ((k8_relset_1 @ X30 @ X31 @ X29 @ X32) = (k10_relat_1 @ X29 @ X32)))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.50  thf(d10_xboole_0, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.50  thf('18', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.22/0.50  thf(t97_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ B ) =>
% 0.22/0.50       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.22/0.50         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (![X9 : $i, X10 : $i]:
% 0.22/0.50         (~ (r1_tarski @ (k1_relat_1 @ X9) @ X10)
% 0.22/0.50          | ((k7_relat_1 @ X9 @ X10) = (X9))
% 0.22/0.50          | ~ (v1_relat_1 @ X9))),
% 0.22/0.50      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t33_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.22/0.50       ( m1_subset_1 @
% 0.22/0.50         ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 0.22/0.50         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.22/0.50         ((m1_subset_1 @ (k5_relset_1 @ X33 @ X34 @ X35 @ X36) @ 
% 0.22/0.50           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X34)))
% 0.22/0.50          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.22/0.50      inference('cnf', [status(esa)], [t33_relset_1])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (m1_subset_1 @ (k5_relset_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.22/0.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(redefinition_k5_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( ( k5_relset_1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.22/0.50          | ((k5_relset_1 @ X18 @ X19 @ X17 @ X20) = (k7_relat_1 @ X17 @ X20)))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k5_relset_1])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((k5_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k7_relat_1 @ sk_C @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.50  thf('29', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (m1_subset_1 @ (k7_relat_1 @ sk_C @ X0) @ 
% 0.22/0.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['25', '28'])).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.50         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.22/0.50          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((k2_relset_1 @ X0 @ sk_A @ (k7_relat_1 @ sk_C @ X0))
% 0.22/0.50           = (k2_relat_1 @ (k7_relat_1 @ sk_C @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      ((((k2_relset_1 @ (k1_relat_1 @ sk_C) @ sk_A @ sk_C)
% 0.22/0.50          = (k2_relat_1 @ (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))
% 0.22/0.50        | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.50      inference('sup+', [status(thm)], ['22', '31'])).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.50  thf('34', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (m1_subset_1 @ (k7_relat_1 @ sk_C @ X0) @ 
% 0.22/0.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['25', '28'])).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      (((m1_subset_1 @ sk_C @ 
% 0.22/0.50         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A)))
% 0.22/0.50        | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.50      inference('sup+', [status(thm)], ['33', '34'])).
% 0.22/0.50  thf('36', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(cc2_relat_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.22/0.50  thf('37', plain,
% 0.22/0.50      (![X3 : $i, X4 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.22/0.50          | (v1_relat_1 @ X3)
% 0.22/0.50          | ~ (v1_relat_1 @ X4))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.50  thf(fc6_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.50  thf('39', plain,
% 0.22/0.50      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.50  thf('40', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.50      inference('demod', [status(thm)], ['38', '39'])).
% 0.22/0.50  thf('41', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ 
% 0.22/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['35', '40'])).
% 0.22/0.50  thf('42', plain,
% 0.22/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.50         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.22/0.50          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.22/0.50  thf('43', plain,
% 0.22/0.50      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.50  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.50      inference('demod', [status(thm)], ['38', '39'])).
% 0.22/0.50  thf('45', plain,
% 0.22/0.50      (((k2_relat_1 @ sk_C)
% 0.22/0.50         = (k2_relat_1 @ (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))),
% 0.22/0.50      inference('demod', [status(thm)], ['32', '43', '44'])).
% 0.22/0.50  thf('46', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.22/0.50  thf(t125_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ B ) =>
% 0.22/0.50       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.22/0.50         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.22/0.50  thf('47', plain,
% 0.22/0.50      (![X7 : $i, X8 : $i]:
% 0.22/0.50         (~ (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 0.22/0.50          | ((k8_relat_1 @ X8 @ X7) = (X7))
% 0.22/0.50          | ~ (v1_relat_1 @ X7))),
% 0.22/0.50      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.22/0.50  thf('48', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X0) | ((k8_relat_1 @ (k2_relat_1 @ X0) @ X0) = (X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.50  thf('49', plain,
% 0.22/0.50      ((((k8_relat_1 @ (k2_relat_1 @ sk_C) @ 
% 0.22/0.50          (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 0.22/0.50          = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 0.22/0.50        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))),
% 0.22/0.50      inference('sup+', [status(thm)], ['45', '48'])).
% 0.22/0.50  thf('50', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (m1_subset_1 @ (k5_relset_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.22/0.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.50  thf('51', plain,
% 0.22/0.50      (![X3 : $i, X4 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.22/0.50          | (v1_relat_1 @ X3)
% 0.22/0.50          | ~ (v1_relat_1 @ X4))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.50  thf('52', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ sk_A))
% 0.22/0.50          | (v1_relat_1 @ (k5_relset_1 @ sk_B @ sk_A @ sk_C @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['50', '51'])).
% 0.22/0.50  thf('53', plain,
% 0.22/0.50      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.50  thf('54', plain,
% 0.22/0.50      (![X0 : $i]: (v1_relat_1 @ (k5_relset_1 @ sk_B @ sk_A @ sk_C @ X0))),
% 0.22/0.50      inference('demod', [status(thm)], ['52', '53'])).
% 0.22/0.50  thf('55', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((k5_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k7_relat_1 @ sk_C @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.50  thf('56', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_C @ X0))),
% 0.22/0.50      inference('demod', [status(thm)], ['54', '55'])).
% 0.22/0.50  thf('57', plain,
% 0.22/0.50      (((k8_relat_1 @ (k2_relat_1 @ sk_C) @ 
% 0.22/0.50         (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 0.22/0.50         = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.22/0.50      inference('demod', [status(thm)], ['49', '56'])).
% 0.22/0.50  thf('58', plain,
% 0.22/0.50      ((((k8_relat_1 @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.22/0.50          = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 0.22/0.50        | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.50      inference('sup+', [status(thm)], ['21', '57'])).
% 0.22/0.50  thf('59', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.50      inference('demod', [status(thm)], ['38', '39'])).
% 0.22/0.50  thf('60', plain,
% 0.22/0.50      (((k8_relat_1 @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.22/0.50         = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.22/0.50      inference('demod', [status(thm)], ['58', '59'])).
% 0.22/0.50  thf('61', plain,
% 0.22/0.50      ((((k8_relat_1 @ (k2_relat_1 @ sk_C) @ sk_C) = (sk_C))
% 0.22/0.50        | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.50      inference('sup+', [status(thm)], ['20', '60'])).
% 0.22/0.50  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.50      inference('demod', [status(thm)], ['38', '39'])).
% 0.22/0.50  thf('63', plain, (((k8_relat_1 @ (k2_relat_1 @ sk_C) @ sk_C) = (sk_C))),
% 0.22/0.50      inference('demod', [status(thm)], ['61', '62'])).
% 0.22/0.50  thf('64', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t35_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.22/0.50       ( m1_subset_1 @
% 0.22/0.50         ( k6_relset_1 @ C @ A @ B @ D ) @ 
% 0.22/0.50         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 0.22/0.50  thf('65', plain,
% 0.22/0.50      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.22/0.50         ((m1_subset_1 @ (k6_relset_1 @ X37 @ X38 @ X39 @ X40) @ 
% 0.22/0.50           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X39)))
% 0.22/0.50          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.22/0.50      inference('cnf', [status(esa)], [t35_relset_1])).
% 0.22/0.50  thf('66', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (m1_subset_1 @ (k6_relset_1 @ sk_B @ sk_A @ X0 @ sk_C) @ 
% 0.22/0.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['64', '65'])).
% 0.22/0.50  thf('67', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(redefinition_k6_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( ( k6_relset_1 @ A @ B @ C @ D ) = ( k8_relat_1 @ C @ D ) ) ))).
% 0.22/0.50  thf('68', plain,
% 0.22/0.50      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.22/0.50         (((k6_relset_1 @ X23 @ X24 @ X21 @ X22) = (k8_relat_1 @ X21 @ X22))
% 0.22/0.50          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k6_relset_1])).
% 0.22/0.50  thf('69', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((k6_relset_1 @ sk_B @ sk_A @ X0 @ sk_C) = (k8_relat_1 @ X0 @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['67', '68'])).
% 0.22/0.50  thf('70', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_C) @ 
% 0.22/0.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['66', '69'])).
% 0.22/0.50  thf('71', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ 
% 0.22/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_C))))),
% 0.22/0.50      inference('sup+', [status(thm)], ['63', '70'])).
% 0.22/0.50  thf('72', plain,
% 0.22/0.50      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.22/0.50         (((k8_relset_1 @ X41 @ X42 @ X43 @ X42)
% 0.22/0.50            = (k1_relset_1 @ X41 @ X42 @ X43))
% 0.22/0.50          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 0.22/0.50      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.22/0.50  thf('73', plain,
% 0.22/0.50      (((k8_relset_1 @ sk_B @ (k2_relat_1 @ sk_C) @ sk_C @ (k2_relat_1 @ sk_C))
% 0.22/0.50         = (k1_relset_1 @ sk_B @ (k2_relat_1 @ sk_C) @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['71', '72'])).
% 0.22/0.50  thf('74', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ 
% 0.22/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_C))))),
% 0.22/0.50      inference('sup+', [status(thm)], ['63', '70'])).
% 0.22/0.50  thf('75', plain,
% 0.22/0.50      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.22/0.50          | ((k8_relset_1 @ X30 @ X31 @ X29 @ X32) = (k10_relat_1 @ X29 @ X32)))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.22/0.50  thf('76', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((k8_relset_1 @ sk_B @ (k2_relat_1 @ sk_C) @ sk_C @ X0)
% 0.22/0.50           = (k10_relat_1 @ sk_C @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['74', '75'])).
% 0.22/0.50  thf('77', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ 
% 0.22/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_C))))),
% 0.22/0.50      inference('sup+', [status(thm)], ['63', '70'])).
% 0.22/0.50  thf(redefinition_k1_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.22/0.50  thf('78', plain,
% 0.22/0.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.50         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 0.22/0.50          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.22/0.50  thf('79', plain,
% 0.22/0.50      (((k1_relset_1 @ sk_B @ (k2_relat_1 @ sk_C) @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['77', '78'])).
% 0.22/0.50  thf('80', plain,
% 0.22/0.50      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.22/0.50      inference('demod', [status(thm)], ['73', '76', '79'])).
% 0.22/0.50  thf('81', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('82', plain,
% 0.22/0.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.50         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 0.22/0.50          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.22/0.50  thf('83', plain,
% 0.22/0.50      (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['81', '82'])).
% 0.22/0.50  thf('84', plain,
% 0.22/0.50      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 0.22/0.50         <= (~
% 0.22/0.50             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.50                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.22/0.50                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.50      inference('demod', [status(thm)], ['1', '4', '13', '16', '80', '83'])).
% 0.22/0.50  thf('85', plain,
% 0.22/0.50      (($false)
% 0.22/0.50         <= (~
% 0.22/0.50             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.50                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.22/0.50                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.50      inference('simplify', [status(thm)], ['84'])).
% 0.22/0.50  thf('86', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('87', plain,
% 0.22/0.50      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.22/0.50         (((k8_relset_1 @ X41 @ X42 @ X43 @ X42)
% 0.22/0.50            = (k1_relset_1 @ X41 @ X42 @ X43))
% 0.22/0.50          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 0.22/0.50      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.22/0.50  thf('88', plain,
% 0.22/0.50      (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 0.22/0.50         = (k1_relset_1 @ sk_B @ sk_A @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['86', '87'])).
% 0.22/0.50  thf('89', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.50  thf('90', plain,
% 0.22/0.50      (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['81', '82'])).
% 0.22/0.50  thf('91', plain, (((k10_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.22/0.50      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.22/0.50  thf('92', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.50  thf('93', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.50  thf('94', plain,
% 0.22/0.50      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.50          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.22/0.50          != (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.22/0.50         <= (~
% 0.22/0.50             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.50                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.22/0.50                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('95', plain,
% 0.22/0.50      ((((k9_relat_1 @ sk_C @ (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.22/0.50          != (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.22/0.50         <= (~
% 0.22/0.50             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.50                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.22/0.50                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['93', '94'])).
% 0.22/0.50  thf('96', plain,
% 0.22/0.50      (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.50  thf('97', plain,
% 0.22/0.50      ((((k9_relat_1 @ sk_C @ (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.22/0.50          != (k2_relat_1 @ sk_C)))
% 0.22/0.50         <= (~
% 0.22/0.50             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.50                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.22/0.50                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.50      inference('demod', [status(thm)], ['95', '96'])).
% 0.22/0.50  thf('98', plain,
% 0.22/0.50      ((((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A))
% 0.22/0.50          != (k2_relat_1 @ sk_C)))
% 0.22/0.50         <= (~
% 0.22/0.50             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.50                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.22/0.50                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['92', '97'])).
% 0.22/0.50  thf('99', plain,
% 0.22/0.50      ((((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.22/0.50         <= (~
% 0.22/0.50             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.50                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.22/0.50                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['91', '98'])).
% 0.22/0.50  thf('100', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ 
% 0.22/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['35', '40'])).
% 0.22/0.50  thf('101', plain,
% 0.22/0.50      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.22/0.50         (((k7_relset_1 @ X41 @ X42 @ X43 @ X41)
% 0.22/0.50            = (k2_relset_1 @ X41 @ X42 @ X43))
% 0.22/0.50          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 0.22/0.50      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.22/0.50  thf('102', plain,
% 0.22/0.50      (((k7_relset_1 @ (k1_relat_1 @ sk_C) @ sk_A @ sk_C @ (k1_relat_1 @ sk_C))
% 0.22/0.50         = (k2_relset_1 @ (k1_relat_1 @ sk_C) @ sk_A @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['100', '101'])).
% 0.22/0.50  thf('103', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ 
% 0.22/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['35', '40'])).
% 0.22/0.50  thf('104', plain,
% 0.22/0.50      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.22/0.50          | ((k7_relset_1 @ X26 @ X27 @ X25 @ X28) = (k9_relat_1 @ X25 @ X28)))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.22/0.50  thf('105', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((k7_relset_1 @ (k1_relat_1 @ sk_C) @ sk_A @ sk_C @ X0)
% 0.22/0.50           = (k9_relat_1 @ sk_C @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['103', '104'])).
% 0.22/0.50  thf('106', plain,
% 0.22/0.50      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.50  thf('107', plain,
% 0.22/0.50      (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.22/0.50      inference('demod', [status(thm)], ['102', '105', '106'])).
% 0.22/0.50  thf('108', plain,
% 0.22/0.50      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.22/0.50         <= (~
% 0.22/0.50             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.50                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.22/0.50                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.50      inference('demod', [status(thm)], ['99', '107'])).
% 0.22/0.50  thf('109', plain,
% 0.22/0.50      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.50          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.22/0.50          = (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['108'])).
% 0.22/0.50  thf('110', plain,
% 0.22/0.50      (~
% 0.22/0.50       (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.50          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.22/0.50          = (k1_relset_1 @ sk_B @ sk_A @ sk_C))) | 
% 0.22/0.50       ~
% 0.22/0.50       (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.50          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.22/0.50          = (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('111', plain,
% 0.22/0.50      (~
% 0.22/0.50       (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.50          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.22/0.50          = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['109', '110'])).
% 0.22/0.50  thf('112', plain, ($false),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['85', '111'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
