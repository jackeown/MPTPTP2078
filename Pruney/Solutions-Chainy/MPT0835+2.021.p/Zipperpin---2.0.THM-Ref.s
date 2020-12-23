%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QcKAmSdmrU

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:47 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 239 expanded)
%              Number of leaves         :   28 (  81 expanded)
%              Depth                    :   12
%              Number of atoms          : 1054 (3613 expanded)
%              Number of equality atoms :   69 ( 211 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( r1_tarski @ X12 @ ( k10_relat_1 @ X13 @ ( k9_relat_1 @ X13 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

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

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X35 ) @ X36 )
      | ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X18 @ X19 @ X17 @ X20 ) @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_A @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_A @ sk_C @ X0 ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('14',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k8_relset_1 @ X32 @ X33 @ X31 @ X34 )
        = ( k10_relat_1 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ X0 ) )
      | ( ( k1_relat_1 @ sk_C )
        = ( k10_relat_1 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['3','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('21',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('24',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k7_relset_1 @ X40 @ X41 @ X42 @ X40 )
        = ( k2_relset_1 @ X40 @ X41 @ X42 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('25',plain,
    ( ( k7_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_A @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('27',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k7_relset_1 @ X28 @ X29 @ X27 @ X30 )
        = ( k9_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('30',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('31',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['25','28','31'])).

thf('33',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','22','32'])).

thf('34',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k7_relset_1 @ X28 @ X29 @ X27 @ X30 )
        = ( k9_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k7_relset_1 @ X40 @ X41 @ X42 @ X40 )
        = ( k2_relset_1 @ X40 @ X41 @ X42 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('41',plain,
    ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B )
    = ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('45',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k9_relat_1 @ sk_C @ sk_B )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['41','42','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k8_relset_1 @ X32 @ X33 @ X31 @ X34 )
        = ( k10_relat_1 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('51',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('52',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['35','38','46','49','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k8_relset_1 @ X40 @ X41 @ X42 @ X41 )
        = ( k1_relset_1 @ X40 @ X41 @ X42 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('56',plain,
    ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A )
    = ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('58',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('59',plain,
    ( ( k10_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('62',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['34'])).

thf('63',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('65',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf('68',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['25','28','31'])).

thf('69',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
    = ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['34'])).

thf('72',plain,(
    ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
 != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['70','71'])).

thf('73',plain,(
    ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['53','72'])).

thf('74',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['33','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QcKAmSdmrU
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:19:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.59  % Solved by: fo/fo7.sh
% 0.37/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.59  % done 239 iterations in 0.126s
% 0.37/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.59  % SZS output start Refutation
% 0.37/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.59  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.37/0.59  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.37/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.59  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.37/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.37/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.59  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.37/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.59  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.37/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.59  thf(d10_xboole_0, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.59  thf('0', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.37/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.59  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.37/0.59      inference('simplify', [status(thm)], ['0'])).
% 0.37/0.59  thf(t146_funct_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( v1_relat_1 @ B ) =>
% 0.37/0.59       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.37/0.59         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.37/0.59  thf('2', plain,
% 0.37/0.59      (![X12 : $i, X13 : $i]:
% 0.37/0.59         (~ (r1_tarski @ X12 @ (k1_relat_1 @ X13))
% 0.37/0.59          | (r1_tarski @ X12 @ (k10_relat_1 @ X13 @ (k9_relat_1 @ X13 @ X12)))
% 0.37/0.59          | ~ (v1_relat_1 @ X13))),
% 0.37/0.59      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.37/0.59  thf('3', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (~ (v1_relat_1 @ X0)
% 0.37/0.59          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.37/0.59             (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 0.37/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.59  thf('4', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.37/0.59      inference('simplify', [status(thm)], ['0'])).
% 0.37/0.59  thf(t39_relset_1, conjecture,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.37/0.59       ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.37/0.59           ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.37/0.59         ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.37/0.59           ( k1_relset_1 @ B @ A @ C ) ) ) ))).
% 0.37/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.59        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.37/0.59          ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.37/0.59              ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.37/0.59            ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.37/0.59              ( k1_relset_1 @ B @ A @ C ) ) ) ) )),
% 0.37/0.59    inference('cnf.neg', [status(esa)], [t39_relset_1])).
% 0.37/0.59  thf('5', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(t13_relset_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.37/0.59       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.37/0.59         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.37/0.59  thf('6', plain,
% 0.37/0.59      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.37/0.59         (~ (r1_tarski @ (k1_relat_1 @ X35) @ X36)
% 0.37/0.59          | (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.37/0.59          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 0.37/0.59      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.37/0.59  thf('7', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A)))
% 0.37/0.59          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.59  thf('8', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_C @ 
% 0.37/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['4', '7'])).
% 0.37/0.59  thf(dt_k8_relset_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.59       ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.37/0.59  thf('9', plain,
% 0.37/0.59      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.37/0.59         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.37/0.59          | (m1_subset_1 @ (k8_relset_1 @ X18 @ X19 @ X17 @ X20) @ 
% 0.37/0.59             (k1_zfmisc_1 @ X18)))),
% 0.37/0.59      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 0.37/0.59  thf('10', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (m1_subset_1 @ 
% 0.37/0.59          (k8_relset_1 @ (k1_relat_1 @ sk_C) @ sk_A @ sk_C @ X0) @ 
% 0.37/0.59          (k1_zfmisc_1 @ (k1_relat_1 @ sk_C)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.59  thf(t3_subset, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.59  thf('11', plain,
% 0.37/0.59      (![X3 : $i, X4 : $i]:
% 0.37/0.59         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.37/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.59  thf('12', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (r1_tarski @ (k8_relset_1 @ (k1_relat_1 @ sk_C) @ sk_A @ sk_C @ X0) @ 
% 0.37/0.59          (k1_relat_1 @ sk_C))),
% 0.37/0.59      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.59  thf('13', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_C @ 
% 0.37/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['4', '7'])).
% 0.37/0.59  thf(redefinition_k8_relset_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.59       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.37/0.59  thf('14', plain,
% 0.37/0.59      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.37/0.59         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.37/0.59          | ((k8_relset_1 @ X32 @ X33 @ X31 @ X34) = (k10_relat_1 @ X31 @ X34)))),
% 0.37/0.59      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.37/0.59  thf('15', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((k8_relset_1 @ (k1_relat_1 @ sk_C) @ sk_A @ sk_C @ X0)
% 0.37/0.59           = (k10_relat_1 @ sk_C @ X0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.59  thf('16', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (r1_tarski @ (k10_relat_1 @ sk_C @ X0) @ (k1_relat_1 @ sk_C))),
% 0.37/0.59      inference('demod', [status(thm)], ['12', '15'])).
% 0.37/0.59  thf('17', plain,
% 0.37/0.59      (![X0 : $i, X2 : $i]:
% 0.37/0.59         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.37/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.59  thf('18', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (~ (r1_tarski @ (k1_relat_1 @ sk_C) @ (k10_relat_1 @ sk_C @ X0))
% 0.37/0.59          | ((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ X0)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.59  thf('19', plain,
% 0.37/0.59      ((~ (v1_relat_1 @ sk_C)
% 0.37/0.59        | ((k1_relat_1 @ sk_C)
% 0.37/0.59            = (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))))),
% 0.37/0.59      inference('sup-', [status(thm)], ['3', '18'])).
% 0.37/0.59  thf('20', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(cc1_relset_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.59       ( v1_relat_1 @ C ) ))).
% 0.37/0.59  thf('21', plain,
% 0.37/0.59      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.59         ((v1_relat_1 @ X14)
% 0.37/0.59          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.37/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.37/0.59  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.59  thf('23', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_C @ 
% 0.37/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['4', '7'])).
% 0.37/0.59  thf(t38_relset_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.59       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.37/0.59         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.37/0.59  thf('24', plain,
% 0.37/0.59      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.37/0.59         (((k7_relset_1 @ X40 @ X41 @ X42 @ X40)
% 0.37/0.59            = (k2_relset_1 @ X40 @ X41 @ X42))
% 0.37/0.59          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 0.37/0.59      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.37/0.59  thf('25', plain,
% 0.37/0.59      (((k7_relset_1 @ (k1_relat_1 @ sk_C) @ sk_A @ sk_C @ (k1_relat_1 @ sk_C))
% 0.37/0.59         = (k2_relset_1 @ (k1_relat_1 @ sk_C) @ sk_A @ sk_C))),
% 0.37/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.59  thf('26', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_C @ 
% 0.37/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['4', '7'])).
% 0.37/0.59  thf(redefinition_k7_relset_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.59       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.37/0.59  thf('27', plain,
% 0.37/0.59      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.37/0.59         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.37/0.59          | ((k7_relset_1 @ X28 @ X29 @ X27 @ X30) = (k9_relat_1 @ X27 @ X30)))),
% 0.37/0.59      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.37/0.59  thf('28', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((k7_relset_1 @ (k1_relat_1 @ sk_C) @ sk_A @ sk_C @ X0)
% 0.37/0.59           = (k9_relat_1 @ sk_C @ X0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.37/0.59  thf('29', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_C @ 
% 0.37/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['4', '7'])).
% 0.37/0.59  thf(redefinition_k2_relset_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.59       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.37/0.59  thf('30', plain,
% 0.37/0.59      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.37/0.59         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 0.37/0.59          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.37/0.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.37/0.59  thf('31', plain,
% 0.37/0.59      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.37/0.59      inference('sup-', [status(thm)], ['29', '30'])).
% 0.37/0.59  thf('32', plain,
% 0.37/0.59      (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.37/0.59      inference('demod', [status(thm)], ['25', '28', '31'])).
% 0.37/0.59  thf('33', plain,
% 0.37/0.59      (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 0.37/0.59      inference('demod', [status(thm)], ['19', '22', '32'])).
% 0.37/0.59  thf('34', plain,
% 0.37/0.59      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.59          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.37/0.59          != (k2_relset_1 @ sk_B @ sk_A @ sk_C))
% 0.37/0.59        | ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.59            (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.37/0.59            != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('35', plain,
% 0.37/0.59      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.59          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.37/0.59          != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.37/0.59         <= (~
% 0.37/0.59             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.59                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.37/0.59                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.37/0.59      inference('split', [status(esa)], ['34'])).
% 0.37/0.59  thf('36', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('37', plain,
% 0.37/0.59      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.37/0.59         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.37/0.59          | ((k7_relset_1 @ X28 @ X29 @ X27 @ X30) = (k9_relat_1 @ X27 @ X30)))),
% 0.37/0.59      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.37/0.59  thf('38', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.59  thf('39', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('40', plain,
% 0.37/0.59      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.37/0.59         (((k7_relset_1 @ X40 @ X41 @ X42 @ X40)
% 0.37/0.59            = (k2_relset_1 @ X40 @ X41 @ X42))
% 0.37/0.59          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 0.37/0.59      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.37/0.59  thf('41', plain,
% 0.37/0.59      (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B)
% 0.37/0.59         = (k2_relset_1 @ sk_B @ sk_A @ sk_C))),
% 0.37/0.59      inference('sup-', [status(thm)], ['39', '40'])).
% 0.37/0.59  thf('42', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.59  thf('43', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('44', plain,
% 0.37/0.59      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.37/0.59         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 0.37/0.59          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.37/0.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.37/0.59  thf('45', plain,
% 0.37/0.59      (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.37/0.59      inference('sup-', [status(thm)], ['43', '44'])).
% 0.37/0.59  thf('46', plain, (((k9_relat_1 @ sk_C @ sk_B) = (k2_relat_1 @ sk_C))),
% 0.37/0.59      inference('demod', [status(thm)], ['41', '42', '45'])).
% 0.37/0.59  thf('47', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('48', plain,
% 0.37/0.59      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.37/0.59         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.37/0.59          | ((k8_relset_1 @ X32 @ X33 @ X31 @ X34) = (k10_relat_1 @ X31 @ X34)))),
% 0.37/0.59      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.37/0.59  thf('49', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['47', '48'])).
% 0.37/0.59  thf('50', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(redefinition_k1_relset_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.59       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.37/0.59  thf('51', plain,
% 0.37/0.59      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.37/0.59         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 0.37/0.59          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.37/0.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.37/0.59  thf('52', plain,
% 0.37/0.59      (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.37/0.59      inference('sup-', [status(thm)], ['50', '51'])).
% 0.37/0.59  thf('53', plain,
% 0.37/0.59      ((((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.37/0.59         <= (~
% 0.37/0.59             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.59                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.37/0.59                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.37/0.59      inference('demod', [status(thm)], ['35', '38', '46', '49', '52'])).
% 0.37/0.59  thf('54', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('55', plain,
% 0.37/0.59      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.37/0.59         (((k8_relset_1 @ X40 @ X41 @ X42 @ X41)
% 0.37/0.59            = (k1_relset_1 @ X40 @ X41 @ X42))
% 0.37/0.59          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 0.37/0.59      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.37/0.59  thf('56', plain,
% 0.37/0.59      (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 0.37/0.59         = (k1_relset_1 @ sk_B @ sk_A @ sk_C))),
% 0.37/0.59      inference('sup-', [status(thm)], ['54', '55'])).
% 0.37/0.59  thf('57', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['47', '48'])).
% 0.37/0.59  thf('58', plain,
% 0.37/0.59      (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.37/0.59      inference('sup-', [status(thm)], ['50', '51'])).
% 0.37/0.59  thf('59', plain, (((k10_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.37/0.59      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.37/0.59  thf('60', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['47', '48'])).
% 0.37/0.59  thf('61', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.59  thf('62', plain,
% 0.37/0.59      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.59          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.37/0.59          != (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.37/0.59         <= (~
% 0.37/0.59             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.59                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.37/0.59                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.37/0.59      inference('split', [status(esa)], ['34'])).
% 0.37/0.59  thf('63', plain,
% 0.37/0.59      ((((k9_relat_1 @ sk_C @ (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.37/0.59          != (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.37/0.59         <= (~
% 0.37/0.59             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.59                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.37/0.59                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.37/0.59      inference('sup-', [status(thm)], ['61', '62'])).
% 0.37/0.59  thf('64', plain,
% 0.37/0.59      (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.37/0.59      inference('sup-', [status(thm)], ['43', '44'])).
% 0.37/0.59  thf('65', plain,
% 0.37/0.59      ((((k9_relat_1 @ sk_C @ (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.37/0.59          != (k2_relat_1 @ sk_C)))
% 0.37/0.59         <= (~
% 0.37/0.59             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.59                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.37/0.59                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.37/0.59      inference('demod', [status(thm)], ['63', '64'])).
% 0.37/0.59  thf('66', plain,
% 0.37/0.59      ((((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A))
% 0.37/0.59          != (k2_relat_1 @ sk_C)))
% 0.37/0.59         <= (~
% 0.37/0.59             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.59                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.37/0.59                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.37/0.59      inference('sup-', [status(thm)], ['60', '65'])).
% 0.37/0.59  thf('67', plain,
% 0.37/0.59      ((((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.37/0.59         <= (~
% 0.37/0.59             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.59                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.37/0.59                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.37/0.59      inference('sup-', [status(thm)], ['59', '66'])).
% 0.37/0.59  thf('68', plain,
% 0.37/0.59      (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.37/0.59      inference('demod', [status(thm)], ['25', '28', '31'])).
% 0.37/0.59  thf('69', plain,
% 0.37/0.59      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.37/0.59         <= (~
% 0.37/0.59             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.59                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.37/0.59                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.37/0.59      inference('demod', [status(thm)], ['67', '68'])).
% 0.37/0.59  thf('70', plain,
% 0.37/0.59      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.59          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.37/0.59          = (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.37/0.59      inference('simplify', [status(thm)], ['69'])).
% 0.37/0.59  thf('71', plain,
% 0.37/0.59      (~
% 0.37/0.59       (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.59          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.37/0.59          = (k1_relset_1 @ sk_B @ sk_A @ sk_C))) | 
% 0.37/0.59       ~
% 0.37/0.59       (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.59          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.37/0.59          = (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.37/0.59      inference('split', [status(esa)], ['34'])).
% 0.37/0.59  thf('72', plain,
% 0.37/0.59      (~
% 0.37/0.59       (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.59          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.37/0.59          = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.37/0.59      inference('sat_resolution*', [status(thm)], ['70', '71'])).
% 0.37/0.59  thf('73', plain,
% 0.37/0.59      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 0.37/0.59      inference('simpl_trail', [status(thm)], ['53', '72'])).
% 0.37/0.59  thf('74', plain, ($false),
% 0.37/0.59      inference('simplify_reflect-', [status(thm)], ['33', '73'])).
% 0.37/0.59  
% 0.37/0.59  % SZS output end Refutation
% 0.37/0.59  
% 0.37/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
