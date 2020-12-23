%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zIyusJheA7

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 225 expanded)
%              Number of leaves         :   36 (  96 expanded)
%              Depth                    :   10
%              Number of atoms          :  613 (1372 expanded)
%              Number of equality atoms :   56 ( 140 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
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
    ! [X15: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('5',plain,(
    ! [X15: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X15 ) )
      = X15 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('6',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k2_relat_1 @ X21 ) )
      | ( ( k9_relat_1 @ X21 @ ( k10_relat_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
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
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('9',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('10',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X16 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X17: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('12',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('13',plain,(
    ! [X17: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['7','10','13'])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('15',plain,(
    ! [X26: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X26 ) )
      = ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf('16',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('17',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('18',plain,(
    ! [X26: $i] :
      ( ( k2_funct_1 @ ( k6_partfun1 @ X26 ) )
      = ( k6_partfun1 @ X26 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('19',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k10_relat_1 @ X22 @ X23 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X22 ) @ X23 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X16 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('22',plain,(
    ! [X17: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X19: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('24',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('25',plain,(
    ! [X19: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21','22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['14','26'])).

thf('28',plain,
    ( ( k9_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k9_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['2','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21','22','25'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21','22','25'])).

thf(t181_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('31',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) @ X13 )
        = ( k10_relat_1 @ X12 @ ( k10_relat_1 @ X11 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X2 ) @ X1 ) @ X0 )
        = ( k9_relat_1 @ ( k6_partfun1 @ X2 ) @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X16 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X2 ) @ X1 ) @ X0 )
        = ( k9_relat_1 @ ( k6_partfun1 @ X2 ) @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X2 ) @ ( k6_partfun1 @ X1 ) ) @ X0 )
        = ( k9_relat_1 @ ( k6_partfun1 @ X2 ) @ ( k9_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('36',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X25 ) @ ( k6_relat_1 @ X24 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('37',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('38',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('39',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('40',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('41',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X25 ) @ ( k6_partfun1 @ X24 ) )
      = ( k6_partfun1 @ ( k1_setfam_1 @ ( k2_tarski @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['36','37','38','39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21','22','25'])).

thf('43',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X16 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k9_relat_1 @ ( k6_partfun1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) ) @ X0 )
      = ( k9_relat_1 @ ( k6_partfun1 @ X2 ) @ ( k9_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','41','42','43'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('46',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k9_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['28','44','47'])).

thf('49',plain,(
    ( k8_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('50',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('51',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('52',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('53',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k8_relset_1 @ X28 @ X29 @ X27 @ X30 )
        = ( k10_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21','22','25'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ( k9_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(demod,[status(thm)],['49','56'])).

thf('58',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['48','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zIyusJheA7
% 0.13/0.36  % Computer   : n020.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 19:00:37 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.45  % Solved by: fo/fo7.sh
% 0.21/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.45  % done 48 iterations in 0.015s
% 0.21/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.45  % SZS output start Refutation
% 0.21/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.45  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.45  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.21/0.45  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.45  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.45  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.45  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.45  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.45  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.45  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.45  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.45  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.45  thf(t171_funct_2, conjecture,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.45       ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ))).
% 0.21/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.45    (~( ![A:$i,B:$i]:
% 0.21/0.45        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.45          ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ) )),
% 0.21/0.45    inference('cnf.neg', [status(esa)], [t171_funct_2])).
% 0.21/0.45  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(t3_subset, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.45  thf('1', plain,
% 0.21/0.45      (![X8 : $i, X9 : $i]:
% 0.21/0.45         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.21/0.45      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.45  thf('2', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.21/0.45      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.45  thf(t71_relat_1, axiom,
% 0.21/0.45    (![A:$i]:
% 0.21/0.45     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.45       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.45  thf('3', plain, (![X15 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 0.21/0.45      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.45  thf(redefinition_k6_partfun1, axiom,
% 0.21/0.45    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.21/0.45  thf('4', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.21/0.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.45  thf('5', plain, (![X15 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X15)) = (X15))),
% 0.21/0.45      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.45  thf(t147_funct_1, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.45       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.21/0.45         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.21/0.45  thf('6', plain,
% 0.21/0.45      (![X20 : $i, X21 : $i]:
% 0.21/0.45         (~ (r1_tarski @ X20 @ (k2_relat_1 @ X21))
% 0.21/0.45          | ((k9_relat_1 @ X21 @ (k10_relat_1 @ X21 @ X20)) = (X20))
% 0.21/0.45          | ~ (v1_funct_1 @ X21)
% 0.21/0.45          | ~ (v1_relat_1 @ X21))),
% 0.21/0.45      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.21/0.45  thf('7', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]:
% 0.21/0.45         (~ (r1_tarski @ X1 @ X0)
% 0.21/0.45          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.21/0.45          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.21/0.45          | ((k9_relat_1 @ (k6_partfun1 @ X0) @ 
% 0.21/0.45              (k10_relat_1 @ (k6_partfun1 @ X0) @ X1)) = (X1)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.45  thf(fc3_funct_1, axiom,
% 0.21/0.45    (![A:$i]:
% 0.21/0.45     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.45       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.45  thf('8', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.21/0.45      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.45  thf('9', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.21/0.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.45  thf('10', plain, (![X16 : $i]: (v1_relat_1 @ (k6_partfun1 @ X16))),
% 0.21/0.45      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.45  thf('11', plain, (![X17 : $i]: (v1_funct_1 @ (k6_relat_1 @ X17))),
% 0.21/0.45      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.45  thf('12', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.21/0.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.45  thf('13', plain, (![X17 : $i]: (v1_funct_1 @ (k6_partfun1 @ X17))),
% 0.21/0.45      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.45  thf('14', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]:
% 0.21/0.45         (~ (r1_tarski @ X1 @ X0)
% 0.21/0.45          | ((k9_relat_1 @ (k6_partfun1 @ X0) @ 
% 0.21/0.45              (k10_relat_1 @ (k6_partfun1 @ X0) @ X1)) = (X1)))),
% 0.21/0.45      inference('demod', [status(thm)], ['7', '10', '13'])).
% 0.21/0.45  thf(t67_funct_1, axiom,
% 0.21/0.45    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.21/0.45  thf('15', plain,
% 0.21/0.45      (![X26 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X26)) = (k6_relat_1 @ X26))),
% 0.21/0.45      inference('cnf', [status(esa)], [t67_funct_1])).
% 0.21/0.45  thf('16', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.21/0.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.45  thf('17', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.21/0.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.45  thf('18', plain,
% 0.21/0.45      (![X26 : $i]: ((k2_funct_1 @ (k6_partfun1 @ X26)) = (k6_partfun1 @ X26))),
% 0.21/0.45      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.45  thf(t155_funct_1, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.45       ( ( v2_funct_1 @ B ) =>
% 0.21/0.45         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.21/0.45  thf('19', plain,
% 0.21/0.45      (![X22 : $i, X23 : $i]:
% 0.21/0.45         (~ (v2_funct_1 @ X22)
% 0.21/0.45          | ((k10_relat_1 @ X22 @ X23)
% 0.21/0.45              = (k9_relat_1 @ (k2_funct_1 @ X22) @ X23))
% 0.21/0.45          | ~ (v1_funct_1 @ X22)
% 0.21/0.45          | ~ (v1_relat_1 @ X22))),
% 0.21/0.45      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.21/0.45  thf('20', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]:
% 0.21/0.45         (((k10_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 0.21/0.45            = (k9_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 0.21/0.45          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.21/0.45          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.21/0.45          | ~ (v2_funct_1 @ (k6_partfun1 @ X0)))),
% 0.21/0.45      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.45  thf('21', plain, (![X16 : $i]: (v1_relat_1 @ (k6_partfun1 @ X16))),
% 0.21/0.45      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.45  thf('22', plain, (![X17 : $i]: (v1_funct_1 @ (k6_partfun1 @ X17))),
% 0.21/0.45      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.45  thf(fc4_funct_1, axiom,
% 0.21/0.45    (![A:$i]:
% 0.21/0.45     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.45       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.45  thf('23', plain, (![X19 : $i]: (v2_funct_1 @ (k6_relat_1 @ X19))),
% 0.21/0.45      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.21/0.45  thf('24', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.21/0.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.45  thf('25', plain, (![X19 : $i]: (v2_funct_1 @ (k6_partfun1 @ X19))),
% 0.21/0.45      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.45  thf('26', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]:
% 0.21/0.45         ((k10_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 0.21/0.45           = (k9_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.21/0.45      inference('demod', [status(thm)], ['20', '21', '22', '25'])).
% 0.21/0.45  thf('27', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]:
% 0.21/0.45         (~ (r1_tarski @ X1 @ X0)
% 0.21/0.45          | ((k9_relat_1 @ (k6_partfun1 @ X0) @ 
% 0.21/0.45              (k9_relat_1 @ (k6_partfun1 @ X0) @ X1)) = (X1)))),
% 0.21/0.45      inference('demod', [status(thm)], ['14', '26'])).
% 0.21/0.45  thf('28', plain,
% 0.21/0.45      (((k9_relat_1 @ (k6_partfun1 @ sk_A) @ 
% 0.21/0.45         (k9_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B)) = (sk_B))),
% 0.21/0.45      inference('sup-', [status(thm)], ['2', '27'])).
% 0.21/0.45  thf('29', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]:
% 0.21/0.45         ((k10_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 0.21/0.45           = (k9_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.21/0.45      inference('demod', [status(thm)], ['20', '21', '22', '25'])).
% 0.21/0.45  thf('30', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]:
% 0.21/0.45         ((k10_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 0.21/0.45           = (k9_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.21/0.45      inference('demod', [status(thm)], ['20', '21', '22', '25'])).
% 0.21/0.45  thf(t181_relat_1, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( v1_relat_1 @ B ) =>
% 0.21/0.45       ( ![C:$i]:
% 0.21/0.45         ( ( v1_relat_1 @ C ) =>
% 0.21/0.45           ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.21/0.45             ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.21/0.45  thf('31', plain,
% 0.21/0.45      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.45         (~ (v1_relat_1 @ X11)
% 0.21/0.45          | ((k10_relat_1 @ (k5_relat_1 @ X12 @ X11) @ X13)
% 0.21/0.45              = (k10_relat_1 @ X12 @ (k10_relat_1 @ X11 @ X13)))
% 0.21/0.45          | ~ (v1_relat_1 @ X12))),
% 0.21/0.45      inference('cnf', [status(esa)], [t181_relat_1])).
% 0.21/0.45  thf('32', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.45         (((k10_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X2) @ X1) @ X0)
% 0.21/0.45            = (k9_relat_1 @ (k6_partfun1 @ X2) @ (k10_relat_1 @ X1 @ X0)))
% 0.21/0.45          | ~ (v1_relat_1 @ (k6_partfun1 @ X2))
% 0.21/0.45          | ~ (v1_relat_1 @ X1))),
% 0.21/0.45      inference('sup+', [status(thm)], ['30', '31'])).
% 0.21/0.45  thf('33', plain, (![X16 : $i]: (v1_relat_1 @ (k6_partfun1 @ X16))),
% 0.21/0.45      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.45  thf('34', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.45         (((k10_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X2) @ X1) @ X0)
% 0.21/0.45            = (k9_relat_1 @ (k6_partfun1 @ X2) @ (k10_relat_1 @ X1 @ X0)))
% 0.21/0.45          | ~ (v1_relat_1 @ X1))),
% 0.21/0.45      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.45  thf('35', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.45         (((k10_relat_1 @ 
% 0.21/0.45            (k5_relat_1 @ (k6_partfun1 @ X2) @ (k6_partfun1 @ X1)) @ X0)
% 0.21/0.45            = (k9_relat_1 @ (k6_partfun1 @ X2) @ 
% 0.21/0.45               (k9_relat_1 @ (k6_partfun1 @ X1) @ X0)))
% 0.21/0.45          | ~ (v1_relat_1 @ (k6_partfun1 @ X1)))),
% 0.21/0.45      inference('sup+', [status(thm)], ['29', '34'])).
% 0.21/0.45  thf(t43_funct_1, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.21/0.45       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.45  thf('36', plain,
% 0.21/0.45      (![X24 : $i, X25 : $i]:
% 0.21/0.45         ((k5_relat_1 @ (k6_relat_1 @ X25) @ (k6_relat_1 @ X24))
% 0.21/0.45           = (k6_relat_1 @ (k3_xboole_0 @ X24 @ X25)))),
% 0.21/0.45      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.21/0.45  thf('37', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.21/0.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.45  thf('38', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.21/0.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.45  thf(t12_setfam_1, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.45  thf('39', plain,
% 0.21/0.45      (![X6 : $i, X7 : $i]:
% 0.21/0.45         ((k1_setfam_1 @ (k2_tarski @ X6 @ X7)) = (k3_xboole_0 @ X6 @ X7))),
% 0.21/0.45      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.45  thf('40', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.21/0.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.45  thf('41', plain,
% 0.21/0.45      (![X24 : $i, X25 : $i]:
% 0.21/0.45         ((k5_relat_1 @ (k6_partfun1 @ X25) @ (k6_partfun1 @ X24))
% 0.21/0.45           = (k6_partfun1 @ (k1_setfam_1 @ (k2_tarski @ X24 @ X25))))),
% 0.21/0.45      inference('demod', [status(thm)], ['36', '37', '38', '39', '40'])).
% 0.21/0.45  thf('42', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]:
% 0.21/0.45         ((k10_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 0.21/0.45           = (k9_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.21/0.45      inference('demod', [status(thm)], ['20', '21', '22', '25'])).
% 0.21/0.45  thf('43', plain, (![X16 : $i]: (v1_relat_1 @ (k6_partfun1 @ X16))),
% 0.21/0.45      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.45  thf('44', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.45         ((k9_relat_1 @ 
% 0.21/0.45           (k6_partfun1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X2))) @ X0)
% 0.21/0.45           = (k9_relat_1 @ (k6_partfun1 @ X2) @ 
% 0.21/0.45              (k9_relat_1 @ (k6_partfun1 @ X1) @ X0)))),
% 0.21/0.45      inference('demod', [status(thm)], ['35', '41', '42', '43'])).
% 0.21/0.45  thf(idempotence_k3_xboole_0, axiom,
% 0.21/0.45    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.45  thf('45', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.45      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.21/0.45  thf('46', plain,
% 0.21/0.45      (![X6 : $i, X7 : $i]:
% 0.21/0.45         ((k1_setfam_1 @ (k2_tarski @ X6 @ X7)) = (k3_xboole_0 @ X6 @ X7))),
% 0.21/0.45      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.45  thf('47', plain,
% 0.21/0.45      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.21/0.45      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.45  thf('48', plain, (((k9_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B) = (sk_B))),
% 0.21/0.45      inference('demod', [status(thm)], ['28', '44', '47'])).
% 0.21/0.45  thf('49', plain,
% 0.21/0.45      (((k8_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ sk_B) != (sk_B))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(t29_relset_1, axiom,
% 0.21/0.45    (![A:$i]:
% 0.21/0.45     ( m1_subset_1 @
% 0.21/0.45       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.21/0.45  thf('50', plain,
% 0.21/0.45      (![X31 : $i]:
% 0.21/0.45         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 0.21/0.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 0.21/0.45      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.21/0.45  thf('51', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.21/0.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.45  thf('52', plain,
% 0.21/0.45      (![X31 : $i]:
% 0.21/0.45         (m1_subset_1 @ (k6_partfun1 @ X31) @ 
% 0.21/0.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 0.21/0.45      inference('demod', [status(thm)], ['50', '51'])).
% 0.21/0.45  thf(redefinition_k8_relset_1, axiom,
% 0.21/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.45       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.21/0.45  thf('53', plain,
% 0.21/0.45      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.45         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.21/0.45          | ((k8_relset_1 @ X28 @ X29 @ X27 @ X30) = (k10_relat_1 @ X27 @ X30)))),
% 0.21/0.45      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.45  thf('54', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]:
% 0.21/0.45         ((k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 0.21/0.45           = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.21/0.45      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.45  thf('55', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]:
% 0.21/0.45         ((k10_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 0.21/0.45           = (k9_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.21/0.45      inference('demod', [status(thm)], ['20', '21', '22', '25'])).
% 0.21/0.45  thf('56', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]:
% 0.21/0.45         ((k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 0.21/0.45           = (k9_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.21/0.45      inference('demod', [status(thm)], ['54', '55'])).
% 0.21/0.45  thf('57', plain, (((k9_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B) != (sk_B))),
% 0.21/0.45      inference('demod', [status(thm)], ['49', '56'])).
% 0.21/0.45  thf('58', plain, ($false),
% 0.21/0.45      inference('simplify_reflect-', [status(thm)], ['48', '57'])).
% 0.21/0.45  
% 0.21/0.45  % SZS output end Refutation
% 0.21/0.45  
% 0.21/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
