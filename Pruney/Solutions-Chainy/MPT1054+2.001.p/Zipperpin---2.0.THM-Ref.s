%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WpTtMzlYUG

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 248 expanded)
%              Number of leaves         :   47 ( 106 expanded)
%              Depth                    :   15
%              Number of atoms          :  708 (1513 expanded)
%              Number of equality atoms :   65 ( 158 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ( k8_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('1',plain,(
    ! [X45: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X45 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k8_relset_1 @ X41 @ X42 @ X40 @ X43 )
        = ( k10_relat_1 @ X40 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X39: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X39 ) )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('6',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('7',plain,(
    ! [X39: $i] :
      ( ( k2_funct_1 @ ( k6_partfun1 @ X39 ) )
      = ( k6_partfun1 @ X39 ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('8',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v2_funct_1 @ X35 )
      | ( ( k10_relat_1 @ X35 @ X36 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X35 ) @ X36 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(fc24_relat_1,axiom,(
    ! [A: $i] :
      ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('11',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('12',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X28 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X32: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('14',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('15',plain,(
    ! [X32: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X32 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X34: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('17',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('18',plain,(
    ! [X34: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X34 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['9','12','15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['3','19'])).

thf('21',plain,(
    ( k9_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(demod,[status(thm)],['0','20'])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X38 ) @ ( k6_relat_1 @ X37 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('23',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('24',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('25',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X38 ) @ ( k6_partfun1 @ X37 ) )
      = ( k6_partfun1 @ ( k3_xboole_0 @ X37 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('27',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('28',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('29',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X26 ) )
      = X26 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('30',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X20 @ X19 ) )
        = ( k10_relat_1 @ X20 @ ( k1_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X28 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k6_partfun1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','33'])).

thf('35',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X26 ) )
      = X26 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['9','12','15','18'])).

thf('37',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X28 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,(
    ( k3_xboole_0 @ sk_B @ sk_A )
 != sk_B ),
    inference(demod,[status(thm)],['21','38'])).

thf('40',plain,(
    ! [X29: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X29 ) @ X29 ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('41',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('42',plain,(
    ! [X29: $i] :
      ( v4_relat_1 @ ( k6_partfun1 @ X29 ) @ X29 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('44',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('46',plain,(
    ! [X12: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('47',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['45','46'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('48',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r1_tarski @ X10 @ X8 )
      | ( X9
       != ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('49',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['47','49'])).

thf(t217_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v4_relat_1 @ C @ A ) )
         => ( v4_relat_1 @ C @ B ) ) ) )).

thf('51',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v4_relat_1 @ X23 @ X24 )
      | ( v4_relat_1 @ X23 @ X25 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t217_relat_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ sk_A )
      | ~ ( v4_relat_1 @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    | ( v4_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['42','52'])).

thf('54',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X28 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('55',plain,(
    v4_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['53','54'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('56',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X21
        = ( k7_relat_1 @ X21 @ X22 ) )
      | ~ ( v4_relat_1 @ X21 @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('57',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    | ( ( k6_partfun1 @ sk_B )
      = ( k7_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X28 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('59',plain,
    ( ( k6_partfun1 @ sk_B )
    = ( k7_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('60',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) )
        = ( k9_relat_1 @ X17 @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('61',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_B ) )
      = ( k9_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('63',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('64',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X27 ) )
      = X27 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X28 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('66',plain,
    ( sk_B
    = ( k9_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['61','64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('69',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['66','67','72'])).

thf('74',plain,(
    sk_B != sk_B ),
    inference(demod,[status(thm)],['39','73'])).

thf('75',plain,(
    $false ),
    inference(simplify,[status(thm)],['74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WpTtMzlYUG
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:38:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 126 iterations in 0.051s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.51  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.51  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.51  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.51  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.51  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.51  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.21/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(t171_funct_2, conjecture,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51       ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i]:
% 0.21/0.51        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51          ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t171_funct_2])).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (((k8_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ sk_B) != (sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_k6_partfun1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( m1_subset_1 @
% 0.21/0.51         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.21/0.51       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X45 : $i]:
% 0.21/0.51         (m1_subset_1 @ (k6_partfun1 @ X45) @ 
% 0.21/0.51          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X45)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.21/0.51  thf(redefinition_k8_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.21/0.51          | ((k8_relset_1 @ X41 @ X42 @ X40 @ X43) = (k10_relat_1 @ X40 @ X43)))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 0.21/0.51           = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf(t67_funct_1, axiom,
% 0.21/0.51    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X39 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X39)) = (k6_relat_1 @ X39))),
% 0.21/0.51      inference('cnf', [status(esa)], [t67_funct_1])).
% 0.21/0.51  thf(redefinition_k6_partfun1, axiom,
% 0.21/0.51    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.21/0.51  thf('5', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.51  thf('6', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X39 : $i]: ((k2_funct_1 @ (k6_partfun1 @ X39)) = (k6_partfun1 @ X39))),
% 0.21/0.51      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.21/0.51  thf(t155_funct_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.51       ( ( v2_funct_1 @ B ) =>
% 0.21/0.51         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X35 : $i, X36 : $i]:
% 0.21/0.51         (~ (v2_funct_1 @ X35)
% 0.21/0.51          | ((k10_relat_1 @ X35 @ X36)
% 0.21/0.51              = (k9_relat_1 @ (k2_funct_1 @ X35) @ X36))
% 0.21/0.51          | ~ (v1_funct_1 @ X35)
% 0.21/0.51          | ~ (v1_relat_1 @ X35))),
% 0.21/0.51      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k10_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 0.21/0.51            = (k9_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 0.21/0.51          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.21/0.51          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.21/0.51          | ~ (v2_funct_1 @ (k6_partfun1 @ X0)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf(fc24_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.21/0.51       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.21/0.51       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.51  thf('10', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.51  thf('11', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.51  thf('12', plain, (![X28 : $i]: (v1_relat_1 @ (k6_partfun1 @ X28))),
% 0.21/0.51      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf(fc3_funct_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.51       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.51  thf('13', plain, (![X32 : $i]: (v1_funct_1 @ (k6_relat_1 @ X32))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.51  thf('14', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.51  thf('15', plain, (![X32 : $i]: (v1_funct_1 @ (k6_partfun1 @ X32))),
% 0.21/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf(fc4_funct_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.51       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.51  thf('16', plain, (![X34 : $i]: (v2_funct_1 @ (k6_relat_1 @ X34))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.21/0.51  thf('17', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.51  thf('18', plain, (![X34 : $i]: (v2_funct_1 @ (k6_partfun1 @ X34))),
% 0.21/0.51      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k10_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 0.21/0.51           = (k9_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.21/0.51      inference('demod', [status(thm)], ['9', '12', '15', '18'])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 0.21/0.51           = (k9_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.21/0.51      inference('demod', [status(thm)], ['3', '19'])).
% 0.21/0.51  thf('21', plain, (((k9_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B) != (sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['0', '20'])).
% 0.21/0.51  thf(t43_funct_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.21/0.51       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X37 : $i, X38 : $i]:
% 0.21/0.51         ((k5_relat_1 @ (k6_relat_1 @ X38) @ (k6_relat_1 @ X37))
% 0.21/0.51           = (k6_relat_1 @ (k3_xboole_0 @ X37 @ X38)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.21/0.51  thf('23', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.51  thf('24', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.51  thf('25', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X37 : $i, X38 : $i]:
% 0.21/0.51         ((k5_relat_1 @ (k6_partfun1 @ X38) @ (k6_partfun1 @ X37))
% 0.21/0.51           = (k6_partfun1 @ (k3_xboole_0 @ X37 @ X38)))),
% 0.21/0.51      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 0.21/0.51  thf(t71_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.51       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.51  thf('27', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 0.21/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.51  thf('28', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.51  thf('29', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X26)) = (X26))),
% 0.21/0.51      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.51  thf(t182_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( v1_relat_1 @ B ) =>
% 0.21/0.51           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.21/0.51             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (![X19 : $i, X20 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X19)
% 0.21/0.51          | ((k1_relat_1 @ (k5_relat_1 @ X20 @ X19))
% 0.21/0.51              = (k10_relat_1 @ X20 @ (k1_relat_1 @ X19)))
% 0.21/0.51          | ~ (v1_relat_1 @ X20))),
% 0.21/0.51      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 0.21/0.51            = (k10_relat_1 @ X1 @ X0))
% 0.21/0.51          | ~ (v1_relat_1 @ X1)
% 0.21/0.51          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['29', '30'])).
% 0.21/0.51  thf('32', plain, (![X28 : $i]: (v1_relat_1 @ (k6_partfun1 @ X28))),
% 0.21/0.51      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 0.21/0.51            = (k10_relat_1 @ X1 @ X0))
% 0.21/0.51          | ~ (v1_relat_1 @ X1))),
% 0.21/0.51      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k1_relat_1 @ (k6_partfun1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.21/0.51            = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 0.21/0.51          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['26', '33'])).
% 0.21/0.51  thf('35', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X26)) = (X26))),
% 0.21/0.51      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k10_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 0.21/0.51           = (k9_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.21/0.51      inference('demod', [status(thm)], ['9', '12', '15', '18'])).
% 0.21/0.51  thf('37', plain, (![X28 : $i]: (v1_relat_1 @ (k6_partfun1 @ X28))),
% 0.21/0.51      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k3_xboole_0 @ X1 @ X0) = (k9_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.21/0.51      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 0.21/0.51  thf('39', plain, (((k3_xboole_0 @ sk_B @ sk_A) != (sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['21', '38'])).
% 0.21/0.51  thf('40', plain, (![X29 : $i]: (v4_relat_1 @ (k6_relat_1 @ X29) @ X29)),
% 0.21/0.51      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.51  thf('41', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.51  thf('42', plain, (![X29 : $i]: (v4_relat_1 @ (k6_partfun1 @ X29) @ X29)),
% 0.21/0.51      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.51  thf('43', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t2_subset, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.51       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      (![X15 : $i, X16 : $i]:
% 0.21/0.51         ((r2_hidden @ X15 @ X16)
% 0.21/0.51          | (v1_xboole_0 @ X16)
% 0.21/0.51          | ~ (m1_subset_1 @ X15 @ X16))),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.51        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.51  thf(fc1_subset_1, axiom,
% 0.21/0.51    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.51  thf('46', plain, (![X12 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.51  thf('47', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['45', '46'])).
% 0.21/0.51  thf(d1_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X10 @ X9)
% 0.21/0.51          | (r1_tarski @ X10 @ X8)
% 0.21/0.51          | ((X9) != (k1_zfmisc_1 @ X8)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      (![X8 : $i, X10 : $i]:
% 0.21/0.51         ((r1_tarski @ X10 @ X8) | ~ (r2_hidden @ X10 @ (k1_zfmisc_1 @ X8)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['48'])).
% 0.21/0.51  thf('50', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['47', '49'])).
% 0.21/0.51  thf(t217_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.51       ( ![C:$i]:
% 0.21/0.51         ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ A ) ) =>
% 0.21/0.51           ( v4_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X23)
% 0.21/0.51          | ~ (v4_relat_1 @ X23 @ X24)
% 0.21/0.51          | (v4_relat_1 @ X23 @ X25)
% 0.21/0.51          | ~ (r1_tarski @ X24 @ X25))),
% 0.21/0.51      inference('cnf', [status(esa)], [t217_relat_1])).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v4_relat_1 @ X0 @ sk_A)
% 0.21/0.51          | ~ (v4_relat_1 @ X0 @ sk_B)
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ (k6_partfun1 @ sk_B))
% 0.21/0.51        | (v4_relat_1 @ (k6_partfun1 @ sk_B) @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['42', '52'])).
% 0.21/0.51  thf('54', plain, (![X28 : $i]: (v1_relat_1 @ (k6_partfun1 @ X28))),
% 0.21/0.51      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf('55', plain, ((v4_relat_1 @ (k6_partfun1 @ sk_B) @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.51  thf(t209_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.51       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      (![X21 : $i, X22 : $i]:
% 0.21/0.51         (((X21) = (k7_relat_1 @ X21 @ X22))
% 0.21/0.51          | ~ (v4_relat_1 @ X21 @ X22)
% 0.21/0.51          | ~ (v1_relat_1 @ X21))),
% 0.21/0.51      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ (k6_partfun1 @ sk_B))
% 0.21/0.51        | ((k6_partfun1 @ sk_B) = (k7_relat_1 @ (k6_partfun1 @ sk_B) @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.51  thf('58', plain, (![X28 : $i]: (v1_relat_1 @ (k6_partfun1 @ X28))),
% 0.21/0.51      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      (((k6_partfun1 @ sk_B) = (k7_relat_1 @ (k6_partfun1 @ sk_B) @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['57', '58'])).
% 0.21/0.51  thf(t148_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ B ) =>
% 0.21/0.51       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.51  thf('60', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i]:
% 0.21/0.51         (((k2_relat_1 @ (k7_relat_1 @ X17 @ X18)) = (k9_relat_1 @ X17 @ X18))
% 0.21/0.51          | ~ (v1_relat_1 @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.51  thf('61', plain,
% 0.21/0.51      ((((k2_relat_1 @ (k6_partfun1 @ sk_B))
% 0.21/0.51          = (k9_relat_1 @ (k6_partfun1 @ sk_B) @ sk_A))
% 0.21/0.51        | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['59', '60'])).
% 0.21/0.51  thf('62', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 0.21/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.51  thf('63', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.51  thf('64', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X27)) = (X27))),
% 0.21/0.51      inference('demod', [status(thm)], ['62', '63'])).
% 0.21/0.51  thf('65', plain, (![X28 : $i]: (v1_relat_1 @ (k6_partfun1 @ X28))),
% 0.21/0.51      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf('66', plain, (((sk_B) = (k9_relat_1 @ (k6_partfun1 @ sk_B) @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['61', '64', '65'])).
% 0.21/0.51  thf('67', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k3_xboole_0 @ X1 @ X0) = (k9_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.21/0.51      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 0.21/0.51  thf(commutativity_k2_tarski, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.21/0.51  thf('68', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.51  thf(t12_setfam_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.51  thf('69', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i]:
% 0.21/0.51         ((k1_setfam_1 @ (k2_tarski @ X13 @ X14)) = (k3_xboole_0 @ X13 @ X14))),
% 0.21/0.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.51  thf('70', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('sup+', [status(thm)], ['68', '69'])).
% 0.21/0.51  thf('71', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i]:
% 0.21/0.51         ((k1_setfam_1 @ (k2_tarski @ X13 @ X14)) = (k3_xboole_0 @ X13 @ X14))),
% 0.21/0.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.51  thf('72', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('sup+', [status(thm)], ['70', '71'])).
% 0.21/0.51  thf('73', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['66', '67', '72'])).
% 0.21/0.51  thf('74', plain, (((sk_B) != (sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['39', '73'])).
% 0.21/0.51  thf('75', plain, ($false), inference('simplify', [status(thm)], ['74'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
