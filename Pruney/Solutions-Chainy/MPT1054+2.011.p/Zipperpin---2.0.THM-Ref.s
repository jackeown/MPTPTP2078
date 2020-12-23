%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aSwMpeeOiL

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 232 expanded)
%              Number of leaves         :   39 (  98 expanded)
%              Depth                    :   12
%              Number of atoms          :  628 (1430 expanded)
%              Number of equality atoms :   58 ( 151 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(fc24_relat_1,axiom,(
    ! [A: $i] :
      ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X17: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    ! [X17: $i] :
      ( v4_relat_1 @ ( k6_partfun1 @ X17 ) @ X17 ) ),
    inference(demod,[status(thm)],['0','1'])).

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

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t217_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v4_relat_1 @ C @ A ) )
         => ( v4_relat_1 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ( v4_relat_1 @ X11 @ X13 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t217_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ sk_A )
      | ~ ( v4_relat_1 @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    | ( v4_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('10',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('11',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X16 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    v4_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['8','11'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9
        = ( k7_relat_1 @ X9 @ X10 ) )
      | ~ ( v4_relat_1 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    | ( ( k6_partfun1 @ sk_B )
      = ( k7_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X16 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('16',plain,
    ( ( k6_partfun1 @ sk_B )
    = ( k7_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) )
        = ( k9_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('18',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_B ) )
      = ( k9_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('19',plain,(
    ! [X15: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('20',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('21',plain,(
    ! [X15: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X15 ) )
      = X15 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X16 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('23',plain,
    ( sk_B
    = ( k9_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['18','21','22'])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X26 ) @ ( k6_relat_1 @ X25 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('25',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('27',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X26 ) @ ( k6_partfun1 @ X25 ) )
      = ( k6_partfun1 @ ( k3_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('29',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('30',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('31',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X14 ) )
      = X14 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) )
        = ( k10_relat_1 @ X8 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X16 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k6_partfun1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','35'])).

thf('37',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X14 ) )
      = X14 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('38',plain,(
    ! [X27: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X27 ) )
      = ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf('39',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('40',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('41',plain,(
    ! [X27: $i] :
      ( ( k2_funct_1 @ ( k6_partfun1 @ X27 ) )
      = ( k6_partfun1 @ X27 ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('42',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k10_relat_1 @ X23 @ X24 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X23 ) @ X24 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X16 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('45',plain,(
    ! [X20: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('46',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('47',plain,(
    ! [X20: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X20 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('48',plain,(
    ! [X22: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('49',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('50',plain,(
    ! [X22: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X22 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['43','44','47','50'])).

thf('52',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X16 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37','51','52'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('55',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['23','53','54'])).

thf('56',plain,(
    ( k8_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('57',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('58',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('59',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('60',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k8_relset_1 @ X29 @ X30 @ X28 @ X31 )
        = ( k10_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['43','44','47','50'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ( k9_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(demod,[status(thm)],['56','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37','51','52'])).

thf('66',plain,(
    ( k3_xboole_0 @ sk_B @ sk_A )
 != sk_B ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['55','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aSwMpeeOiL
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:52:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 58 iterations in 0.026s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.45  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.45  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.45  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.20/0.45  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.45  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.45  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.45  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.45  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.45  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.45  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.45  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.45  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.20/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.45  thf(fc24_relat_1, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.20/0.45       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.20/0.45       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.45  thf('0', plain, (![X17 : $i]: (v4_relat_1 @ (k6_relat_1 @ X17) @ X17)),
% 0.20/0.45      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.20/0.45  thf(redefinition_k6_partfun1, axiom,
% 0.20/0.45    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.20/0.45  thf('1', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.20/0.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.45  thf('2', plain, (![X17 : $i]: (v4_relat_1 @ (k6_partfun1 @ X17) @ X17)),
% 0.20/0.45      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.45  thf(t171_funct_2, conjecture,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.45       ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ))).
% 0.20/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.45    (~( ![A:$i,B:$i]:
% 0.20/0.45        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.45          ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ) )),
% 0.20/0.45    inference('cnf.neg', [status(esa)], [t171_funct_2])).
% 0.20/0.45  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(t3_subset, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.45  thf('4', plain,
% 0.20/0.45      (![X2 : $i, X3 : $i]:
% 0.20/0.45         ((r1_tarski @ X2 @ X3) | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.20/0.45      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.45  thf('5', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.45      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.45  thf(t217_relat_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( r1_tarski @ A @ B ) =>
% 0.20/0.45       ( ![C:$i]:
% 0.20/0.45         ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ A ) ) =>
% 0.20/0.45           ( v4_relat_1 @ C @ B ) ) ) ))).
% 0.20/0.45  thf('6', plain,
% 0.20/0.45      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.45         (~ (v1_relat_1 @ X11)
% 0.20/0.45          | ~ (v4_relat_1 @ X11 @ X12)
% 0.20/0.45          | (v4_relat_1 @ X11 @ X13)
% 0.20/0.45          | ~ (r1_tarski @ X12 @ X13))),
% 0.20/0.45      inference('cnf', [status(esa)], [t217_relat_1])).
% 0.20/0.45  thf('7', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         ((v4_relat_1 @ X0 @ sk_A)
% 0.20/0.45          | ~ (v4_relat_1 @ X0 @ sk_B)
% 0.20/0.45          | ~ (v1_relat_1 @ X0))),
% 0.20/0.45      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.45  thf('8', plain,
% 0.20/0.45      ((~ (v1_relat_1 @ (k6_partfun1 @ sk_B))
% 0.20/0.45        | (v4_relat_1 @ (k6_partfun1 @ sk_B) @ sk_A))),
% 0.20/0.45      inference('sup-', [status(thm)], ['2', '7'])).
% 0.20/0.45  thf('9', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.20/0.45      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.20/0.45  thf('10', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.20/0.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.45  thf('11', plain, (![X16 : $i]: (v1_relat_1 @ (k6_partfun1 @ X16))),
% 0.20/0.45      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.45  thf('12', plain, ((v4_relat_1 @ (k6_partfun1 @ sk_B) @ sk_A)),
% 0.20/0.45      inference('demod', [status(thm)], ['8', '11'])).
% 0.20/0.45  thf(t209_relat_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.45       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.20/0.45  thf('13', plain,
% 0.20/0.45      (![X9 : $i, X10 : $i]:
% 0.20/0.45         (((X9) = (k7_relat_1 @ X9 @ X10))
% 0.20/0.45          | ~ (v4_relat_1 @ X9 @ X10)
% 0.20/0.45          | ~ (v1_relat_1 @ X9))),
% 0.20/0.45      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.20/0.45  thf('14', plain,
% 0.20/0.45      ((~ (v1_relat_1 @ (k6_partfun1 @ sk_B))
% 0.20/0.45        | ((k6_partfun1 @ sk_B) = (k7_relat_1 @ (k6_partfun1 @ sk_B) @ sk_A)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.45  thf('15', plain, (![X16 : $i]: (v1_relat_1 @ (k6_partfun1 @ X16))),
% 0.20/0.45      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.45  thf('16', plain,
% 0.20/0.45      (((k6_partfun1 @ sk_B) = (k7_relat_1 @ (k6_partfun1 @ sk_B) @ sk_A))),
% 0.20/0.45      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.45  thf(t148_relat_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ B ) =>
% 0.20/0.45       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.45  thf('17', plain,
% 0.20/0.45      (![X5 : $i, X6 : $i]:
% 0.20/0.45         (((k2_relat_1 @ (k7_relat_1 @ X5 @ X6)) = (k9_relat_1 @ X5 @ X6))
% 0.20/0.45          | ~ (v1_relat_1 @ X5))),
% 0.20/0.45      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.45  thf('18', plain,
% 0.20/0.45      ((((k2_relat_1 @ (k6_partfun1 @ sk_B))
% 0.20/0.45          = (k9_relat_1 @ (k6_partfun1 @ sk_B) @ sk_A))
% 0.20/0.45        | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B)))),
% 0.20/0.45      inference('sup+', [status(thm)], ['16', '17'])).
% 0.20/0.45  thf(t71_relat_1, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.20/0.45       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.45  thf('19', plain, (![X15 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 0.20/0.45      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.45  thf('20', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.20/0.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.45  thf('21', plain, (![X15 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X15)) = (X15))),
% 0.20/0.45      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.45  thf('22', plain, (![X16 : $i]: (v1_relat_1 @ (k6_partfun1 @ X16))),
% 0.20/0.45      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.45  thf('23', plain, (((sk_B) = (k9_relat_1 @ (k6_partfun1 @ sk_B) @ sk_A))),
% 0.20/0.45      inference('demod', [status(thm)], ['18', '21', '22'])).
% 0.20/0.45  thf(t43_funct_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.20/0.45       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.45  thf('24', plain,
% 0.20/0.45      (![X25 : $i, X26 : $i]:
% 0.20/0.45         ((k5_relat_1 @ (k6_relat_1 @ X26) @ (k6_relat_1 @ X25))
% 0.20/0.45           = (k6_relat_1 @ (k3_xboole_0 @ X25 @ X26)))),
% 0.20/0.45      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.20/0.45  thf('25', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.20/0.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.45  thf('26', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.20/0.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.45  thf('27', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.20/0.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.45  thf('28', plain,
% 0.20/0.45      (![X25 : $i, X26 : $i]:
% 0.20/0.45         ((k5_relat_1 @ (k6_partfun1 @ X26) @ (k6_partfun1 @ X25))
% 0.20/0.45           = (k6_partfun1 @ (k3_xboole_0 @ X25 @ X26)))),
% 0.20/0.45      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 0.20/0.45  thf('29', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 0.20/0.45      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.45  thf('30', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.20/0.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.45  thf('31', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X14)) = (X14))),
% 0.20/0.45      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.45  thf(t182_relat_1, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ A ) =>
% 0.20/0.45       ( ![B:$i]:
% 0.20/0.45         ( ( v1_relat_1 @ B ) =>
% 0.20/0.45           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.20/0.45             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.20/0.45  thf('32', plain,
% 0.20/0.45      (![X7 : $i, X8 : $i]:
% 0.20/0.45         (~ (v1_relat_1 @ X7)
% 0.20/0.45          | ((k1_relat_1 @ (k5_relat_1 @ X8 @ X7))
% 0.20/0.45              = (k10_relat_1 @ X8 @ (k1_relat_1 @ X7)))
% 0.20/0.45          | ~ (v1_relat_1 @ X8))),
% 0.20/0.45      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.20/0.45  thf('33', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 0.20/0.45            = (k10_relat_1 @ X1 @ X0))
% 0.20/0.45          | ~ (v1_relat_1 @ X1)
% 0.20/0.45          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.20/0.45      inference('sup+', [status(thm)], ['31', '32'])).
% 0.20/0.45  thf('34', plain, (![X16 : $i]: (v1_relat_1 @ (k6_partfun1 @ X16))),
% 0.20/0.45      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.45  thf('35', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 0.20/0.45            = (k10_relat_1 @ X1 @ X0))
% 0.20/0.45          | ~ (v1_relat_1 @ X1))),
% 0.20/0.45      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.45  thf('36', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         (((k1_relat_1 @ (k6_partfun1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.20/0.45            = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 0.20/0.45          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.20/0.45      inference('sup+', [status(thm)], ['28', '35'])).
% 0.20/0.45  thf('37', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X14)) = (X14))),
% 0.20/0.45      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.45  thf(t67_funct_1, axiom,
% 0.20/0.45    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.20/0.45  thf('38', plain,
% 0.20/0.45      (![X27 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X27)) = (k6_relat_1 @ X27))),
% 0.20/0.45      inference('cnf', [status(esa)], [t67_funct_1])).
% 0.20/0.45  thf('39', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.20/0.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.45  thf('40', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.20/0.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.45  thf('41', plain,
% 0.20/0.45      (![X27 : $i]: ((k2_funct_1 @ (k6_partfun1 @ X27)) = (k6_partfun1 @ X27))),
% 0.20/0.45      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.20/0.45  thf(t155_funct_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.45       ( ( v2_funct_1 @ B ) =>
% 0.20/0.45         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.20/0.45  thf('42', plain,
% 0.20/0.45      (![X23 : $i, X24 : $i]:
% 0.20/0.45         (~ (v2_funct_1 @ X23)
% 0.20/0.45          | ((k10_relat_1 @ X23 @ X24)
% 0.20/0.45              = (k9_relat_1 @ (k2_funct_1 @ X23) @ X24))
% 0.20/0.45          | ~ (v1_funct_1 @ X23)
% 0.20/0.45          | ~ (v1_relat_1 @ X23))),
% 0.20/0.45      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.20/0.45  thf('43', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         (((k10_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 0.20/0.45            = (k9_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 0.20/0.45          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.20/0.45          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.20/0.45          | ~ (v2_funct_1 @ (k6_partfun1 @ X0)))),
% 0.20/0.45      inference('sup+', [status(thm)], ['41', '42'])).
% 0.20/0.45  thf('44', plain, (![X16 : $i]: (v1_relat_1 @ (k6_partfun1 @ X16))),
% 0.20/0.45      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.45  thf(fc3_funct_1, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.45       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.45  thf('45', plain, (![X20 : $i]: (v1_funct_1 @ (k6_relat_1 @ X20))),
% 0.20/0.45      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.45  thf('46', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.20/0.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.45  thf('47', plain, (![X20 : $i]: (v1_funct_1 @ (k6_partfun1 @ X20))),
% 0.20/0.45      inference('demod', [status(thm)], ['45', '46'])).
% 0.20/0.45  thf(fc4_funct_1, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.45       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.45  thf('48', plain, (![X22 : $i]: (v2_funct_1 @ (k6_relat_1 @ X22))),
% 0.20/0.45      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.20/0.45  thf('49', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.20/0.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.45  thf('50', plain, (![X22 : $i]: (v2_funct_1 @ (k6_partfun1 @ X22))),
% 0.20/0.45      inference('demod', [status(thm)], ['48', '49'])).
% 0.20/0.45  thf('51', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         ((k10_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 0.20/0.45           = (k9_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.20/0.45      inference('demod', [status(thm)], ['43', '44', '47', '50'])).
% 0.20/0.45  thf('52', plain, (![X16 : $i]: (v1_relat_1 @ (k6_partfun1 @ X16))),
% 0.20/0.45      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.45  thf('53', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         ((k3_xboole_0 @ X1 @ X0) = (k9_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.20/0.45      inference('demod', [status(thm)], ['36', '37', '51', '52'])).
% 0.20/0.45  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.45    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.45  thf('54', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.45  thf('55', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.20/0.45      inference('demod', [status(thm)], ['23', '53', '54'])).
% 0.20/0.45  thf('56', plain,
% 0.20/0.45      (((k8_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ sk_B) != (sk_B))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(t29_relset_1, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( m1_subset_1 @
% 0.20/0.45       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.20/0.45  thf('57', plain,
% 0.20/0.45      (![X32 : $i]:
% 0.20/0.45         (m1_subset_1 @ (k6_relat_1 @ X32) @ 
% 0.20/0.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 0.20/0.45      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.20/0.45  thf('58', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.20/0.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.45  thf('59', plain,
% 0.20/0.45      (![X32 : $i]:
% 0.20/0.45         (m1_subset_1 @ (k6_partfun1 @ X32) @ 
% 0.20/0.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 0.20/0.45      inference('demod', [status(thm)], ['57', '58'])).
% 0.20/0.45  thf(redefinition_k8_relset_1, axiom,
% 0.20/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.45       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.20/0.45  thf('60', plain,
% 0.20/0.45      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.45         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.20/0.45          | ((k8_relset_1 @ X29 @ X30 @ X28 @ X31) = (k10_relat_1 @ X28 @ X31)))),
% 0.20/0.45      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.45  thf('61', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         ((k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 0.20/0.45           = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.20/0.45      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.45  thf('62', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         ((k10_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 0.20/0.45           = (k9_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.20/0.45      inference('demod', [status(thm)], ['43', '44', '47', '50'])).
% 0.20/0.45  thf('63', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         ((k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 0.20/0.45           = (k9_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.20/0.45      inference('demod', [status(thm)], ['61', '62'])).
% 0.20/0.45  thf('64', plain, (((k9_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B) != (sk_B))),
% 0.20/0.45      inference('demod', [status(thm)], ['56', '63'])).
% 0.20/0.45  thf('65', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         ((k3_xboole_0 @ X1 @ X0) = (k9_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.20/0.45      inference('demod', [status(thm)], ['36', '37', '51', '52'])).
% 0.20/0.45  thf('66', plain, (((k3_xboole_0 @ sk_B @ sk_A) != (sk_B))),
% 0.20/0.45      inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.45  thf('67', plain, ($false),
% 0.20/0.45      inference('simplify_reflect-', [status(thm)], ['55', '66'])).
% 0.20/0.45  
% 0.20/0.45  % SZS output end Refutation
% 0.20/0.45  
% 0.20/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
