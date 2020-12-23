%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.T065jpZJyg

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 129 expanded)
%              Number of leaves         :   42 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :  589 ( 816 expanded)
%              Number of equality atoms :   67 (  86 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t60_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ k1_xboole_0 @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) )
     => ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ k1_xboole_0 @ A )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) )
       => ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t60_funct_2])).

thf('0',plain,(
    ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('1',plain,(
    ! [X58: $i] :
      ( ( X58 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X58 ) @ X58 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k2_zfmisc_1 @ X37 @ X38 )
        = k1_xboole_0 )
      | ( X37 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('4',plain,(
    ! [X38: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X38 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','4'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('6',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ X45 @ X46 )
      | ~ ( v1_xboole_0 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('8',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','9'])).

thf('11',plain,(
    ( k8_relset_1 @ k1_xboole_0 @ sk_A @ k1_xboole_0 @ sk_B_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','10'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('12',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('13',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X56 ) ) )
      | ( ( k8_relset_1 @ X55 @ X56 @ X54 @ X57 )
        = ( k10_relat_1 @ X54 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k10_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ( k10_relat_1 @ k1_xboole_0 @ sk_B_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('16',plain,(
    ! [X48: $i,X49: $i] :
      ( ( ( k10_relat_1 @ X48 @ X49 )
        = ( k10_relat_1 @ X48 @ ( k3_xboole_0 @ ( k2_relat_1 @ X48 ) @ X49 ) ) )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('18',plain,(
    ! [X48: $i,X49: $i] :
      ( ( ( k10_relat_1 @ X48 @ X49 )
        = ( k10_relat_1 @ X48 @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X48 ) @ X49 ) ) ) )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k10_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relset_1 @ X2 @ X1 @ k1_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ) )
        = ( k10_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('21',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('25',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('26',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('27',plain,(
    ! [X4: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X4 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('30',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','33'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('35',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('38',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','43'])).

thf('45',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('46',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( v1_relat_1 @ X51 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('47',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ X2 @ X1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21','44','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k10_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('50',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('51',plain,(
    ! [X50: $i] :
      ( ( ( k10_relat_1 @ X50 @ ( k2_relat_1 @ X50 ) )
        = ( k1_relat_1 @ X50 ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('52',plain,
    ( ( ( k10_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('54',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('55',plain,
    ( ( k10_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','56'])).

thf('58',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['15','57'])).

thf('59',plain,(
    $false ),
    inference(simplify,[status(thm)],['58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.T065jpZJyg
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:06:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.21/0.34  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 92 iterations in 0.035s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.49  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.49  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.49  thf(t60_funct_2, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.21/0.49         ( m1_subset_1 @
% 0.21/0.49           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.21/0.49       ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.49        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.21/0.49            ( m1_subset_1 @
% 0.21/0.49              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.21/0.49          ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t60_funct_2])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (((k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ sk_B_1) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t6_mcart_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ~( ( r2_hidden @ B @ A ) & 
% 0.21/0.49                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.49                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.21/0.49                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.21/0.49                       ( r2_hidden @ G @ B ) ) =>
% 0.21/0.49                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X58 : $i]:
% 0.21/0.49         (((X58) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X58) @ X58))),
% 0.21/0.49      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t113_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.49       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X37 : $i, X38 : $i]:
% 0.21/0.49         (((k2_zfmisc_1 @ X37 @ X38) = (k1_xboole_0))
% 0.21/0.49          | ((X37) != (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X38 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X38) = (k1_xboole_0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.49  thf('5', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.21/0.49      inference('demod', [status(thm)], ['2', '4'])).
% 0.21/0.49  thf(t5_subset, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.21/0.49          ( v1_xboole_0 @ C ) ) ))).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X45 @ X46)
% 0.21/0.49          | ~ (v1_xboole_0 @ X47)
% 0.21/0.49          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t5_subset])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X0 : $i]: (~ (v1_xboole_0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.49  thf('8', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.49      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.49  thf('9', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C)),
% 0.21/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('10', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '9'])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (((k8_relset_1 @ k1_xboole_0 @ sk_A @ k1_xboole_0 @ sk_B_1)
% 0.21/0.49         != (k1_xboole_0))),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '10'])).
% 0.21/0.49  thf(t4_subset_1, axiom,
% 0.21/0.49    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X39 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X39))),
% 0.21/0.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.49  thf(redefinition_k8_relset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.49       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X56)))
% 0.21/0.49          | ((k8_relset_1 @ X55 @ X56 @ X54 @ X57) = (k10_relat_1 @ X54 @ X57)))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 0.21/0.49           = (k10_relat_1 @ k1_xboole_0 @ X2))),
% 0.21/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('15', plain, (((k10_relat_1 @ k1_xboole_0 @ sk_B_1) != (k1_xboole_0))),
% 0.21/0.49      inference('demod', [status(thm)], ['11', '14'])).
% 0.21/0.49  thf(t168_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ B ) =>
% 0.21/0.49       ( ( k10_relat_1 @ B @ A ) =
% 0.21/0.49         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X48 : $i, X49 : $i]:
% 0.21/0.49         (((k10_relat_1 @ X48 @ X49)
% 0.21/0.49            = (k10_relat_1 @ X48 @ (k3_xboole_0 @ (k2_relat_1 @ X48) @ X49)))
% 0.21/0.49          | ~ (v1_relat_1 @ X48))),
% 0.21/0.49      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.21/0.49  thf(t12_setfam_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X40 : $i, X41 : $i]:
% 0.21/0.49         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 0.21/0.49      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X48 : $i, X49 : $i]:
% 0.21/0.49         (((k10_relat_1 @ X48 @ X49)
% 0.21/0.49            = (k10_relat_1 @ X48 @ 
% 0.21/0.49               (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X48) @ X49))))
% 0.21/0.49          | ~ (v1_relat_1 @ X48))),
% 0.21/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 0.21/0.49           = (k10_relat_1 @ k1_xboole_0 @ X2))),
% 0.21/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (((k8_relset_1 @ X2 @ X1 @ k1_xboole_0 @ 
% 0.21/0.49            (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)))
% 0.21/0.49            = (k10_relat_1 @ k1_xboole_0 @ X0))
% 0.21/0.49          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf(t60_relat_1, axiom,
% 0.21/0.49    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.49     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.49  thf('21', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.49  thf(t100_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i]:
% 0.21/0.49         ((k4_xboole_0 @ X2 @ X3)
% 0.21/0.49           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X40 : $i, X41 : $i]:
% 0.21/0.49         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 0.21/0.49      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i]:
% 0.21/0.49         ((k4_xboole_0 @ X2 @ X3)
% 0.21/0.49           = (k5_xboole_0 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X3))))),
% 0.21/0.49      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.49  thf(t2_boole, axiom,
% 0.21/0.49    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X40 : $i, X41 : $i]:
% 0.21/0.49         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 0.21/0.49      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (![X4 : $i]:
% 0.21/0.49         ((k1_setfam_1 @ (k2_tarski @ X4 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.21/0.49      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i]:
% 0.21/0.49         ((k4_xboole_0 @ X2 @ X3)
% 0.21/0.49           = (k5_xboole_0 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X3))))),
% 0.21/0.49      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['27', '28'])).
% 0.21/0.49  thf(t5_boole, axiom,
% 0.21/0.49    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.49  thf('30', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.49  thf('31', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['29', '30'])).
% 0.21/0.49  thf(t98_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i]:
% 0.21/0.49         ((k2_xboole_0 @ X7 @ X8)
% 0.21/0.49           = (k5_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['31', '32'])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((k2_xboole_0 @ k1_xboole_0 @ 
% 0.21/0.49           (k1_setfam_1 @ (k2_tarski @ k1_xboole_0 @ X0)))
% 0.21/0.49           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['24', '33'])).
% 0.21/0.49  thf(t4_boole, axiom,
% 0.21/0.49    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      (![X5 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t4_boole])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((k2_xboole_0 @ k1_xboole_0 @ 
% 0.21/0.49           (k1_setfam_1 @ (k2_tarski @ k1_xboole_0 @ X0))) = (k1_xboole_0))),
% 0.21/0.49      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      (![X5 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t4_boole])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i]:
% 0.21/0.49         ((k2_xboole_0 @ X7 @ X8)
% 0.21/0.49           = (k5_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['37', '38'])).
% 0.21/0.49  thf('40', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.49  thf('41', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['39', '40'])).
% 0.21/0.49  thf(commutativity_k2_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.49  thf('43', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['41', '42'])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((k1_setfam_1 @ (k2_tarski @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 0.21/0.49      inference('demod', [status(thm)], ['36', '43'])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (![X39 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X39))),
% 0.21/0.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.49  thf(cc1_relset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.49       ( v1_relat_1 @ C ) ))).
% 0.21/0.49  thf('46', plain,
% 0.21/0.49      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.21/0.49         ((v1_relat_1 @ X51)
% 0.21/0.49          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53))))),
% 0.21/0.49      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.49  thf('47', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.49      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k8_relset_1 @ X2 @ X1 @ k1_xboole_0 @ k1_xboole_0)
% 0.21/0.49           = (k10_relat_1 @ k1_xboole_0 @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['20', '21', '44', '47'])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 0.21/0.49           = (k10_relat_1 @ k1_xboole_0 @ X2))),
% 0.21/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('50', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.49  thf(t169_relat_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.21/0.49  thf('51', plain,
% 0.21/0.49      (![X50 : $i]:
% 0.21/0.49         (((k10_relat_1 @ X50 @ (k2_relat_1 @ X50)) = (k1_relat_1 @ X50))
% 0.21/0.49          | ~ (v1_relat_1 @ X50))),
% 0.21/0.49      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.21/0.49  thf('52', plain,
% 0.21/0.49      ((((k10_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 0.21/0.49        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['50', '51'])).
% 0.21/0.49  thf('53', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.49  thf('54', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.49      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.49  thf('55', plain,
% 0.21/0.49      (((k10_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.49      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.21/0.49  thf('56', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['49', '55'])).
% 0.21/0.49  thf('57', plain,
% 0.21/0.49      (![X0 : $i]: ((k1_xboole_0) = (k10_relat_1 @ k1_xboole_0 @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['48', '56'])).
% 0.21/0.49  thf('58', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.49      inference('demod', [status(thm)], ['15', '57'])).
% 0.21/0.49  thf('59', plain, ($false), inference('simplify', [status(thm)], ['58'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
