%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1054+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TVv5AZ3cLD

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:58 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 115 expanded)
%              Number of leaves         :   32 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :  550 ( 828 expanded)
%              Number of equality atoms :   23 (  37 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(v3_relat_2_type,type,(
    v3_relat_2: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('2',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('3',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X7 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(t92_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ A )
        & ( v3_funct_2 @ C @ A @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( r1_tarski @ B @ A )
       => ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) )
            = B )
          & ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) )
            = B ) ) ) ) )).

thf('4',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X25 @ X25 )
      | ~ ( v3_funct_2 @ X26 @ X25 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) )
      | ( ( k8_relset_1 @ X25 @ X25 @ X26 @ ( k7_relset_1 @ X25 @ X25 @ X26 @ X24 ) )
        = X24 ) ) ),
    inference(cnf,[status(esa)],[t92_funct_2])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k7_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = X1 )
      | ~ ( v3_funct_2 @ ( k6_partfun1 @ X0 ) @ X0 @ X0 )
      | ~ ( v1_funct_2 @ ( k6_partfun1 @ X0 ) @ X0 @ X0 )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X7 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( ( k7_relset_1 @ X16 @ X17 @ X15 @ X18 )
        = ( k9_relat_1 @ X15 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X7 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(cc4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ( ( ( v1_relat_2 @ B )
          & ( v1_funct_1 @ B )
          & ( v1_partfun1 @ B @ A )
          & ( v1_funct_2 @ B @ A @ A ) )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( v3_funct_2 @ B @ A @ A ) ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_2 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_partfun1 @ X4 @ X5 )
      | ~ ( v1_funct_2 @ X4 @ X5 @ X5 )
      | ( v3_funct_2 @ X4 @ X5 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc4_funct_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v3_funct_2 @ ( k6_partfun1 @ X0 ) @ X0 @ X0 )
      | ~ ( v1_funct_2 @ ( k6_partfun1 @ X0 ) @ X0 @ X0 )
      | ~ ( v1_partfun1 @ ( k6_partfun1 @ X0 ) @ X0 )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_2 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X7 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_partfun1 @ X0 @ X1 )
      | ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k6_partfun1 @ X0 ) @ X0 @ X0 )
      | ~ ( v1_partfun1 @ ( k6_partfun1 @ X0 ) @ X0 )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X6: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X6 ) @ X6 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X9: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('17',plain,(
    ! [X14: $i] :
      ( ( k6_partfun1 @ X14 )
      = ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('18',plain,(
    ! [X9: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X9 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k6_partfun1 @ X0 ) @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['14','15','18'])).

thf('20',plain,(
    ! [X6: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X6 ) @ X6 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('21',plain,(
    ! [X9: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X9 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('22',plain,(
    ! [X8: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('23',plain,(
    ! [X14: $i] :
      ( ( k6_partfun1 @ X14 )
      = ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('24',plain,(
    ! [X8: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X8 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(cc3_partfun1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v3_relat_2 @ A )
        & ( v8_relat_2 @ A ) )
     => ( ( v1_relat_1 @ A )
        & ( v1_relat_2 @ A ) ) ) )).

thf('25',plain,(
    ! [X3: $i] :
      ( ( v1_relat_2 @ X3 )
      | ~ ( v8_relat_2 @ X3 )
      | ~ ( v3_relat_2 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc3_partfun1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v3_relat_2 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v8_relat_2 @ ( k6_partfun1 @ X0 ) )
      | ( v1_relat_2 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(fc3_partfun1,axiom,(
    ! [A: $i] :
      ( ( v8_relat_2 @ ( k6_relat_1 @ A ) )
      & ( v4_relat_2 @ ( k6_relat_1 @ A ) )
      & ( v3_relat_2 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('27',plain,(
    ! [X11: $i] :
      ( v3_relat_2 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_partfun1])).

thf('28',plain,(
    ! [X14: $i] :
      ( ( k6_partfun1 @ X14 )
      = ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('29',plain,(
    ! [X11: $i] :
      ( v3_relat_2 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X13: $i] :
      ( v8_relat_2 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_partfun1])).

thf('31',plain,(
    ! [X14: $i] :
      ( ( k6_partfun1 @ X14 )
      = ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('32',plain,(
    ! [X13: $i] :
      ( v8_relat_2 @ ( k6_partfun1 @ X13 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( v1_relat_2 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( v3_funct_2 @ ( k6_partfun1 @ X0 ) @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['11','19','20','21','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k6_partfun1 @ X0 ) @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['14','15','18'])).

thf('36',plain,(
    ! [X9: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X9 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = X1 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','8','34','35','36'])).

thf('38',plain,
    ( ( k8_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k9_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['2','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t162_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
        = B ) ) )).

thf('40',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X20 ) @ X19 )
        = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t162_funct_1])).

thf('41',plain,(
    ! [X14: $i] :
      ( ( k6_partfun1 @ X14 )
      = ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('42',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k9_relat_1 @ ( k6_partfun1 @ X20 ) @ X19 )
        = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k9_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( k8_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['38','43'])).

thf('45',plain,(
    ( k8_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).


%------------------------------------------------------------------------------
