%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Hg1vAUizma

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:48 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 469 expanded)
%              Number of leaves         :   38 ( 158 expanded)
%              Depth                    :   13
%              Number of atoms          : 1113 (5712 expanded)
%              Number of equality atoms :   88 ( 311 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('1',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( ( k8_relset_1 @ X35 @ X36 @ X34 @ X37 )
        = ( k10_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['10','15'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ( ( k5_relat_1 @ X19 @ ( k6_relat_1 @ X20 ) )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_A ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('20',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_A ) )
    = sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('21',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) )
        = ( k10_relat_1 @ X14 @ ( k1_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('24',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('28',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('30',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k7_relset_1 @ X31 @ X32 @ X30 @ X33 )
        = ( k9_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_A ) )
    = sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('34',plain,(
    ! [X10: $i] :
      ( ( ( k9_relat_1 @ X10 @ ( k1_relat_1 @ X10 ) )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k9_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_A ) ) @ ( k10_relat_1 @ sk_C @ sk_A ) )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('39',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_A ) )
    = sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('40',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_A ) )
    = sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('41',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['36','37','38','39','40'])).

thf('42',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('43',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('45',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('46',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['5','28','31','43','46'])).

thf('48',plain,
    ( $false
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('51',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('52',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('55',plain,(
    v4_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['53','54'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('56',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('57',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('59',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('60',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('61',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('63',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('65',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('66',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k2_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['52','63','66'])).

thf('68',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['49','67'])).

thf('69',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('70',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('72',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ( ( k5_relat_1 @ X19 @ ( k6_relat_1 @ X20 ) )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','77'])).

thf('79',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['69','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('81',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('82',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('83',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('84',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('85',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['79','80','81','82','83','84'])).

thf('86',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['68','85'])).

thf('87',plain,
    ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    = ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('89',plain,(
    ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
 != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['87','88'])).

thf('90',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['48','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Hg1vAUizma
% 0.15/0.35  % Computer   : n004.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:01:54 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.23/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.52  % Solved by: fo/fo7.sh
% 0.23/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.52  % done 97 iterations in 0.052s
% 0.23/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.52  % SZS output start Refutation
% 0.23/0.52  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.23/0.52  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.23/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.52  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.23/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.23/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.23/0.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.23/0.52  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.23/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.23/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.52  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.23/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.23/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.23/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.52  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.23/0.52  thf(t39_relset_1, conjecture,
% 0.23/0.52    (![A:$i,B:$i,C:$i]:
% 0.23/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.23/0.52       ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.23/0.52           ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.23/0.52         ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.23/0.52           ( k1_relset_1 @ B @ A @ C ) ) ) ))).
% 0.23/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.23/0.52        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.23/0.52          ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.23/0.52              ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.23/0.52            ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.23/0.52              ( k1_relset_1 @ B @ A @ C ) ) ) ) )),
% 0.23/0.52    inference('cnf.neg', [status(esa)], [t39_relset_1])).
% 0.23/0.52  thf('0', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf(redefinition_k8_relset_1, axiom,
% 0.23/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.52       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.23/0.52  thf('1', plain,
% 0.23/0.52      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.23/0.52         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.23/0.52          | ((k8_relset_1 @ X35 @ X36 @ X34 @ X37) = (k10_relat_1 @ X34 @ X37)))),
% 0.23/0.52      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.23/0.52  thf('2', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.23/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.23/0.52  thf('3', plain,
% 0.23/0.52      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.23/0.52          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.23/0.52          != (k2_relset_1 @ sk_B @ sk_A @ sk_C))
% 0.23/0.52        | ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.23/0.52            (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.23/0.52            != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('4', plain,
% 0.23/0.52      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.23/0.52          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.23/0.52          != (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.23/0.52         <= (~
% 0.23/0.52             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.23/0.52                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.23/0.52                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.23/0.52      inference('split', [status(esa)], ['3'])).
% 0.23/0.52  thf('5', plain,
% 0.23/0.52      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ (k10_relat_1 @ sk_C @ sk_A))
% 0.23/0.52          != (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.23/0.52         <= (~
% 0.23/0.52             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.23/0.52                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.23/0.52                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.23/0.52      inference('sup-', [status(thm)], ['2', '4'])).
% 0.23/0.52  thf('6', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf(cc2_relset_1, axiom,
% 0.23/0.52    (![A:$i,B:$i,C:$i]:
% 0.23/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.23/0.52  thf('7', plain,
% 0.23/0.52      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.23/0.52         ((v5_relat_1 @ X21 @ X23)
% 0.23/0.52          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.23/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.23/0.52  thf('8', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.23/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.23/0.52  thf(d19_relat_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( v1_relat_1 @ B ) =>
% 0.23/0.52       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.23/0.52  thf('9', plain,
% 0.23/0.52      (![X5 : $i, X6 : $i]:
% 0.23/0.52         (~ (v5_relat_1 @ X5 @ X6)
% 0.23/0.52          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.23/0.52          | ~ (v1_relat_1 @ X5))),
% 0.23/0.52      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.23/0.52  thf('10', plain,
% 0.23/0.52      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.52  thf('11', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf(cc2_relat_1, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( v1_relat_1 @ A ) =>
% 0.23/0.52       ( ![B:$i]:
% 0.23/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.23/0.52  thf('12', plain,
% 0.23/0.52      (![X3 : $i, X4 : $i]:
% 0.23/0.52         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.23/0.52          | (v1_relat_1 @ X3)
% 0.23/0.52          | ~ (v1_relat_1 @ X4))),
% 0.23/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.23/0.52  thf('13', plain,
% 0.23/0.52      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.23/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.52  thf(fc6_relat_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.23/0.52  thf('14', plain,
% 0.23/0.52      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.23/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.23/0.52  thf('15', plain, ((v1_relat_1 @ sk_C)),
% 0.23/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.23/0.52  thf('16', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)),
% 0.23/0.52      inference('demod', [status(thm)], ['10', '15'])).
% 0.23/0.52  thf(t79_relat_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( v1_relat_1 @ B ) =>
% 0.23/0.52       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.23/0.52         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.23/0.52  thf('17', plain,
% 0.23/0.52      (![X19 : $i, X20 : $i]:
% 0.23/0.52         (~ (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 0.23/0.52          | ((k5_relat_1 @ X19 @ (k6_relat_1 @ X20)) = (X19))
% 0.23/0.52          | ~ (v1_relat_1 @ X19))),
% 0.23/0.52      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.23/0.52  thf('18', plain,
% 0.23/0.52      ((~ (v1_relat_1 @ sk_C)
% 0.23/0.52        | ((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_A)) = (sk_C)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.23/0.52  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 0.23/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.23/0.52  thf('20', plain, (((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_A)) = (sk_C))),
% 0.23/0.52      inference('demod', [status(thm)], ['18', '19'])).
% 0.23/0.52  thf(t71_relat_1, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.23/0.52       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.23/0.52  thf('21', plain, (![X17 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 0.23/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.23/0.52  thf(t182_relat_1, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( v1_relat_1 @ A ) =>
% 0.23/0.52       ( ![B:$i]:
% 0.23/0.52         ( ( v1_relat_1 @ B ) =>
% 0.23/0.52           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.23/0.52             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.23/0.52  thf('22', plain,
% 0.23/0.52      (![X13 : $i, X14 : $i]:
% 0.23/0.52         (~ (v1_relat_1 @ X13)
% 0.23/0.52          | ((k1_relat_1 @ (k5_relat_1 @ X14 @ X13))
% 0.23/0.52              = (k10_relat_1 @ X14 @ (k1_relat_1 @ X13)))
% 0.23/0.52          | ~ (v1_relat_1 @ X14))),
% 0.23/0.52      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.23/0.52  thf('23', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.23/0.52            = (k10_relat_1 @ X1 @ X0))
% 0.23/0.52          | ~ (v1_relat_1 @ X1)
% 0.23/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.23/0.52      inference('sup+', [status(thm)], ['21', '22'])).
% 0.23/0.52  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.23/0.52  thf('24', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 0.23/0.52      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.23/0.52  thf('25', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.23/0.52            = (k10_relat_1 @ X1 @ X0))
% 0.23/0.52          | ~ (v1_relat_1 @ X1))),
% 0.23/0.52      inference('demod', [status(thm)], ['23', '24'])).
% 0.23/0.52  thf('26', plain,
% 0.23/0.52      ((((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_A))
% 0.23/0.52        | ~ (v1_relat_1 @ sk_C))),
% 0.23/0.52      inference('sup+', [status(thm)], ['20', '25'])).
% 0.23/0.52  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.23/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.23/0.52  thf('28', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_A))),
% 0.23/0.52      inference('demod', [status(thm)], ['26', '27'])).
% 0.23/0.52  thf('29', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf(redefinition_k7_relset_1, axiom,
% 0.23/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.52       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.23/0.52  thf('30', plain,
% 0.23/0.52      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.23/0.52         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.23/0.52          | ((k7_relset_1 @ X31 @ X32 @ X30 @ X33) = (k9_relat_1 @ X30 @ X33)))),
% 0.23/0.52      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.23/0.52  thf('31', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.23/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.23/0.52  thf('32', plain, (((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_A)) = (sk_C))),
% 0.23/0.52      inference('demod', [status(thm)], ['18', '19'])).
% 0.23/0.52  thf('33', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.23/0.52            = (k10_relat_1 @ X1 @ X0))
% 0.23/0.52          | ~ (v1_relat_1 @ X1))),
% 0.23/0.52      inference('demod', [status(thm)], ['23', '24'])).
% 0.23/0.52  thf(t146_relat_1, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( v1_relat_1 @ A ) =>
% 0.23/0.52       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.23/0.52  thf('34', plain,
% 0.23/0.52      (![X10 : $i]:
% 0.23/0.52         (((k9_relat_1 @ X10 @ (k1_relat_1 @ X10)) = (k2_relat_1 @ X10))
% 0.23/0.52          | ~ (v1_relat_1 @ X10))),
% 0.23/0.52      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.23/0.52  thf('35', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         (((k9_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 0.23/0.52            (k10_relat_1 @ X1 @ X0))
% 0.23/0.52            = (k2_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 0.23/0.52          | ~ (v1_relat_1 @ X1)
% 0.23/0.52          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.23/0.52      inference('sup+', [status(thm)], ['33', '34'])).
% 0.23/0.52  thf('36', plain,
% 0.23/0.52      ((~ (v1_relat_1 @ sk_C)
% 0.23/0.52        | ~ (v1_relat_1 @ sk_C)
% 0.23/0.52        | ((k9_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_A)) @ 
% 0.23/0.52            (k10_relat_1 @ sk_C @ sk_A))
% 0.23/0.52            = (k2_relat_1 @ (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_A)))))),
% 0.23/0.52      inference('sup-', [status(thm)], ['32', '35'])).
% 0.23/0.52  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 0.23/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.23/0.52  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 0.23/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.23/0.52  thf('39', plain, (((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_A)) = (sk_C))),
% 0.23/0.52      inference('demod', [status(thm)], ['18', '19'])).
% 0.23/0.52  thf('40', plain, (((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_A)) = (sk_C))),
% 0.23/0.52      inference('demod', [status(thm)], ['18', '19'])).
% 0.23/0.52  thf('41', plain,
% 0.23/0.52      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A)) = (k2_relat_1 @ sk_C))),
% 0.23/0.52      inference('demod', [status(thm)], ['36', '37', '38', '39', '40'])).
% 0.23/0.52  thf('42', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_A))),
% 0.23/0.52      inference('demod', [status(thm)], ['26', '27'])).
% 0.23/0.52  thf('43', plain,
% 0.23/0.52      (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.23/0.52      inference('demod', [status(thm)], ['41', '42'])).
% 0.23/0.52  thf('44', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf(redefinition_k2_relset_1, axiom,
% 0.23/0.52    (![A:$i,B:$i,C:$i]:
% 0.23/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.52       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.23/0.52  thf('45', plain,
% 0.23/0.52      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.23/0.52         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 0.23/0.52          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.23/0.52      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.23/0.52  thf('46', plain,
% 0.23/0.52      (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.23/0.52      inference('sup-', [status(thm)], ['44', '45'])).
% 0.23/0.52  thf('47', plain,
% 0.23/0.52      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.23/0.52         <= (~
% 0.23/0.52             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.23/0.52                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.23/0.52                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.23/0.52      inference('demod', [status(thm)], ['5', '28', '31', '43', '46'])).
% 0.23/0.52  thf('48', plain,
% 0.23/0.52      (($false)
% 0.23/0.52         <= (~
% 0.23/0.52             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.23/0.52                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.23/0.52                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.23/0.52      inference('simplify', [status(thm)], ['47'])).
% 0.23/0.52  thf('49', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.23/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.23/0.52  thf('50', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.23/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.23/0.52  thf('51', plain,
% 0.23/0.52      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.23/0.52          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.23/0.52          != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.23/0.52         <= (~
% 0.23/0.52             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.23/0.52                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.23/0.52                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.23/0.52      inference('split', [status(esa)], ['3'])).
% 0.23/0.52  thf('52', plain,
% 0.23/0.52      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ (k9_relat_1 @ sk_C @ sk_B))
% 0.23/0.52          != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.23/0.52         <= (~
% 0.23/0.52             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.23/0.52                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.23/0.52                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.23/0.52      inference('sup-', [status(thm)], ['50', '51'])).
% 0.23/0.52  thf('53', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('54', plain,
% 0.23/0.52      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.23/0.52         ((v4_relat_1 @ X21 @ X22)
% 0.23/0.52          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.23/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.23/0.52  thf('55', plain, ((v4_relat_1 @ sk_C @ sk_B)),
% 0.23/0.52      inference('sup-', [status(thm)], ['53', '54'])).
% 0.23/0.52  thf(t209_relat_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.23/0.52       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.23/0.52  thf('56', plain,
% 0.23/0.52      (![X15 : $i, X16 : $i]:
% 0.23/0.52         (((X15) = (k7_relat_1 @ X15 @ X16))
% 0.23/0.52          | ~ (v4_relat_1 @ X15 @ X16)
% 0.23/0.52          | ~ (v1_relat_1 @ X15))),
% 0.23/0.52      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.23/0.52  thf('57', plain,
% 0.23/0.52      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_B)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['55', '56'])).
% 0.23/0.52  thf('58', plain, ((v1_relat_1 @ sk_C)),
% 0.23/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.23/0.52  thf('59', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.23/0.52      inference('demod', [status(thm)], ['57', '58'])).
% 0.23/0.52  thf(t148_relat_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( v1_relat_1 @ B ) =>
% 0.23/0.52       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.23/0.52  thf('60', plain,
% 0.23/0.52      (![X11 : $i, X12 : $i]:
% 0.23/0.52         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.23/0.52          | ~ (v1_relat_1 @ X11))),
% 0.23/0.52      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.23/0.52  thf('61', plain,
% 0.23/0.52      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))
% 0.23/0.52        | ~ (v1_relat_1 @ sk_C))),
% 0.23/0.52      inference('sup+', [status(thm)], ['59', '60'])).
% 0.23/0.52  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 0.23/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.23/0.52  thf('63', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))),
% 0.23/0.52      inference('demod', [status(thm)], ['61', '62'])).
% 0.23/0.52  thf('64', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf(redefinition_k1_relset_1, axiom,
% 0.23/0.52    (![A:$i,B:$i,C:$i]:
% 0.23/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.52       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.23/0.52  thf('65', plain,
% 0.23/0.52      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.23/0.52         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 0.23/0.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.23/0.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.23/0.52  thf('66', plain,
% 0.23/0.52      (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.23/0.52      inference('sup-', [status(thm)], ['64', '65'])).
% 0.23/0.52  thf('67', plain,
% 0.23/0.52      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ (k2_relat_1 @ sk_C))
% 0.23/0.52          != (k1_relat_1 @ sk_C)))
% 0.23/0.52         <= (~
% 0.23/0.52             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.23/0.52                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.23/0.52                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.23/0.52      inference('demod', [status(thm)], ['52', '63', '66'])).
% 0.23/0.52  thf('68', plain,
% 0.23/0.52      ((((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.23/0.52         <= (~
% 0.23/0.52             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.23/0.52                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.23/0.52                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.23/0.52      inference('sup-', [status(thm)], ['49', '67'])).
% 0.23/0.52  thf('69', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.23/0.52      inference('demod', [status(thm)], ['57', '58'])).
% 0.23/0.52  thf('70', plain,
% 0.23/0.52      (![X11 : $i, X12 : $i]:
% 0.23/0.52         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.23/0.52          | ~ (v1_relat_1 @ X11))),
% 0.23/0.52      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.23/0.52  thf(d10_xboole_0, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.23/0.52  thf('71', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.23/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.23/0.52  thf('72', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.23/0.52      inference('simplify', [status(thm)], ['71'])).
% 0.23/0.52  thf('73', plain,
% 0.23/0.52      (![X19 : $i, X20 : $i]:
% 0.23/0.52         (~ (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 0.23/0.52          | ((k5_relat_1 @ X19 @ (k6_relat_1 @ X20)) = (X19))
% 0.23/0.52          | ~ (v1_relat_1 @ X19))),
% 0.23/0.52      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.23/0.52  thf('74', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (~ (v1_relat_1 @ X0)
% 0.23/0.52          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))) = (X0)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['72', '73'])).
% 0.23/0.52  thf('75', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.23/0.52            = (k10_relat_1 @ X1 @ X0))
% 0.23/0.52          | ~ (v1_relat_1 @ X1))),
% 0.23/0.52      inference('demod', [status(thm)], ['23', '24'])).
% 0.23/0.52  thf('76', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.23/0.52          | ~ (v1_relat_1 @ X0)
% 0.23/0.52          | ~ (v1_relat_1 @ X0))),
% 0.23/0.52      inference('sup+', [status(thm)], ['74', '75'])).
% 0.23/0.52  thf('77', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (~ (v1_relat_1 @ X0)
% 0.23/0.52          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 0.23/0.52      inference('simplify', [status(thm)], ['76'])).
% 0.23/0.52  thf('78', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.23/0.52            = (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0)))
% 0.23/0.52          | ~ (v1_relat_1 @ X1)
% 0.23/0.52          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.23/0.52      inference('sup+', [status(thm)], ['70', '77'])).
% 0.23/0.52  thf('79', plain,
% 0.23/0.52      ((~ (v1_relat_1 @ sk_C)
% 0.23/0.52        | ~ (v1_relat_1 @ sk_C)
% 0.23/0.52        | ((k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_B))
% 0.23/0.52            = (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_B) @ 
% 0.23/0.52               (k9_relat_1 @ sk_C @ sk_B))))),
% 0.23/0.52      inference('sup-', [status(thm)], ['69', '78'])).
% 0.23/0.52  thf('80', plain, ((v1_relat_1 @ sk_C)),
% 0.23/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.23/0.52  thf('81', plain, ((v1_relat_1 @ sk_C)),
% 0.23/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.23/0.52  thf('82', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.23/0.52      inference('demod', [status(thm)], ['57', '58'])).
% 0.23/0.52  thf('83', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.23/0.52      inference('demod', [status(thm)], ['57', '58'])).
% 0.23/0.52  thf('84', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))),
% 0.23/0.52      inference('demod', [status(thm)], ['61', '62'])).
% 0.23/0.52  thf('85', plain,
% 0.23/0.52      (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 0.23/0.52      inference('demod', [status(thm)], ['79', '80', '81', '82', '83', '84'])).
% 0.23/0.52  thf('86', plain,
% 0.23/0.52      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 0.23/0.52         <= (~
% 0.23/0.52             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.23/0.52                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.23/0.52                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.23/0.52      inference('demod', [status(thm)], ['68', '85'])).
% 0.23/0.52  thf('87', plain,
% 0.23/0.52      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.23/0.52          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.23/0.52          = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.23/0.52      inference('simplify', [status(thm)], ['86'])).
% 0.23/0.52  thf('88', plain,
% 0.23/0.52      (~
% 0.23/0.52       (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.23/0.52          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.23/0.52          = (k2_relset_1 @ sk_B @ sk_A @ sk_C))) | 
% 0.23/0.52       ~
% 0.23/0.52       (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.23/0.52          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.23/0.52          = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.23/0.52      inference('split', [status(esa)], ['3'])).
% 0.23/0.52  thf('89', plain,
% 0.23/0.52      (~
% 0.23/0.52       (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.23/0.52          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.23/0.52          = (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.23/0.52      inference('sat_resolution*', [status(thm)], ['87', '88'])).
% 0.23/0.52  thf('90', plain, ($false),
% 0.23/0.52      inference('simpl_trail', [status(thm)], ['48', '89'])).
% 0.23/0.52  
% 0.23/0.52  % SZS output end Refutation
% 0.23/0.52  
% 0.23/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
