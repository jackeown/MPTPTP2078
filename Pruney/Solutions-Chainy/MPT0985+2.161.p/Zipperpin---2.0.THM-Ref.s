%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3AwuqL2g9X

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 343 expanded)
%              Number of leaves         :   30 ( 115 expanded)
%              Depth                    :   24
%              Number of atoms          : 1048 (5141 expanded)
%              Number of equality atoms :   33 ( 164 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t31_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v2_funct_1 @ C )
            & ( ( k2_relset_1 @ A @ B @ C )
              = B ) )
         => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
            & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
            & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('6',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X8: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_relat_1 @ X11 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('14',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('15',plain,(
    ! [X8: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('18',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k1_relat_1 @ X11 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('22',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k10_relat_1 @ X9 @ X10 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X9 ) @ X10 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('23',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('24',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_relat_1 @ X11 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('25',plain,(
    ! [X7: $i] :
      ( ( ( k9_relat_1 @ X7 @ ( k1_relat_1 @ X7 ) )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['20','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('39',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X13 @ X14 @ X12 @ X15 ) @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('42',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( ( k8_relset_1 @ X20 @ X21 @ X19 @ X22 )
        = ( k10_relat_1 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['37','44'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k1_relat_1 @ X11 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('49',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ X24 )
      | ( v1_funct_2 @ X23 @ ( k1_relat_1 @ X23 ) @ X24 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('55',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['15','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('58',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('62',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['13','63'])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['18','19'])).

thf('66',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['64','65','66','67','68'])).

thf('70',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('71',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('73',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['12','71','72'])).

thf('74',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','73'])).

thf('75',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_relat_1 @ X11 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('76',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('77',plain,(
    ! [X8: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('78',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['45','46'])).

thf('79',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k1_relat_1 @ X11 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('80',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ X24 )
      | ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X23 ) @ X24 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('86',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['82','83','84','85'])).

thf('87',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['77','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('89',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['76','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('93',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['75','94'])).

thf('96',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['18','19'])).

thf('97',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('98',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','96','97','98','99'])).

thf('101',plain,(
    $false ),
    inference(demod,[status(thm)],['74','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3AwuqL2g9X
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:47:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 97 iterations in 0.062s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.52  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.52  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.20/0.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.52  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.52  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.52  thf(t31_funct_2, conjecture,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.52       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.20/0.52         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.20/0.52           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.20/0.52           ( m1_subset_1 @
% 0.20/0.52             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.52        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.52            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.52          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.20/0.52            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.20/0.52              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.20/0.52              ( m1_subset_1 @
% 0.20/0.52                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.52        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.20/0.52        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.20/0.52         <= (~
% 0.20/0.52             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(cc2_relat_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X3 : $i, X4 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.20/0.52          | (v1_relat_1 @ X3)
% 0.20/0.52          | ~ (v1_relat_1 @ X4))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.52  thf(fc6_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.52  thf('6', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf(dt_k2_funct_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.52       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.20/0.52         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X8 : $i]:
% 0.20/0.52         ((v1_funct_1 @ (k2_funct_1 @ X8))
% 0.20/0.52          | ~ (v1_funct_1 @ X8)
% 0.20/0.52          | ~ (v1_relat_1 @ X8))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.20/0.52         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 0.20/0.52         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.20/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.52  thf('12', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['6', '11'])).
% 0.20/0.52  thf(t55_funct_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.52       ( ( v2_funct_1 @ A ) =>
% 0.20/0.52         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.20/0.52           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X11 : $i]:
% 0.20/0.52         (~ (v2_funct_1 @ X11)
% 0.20/0.52          | ((k2_relat_1 @ X11) = (k1_relat_1 @ (k2_funct_1 @ X11)))
% 0.20/0.52          | ~ (v1_funct_1 @ X11)
% 0.20/0.52          | ~ (v1_relat_1 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X8 : $i]:
% 0.20/0.52         ((v1_relat_1 @ (k2_funct_1 @ X8))
% 0.20/0.52          | ~ (v1_funct_1 @ X8)
% 0.20/0.52          | ~ (v1_relat_1 @ X8))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X8 : $i]:
% 0.20/0.52         ((v1_funct_1 @ (k2_funct_1 @ X8))
% 0.20/0.52          | ~ (v1_funct_1 @ X8)
% 0.20/0.52          | ~ (v1_relat_1 @ X8))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.52         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 0.20/0.52          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.52  thf('19', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('20', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.20/0.52      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X11 : $i]:
% 0.20/0.52         (~ (v2_funct_1 @ X11)
% 0.20/0.52          | ((k1_relat_1 @ X11) = (k2_relat_1 @ (k2_funct_1 @ X11)))
% 0.20/0.52          | ~ (v1_funct_1 @ X11)
% 0.20/0.52          | ~ (v1_relat_1 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.20/0.52  thf(t155_funct_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.52       ( ( v2_funct_1 @ B ) =>
% 0.20/0.52         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X9 : $i, X10 : $i]:
% 0.20/0.52         (~ (v2_funct_1 @ X9)
% 0.20/0.52          | ((k10_relat_1 @ X9 @ X10) = (k9_relat_1 @ (k2_funct_1 @ X9) @ X10))
% 0.20/0.52          | ~ (v1_funct_1 @ X9)
% 0.20/0.52          | ~ (v1_relat_1 @ X9))),
% 0.20/0.52      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X8 : $i]:
% 0.20/0.52         ((v1_relat_1 @ (k2_funct_1 @ X8))
% 0.20/0.52          | ~ (v1_funct_1 @ X8)
% 0.20/0.52          | ~ (v1_relat_1 @ X8))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X11 : $i]:
% 0.20/0.52         (~ (v2_funct_1 @ X11)
% 0.20/0.52          | ((k2_relat_1 @ X11) = (k1_relat_1 @ (k2_funct_1 @ X11)))
% 0.20/0.52          | ~ (v1_funct_1 @ X11)
% 0.20/0.52          | ~ (v1_relat_1 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.20/0.52  thf(t146_relat_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ A ) =>
% 0.20/0.52       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X7 : $i]:
% 0.20/0.52         (((k9_relat_1 @ X7 @ (k1_relat_1 @ X7)) = (k2_relat_1 @ X7))
% 0.20/0.52          | ~ (v1_relat_1 @ X7))),
% 0.20/0.52      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.20/0.52            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.20/0.52          | ~ (v1_relat_1 @ X0)
% 0.20/0.52          | ~ (v1_funct_1 @ X0)
% 0.20/0.52          | ~ (v2_funct_1 @ X0)
% 0.20/0.52          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['24', '25'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X0)
% 0.20/0.52          | ~ (v1_funct_1 @ X0)
% 0.20/0.52          | ~ (v2_funct_1 @ X0)
% 0.20/0.52          | ~ (v1_funct_1 @ X0)
% 0.20/0.52          | ~ (v1_relat_1 @ X0)
% 0.20/0.52          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.20/0.52              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['23', '26'])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.20/0.52            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.20/0.52          | ~ (v2_funct_1 @ X0)
% 0.20/0.52          | ~ (v1_funct_1 @ X0)
% 0.20/0.52          | ~ (v1_relat_1 @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k10_relat_1 @ X0 @ (k2_relat_1 @ X0))
% 0.20/0.52            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.20/0.52          | ~ (v1_relat_1 @ X0)
% 0.20/0.52          | ~ (v1_funct_1 @ X0)
% 0.20/0.52          | ~ (v2_funct_1 @ X0)
% 0.20/0.52          | ~ (v1_relat_1 @ X0)
% 0.20/0.52          | ~ (v1_funct_1 @ X0)
% 0.20/0.52          | ~ (v2_funct_1 @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['22', '28'])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v2_funct_1 @ X0)
% 0.20/0.52          | ~ (v1_funct_1 @ X0)
% 0.20/0.52          | ~ (v1_relat_1 @ X0)
% 0.20/0.52          | ((k10_relat_1 @ X0 @ (k2_relat_1 @ X0))
% 0.20/0.52              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.20/0.52      inference('simplify', [status(thm)], ['29'])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) = (k1_relat_1 @ X0))
% 0.20/0.52          | ~ (v1_relat_1 @ X0)
% 0.20/0.52          | ~ (v1_funct_1 @ X0)
% 0.20/0.52          | ~ (v2_funct_1 @ X0)
% 0.20/0.52          | ~ (v1_relat_1 @ X0)
% 0.20/0.52          | ~ (v1_funct_1 @ X0)
% 0.20/0.52          | ~ (v2_funct_1 @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['21', '30'])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v2_funct_1 @ X0)
% 0.20/0.52          | ~ (v1_funct_1 @ X0)
% 0.20/0.52          | ~ (v1_relat_1 @ X0)
% 0.20/0.52          | ((k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) = (k1_relat_1 @ X0)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      ((((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))
% 0.20/0.52        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.52        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.52        | ~ (v2_funct_1 @ sk_C))),
% 0.20/0.52      inference('sup+', [status(thm)], ['20', '32'])).
% 0.20/0.52  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('36', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('37', plain, (((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))),
% 0.20/0.52      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(dt_k8_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.20/0.52          | (m1_subset_1 @ (k8_relset_1 @ X13 @ X14 @ X12 @ X15) @ 
% 0.20/0.52             (k1_zfmisc_1 @ X13)))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (m1_subset_1 @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.20/0.52          (k1_zfmisc_1 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(redefinition_k8_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.20/0.52          | ((k8_relset_1 @ X20 @ X21 @ X19 @ X22) = (k10_relat_1 @ X19 @ X22)))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (m1_subset_1 @ (k10_relat_1 @ sk_C @ X0) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['40', '43'])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      ((m1_subset_1 @ (k1_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.52      inference('sup+', [status(thm)], ['37', '44'])).
% 0.20/0.52  thf(t3_subset, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.52  thf('47', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.20/0.52      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (![X11 : $i]:
% 0.20/0.52         (~ (v2_funct_1 @ X11)
% 0.20/0.52          | ((k1_relat_1 @ X11) = (k2_relat_1 @ (k2_funct_1 @ X11)))
% 0.20/0.52          | ~ (v1_funct_1 @ X11)
% 0.20/0.52          | ~ (v1_relat_1 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.20/0.52  thf(t4_funct_2, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.52       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.20/0.52         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.20/0.52           ( m1_subset_1 @
% 0.20/0.52             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      (![X23 : $i, X24 : $i]:
% 0.20/0.52         (~ (r1_tarski @ (k2_relat_1 @ X23) @ X24)
% 0.20/0.52          | (v1_funct_2 @ X23 @ (k1_relat_1 @ X23) @ X24)
% 0.20/0.52          | ~ (v1_funct_1 @ X23)
% 0.20/0.52          | ~ (v1_relat_1 @ X23))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.20/0.52          | ~ (v1_relat_1 @ X0)
% 0.20/0.52          | ~ (v1_funct_1 @ X0)
% 0.20/0.52          | ~ (v2_funct_1 @ X0)
% 0.20/0.52          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.52          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.52          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 0.20/0.52             (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.52         (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)
% 0.20/0.52        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.52        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.52        | ~ (v2_funct_1 @ sk_C)
% 0.20/0.52        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.52        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['47', '50'])).
% 0.20/0.52  thf('52', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('53', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('54', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf('55', plain,
% 0.20/0.52      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.52         (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)
% 0.20/0.52        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.52        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.20/0.52      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.20/0.52  thf('56', plain,
% 0.20/0.52      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.52        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.52        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.52        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.52           (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['15', '55'])).
% 0.20/0.52  thf('57', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf('58', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('59', plain,
% 0.20/0.52      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.52        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.52           (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.20/0.52  thf('60', plain,
% 0.20/0.52      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.52        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.52        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.52           (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['14', '59'])).
% 0.20/0.52  thf('61', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf('62', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('63', plain,
% 0.20/0.52      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.52        (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)),
% 0.20/0.52      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.20/0.52  thf('64', plain,
% 0.20/0.52      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 0.20/0.52        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.52        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.52        | ~ (v2_funct_1 @ sk_C))),
% 0.20/0.52      inference('sup+', [status(thm)], ['13', '63'])).
% 0.20/0.52  thf('65', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.20/0.52      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.52  thf('66', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('68', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('69', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.20/0.52      inference('demod', [status(thm)], ['64', '65', '66', '67', '68'])).
% 0.20/0.52  thf('70', plain,
% 0.20/0.52      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 0.20/0.52         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('71', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.52  thf('72', plain,
% 0.20/0.52      (~
% 0.20/0.52       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 0.20/0.52       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 0.20/0.52       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('73', plain,
% 0.20/0.52      (~
% 0.20/0.52       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['12', '71', '72'])).
% 0.20/0.52  thf('74', plain,
% 0.20/0.52      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['1', '73'])).
% 0.20/0.52  thf('75', plain,
% 0.20/0.52      (![X11 : $i]:
% 0.20/0.52         (~ (v2_funct_1 @ X11)
% 0.20/0.52          | ((k2_relat_1 @ X11) = (k1_relat_1 @ (k2_funct_1 @ X11)))
% 0.20/0.52          | ~ (v1_funct_1 @ X11)
% 0.20/0.52          | ~ (v1_relat_1 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.20/0.52  thf('76', plain,
% 0.20/0.52      (![X8 : $i]:
% 0.20/0.52         ((v1_relat_1 @ (k2_funct_1 @ X8))
% 0.20/0.52          | ~ (v1_funct_1 @ X8)
% 0.20/0.52          | ~ (v1_relat_1 @ X8))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.52  thf('77', plain,
% 0.20/0.52      (![X8 : $i]:
% 0.20/0.52         ((v1_funct_1 @ (k2_funct_1 @ X8))
% 0.20/0.52          | ~ (v1_funct_1 @ X8)
% 0.20/0.52          | ~ (v1_relat_1 @ X8))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.52  thf('78', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.20/0.52      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.52  thf('79', plain,
% 0.20/0.52      (![X11 : $i]:
% 0.20/0.52         (~ (v2_funct_1 @ X11)
% 0.20/0.52          | ((k1_relat_1 @ X11) = (k2_relat_1 @ (k2_funct_1 @ X11)))
% 0.20/0.52          | ~ (v1_funct_1 @ X11)
% 0.20/0.52          | ~ (v1_relat_1 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.20/0.52  thf('80', plain,
% 0.20/0.52      (![X23 : $i, X24 : $i]:
% 0.20/0.52         (~ (r1_tarski @ (k2_relat_1 @ X23) @ X24)
% 0.20/0.52          | (m1_subset_1 @ X23 @ 
% 0.20/0.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X23) @ X24)))
% 0.20/0.52          | ~ (v1_funct_1 @ X23)
% 0.20/0.52          | ~ (v1_relat_1 @ X23))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.20/0.52  thf('81', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.20/0.52          | ~ (v1_relat_1 @ X0)
% 0.20/0.52          | ~ (v1_funct_1 @ X0)
% 0.20/0.52          | ~ (v2_funct_1 @ X0)
% 0.20/0.52          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.52          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.52          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.20/0.52             (k1_zfmisc_1 @ 
% 0.20/0.52              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['79', '80'])).
% 0.20/0.52  thf('82', plain,
% 0.20/0.52      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.52         (k1_zfmisc_1 @ 
% 0.20/0.52          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))
% 0.20/0.52        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.52        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.52        | ~ (v2_funct_1 @ sk_C)
% 0.20/0.52        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.52        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['78', '81'])).
% 0.20/0.52  thf('83', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('85', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf('86', plain,
% 0.20/0.52      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.52         (k1_zfmisc_1 @ 
% 0.20/0.52          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))
% 0.20/0.52        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.52        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.20/0.52      inference('demod', [status(thm)], ['82', '83', '84', '85'])).
% 0.20/0.52  thf('87', plain,
% 0.20/0.52      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.52        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.52        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.52        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.52           (k1_zfmisc_1 @ 
% 0.20/0.52            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['77', '86'])).
% 0.20/0.52  thf('88', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf('89', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('90', plain,
% 0.20/0.52      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.52        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.52           (k1_zfmisc_1 @ 
% 0.20/0.52            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))))),
% 0.20/0.52      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.20/0.52  thf('91', plain,
% 0.20/0.52      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.52        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.52        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.52           (k1_zfmisc_1 @ 
% 0.20/0.52            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['76', '90'])).
% 0.20/0.52  thf('92', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf('93', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('94', plain,
% 0.20/0.52      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.52        (k1_zfmisc_1 @ 
% 0.20/0.52         (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.20/0.52  thf('95', plain,
% 0.20/0.52      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ sk_A)))
% 0.20/0.52        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.52        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.52        | ~ (v2_funct_1 @ sk_C))),
% 0.20/0.52      inference('sup+', [status(thm)], ['75', '94'])).
% 0.20/0.52  thf('96', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.20/0.52      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.52  thf('97', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf('98', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('99', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('100', plain,
% 0.20/0.52      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['95', '96', '97', '98', '99'])).
% 0.20/0.52  thf('101', plain, ($false), inference('demod', [status(thm)], ['74', '100'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
