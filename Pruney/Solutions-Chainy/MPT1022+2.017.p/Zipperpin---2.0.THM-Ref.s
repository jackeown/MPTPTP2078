%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.blW3V0VFE5

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:27 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 648 expanded)
%              Number of leaves         :   41 ( 213 expanded)
%              Depth                    :   18
%              Number of atoms          : 1615 (12984 expanded)
%              Number of equality atoms :   89 ( 585 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(t92_funct_2,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ A )
          & ( v3_funct_2 @ C @ A @ A )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( r1_tarski @ B @ A )
         => ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) )
              = B )
            & ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) )
              = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t92_funct_2])).

thf('0',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) )
        & ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A )
        & ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A )
        & ( m1_subset_1 @ ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X33: $i,X34: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X33 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) )
      | ~ ( v3_funct_2 @ X34 @ X33 @ X33 )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X33 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k2_funct_2 @ A @ B )
        = ( k2_funct_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k2_funct_2 @ X36 @ X35 )
        = ( k2_funct_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) )
      | ~ ( v3_funct_2 @ X35 @ X36 @ X36 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X36 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k2_funct_2 @ sk_A @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('14',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5','6','13'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('16',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9
        = ( k7_relat_1 @ X9 @ X10 ) )
      | ~ ( v4_relat_1 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_funct_1 @ sk_C )
      = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5','6','13'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('22',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('23',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['18','23'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('26',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5','6','13'])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('28',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_1 @ X28 )
      | ~ ( v3_funct_2 @ X28 @ X29 @ X30 )
      | ( v2_funct_2 @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('29',plain,
    ( ( v2_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X33 @ X34 ) @ X33 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) )
      | ~ ( v3_funct_2 @ X34 @ X33 @ X33 )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X33 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('32',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_C ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k2_funct_2 @ sk_A @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('37',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['32','33','34','35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X33 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) )
      | ~ ( v3_funct_2 @ X34 @ X33 @ X33 )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X33 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('40',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['40','41','42','43'])).

thf('45',plain,
    ( ( k2_funct_2 @ sk_A @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('46',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    v2_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['29','37','46'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('48',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v2_funct_2 @ X32 @ X31 )
      | ( ( k2_relat_1 @ X32 )
        = X31 )
      | ~ ( v5_relat_1 @ X32 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('51',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5','6','13'])).

thf('52',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('53',plain,(
    v5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['49','50','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_1 @ X28 )
      | ~ ( v3_funct_2 @ X28 @ X29 @ X30 )
      | ( v2_funct_2 @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('57',plain,
    ( ( v2_funct_2 @ sk_C @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_funct_2 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v2_funct_2 @ X32 @ X31 )
      | ( ( k2_relat_1 @ X32 )
        = X31 )
      | ~ ( v5_relat_1 @ X32 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v5_relat_1 @ sk_C @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('65',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('67',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('70',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['62','67','70'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('73',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['72'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('74',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X11 @ ( k2_relat_1 @ X12 ) )
      | ( ( k9_relat_1 @ X12 @ ( k10_relat_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['71','75'])).

thf('77',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['62','67','70'])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['65','66'])).

thf('80',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['76','77','78','79'])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['62','67','70'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('82',plain,(
    ! [X37: $i] :
      ( ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X37 ) @ ( k2_relat_1 @ X37 ) ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('83',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9
        = ( k7_relat_1 @ X9 @ X10 ) )
      | ~ ( v4_relat_1 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['72'])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('92',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X13 @ ( k1_relat_1 @ X14 ) )
      | ~ ( v2_funct_1 @ X14 )
      | ( ( k10_relat_1 @ X14 @ ( k9_relat_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['90','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['81','95'])).

thf('97',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['65','66'])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_1 @ X28 )
      | ~ ( v3_funct_2 @ X28 @ X29 @ X30 )
      | ( v2_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('101',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,
    ( ( k10_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['96','97','98','104'])).

thf('106',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['80','105'])).

thf('107',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['72'])).

thf(t177_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v2_funct_1 @ A )
            & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) )
         => ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) )
            = B ) ) ) )).

thf('108',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X16 ) @ ( k9_relat_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( v2_funct_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t177_funct_1])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['106','109'])).

thf('111',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('112',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['65','66'])).

thf('114',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['110','111','112','113'])).

thf('115',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('116',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['26','54','114','115'])).

thf('117',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X13 @ ( k1_relat_1 @ X14 ) )
      | ~ ( v2_funct_1 @ X14 )
      | ( ( k10_relat_1 @ X14 @ ( k9_relat_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['65','66'])).

thf('120',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['118','119','120','121'])).

thf('123',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','122'])).

thf('124',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('125',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k8_relset_1 @ X25 @ X26 @ X24 @ X27 )
        = ( k10_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('128',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k7_relset_1 @ X21 @ X22 @ X20 @ X23 )
        = ( k9_relat_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
    | ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['130'])).

thf('132',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['129','131'])).

thf('133',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['126','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('135',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['130'])).

thf('136',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('138',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['62','67','70'])).

thf('140',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X11 @ ( k2_relat_1 @ X12 ) )
      | ( ( k9_relat_1 @ X12 @ ( k10_relat_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['65','66'])).

thf('143',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['138','144'])).

thf('146',plain,
    ( ( sk_B != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(demod,[status(thm)],['136','137','145'])).

thf('147',plain,
    ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
    = sk_B ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
    | ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['130'])).

thf('149',plain,(
    ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['147','148'])).

thf('150',plain,(
    ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['133','149'])).

thf('151',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['123','150'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.blW3V0VFE5
% 0.14/0.37  % Computer   : n023.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 14:40:21 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.38/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.61  % Solved by: fo/fo7.sh
% 0.38/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.61  % done 230 iterations in 0.133s
% 0.38/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.61  % SZS output start Refutation
% 0.38/0.61  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.38/0.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.38/0.61  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.38/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.61  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.38/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.61  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.38/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.61  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.38/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.61  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.38/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.61  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.38/0.61  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.38/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.61  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.38/0.61  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.38/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.61  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.38/0.61  thf(t92_funct_2, conjecture,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.38/0.61         ( v3_funct_2 @ C @ A @ A ) & 
% 0.38/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.38/0.61       ( ( r1_tarski @ B @ A ) =>
% 0.38/0.61         ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) ) =
% 0.38/0.61             ( B ) ) & 
% 0.38/0.61           ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) ) =
% 0.38/0.61             ( B ) ) ) ) ))).
% 0.38/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.61        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.38/0.61            ( v3_funct_2 @ C @ A @ A ) & 
% 0.38/0.61            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.38/0.61          ( ( r1_tarski @ B @ A ) =>
% 0.38/0.61            ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) ) =
% 0.38/0.61                ( B ) ) & 
% 0.38/0.61              ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) ) =
% 0.38/0.61                ( B ) ) ) ) ) )),
% 0.38/0.61    inference('cnf.neg', [status(esa)], [t92_funct_2])).
% 0.38/0.61  thf('0', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('1', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(dt_k2_funct_2, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.38/0.61         ( v3_funct_2 @ B @ A @ A ) & 
% 0.38/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.38/0.61       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.38/0.61         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.38/0.61         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.38/0.61         ( m1_subset_1 @
% 0.38/0.61           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.38/0.61  thf('2', plain,
% 0.38/0.61      (![X33 : $i, X34 : $i]:
% 0.38/0.61         ((m1_subset_1 @ (k2_funct_2 @ X33 @ X34) @ 
% 0.38/0.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))
% 0.38/0.61          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))
% 0.38/0.61          | ~ (v3_funct_2 @ X34 @ X33 @ X33)
% 0.38/0.61          | ~ (v1_funct_2 @ X34 @ X33 @ X33)
% 0.38/0.61          | ~ (v1_funct_1 @ X34))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.38/0.61  thf('3', plain,
% 0.38/0.61      ((~ (v1_funct_1 @ sk_C)
% 0.38/0.61        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.38/0.61        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.38/0.61        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_C) @ 
% 0.38/0.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.61  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('5', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('6', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('7', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(redefinition_k2_funct_2, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.38/0.61         ( v3_funct_2 @ B @ A @ A ) & 
% 0.38/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.38/0.61       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.38/0.61  thf('8', plain,
% 0.38/0.61      (![X35 : $i, X36 : $i]:
% 0.38/0.61         (((k2_funct_2 @ X36 @ X35) = (k2_funct_1 @ X35))
% 0.38/0.61          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))
% 0.38/0.61          | ~ (v3_funct_2 @ X35 @ X36 @ X36)
% 0.38/0.61          | ~ (v1_funct_2 @ X35 @ X36 @ X36)
% 0.38/0.61          | ~ (v1_funct_1 @ X35))),
% 0.38/0.61      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.38/0.61  thf('9', plain,
% 0.38/0.61      ((~ (v1_funct_1 @ sk_C)
% 0.38/0.61        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.38/0.61        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.38/0.61        | ((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.61  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('11', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('12', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('13', plain, (((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.38/0.61      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.38/0.61  thf('14', plain,
% 0.38/0.61      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.38/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.61      inference('demod', [status(thm)], ['3', '4', '5', '6', '13'])).
% 0.38/0.61  thf(cc2_relset_1, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.61       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.38/0.61  thf('15', plain,
% 0.38/0.61      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.61         ((v4_relat_1 @ X17 @ X18)
% 0.38/0.61          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.38/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.61  thf('16', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)),
% 0.38/0.61      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.61  thf(t209_relat_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.38/0.61       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.38/0.61  thf('17', plain,
% 0.38/0.61      (![X9 : $i, X10 : $i]:
% 0.38/0.61         (((X9) = (k7_relat_1 @ X9 @ X10))
% 0.38/0.61          | ~ (v4_relat_1 @ X9 @ X10)
% 0.38/0.61          | ~ (v1_relat_1 @ X9))),
% 0.38/0.61      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.38/0.61  thf('18', plain,
% 0.38/0.61      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.61        | ((k2_funct_1 @ sk_C) = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.61  thf('19', plain,
% 0.38/0.61      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.38/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.61      inference('demod', [status(thm)], ['3', '4', '5', '6', '13'])).
% 0.38/0.61  thf(cc2_relat_1, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( v1_relat_1 @ A ) =>
% 0.38/0.62       ( ![B:$i]:
% 0.38/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.38/0.62  thf('20', plain,
% 0.38/0.62      (![X3 : $i, X4 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.38/0.62          | (v1_relat_1 @ X3)
% 0.38/0.62          | ~ (v1_relat_1 @ X4))),
% 0.38/0.62      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.38/0.62  thf('21', plain,
% 0.38/0.62      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 0.38/0.62        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['19', '20'])).
% 0.38/0.62  thf(fc6_relat_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.38/0.62  thf('22', plain,
% 0.38/0.62      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.38/0.62      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.38/0.62  thf('23', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.38/0.62      inference('demod', [status(thm)], ['21', '22'])).
% 0.38/0.62  thf('24', plain,
% 0.38/0.62      (((k2_funct_1 @ sk_C) = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['18', '23'])).
% 0.38/0.62  thf(t148_relat_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( v1_relat_1 @ B ) =>
% 0.38/0.62       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.38/0.62  thf('25', plain,
% 0.38/0.62      (![X7 : $i, X8 : $i]:
% 0.38/0.62         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 0.38/0.62          | ~ (v1_relat_1 @ X7))),
% 0.38/0.62      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.38/0.62  thf('26', plain,
% 0.38/0.62      ((((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.62          = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A))
% 0.38/0.62        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.38/0.62      inference('sup+', [status(thm)], ['24', '25'])).
% 0.38/0.62  thf('27', plain,
% 0.38/0.62      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.38/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.62      inference('demod', [status(thm)], ['3', '4', '5', '6', '13'])).
% 0.38/0.62  thf(cc2_funct_2, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.62       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.38/0.62         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.38/0.62  thf('28', plain,
% 0.38/0.62      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.38/0.62         (~ (v1_funct_1 @ X28)
% 0.38/0.62          | ~ (v3_funct_2 @ X28 @ X29 @ X30)
% 0.38/0.62          | (v2_funct_2 @ X28 @ X30)
% 0.38/0.62          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.38/0.62      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.38/0.62  thf('29', plain,
% 0.38/0.62      (((v2_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A)
% 0.38/0.62        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_A)
% 0.38/0.62        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['27', '28'])).
% 0.38/0.62  thf('30', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('31', plain,
% 0.38/0.62      (![X33 : $i, X34 : $i]:
% 0.38/0.62         ((v3_funct_2 @ (k2_funct_2 @ X33 @ X34) @ X33 @ X33)
% 0.38/0.62          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))
% 0.38/0.62          | ~ (v3_funct_2 @ X34 @ X33 @ X33)
% 0.38/0.62          | ~ (v1_funct_2 @ X34 @ X33 @ X33)
% 0.38/0.62          | ~ (v1_funct_1 @ X34))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.38/0.62  thf('32', plain,
% 0.38/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.38/0.62        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.38/0.62        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.38/0.62        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_C) @ sk_A @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.62  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('34', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('35', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('36', plain, (((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.38/0.62      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.38/0.62  thf('37', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_A)),
% 0.38/0.62      inference('demod', [status(thm)], ['32', '33', '34', '35', '36'])).
% 0.38/0.62  thf('38', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('39', plain,
% 0.38/0.62      (![X33 : $i, X34 : $i]:
% 0.38/0.62         ((v1_funct_1 @ (k2_funct_2 @ X33 @ X34))
% 0.38/0.62          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))
% 0.38/0.62          | ~ (v3_funct_2 @ X34 @ X33 @ X33)
% 0.38/0.62          | ~ (v1_funct_2 @ X34 @ X33 @ X33)
% 0.38/0.62          | ~ (v1_funct_1 @ X34))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.38/0.62  thf('40', plain,
% 0.38/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.38/0.62        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.38/0.62        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.38/0.62        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_C)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['38', '39'])).
% 0.38/0.62  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('42', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('43', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('44', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_C))),
% 0.38/0.62      inference('demod', [status(thm)], ['40', '41', '42', '43'])).
% 0.38/0.62  thf('45', plain, (((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.38/0.62      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.38/0.62  thf('46', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.38/0.62      inference('demod', [status(thm)], ['44', '45'])).
% 0.38/0.62  thf('47', plain, ((v2_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A)),
% 0.38/0.62      inference('demod', [status(thm)], ['29', '37', '46'])).
% 0.38/0.62  thf(d3_funct_2, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.38/0.62       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.38/0.62  thf('48', plain,
% 0.38/0.62      (![X31 : $i, X32 : $i]:
% 0.38/0.62         (~ (v2_funct_2 @ X32 @ X31)
% 0.38/0.62          | ((k2_relat_1 @ X32) = (X31))
% 0.38/0.62          | ~ (v5_relat_1 @ X32 @ X31)
% 0.38/0.62          | ~ (v1_relat_1 @ X32))),
% 0.38/0.62      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.38/0.62  thf('49', plain,
% 0.38/0.62      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.62        | ~ (v5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)
% 0.38/0.62        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['47', '48'])).
% 0.38/0.62  thf('50', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.38/0.62      inference('demod', [status(thm)], ['21', '22'])).
% 0.38/0.62  thf('51', plain,
% 0.38/0.62      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.38/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.62      inference('demod', [status(thm)], ['3', '4', '5', '6', '13'])).
% 0.38/0.62  thf('52', plain,
% 0.38/0.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.62         ((v5_relat_1 @ X17 @ X19)
% 0.38/0.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.38/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.62  thf('53', plain, ((v5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)),
% 0.38/0.62      inference('sup-', [status(thm)], ['51', '52'])).
% 0.38/0.62  thf('54', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['49', '50', '53'])).
% 0.38/0.62  thf('55', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('56', plain,
% 0.38/0.62      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.38/0.62         (~ (v1_funct_1 @ X28)
% 0.38/0.62          | ~ (v3_funct_2 @ X28 @ X29 @ X30)
% 0.38/0.62          | (v2_funct_2 @ X28 @ X30)
% 0.38/0.62          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.38/0.62      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.38/0.62  thf('57', plain,
% 0.38/0.62      (((v2_funct_2 @ sk_C @ sk_A)
% 0.38/0.62        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.38/0.62        | ~ (v1_funct_1 @ sk_C))),
% 0.38/0.62      inference('sup-', [status(thm)], ['55', '56'])).
% 0.38/0.62  thf('58', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('59', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('60', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 0.38/0.62      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.38/0.62  thf('61', plain,
% 0.38/0.62      (![X31 : $i, X32 : $i]:
% 0.38/0.62         (~ (v2_funct_2 @ X32 @ X31)
% 0.38/0.62          | ((k2_relat_1 @ X32) = (X31))
% 0.38/0.62          | ~ (v5_relat_1 @ X32 @ X31)
% 0.38/0.62          | ~ (v1_relat_1 @ X32))),
% 0.38/0.62      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.38/0.62  thf('62', plain,
% 0.38/0.62      ((~ (v1_relat_1 @ sk_C)
% 0.38/0.62        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 0.38/0.62        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['60', '61'])).
% 0.38/0.62  thf('63', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('64', plain,
% 0.38/0.62      (![X3 : $i, X4 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.38/0.62          | (v1_relat_1 @ X3)
% 0.38/0.62          | ~ (v1_relat_1 @ X4))),
% 0.38/0.62      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.38/0.62  thf('65', plain,
% 0.38/0.62      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.38/0.62      inference('sup-', [status(thm)], ['63', '64'])).
% 0.38/0.62  thf('66', plain,
% 0.38/0.62      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.38/0.62      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.38/0.62  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.62      inference('demod', [status(thm)], ['65', '66'])).
% 0.38/0.62  thf('68', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('69', plain,
% 0.38/0.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.62         ((v5_relat_1 @ X17 @ X19)
% 0.38/0.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.38/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.62  thf('70', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.38/0.62      inference('sup-', [status(thm)], ['68', '69'])).
% 0.38/0.62  thf('71', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['62', '67', '70'])).
% 0.38/0.62  thf(d10_xboole_0, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.62  thf('72', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.38/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.62  thf('73', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.38/0.62      inference('simplify', [status(thm)], ['72'])).
% 0.38/0.62  thf(t147_funct_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.62       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.38/0.62         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.38/0.62  thf('74', plain,
% 0.38/0.62      (![X11 : $i, X12 : $i]:
% 0.38/0.62         (~ (r1_tarski @ X11 @ (k2_relat_1 @ X12))
% 0.38/0.62          | ((k9_relat_1 @ X12 @ (k10_relat_1 @ X12 @ X11)) = (X11))
% 0.38/0.62          | ~ (v1_funct_1 @ X12)
% 0.38/0.62          | ~ (v1_relat_1 @ X12))),
% 0.38/0.62      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.38/0.62  thf('75', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.38/0.62              = (k2_relat_1 @ X0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['73', '74'])).
% 0.38/0.62  thf('76', plain,
% 0.38/0.62      ((((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A))
% 0.38/0.62          = (k2_relat_1 @ sk_C))
% 0.38/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.62        | ~ (v1_relat_1 @ sk_C))),
% 0.38/0.62      inference('sup+', [status(thm)], ['71', '75'])).
% 0.38/0.62  thf('77', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['62', '67', '70'])).
% 0.38/0.62  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('79', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.62      inference('demod', [status(thm)], ['65', '66'])).
% 0.38/0.62  thf('80', plain,
% 0.38/0.62      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A)) = (sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['76', '77', '78', '79'])).
% 0.38/0.62  thf('81', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['62', '67', '70'])).
% 0.38/0.62  thf(t3_funct_2, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.62       ( ( v1_funct_1 @ A ) & 
% 0.38/0.62         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.38/0.62         ( m1_subset_1 @
% 0.38/0.62           A @ 
% 0.38/0.62           ( k1_zfmisc_1 @
% 0.38/0.62             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.38/0.62  thf('82', plain,
% 0.38/0.62      (![X37 : $i]:
% 0.38/0.62         ((m1_subset_1 @ X37 @ 
% 0.38/0.62           (k1_zfmisc_1 @ 
% 0.38/0.62            (k2_zfmisc_1 @ (k1_relat_1 @ X37) @ (k2_relat_1 @ X37))))
% 0.38/0.62          | ~ (v1_funct_1 @ X37)
% 0.38/0.62          | ~ (v1_relat_1 @ X37))),
% 0.38/0.62      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.38/0.62  thf('83', plain,
% 0.38/0.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.62         ((v4_relat_1 @ X17 @ X18)
% 0.38/0.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.38/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.62  thf('84', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['82', '83'])).
% 0.38/0.62  thf('85', plain,
% 0.38/0.62      (![X9 : $i, X10 : $i]:
% 0.38/0.62         (((X9) = (k7_relat_1 @ X9 @ X10))
% 0.38/0.62          | ~ (v4_relat_1 @ X9 @ X10)
% 0.38/0.62          | ~ (v1_relat_1 @ X9))),
% 0.38/0.62      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.38/0.62  thf('86', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | ((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['84', '85'])).
% 0.38/0.62  thf('87', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0))),
% 0.38/0.62      inference('simplify', [status(thm)], ['86'])).
% 0.38/0.62  thf('88', plain,
% 0.38/0.62      (![X7 : $i, X8 : $i]:
% 0.38/0.62         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 0.38/0.62          | ~ (v1_relat_1 @ X7))),
% 0.38/0.62      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.38/0.62  thf('89', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['87', '88'])).
% 0.38/0.62  thf('90', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.38/0.62      inference('simplify', [status(thm)], ['89'])).
% 0.38/0.62  thf('91', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.38/0.62      inference('simplify', [status(thm)], ['72'])).
% 0.38/0.62  thf(t164_funct_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.62       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.38/0.62         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.38/0.62  thf('92', plain,
% 0.38/0.62      (![X13 : $i, X14 : $i]:
% 0.38/0.62         (~ (r1_tarski @ X13 @ (k1_relat_1 @ X14))
% 0.38/0.62          | ~ (v2_funct_1 @ X14)
% 0.38/0.62          | ((k10_relat_1 @ X14 @ (k9_relat_1 @ X14 @ X13)) = (X13))
% 0.38/0.62          | ~ (v1_funct_1 @ X14)
% 0.38/0.62          | ~ (v1_relat_1 @ X14))),
% 0.38/0.62      inference('cnf', [status(esa)], [t164_funct_1])).
% 0.38/0.62  thf('93', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ((k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.38/0.62              = (k1_relat_1 @ X0))
% 0.38/0.62          | ~ (v2_funct_1 @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['91', '92'])).
% 0.38/0.62  thf('94', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (((k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) = (k1_relat_1 @ X0))
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v2_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['90', '93'])).
% 0.38/0.62  thf('95', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v2_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ((k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) = (k1_relat_1 @ X0)))),
% 0.38/0.62      inference('simplify', [status(thm)], ['94'])).
% 0.38/0.62  thf('96', plain,
% 0.38/0.62      ((((k10_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_C))
% 0.38/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.38/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.38/0.62      inference('sup+', [status(thm)], ['81', '95'])).
% 0.38/0.62  thf('97', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('98', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.62      inference('demod', [status(thm)], ['65', '66'])).
% 0.38/0.62  thf('99', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('100', plain,
% 0.38/0.62      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.38/0.62         (~ (v1_funct_1 @ X28)
% 0.38/0.62          | ~ (v3_funct_2 @ X28 @ X29 @ X30)
% 0.38/0.62          | (v2_funct_1 @ X28)
% 0.38/0.62          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.38/0.62      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.38/0.62  thf('101', plain,
% 0.38/0.62      (((v2_funct_1 @ sk_C)
% 0.38/0.62        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.38/0.62        | ~ (v1_funct_1 @ sk_C))),
% 0.38/0.62      inference('sup-', [status(thm)], ['99', '100'])).
% 0.38/0.62  thf('102', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('103', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('104', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.62      inference('demod', [status(thm)], ['101', '102', '103'])).
% 0.38/0.62  thf('105', plain, (((k10_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.38/0.62      inference('demod', [status(thm)], ['96', '97', '98', '104'])).
% 0.38/0.62  thf('106', plain, (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) = (sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['80', '105'])).
% 0.38/0.62  thf('107', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.38/0.62      inference('simplify', [status(thm)], ['72'])).
% 0.38/0.62  thf(t177_funct_1, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.62       ( ![B:$i]:
% 0.38/0.62         ( ( ( v2_funct_1 @ A ) & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.38/0.62           ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) ) =
% 0.38/0.62             ( B ) ) ) ) ))).
% 0.38/0.62  thf('108', plain,
% 0.38/0.62      (![X15 : $i, X16 : $i]:
% 0.38/0.62         (~ (r1_tarski @ X15 @ (k1_relat_1 @ X16))
% 0.38/0.62          | ((k9_relat_1 @ (k2_funct_1 @ X16) @ (k9_relat_1 @ X16 @ X15))
% 0.38/0.62              = (X15))
% 0.38/0.62          | ~ (v2_funct_1 @ X16)
% 0.38/0.62          | ~ (v1_funct_1 @ X16)
% 0.38/0.62          | ~ (v1_relat_1 @ X16))),
% 0.38/0.62      inference('cnf', [status(esa)], [t177_funct_1])).
% 0.38/0.62  thf('109', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v2_funct_1 @ X0)
% 0.38/0.62          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ 
% 0.38/0.62              (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))) = (k1_relat_1 @ X0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['107', '108'])).
% 0.38/0.62  thf('110', plain,
% 0.38/0.62      ((((k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A) = (k1_relat_1 @ sk_C))
% 0.38/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.38/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.62        | ~ (v1_relat_1 @ sk_C))),
% 0.38/0.62      inference('sup+', [status(thm)], ['106', '109'])).
% 0.38/0.62  thf('111', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.62      inference('demod', [status(thm)], ['101', '102', '103'])).
% 0.38/0.62  thf('112', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('113', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.62      inference('demod', [status(thm)], ['65', '66'])).
% 0.38/0.62  thf('114', plain,
% 0.38/0.62      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.38/0.62      inference('demod', [status(thm)], ['110', '111', '112', '113'])).
% 0.38/0.62  thf('115', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.38/0.62      inference('demod', [status(thm)], ['21', '22'])).
% 0.38/0.62  thf('116', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.38/0.62      inference('demod', [status(thm)], ['26', '54', '114', '115'])).
% 0.38/0.62  thf('117', plain,
% 0.38/0.62      (![X13 : $i, X14 : $i]:
% 0.38/0.62         (~ (r1_tarski @ X13 @ (k1_relat_1 @ X14))
% 0.38/0.62          | ~ (v2_funct_1 @ X14)
% 0.38/0.62          | ((k10_relat_1 @ X14 @ (k9_relat_1 @ X14 @ X13)) = (X13))
% 0.38/0.62          | ~ (v1_funct_1 @ X14)
% 0.38/0.62          | ~ (v1_relat_1 @ X14))),
% 0.38/0.62      inference('cnf', [status(esa)], [t164_funct_1])).
% 0.38/0.62  thf('118', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (r1_tarski @ X0 @ sk_A)
% 0.38/0.62          | ~ (v1_relat_1 @ sk_C)
% 0.38/0.62          | ~ (v1_funct_1 @ sk_C)
% 0.38/0.62          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0))
% 0.38/0.62          | ~ (v2_funct_1 @ sk_C))),
% 0.38/0.62      inference('sup-', [status(thm)], ['116', '117'])).
% 0.38/0.62  thf('119', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.62      inference('demod', [status(thm)], ['65', '66'])).
% 0.38/0.62  thf('120', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('121', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.62      inference('demod', [status(thm)], ['101', '102', '103'])).
% 0.38/0.62  thf('122', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (r1_tarski @ X0 @ sk_A)
% 0.38/0.62          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.38/0.62      inference('demod', [status(thm)], ['118', '119', '120', '121'])).
% 0.38/0.62  thf('123', plain,
% 0.38/0.62      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) = (sk_B))),
% 0.38/0.62      inference('sup-', [status(thm)], ['0', '122'])).
% 0.38/0.62  thf('124', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(redefinition_k8_relset_1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.62       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.38/0.62  thf('125', plain,
% 0.38/0.62      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.38/0.62          | ((k8_relset_1 @ X25 @ X26 @ X24 @ X27) = (k10_relat_1 @ X24 @ X27)))),
% 0.38/0.62      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.38/0.62  thf('126', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['124', '125'])).
% 0.38/0.62  thf('127', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(redefinition_k7_relset_1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.62       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.38/0.62  thf('128', plain,
% 0.38/0.62      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.38/0.62          | ((k7_relset_1 @ X21 @ X22 @ X20 @ X23) = (k9_relat_1 @ X20 @ X23)))),
% 0.38/0.62      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.38/0.62  thf('129', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['127', '128'])).
% 0.38/0.62  thf('130', plain,
% 0.38/0.62      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.38/0.62          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B))
% 0.38/0.62        | ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.38/0.62            (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('131', plain,
% 0.38/0.62      ((((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.38/0.62          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))
% 0.38/0.62         <= (~
% 0.38/0.62             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.38/0.62                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.38/0.62      inference('split', [status(esa)], ['130'])).
% 0.38/0.62  thf('132', plain,
% 0.38/0.62      ((((k8_relset_1 @ sk_A @ sk_A @ sk_C @ (k9_relat_1 @ sk_C @ sk_B))
% 0.38/0.62          != (sk_B)))
% 0.38/0.62         <= (~
% 0.38/0.62             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.38/0.62                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['129', '131'])).
% 0.38/0.62  thf('133', plain,
% 0.38/0.62      ((((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) != (sk_B)))
% 0.38/0.62         <= (~
% 0.38/0.62             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.38/0.62                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['126', '132'])).
% 0.38/0.62  thf('134', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['124', '125'])).
% 0.38/0.62  thf('135', plain,
% 0.38/0.62      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.38/0.62          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))
% 0.38/0.62         <= (~
% 0.38/0.62             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.38/0.62                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.38/0.62      inference('split', [status(esa)], ['130'])).
% 0.38/0.62  thf('136', plain,
% 0.38/0.62      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ (k10_relat_1 @ sk_C @ sk_B))
% 0.38/0.62          != (sk_B)))
% 0.38/0.62         <= (~
% 0.38/0.62             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.38/0.62                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['134', '135'])).
% 0.38/0.62  thf('137', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['127', '128'])).
% 0.38/0.62  thf('138', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('139', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['62', '67', '70'])).
% 0.38/0.62  thf('140', plain,
% 0.38/0.62      (![X11 : $i, X12 : $i]:
% 0.38/0.62         (~ (r1_tarski @ X11 @ (k2_relat_1 @ X12))
% 0.38/0.62          | ((k9_relat_1 @ X12 @ (k10_relat_1 @ X12 @ X11)) = (X11))
% 0.38/0.62          | ~ (v1_funct_1 @ X12)
% 0.38/0.62          | ~ (v1_relat_1 @ X12))),
% 0.38/0.62      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.38/0.62  thf('141', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (r1_tarski @ X0 @ sk_A)
% 0.38/0.62          | ~ (v1_relat_1 @ sk_C)
% 0.38/0.62          | ~ (v1_funct_1 @ sk_C)
% 0.38/0.62          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['139', '140'])).
% 0.38/0.62  thf('142', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.62      inference('demod', [status(thm)], ['65', '66'])).
% 0.38/0.62  thf('143', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('144', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (r1_tarski @ X0 @ sk_A)
% 0.38/0.62          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.38/0.62      inference('demod', [status(thm)], ['141', '142', '143'])).
% 0.38/0.62  thf('145', plain,
% 0.38/0.62      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)) = (sk_B))),
% 0.38/0.62      inference('sup-', [status(thm)], ['138', '144'])).
% 0.38/0.62  thf('146', plain,
% 0.38/0.62      ((((sk_B) != (sk_B)))
% 0.38/0.62         <= (~
% 0.38/0.62             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.38/0.62                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.38/0.62      inference('demod', [status(thm)], ['136', '137', '145'])).
% 0.38/0.62  thf('147', plain,
% 0.38/0.62      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.38/0.62          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.38/0.62      inference('simplify', [status(thm)], ['146'])).
% 0.38/0.62  thf('148', plain,
% 0.38/0.62      (~
% 0.38/0.62       (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.38/0.62          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))) | 
% 0.38/0.62       ~
% 0.38/0.62       (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.38/0.62          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.38/0.62      inference('split', [status(esa)], ['130'])).
% 0.38/0.62  thf('149', plain,
% 0.38/0.62      (~
% 0.38/0.62       (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.38/0.62          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.38/0.62      inference('sat_resolution*', [status(thm)], ['147', '148'])).
% 0.38/0.62  thf('150', plain,
% 0.38/0.62      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) != (sk_B))),
% 0.38/0.62      inference('simpl_trail', [status(thm)], ['133', '149'])).
% 0.38/0.62  thf('151', plain, ($false),
% 0.38/0.62      inference('simplify_reflect-', [status(thm)], ['123', '150'])).
% 0.38/0.62  
% 0.38/0.62  % SZS output end Refutation
% 0.38/0.62  
% 0.38/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
