%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lHN6S6FBhw

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:27 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  203 ( 771 expanded)
%              Number of leaves         :   41 ( 253 expanded)
%              Depth                    :   18
%              Number of atoms          : 1644 (14261 expanded)
%              Number of equality atoms :   98 ( 647 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

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
    ! [X34: $i,X35: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X34 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) )
      | ~ ( v3_funct_2 @ X35 @ X34 @ X34 )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X34 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
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
    ! [X36: $i,X37: $i] :
      ( ( ( k2_funct_2 @ X37 @ X36 )
        = ( k2_funct_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) )
      | ~ ( v3_funct_2 @ X36 @ X37 @ X37 )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X37 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( X10
        = ( k7_relat_1 @ X10 @ X11 ) )
      | ~ ( v4_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_1 @ X29 )
      | ~ ( v3_funct_2 @ X29 @ X30 @ X31 )
      | ( v2_funct_2 @ X29 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
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
    ! [X34: $i,X35: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X34 @ X35 ) @ X34 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) )
      | ~ ( v3_funct_2 @ X35 @ X34 @ X34 )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X34 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
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
    ! [X34: $i,X35: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) )
      | ~ ( v3_funct_2 @ X35 @ X34 @ X34 )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X34 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ~ ( v2_funct_2 @ X33 @ X32 )
      | ( ( k2_relat_1 @ X33 )
        = X32 )
      | ~ ( v5_relat_1 @ X33 @ X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('57',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10
        = ( k7_relat_1 @ X10 @ X11 ) )
      | ~ ( v4_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('64',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['59','64'])).

thf('66',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('67',plain,(
    ! [X9: $i] :
      ( ( ( k10_relat_1 @ X9 @ ( k2_relat_1 @ X9 ) )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['62','63'])).

thf('71',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['62','63'])).

thf('72',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['59','64'])).

thf('73',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['59','64'])).

thf('74',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('75',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['62','63'])).

thf('77',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['59','64'])).

thf('79',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['69','70','71','72','77','78'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('81',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['80'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('82',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k2_relat_1 @ X13 ) )
      | ( ( k9_relat_1 @ X13 @ ( k10_relat_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['79','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['62','63'])).

thf('87',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_1 @ X29 )
      | ~ ( v3_funct_2 @ X29 @ X30 @ X31 )
      | ( v2_funct_2 @ X29 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('90',plain,
    ( ( v2_funct_2 @ sk_C @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v2_funct_2 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v2_funct_2 @ X33 @ X32 )
      | ( ( k2_relat_1 @ X33 )
        = X32 )
      | ~ ( v5_relat_1 @ X33 @ X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('95',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v5_relat_1 @ sk_C @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['62','63'])).

thf('97',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('99',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['95','96','99'])).

thf('101',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['87','100'])).

thf('102',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['80'])).

thf(t177_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v2_funct_1 @ A )
            & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) )
         => ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) )
            = B ) ) ) )).

thf('103',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X16 @ ( k1_relat_1 @ X17 ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X17 ) @ ( k9_relat_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( v2_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t177_funct_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['101','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_1 @ X29 )
      | ~ ( v3_funct_2 @ X29 @ X30 @ X31 )
      | ( v2_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('108',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['62','63'])).

thf('114',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['105','111','112','113'])).

thf('115',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('116',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['26','54','114','115'])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('117',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X14 @ ( k1_relat_1 @ X15 ) )
      | ~ ( v2_funct_1 @ X15 )
      | ( ( k10_relat_1 @ X15 @ ( k9_relat_1 @ X15 @ X14 ) )
        = X14 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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
    inference(demod,[status(thm)],['62','63'])).

thf('120',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['108','109','110'])).

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
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k8_relset_1 @ X26 @ X27 @ X25 @ X28 )
        = ( k10_relat_1 @ X25 @ X28 ) ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( ( k7_relset_1 @ X22 @ X23 @ X21 @ X24 )
        = ( k9_relat_1 @ X21 @ X24 ) ) ) ),
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
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('140',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('141',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k2_relat_1 @ X13 ) )
      | ( ( k9_relat_1 @ X13 @ ( k10_relat_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C ) )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['139','142'])).

thf('144',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['59','64'])).

thf('145',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['59','64'])).

thf('146',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['59','64'])).

thf('147',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['59','64'])).

thf('149',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['62','63'])).

thf('150',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['62','63'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C ) )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['143','144','145','146','147','148','149','150'])).

thf('152',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['95','96','99'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['138','153'])).

thf('155',plain,
    ( ( sk_B != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(demod,[status(thm)],['136','137','154'])).

thf('156',plain,
    ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
    = sk_B ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
    | ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['130'])).

thf('158',plain,(
    ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['156','157'])).

thf('159',plain,(
    ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['133','158'])).

thf('160',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['123','159'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lHN6S6FBhw
% 0.12/0.35  % Computer   : n024.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 15:24:36 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 195 iterations in 0.180s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.46/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.64  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.46/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.64  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.46/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.64  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.46/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.64  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.46/0.64  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.64  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.46/0.64  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.64  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.46/0.64  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.46/0.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.64  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.64  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.46/0.64  thf(t92_funct_2, conjecture,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.46/0.64         ( v3_funct_2 @ C @ A @ A ) & 
% 0.46/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.46/0.64       ( ( r1_tarski @ B @ A ) =>
% 0.46/0.64         ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) ) =
% 0.46/0.64             ( B ) ) & 
% 0.46/0.64           ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) ) =
% 0.46/0.64             ( B ) ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.64        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.46/0.64            ( v3_funct_2 @ C @ A @ A ) & 
% 0.46/0.64            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.46/0.64          ( ( r1_tarski @ B @ A ) =>
% 0.46/0.64            ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) ) =
% 0.46/0.64                ( B ) ) & 
% 0.46/0.64              ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) ) =
% 0.46/0.64                ( B ) ) ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t92_funct_2])).
% 0.46/0.64  thf('0', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(dt_k2_funct_2, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.46/0.64         ( v3_funct_2 @ B @ A @ A ) & 
% 0.46/0.64         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.46/0.64       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.46/0.64         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.46/0.64         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.46/0.64         ( m1_subset_1 @
% 0.46/0.64           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      (![X34 : $i, X35 : $i]:
% 0.46/0.64         ((m1_subset_1 @ (k2_funct_2 @ X34 @ X35) @ 
% 0.46/0.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))
% 0.46/0.64          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))
% 0.46/0.64          | ~ (v3_funct_2 @ X35 @ X34 @ X34)
% 0.46/0.64          | ~ (v1_funct_2 @ X35 @ X34 @ X34)
% 0.46/0.64          | ~ (v1_funct_1 @ X35))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.46/0.64  thf('3', plain,
% 0.46/0.64      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.46/0.64        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.46/0.64        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_C) @ 
% 0.46/0.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.64  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('5', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('6', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('7', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(redefinition_k2_funct_2, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.46/0.64         ( v3_funct_2 @ B @ A @ A ) & 
% 0.46/0.64         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.46/0.64       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.46/0.64  thf('8', plain,
% 0.46/0.64      (![X36 : $i, X37 : $i]:
% 0.46/0.64         (((k2_funct_2 @ X37 @ X36) = (k2_funct_1 @ X36))
% 0.46/0.64          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))
% 0.46/0.64          | ~ (v3_funct_2 @ X36 @ X37 @ X37)
% 0.46/0.64          | ~ (v1_funct_2 @ X36 @ X37 @ X37)
% 0.46/0.64          | ~ (v1_funct_1 @ X36))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.46/0.64  thf('9', plain,
% 0.46/0.64      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.46/0.64        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.46/0.64        | ((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.64  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('11', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('12', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('13', plain, (((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.46/0.64  thf('14', plain,
% 0.46/0.64      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['3', '4', '5', '6', '13'])).
% 0.46/0.64  thf(cc2_relset_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.64       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.64  thf('15', plain,
% 0.46/0.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.64         ((v4_relat_1 @ X18 @ X19)
% 0.46/0.64          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.64  thf('16', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)),
% 0.46/0.64      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.64  thf(t209_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.46/0.64       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.46/0.64  thf('17', plain,
% 0.46/0.64      (![X10 : $i, X11 : $i]:
% 0.46/0.64         (((X10) = (k7_relat_1 @ X10 @ X11))
% 0.46/0.64          | ~ (v4_relat_1 @ X10 @ X11)
% 0.46/0.64          | ~ (v1_relat_1 @ X10))),
% 0.46/0.64      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ((k2_funct_1 @ sk_C) = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.64  thf('19', plain,
% 0.46/0.64      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['3', '4', '5', '6', '13'])).
% 0.46/0.64  thf(cc2_relat_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ A ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.46/0.64  thf('20', plain,
% 0.46/0.64      (![X3 : $i, X4 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.46/0.64          | (v1_relat_1 @ X3)
% 0.46/0.64          | ~ (v1_relat_1 @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.46/0.64  thf('21', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 0.46/0.64        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.64  thf(fc6_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.64  thf('23', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['21', '22'])).
% 0.46/0.64  thf('24', plain,
% 0.46/0.64      (((k2_funct_1 @ sk_C) = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['18', '23'])).
% 0.46/0.64  thf(t148_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ B ) =>
% 0.46/0.64       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      (![X7 : $i, X8 : $i]:
% 0.46/0.64         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 0.46/0.64          | ~ (v1_relat_1 @ X7))),
% 0.46/0.64      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.46/0.64  thf('26', plain,
% 0.46/0.64      ((((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64          = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A))
% 0.46/0.64        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['24', '25'])).
% 0.46/0.64  thf('27', plain,
% 0.46/0.64      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['3', '4', '5', '6', '13'])).
% 0.46/0.64  thf(cc2_funct_2, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.64       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.46/0.64         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.46/0.64  thf('28', plain,
% 0.46/0.64      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.64         (~ (v1_funct_1 @ X29)
% 0.46/0.64          | ~ (v3_funct_2 @ X29 @ X30 @ X31)
% 0.46/0.64          | (v2_funct_2 @ X29 @ X31)
% 0.46/0.64          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.46/0.64  thf('29', plain,
% 0.46/0.64      (((v2_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A)
% 0.46/0.64        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_A)
% 0.46/0.64        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['27', '28'])).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('31', plain,
% 0.46/0.64      (![X34 : $i, X35 : $i]:
% 0.46/0.64         ((v3_funct_2 @ (k2_funct_2 @ X34 @ X35) @ X34 @ X34)
% 0.46/0.64          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))
% 0.46/0.64          | ~ (v3_funct_2 @ X35 @ X34 @ X34)
% 0.46/0.64          | ~ (v1_funct_2 @ X35 @ X34 @ X34)
% 0.46/0.64          | ~ (v1_funct_1 @ X35))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.46/0.64        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.46/0.64        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_C) @ sk_A @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.64  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('34', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('35', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('36', plain, (((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.46/0.64  thf('37', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['32', '33', '34', '35', '36'])).
% 0.46/0.64  thf('38', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('39', plain,
% 0.46/0.64      (![X34 : $i, X35 : $i]:
% 0.46/0.64         ((v1_funct_1 @ (k2_funct_2 @ X34 @ X35))
% 0.46/0.64          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))
% 0.46/0.64          | ~ (v3_funct_2 @ X35 @ X34 @ X34)
% 0.46/0.64          | ~ (v1_funct_2 @ X35 @ X34 @ X34)
% 0.46/0.64          | ~ (v1_funct_1 @ X35))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.46/0.64  thf('40', plain,
% 0.46/0.64      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.46/0.64        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.46/0.64        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('42', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('43', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('44', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['40', '41', '42', '43'])).
% 0.46/0.64  thf('45', plain, (((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.46/0.64  thf('46', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['44', '45'])).
% 0.46/0.64  thf('47', plain, ((v2_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['29', '37', '46'])).
% 0.46/0.64  thf(d3_funct_2, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.46/0.64       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.46/0.64  thf('48', plain,
% 0.46/0.64      (![X32 : $i, X33 : $i]:
% 0.46/0.64         (~ (v2_funct_2 @ X33 @ X32)
% 0.46/0.64          | ((k2_relat_1 @ X33) = (X32))
% 0.46/0.64          | ~ (v5_relat_1 @ X33 @ X32)
% 0.46/0.64          | ~ (v1_relat_1 @ X33))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.46/0.64  thf('49', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ~ (v5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)
% 0.46/0.64        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['47', '48'])).
% 0.46/0.64  thf('50', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['21', '22'])).
% 0.46/0.64  thf('51', plain,
% 0.46/0.64      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['3', '4', '5', '6', '13'])).
% 0.46/0.64  thf('52', plain,
% 0.46/0.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.64         ((v5_relat_1 @ X18 @ X20)
% 0.46/0.64          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.64  thf('53', plain, ((v5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)),
% 0.46/0.64      inference('sup-', [status(thm)], ['51', '52'])).
% 0.46/0.64  thf('54', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['49', '50', '53'])).
% 0.46/0.64  thf('55', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('56', plain,
% 0.46/0.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.64         ((v4_relat_1 @ X18 @ X19)
% 0.46/0.64          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.64  thf('57', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.46/0.64      inference('sup-', [status(thm)], ['55', '56'])).
% 0.46/0.64  thf('58', plain,
% 0.46/0.64      (![X10 : $i, X11 : $i]:
% 0.46/0.64         (((X10) = (k7_relat_1 @ X10 @ X11))
% 0.46/0.64          | ~ (v4_relat_1 @ X10 @ X11)
% 0.46/0.64          | ~ (v1_relat_1 @ X10))),
% 0.46/0.64      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.46/0.64  thf('59', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['57', '58'])).
% 0.46/0.64  thf('60', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('61', plain,
% 0.46/0.64      (![X3 : $i, X4 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.46/0.64          | (v1_relat_1 @ X3)
% 0.46/0.64          | ~ (v1_relat_1 @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.46/0.64  thf('62', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['60', '61'])).
% 0.46/0.64  thf('63', plain,
% 0.46/0.64      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.64  thf('64', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['62', '63'])).
% 0.46/0.64  thf('65', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['59', '64'])).
% 0.46/0.64  thf('66', plain,
% 0.46/0.64      (![X7 : $i, X8 : $i]:
% 0.46/0.64         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 0.46/0.64          | ~ (v1_relat_1 @ X7))),
% 0.46/0.64      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.46/0.64  thf(t169_relat_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ A ) =>
% 0.46/0.64       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.46/0.64  thf('67', plain,
% 0.46/0.64      (![X9 : $i]:
% 0.46/0.64         (((k10_relat_1 @ X9 @ (k2_relat_1 @ X9)) = (k1_relat_1 @ X9))
% 0.46/0.64          | ~ (v1_relat_1 @ X9))),
% 0.46/0.64      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.46/0.64  thf('68', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.46/0.64            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.46/0.64          | ~ (v1_relat_1 @ X1)
% 0.46/0.64          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['66', '67'])).
% 0.46/0.64  thf('69', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ 
% 0.46/0.64            (k9_relat_1 @ sk_C @ sk_A))
% 0.46/0.64            = (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['65', '68'])).
% 0.46/0.64  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['62', '63'])).
% 0.46/0.64  thf('71', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['62', '63'])).
% 0.46/0.64  thf('72', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['59', '64'])).
% 0.46/0.64  thf('73', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['59', '64'])).
% 0.46/0.64  thf('74', plain,
% 0.46/0.64      (![X7 : $i, X8 : $i]:
% 0.46/0.64         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 0.46/0.64          | ~ (v1_relat_1 @ X7))),
% 0.46/0.64      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.46/0.64  thf('75', plain,
% 0.46/0.64      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 0.46/0.64        | ~ (v1_relat_1 @ sk_C))),
% 0.46/0.64      inference('sup+', [status(thm)], ['73', '74'])).
% 0.46/0.64  thf('76', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['62', '63'])).
% 0.46/0.64  thf('77', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['75', '76'])).
% 0.46/0.64  thf('78', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['59', '64'])).
% 0.46/0.64  thf('79', plain,
% 0.46/0.64      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['69', '70', '71', '72', '77', '78'])).
% 0.46/0.64  thf(d10_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.64  thf('80', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.64  thf('81', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.46/0.64      inference('simplify', [status(thm)], ['80'])).
% 0.46/0.64  thf(t147_funct_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.64       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.46/0.64         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.46/0.64  thf('82', plain,
% 0.46/0.64      (![X12 : $i, X13 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X12 @ (k2_relat_1 @ X13))
% 0.46/0.64          | ((k9_relat_1 @ X13 @ (k10_relat_1 @ X13 @ X12)) = (X12))
% 0.46/0.64          | ~ (v1_funct_1 @ X13)
% 0.46/0.64          | ~ (v1_relat_1 @ X13))),
% 0.46/0.64      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.46/0.64  thf('83', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.46/0.64              = (k2_relat_1 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['81', '82'])).
% 0.46/0.64  thf('84', plain,
% 0.46/0.64      ((((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v1_relat_1 @ sk_C))),
% 0.46/0.64      inference('sup+', [status(thm)], ['79', '83'])).
% 0.46/0.64  thf('85', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('86', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['62', '63'])).
% 0.46/0.64  thf('87', plain,
% 0.46/0.64      (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.46/0.64  thf('88', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('89', plain,
% 0.46/0.64      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.64         (~ (v1_funct_1 @ X29)
% 0.46/0.64          | ~ (v3_funct_2 @ X29 @ X30 @ X31)
% 0.46/0.64          | (v2_funct_2 @ X29 @ X31)
% 0.46/0.64          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.46/0.64  thf('90', plain,
% 0.46/0.64      (((v2_funct_2 @ sk_C @ sk_A)
% 0.46/0.64        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['88', '89'])).
% 0.46/0.64  thf('91', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('92', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('93', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.46/0.64  thf('94', plain,
% 0.46/0.64      (![X32 : $i, X33 : $i]:
% 0.46/0.64         (~ (v2_funct_2 @ X33 @ X32)
% 0.46/0.64          | ((k2_relat_1 @ X33) = (X32))
% 0.46/0.64          | ~ (v5_relat_1 @ X33 @ X32)
% 0.46/0.64          | ~ (v1_relat_1 @ X33))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.46/0.64  thf('95', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 0.46/0.64        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['93', '94'])).
% 0.46/0.64  thf('96', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['62', '63'])).
% 0.46/0.64  thf('97', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('98', plain,
% 0.46/0.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.64         ((v5_relat_1 @ X18 @ X20)
% 0.46/0.64          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.64  thf('99', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.46/0.64      inference('sup-', [status(thm)], ['97', '98'])).
% 0.46/0.64  thf('100', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['95', '96', '99'])).
% 0.46/0.64  thf('101', plain, (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) = (sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['87', '100'])).
% 0.46/0.64  thf('102', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.46/0.64      inference('simplify', [status(thm)], ['80'])).
% 0.46/0.64  thf(t177_funct_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( ( v2_funct_1 @ A ) & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.46/0.64           ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) ) =
% 0.46/0.64             ( B ) ) ) ) ))).
% 0.46/0.64  thf('103', plain,
% 0.46/0.64      (![X16 : $i, X17 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X16 @ (k1_relat_1 @ X17))
% 0.46/0.64          | ((k9_relat_1 @ (k2_funct_1 @ X17) @ (k9_relat_1 @ X17 @ X16))
% 0.46/0.64              = (X16))
% 0.46/0.64          | ~ (v2_funct_1 @ X17)
% 0.46/0.64          | ~ (v1_funct_1 @ X17)
% 0.46/0.64          | ~ (v1_relat_1 @ X17))),
% 0.46/0.64      inference('cnf', [status(esa)], [t177_funct_1])).
% 0.46/0.64  thf('104', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ 
% 0.46/0.64              (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))) = (k1_relat_1 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['102', '103'])).
% 0.46/0.64  thf('105', plain,
% 0.46/0.64      ((((k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A) = (k1_relat_1 @ sk_C))
% 0.46/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v1_relat_1 @ sk_C))),
% 0.46/0.64      inference('sup+', [status(thm)], ['101', '104'])).
% 0.46/0.64  thf('106', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('107', plain,
% 0.46/0.64      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.64         (~ (v1_funct_1 @ X29)
% 0.46/0.64          | ~ (v3_funct_2 @ X29 @ X30 @ X31)
% 0.46/0.64          | (v2_funct_1 @ X29)
% 0.46/0.64          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.46/0.64  thf('108', plain,
% 0.46/0.64      (((v2_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['106', '107'])).
% 0.46/0.64  thf('109', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('110', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('111', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.46/0.64  thf('112', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('113', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['62', '63'])).
% 0.46/0.64  thf('114', plain,
% 0.46/0.64      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['105', '111', '112', '113'])).
% 0.46/0.64  thf('115', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['21', '22'])).
% 0.46/0.64  thf('116', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['26', '54', '114', '115'])).
% 0.46/0.64  thf(t164_funct_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.64       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.46/0.64         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.46/0.64  thf('117', plain,
% 0.46/0.64      (![X14 : $i, X15 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X14 @ (k1_relat_1 @ X15))
% 0.46/0.64          | ~ (v2_funct_1 @ X15)
% 0.46/0.64          | ((k10_relat_1 @ X15 @ (k9_relat_1 @ X15 @ X14)) = (X14))
% 0.46/0.64          | ~ (v1_funct_1 @ X15)
% 0.46/0.64          | ~ (v1_relat_1 @ X15))),
% 0.46/0.64      inference('cnf', [status(esa)], [t164_funct_1])).
% 0.46/0.64  thf('118', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X0 @ sk_A)
% 0.46/0.64          | ~ (v1_relat_1 @ sk_C)
% 0.46/0.64          | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0))
% 0.46/0.64          | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['116', '117'])).
% 0.46/0.64  thf('119', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['62', '63'])).
% 0.46/0.64  thf('120', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('121', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.46/0.64  thf('122', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X0 @ sk_A)
% 0.46/0.64          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['118', '119', '120', '121'])).
% 0.46/0.64  thf('123', plain,
% 0.46/0.64      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) = (sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['0', '122'])).
% 0.46/0.64  thf('124', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(redefinition_k8_relset_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.64       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.46/0.64  thf('125', plain,
% 0.46/0.64      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.46/0.64          | ((k8_relset_1 @ X26 @ X27 @ X25 @ X28) = (k10_relat_1 @ X25 @ X28)))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.46/0.64  thf('126', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['124', '125'])).
% 0.46/0.64  thf('127', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(redefinition_k7_relset_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.64       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.46/0.64  thf('128', plain,
% 0.46/0.64      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.46/0.64          | ((k7_relset_1 @ X22 @ X23 @ X21 @ X24) = (k9_relat_1 @ X21 @ X24)))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.46/0.64  thf('129', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['127', '128'])).
% 0.46/0.64  thf('130', plain,
% 0.46/0.64      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.46/0.64          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B))
% 0.46/0.64        | ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.46/0.64            (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('131', plain,
% 0.46/0.64      ((((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.46/0.64          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.46/0.64                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.46/0.64      inference('split', [status(esa)], ['130'])).
% 0.46/0.64  thf('132', plain,
% 0.46/0.64      ((((k8_relset_1 @ sk_A @ sk_A @ sk_C @ (k9_relat_1 @ sk_C @ sk_B))
% 0.46/0.64          != (sk_B)))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.46/0.64                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['129', '131'])).
% 0.46/0.64  thf('133', plain,
% 0.46/0.64      ((((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) != (sk_B)))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.46/0.64                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['126', '132'])).
% 0.46/0.64  thf('134', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['124', '125'])).
% 0.46/0.64  thf('135', plain,
% 0.46/0.64      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.46/0.64          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.46/0.64                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.46/0.64      inference('split', [status(esa)], ['130'])).
% 0.46/0.64  thf('136', plain,
% 0.46/0.64      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ (k10_relat_1 @ sk_C @ sk_B))
% 0.46/0.64          != (sk_B)))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.46/0.64                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['134', '135'])).
% 0.46/0.64  thf('137', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['127', '128'])).
% 0.46/0.64  thf('138', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('139', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['75', '76'])).
% 0.46/0.64  thf('140', plain,
% 0.46/0.64      (![X7 : $i, X8 : $i]:
% 0.46/0.64         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 0.46/0.64          | ~ (v1_relat_1 @ X7))),
% 0.46/0.64      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.46/0.64  thf('141', plain,
% 0.46/0.64      (![X12 : $i, X13 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X12 @ (k2_relat_1 @ X13))
% 0.46/0.64          | ((k9_relat_1 @ X13 @ (k10_relat_1 @ X13 @ X12)) = (X12))
% 0.46/0.64          | ~ (v1_funct_1 @ X13)
% 0.46/0.64          | ~ (v1_relat_1 @ X13))),
% 0.46/0.64      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.46/0.64  thf('142', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X2 @ (k9_relat_1 @ X1 @ X0))
% 0.46/0.64          | ~ (v1_relat_1 @ X1)
% 0.46/0.64          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.46/0.64          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 0.46/0.64          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.46/0.64              (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)) = (X2)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['140', '141'])).
% 0.46/0.64  thf('143', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X0 @ (k2_relat_1 @ sk_C))
% 0.46/0.64          | ((k9_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ 
% 0.46/0.64              (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ X0)) = (X0))
% 0.46/0.64          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C @ sk_A))
% 0.46/0.64          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A))
% 0.46/0.64          | ~ (v1_relat_1 @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['139', '142'])).
% 0.46/0.64  thf('144', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['59', '64'])).
% 0.46/0.64  thf('145', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['59', '64'])).
% 0.46/0.64  thf('146', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['59', '64'])).
% 0.46/0.64  thf('147', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('148', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['59', '64'])).
% 0.46/0.64  thf('149', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['62', '63'])).
% 0.46/0.64  thf('150', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['62', '63'])).
% 0.46/0.64  thf('151', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X0 @ (k2_relat_1 @ sk_C))
% 0.46/0.64          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.46/0.64      inference('demod', [status(thm)],
% 0.46/0.64                ['143', '144', '145', '146', '147', '148', '149', '150'])).
% 0.46/0.64  thf('152', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['95', '96', '99'])).
% 0.46/0.64  thf('153', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X0 @ sk_A)
% 0.46/0.64          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['151', '152'])).
% 0.46/0.64  thf('154', plain,
% 0.46/0.64      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)) = (sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['138', '153'])).
% 0.46/0.64  thf('155', plain,
% 0.46/0.64      ((((sk_B) != (sk_B)))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.46/0.64                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.46/0.64      inference('demod', [status(thm)], ['136', '137', '154'])).
% 0.46/0.64  thf('156', plain,
% 0.46/0.64      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.46/0.64          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['155'])).
% 0.46/0.64  thf('157', plain,
% 0.46/0.64      (~
% 0.46/0.64       (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.46/0.64          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))) | 
% 0.46/0.64       ~
% 0.46/0.64       (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.46/0.64          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.46/0.64      inference('split', [status(esa)], ['130'])).
% 0.46/0.64  thf('158', plain,
% 0.46/0.64      (~
% 0.46/0.64       (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.46/0.64          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.46/0.64      inference('sat_resolution*', [status(thm)], ['156', '157'])).
% 0.46/0.64  thf('159', plain,
% 0.46/0.64      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) != (sk_B))),
% 0.46/0.64      inference('simpl_trail', [status(thm)], ['133', '158'])).
% 0.46/0.64  thf('160', plain, ($false),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['123', '159'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
