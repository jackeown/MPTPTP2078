%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.COHZ1ckPfZ

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:26 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  224 ( 957 expanded)
%              Number of leaves         :   41 ( 306 expanded)
%              Depth                    :   26
%              Number of atoms          : 1800 (18027 expanded)
%              Number of equality atoms :   96 ( 762 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

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
    ! [X38: $i,X39: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X38 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) )
      | ~ ( v3_funct_2 @ X39 @ X38 @ X38 )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X38 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
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
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_2 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('11',plain,(
    v1_relat_1 @ ( k2_funct_2 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k2_funct_2 @ X41 @ X40 )
        = ( k2_funct_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) )
      | ~ ( v3_funct_2 @ X40 @ X41 @ X41 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X41 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k2_funct_2 @ sk_A @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('19',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['11','18'])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('20',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k10_relat_1 @ X18 @ X19 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X18 ) @ X19 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('21',plain,(
    ! [X11: $i] :
      ( ( ( k9_relat_1 @ X11 @ ( k1_relat_1 @ X11 ) )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('25',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v3_funct_2 @ X33 @ X34 @ X35 )
      | ( v2_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('26',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['23','29','30','35'])).

thf('37',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('38',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v3_funct_2 @ X33 @ X34 @ X35 )
      | ( v2_funct_2 @ X33 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('39',plain,
    ( ( v2_funct_2 @ ( k2_funct_2 @ sk_A @ sk_C ) @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_C ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X38: $i,X39: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X38 @ X39 ) @ X38 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) )
      | ~ ( v3_funct_2 @ X39 @ X38 @ X38 )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X38 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('42',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_C ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_C ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X38: $i,X39: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X38 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) )
      | ~ ( v3_funct_2 @ X39 @ X38 @ X38 )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X38 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('49',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('54',plain,(
    v2_funct_2 @ ( k2_funct_2 @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['39','46','53'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('55',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v2_funct_2 @ X37 @ X36 )
      | ( ( k2_relat_1 @ X37 )
        = X36 )
      | ~ ( v5_relat_1 @ X37 @ X36 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('56',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_2 @ sk_A @ sk_C ) )
    | ~ ( v5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_C ) @ sk_A )
    | ( ( k2_relat_1 @ ( k2_funct_2 @ sk_A @ sk_C ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ ( k2_funct_2 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('58',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('59',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v5_relat_1 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('60',plain,(
    v5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k2_relat_1 @ ( k2_funct_2 @ sk_A @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['56','57','60'])).

thf('62',plain,
    ( ( k2_funct_2 @ sk_A @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('63',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['36','63'])).

thf('65',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('66',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('67',plain,(
    v4_relat_1 @ ( k2_funct_2 @ sk_A @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k2_funct_2 @ sk_A @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('69',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['67','68'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('70',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('71',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['11','18'])).

thf('73',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v3_funct_2 @ X33 @ X34 @ X35 )
      | ( v2_funct_2 @ X33 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('76',plain,
    ( ( v2_funct_2 @ sk_C @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_funct_2 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v2_funct_2 @ X37 @ X36 )
      | ( ( k2_relat_1 @ X37 )
        = X36 )
      | ~ ( v5_relat_1 @ X37 @ X36 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('81',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v5_relat_1 @ sk_C @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['33','34'])).

thf('83',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v5_relat_1 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('85',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['81','82','85'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('87',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X16 @ ( k2_relat_1 @ X17 ) )
      | ( ( k9_relat_1 @ X17 @ ( k10_relat_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['33','34'])).

thf('90',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['73','91'])).

thf('93',plain,
    ( ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['36','63'])).

thf('94',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X11: $i] :
      ( ( ( k9_relat_1 @ X11 @ ( k1_relat_1 @ X11 ) )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('98',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('100',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['33','34'])).

thf('102',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['100','101'])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('103',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X14 )
      | ( r1_tarski @ ( k9_relat_1 @ X14 @ X12 ) @ ( k9_relat_1 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_C ) ) @ ( k9_relat_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['95','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['33','34'])).

thf('107',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['33','34'])).

thf('108',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('109',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X9 @ X10 ) @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('110',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['33','34'])).

thf('114',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['81','82','85'])).

thf('116',plain,
    ( sk_A
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['94','116'])).

thf('118',plain,
    ( ( k10_relat_1 @ sk_C @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['64','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('120',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X16 @ ( k2_relat_1 @ X17 ) )
      | ( ( k9_relat_1 @ X17 @ ( k10_relat_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X11: $i] :
      ( ( ( k9_relat_1 @ X11 @ ( k1_relat_1 @ X11 ) )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('124',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_C ) ) @ ( k9_relat_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('126',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['33','34'])).

thf('128',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X16 @ ( k2_relat_1 @ X17 ) )
      | ( ( k9_relat_1 @ X17 @ ( k10_relat_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('130',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) )
      = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['33','34'])).

thf('132',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
      = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['123','133'])).

thf('135',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['33','34'])).

thf('136',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['122','136'])).

thf('138',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['33','34'])).

thf('140',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['137','138','139'])).

thf('141',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['119'])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('142',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k1_relat_1 @ X21 ) )
      | ~ ( v2_funct_1 @ X21 )
      | ( ( k10_relat_1 @ X21 @ ( k9_relat_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['140','143'])).

thf('145',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('146',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['33','34'])).

thf('148',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['144','145','146','147'])).

thf('149',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['81','82','85'])).

thf('150',plain,
    ( ( k10_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['118','150'])).

thf('152',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k1_relat_1 @ X21 ) )
      | ~ ( v2_funct_1 @ X21 )
      | ( ( k10_relat_1 @ X21 @ ( k9_relat_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['33','34'])).

thf('155',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['153','154','155','156'])).

thf('158',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','157'])).

thf('159',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
    | ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['159'])).

thf('161',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('162',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k7_relset_1 @ X26 @ X27 @ X25 @ X28 )
        = ( k9_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('165',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k8_relset_1 @ X30 @ X31 @ X29 @ X32 )
        = ( k10_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(demod,[status(thm)],['160','163','166'])).

thf('168',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('170',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('173',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['159'])).

thf('174',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['171','174'])).

thf('176',plain,
    ( ( sk_B != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['170','175'])).

thf('177',plain,
    ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
    = sk_B ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
    | ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['159'])).

thf('179',plain,(
    ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['177','178'])).

thf('180',plain,(
    ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['167','179'])).

thf('181',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['158','180'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.COHZ1ckPfZ
% 0.13/0.37  % Computer   : n009.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 12:21:41 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.54/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.74  % Solved by: fo/fo7.sh
% 0.54/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.74  % done 411 iterations in 0.250s
% 0.54/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.74  % SZS output start Refutation
% 0.54/0.74  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.54/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.54/0.74  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.54/0.74  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.74  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.54/0.74  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.54/0.74  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.54/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.54/0.74  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.54/0.74  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.54/0.74  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.54/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.74  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.54/0.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.74  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.54/0.74  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.54/0.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.74  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.54/0.74  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.54/0.74  thf(t92_funct_2, conjecture,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.54/0.74         ( v3_funct_2 @ C @ A @ A ) & 
% 0.54/0.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.54/0.74       ( ( r1_tarski @ B @ A ) =>
% 0.54/0.74         ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) ) =
% 0.54/0.74             ( B ) ) & 
% 0.54/0.74           ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) ) =
% 0.54/0.74             ( B ) ) ) ) ))).
% 0.54/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.74    (~( ![A:$i,B:$i,C:$i]:
% 0.54/0.74        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.54/0.74            ( v3_funct_2 @ C @ A @ A ) & 
% 0.54/0.74            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.54/0.74          ( ( r1_tarski @ B @ A ) =>
% 0.54/0.74            ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) ) =
% 0.54/0.74                ( B ) ) & 
% 0.54/0.74              ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) ) =
% 0.54/0.74                ( B ) ) ) ) ) )),
% 0.54/0.74    inference('cnf.neg', [status(esa)], [t92_funct_2])).
% 0.54/0.74  thf('0', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('1', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf(dt_k2_funct_2, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.54/0.74         ( v3_funct_2 @ B @ A @ A ) & 
% 0.54/0.74         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.54/0.74       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.54/0.74         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.54/0.74         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.54/0.74         ( m1_subset_1 @
% 0.54/0.74           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.54/0.74  thf('2', plain,
% 0.54/0.74      (![X38 : $i, X39 : $i]:
% 0.54/0.74         ((m1_subset_1 @ (k2_funct_2 @ X38 @ X39) @ 
% 0.54/0.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))
% 0.54/0.74          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))
% 0.54/0.74          | ~ (v3_funct_2 @ X39 @ X38 @ X38)
% 0.54/0.74          | ~ (v1_funct_2 @ X39 @ X38 @ X38)
% 0.54/0.74          | ~ (v1_funct_1 @ X39))),
% 0.54/0.74      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.54/0.74  thf('3', plain,
% 0.54/0.74      ((~ (v1_funct_1 @ sk_C)
% 0.54/0.74        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.54/0.74        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.54/0.74        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_C) @ 
% 0.54/0.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['1', '2'])).
% 0.54/0.74  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('5', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('6', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('7', plain,
% 0.54/0.74      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_C) @ 
% 0.54/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.74      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.54/0.74  thf(cc2_relat_1, axiom,
% 0.54/0.74    (![A:$i]:
% 0.54/0.74     ( ( v1_relat_1 @ A ) =>
% 0.54/0.74       ( ![B:$i]:
% 0.54/0.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.54/0.74  thf('8', plain,
% 0.54/0.74      (![X3 : $i, X4 : $i]:
% 0.54/0.74         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.54/0.74          | (v1_relat_1 @ X3)
% 0.54/0.74          | ~ (v1_relat_1 @ X4))),
% 0.54/0.74      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.54/0.74  thf('9', plain,
% 0.54/0.74      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 0.54/0.74        | (v1_relat_1 @ (k2_funct_2 @ sk_A @ sk_C)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['7', '8'])).
% 0.54/0.74  thf(fc6_relat_1, axiom,
% 0.54/0.74    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.54/0.74  thf('10', plain,
% 0.54/0.74      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.54/0.74      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.54/0.74  thf('11', plain, ((v1_relat_1 @ (k2_funct_2 @ sk_A @ sk_C))),
% 0.54/0.74      inference('demod', [status(thm)], ['9', '10'])).
% 0.54/0.74  thf('12', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf(redefinition_k2_funct_2, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.54/0.74         ( v3_funct_2 @ B @ A @ A ) & 
% 0.54/0.74         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.54/0.74       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.54/0.74  thf('13', plain,
% 0.54/0.74      (![X40 : $i, X41 : $i]:
% 0.54/0.74         (((k2_funct_2 @ X41 @ X40) = (k2_funct_1 @ X40))
% 0.54/0.74          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))
% 0.54/0.74          | ~ (v3_funct_2 @ X40 @ X41 @ X41)
% 0.54/0.74          | ~ (v1_funct_2 @ X40 @ X41 @ X41)
% 0.54/0.74          | ~ (v1_funct_1 @ X40))),
% 0.54/0.74      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.54/0.74  thf('14', plain,
% 0.54/0.74      ((~ (v1_funct_1 @ sk_C)
% 0.54/0.74        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.54/0.74        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.54/0.74        | ((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['12', '13'])).
% 0.54/0.74  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('16', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('17', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('18', plain, (((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.54/0.74      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 0.54/0.74  thf('19', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.54/0.74      inference('demod', [status(thm)], ['11', '18'])).
% 0.54/0.74  thf(t155_funct_1, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.54/0.74       ( ( v2_funct_1 @ B ) =>
% 0.54/0.74         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.54/0.74  thf('20', plain,
% 0.54/0.74      (![X18 : $i, X19 : $i]:
% 0.54/0.74         (~ (v2_funct_1 @ X18)
% 0.54/0.74          | ((k10_relat_1 @ X18 @ X19)
% 0.54/0.74              = (k9_relat_1 @ (k2_funct_1 @ X18) @ X19))
% 0.54/0.74          | ~ (v1_funct_1 @ X18)
% 0.54/0.74          | ~ (v1_relat_1 @ X18))),
% 0.54/0.74      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.54/0.74  thf(t146_relat_1, axiom,
% 0.54/0.74    (![A:$i]:
% 0.54/0.74     ( ( v1_relat_1 @ A ) =>
% 0.54/0.74       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.54/0.74  thf('21', plain,
% 0.54/0.74      (![X11 : $i]:
% 0.54/0.74         (((k9_relat_1 @ X11 @ (k1_relat_1 @ X11)) = (k2_relat_1 @ X11))
% 0.54/0.74          | ~ (v1_relat_1 @ X11))),
% 0.54/0.74      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.54/0.74  thf('22', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.54/0.74            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.54/0.74          | ~ (v1_relat_1 @ X0)
% 0.54/0.74          | ~ (v1_funct_1 @ X0)
% 0.54/0.74          | ~ (v2_funct_1 @ X0)
% 0.54/0.74          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.54/0.74      inference('sup+', [status(thm)], ['20', '21'])).
% 0.54/0.74  thf('23', plain,
% 0.54/0.74      ((~ (v2_funct_1 @ sk_C)
% 0.54/0.74        | ~ (v1_funct_1 @ sk_C)
% 0.54/0.74        | ~ (v1_relat_1 @ sk_C)
% 0.54/0.74        | ((k10_relat_1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.54/0.74            = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['19', '22'])).
% 0.54/0.74  thf('24', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf(cc2_funct_2, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.74       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.54/0.74         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.54/0.74  thf('25', plain,
% 0.54/0.74      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.54/0.74         (~ (v1_funct_1 @ X33)
% 0.54/0.74          | ~ (v3_funct_2 @ X33 @ X34 @ X35)
% 0.54/0.74          | (v2_funct_1 @ X33)
% 0.54/0.74          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.54/0.74      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.54/0.74  thf('26', plain,
% 0.54/0.74      (((v2_funct_1 @ sk_C)
% 0.54/0.74        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.54/0.74        | ~ (v1_funct_1 @ sk_C))),
% 0.54/0.74      inference('sup-', [status(thm)], ['24', '25'])).
% 0.54/0.74  thf('27', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('28', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('29', plain, ((v2_funct_1 @ sk_C)),
% 0.54/0.74      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.54/0.74  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('31', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('32', plain,
% 0.54/0.74      (![X3 : $i, X4 : $i]:
% 0.54/0.74         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.54/0.74          | (v1_relat_1 @ X3)
% 0.54/0.74          | ~ (v1_relat_1 @ X4))),
% 0.54/0.74      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.54/0.74  thf('33', plain,
% 0.54/0.74      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.54/0.74      inference('sup-', [status(thm)], ['31', '32'])).
% 0.54/0.74  thf('34', plain,
% 0.54/0.74      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.54/0.74      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.54/0.74  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.74      inference('demod', [status(thm)], ['33', '34'])).
% 0.54/0.74  thf('36', plain,
% 0.54/0.74      (((k10_relat_1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.54/0.74         = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.54/0.74      inference('demod', [status(thm)], ['23', '29', '30', '35'])).
% 0.54/0.74  thf('37', plain,
% 0.54/0.74      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_C) @ 
% 0.54/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.74      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.54/0.74  thf('38', plain,
% 0.54/0.74      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.54/0.74         (~ (v1_funct_1 @ X33)
% 0.54/0.74          | ~ (v3_funct_2 @ X33 @ X34 @ X35)
% 0.54/0.74          | (v2_funct_2 @ X33 @ X35)
% 0.54/0.74          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.54/0.74      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.54/0.74  thf('39', plain,
% 0.54/0.74      (((v2_funct_2 @ (k2_funct_2 @ sk_A @ sk_C) @ sk_A)
% 0.54/0.74        | ~ (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_C) @ sk_A @ sk_A)
% 0.54/0.74        | ~ (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_C)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['37', '38'])).
% 0.54/0.74  thf('40', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('41', plain,
% 0.54/0.74      (![X38 : $i, X39 : $i]:
% 0.54/0.74         ((v3_funct_2 @ (k2_funct_2 @ X38 @ X39) @ X38 @ X38)
% 0.54/0.74          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))
% 0.54/0.74          | ~ (v3_funct_2 @ X39 @ X38 @ X38)
% 0.54/0.74          | ~ (v1_funct_2 @ X39 @ X38 @ X38)
% 0.54/0.74          | ~ (v1_funct_1 @ X39))),
% 0.54/0.74      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.54/0.74  thf('42', plain,
% 0.54/0.74      ((~ (v1_funct_1 @ sk_C)
% 0.54/0.74        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.54/0.74        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.54/0.74        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_C) @ sk_A @ sk_A))),
% 0.54/0.74      inference('sup-', [status(thm)], ['40', '41'])).
% 0.54/0.74  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('44', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('45', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('46', plain, ((v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_C) @ sk_A @ sk_A)),
% 0.54/0.74      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.54/0.74  thf('47', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('48', plain,
% 0.54/0.74      (![X38 : $i, X39 : $i]:
% 0.54/0.74         ((v1_funct_1 @ (k2_funct_2 @ X38 @ X39))
% 0.54/0.74          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))
% 0.54/0.74          | ~ (v3_funct_2 @ X39 @ X38 @ X38)
% 0.54/0.74          | ~ (v1_funct_2 @ X39 @ X38 @ X38)
% 0.54/0.74          | ~ (v1_funct_1 @ X39))),
% 0.54/0.74      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.54/0.74  thf('49', plain,
% 0.54/0.74      ((~ (v1_funct_1 @ sk_C)
% 0.54/0.74        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.54/0.74        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.54/0.74        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_C)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['47', '48'])).
% 0.54/0.74  thf('50', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('51', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('52', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('53', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_C))),
% 0.54/0.74      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 0.54/0.74  thf('54', plain, ((v2_funct_2 @ (k2_funct_2 @ sk_A @ sk_C) @ sk_A)),
% 0.54/0.74      inference('demod', [status(thm)], ['39', '46', '53'])).
% 0.54/0.74  thf(d3_funct_2, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.54/0.74       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.54/0.74  thf('55', plain,
% 0.54/0.74      (![X36 : $i, X37 : $i]:
% 0.54/0.74         (~ (v2_funct_2 @ X37 @ X36)
% 0.54/0.74          | ((k2_relat_1 @ X37) = (X36))
% 0.54/0.74          | ~ (v5_relat_1 @ X37 @ X36)
% 0.54/0.74          | ~ (v1_relat_1 @ X37))),
% 0.54/0.74      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.54/0.74  thf('56', plain,
% 0.54/0.74      ((~ (v1_relat_1 @ (k2_funct_2 @ sk_A @ sk_C))
% 0.54/0.74        | ~ (v5_relat_1 @ (k2_funct_2 @ sk_A @ sk_C) @ sk_A)
% 0.54/0.74        | ((k2_relat_1 @ (k2_funct_2 @ sk_A @ sk_C)) = (sk_A)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['54', '55'])).
% 0.54/0.74  thf('57', plain, ((v1_relat_1 @ (k2_funct_2 @ sk_A @ sk_C))),
% 0.54/0.74      inference('demod', [status(thm)], ['9', '10'])).
% 0.54/0.74  thf('58', plain,
% 0.54/0.74      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_C) @ 
% 0.54/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.74      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.54/0.74  thf(cc2_relset_1, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.74       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.54/0.74  thf('59', plain,
% 0.54/0.74      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.54/0.74         ((v5_relat_1 @ X22 @ X24)
% 0.54/0.74          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.54/0.74      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.74  thf('60', plain, ((v5_relat_1 @ (k2_funct_2 @ sk_A @ sk_C) @ sk_A)),
% 0.54/0.74      inference('sup-', [status(thm)], ['58', '59'])).
% 0.54/0.74  thf('61', plain, (((k2_relat_1 @ (k2_funct_2 @ sk_A @ sk_C)) = (sk_A))),
% 0.54/0.74      inference('demod', [status(thm)], ['56', '57', '60'])).
% 0.54/0.74  thf('62', plain, (((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.54/0.74      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 0.54/0.74  thf('63', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A))),
% 0.54/0.74      inference('demod', [status(thm)], ['61', '62'])).
% 0.54/0.74  thf('64', plain,
% 0.54/0.74      (((k10_relat_1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ sk_C))) = (sk_A))),
% 0.54/0.74      inference('demod', [status(thm)], ['36', '63'])).
% 0.54/0.74  thf('65', plain,
% 0.54/0.74      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_C) @ 
% 0.54/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.74      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.54/0.74  thf('66', plain,
% 0.54/0.74      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.54/0.74         ((v4_relat_1 @ X22 @ X23)
% 0.54/0.74          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.54/0.74      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.74  thf('67', plain, ((v4_relat_1 @ (k2_funct_2 @ sk_A @ sk_C) @ sk_A)),
% 0.54/0.74      inference('sup-', [status(thm)], ['65', '66'])).
% 0.54/0.74  thf('68', plain, (((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.54/0.74      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 0.54/0.74  thf('69', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)),
% 0.54/0.74      inference('demod', [status(thm)], ['67', '68'])).
% 0.54/0.74  thf(d18_relat_1, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( v1_relat_1 @ B ) =>
% 0.54/0.74       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.54/0.74  thf('70', plain,
% 0.54/0.74      (![X5 : $i, X6 : $i]:
% 0.54/0.74         (~ (v4_relat_1 @ X5 @ X6)
% 0.54/0.74          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 0.54/0.74          | ~ (v1_relat_1 @ X5))),
% 0.54/0.74      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.54/0.74  thf('71', plain,
% 0.54/0.74      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.54/0.74        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))),
% 0.54/0.74      inference('sup-', [status(thm)], ['69', '70'])).
% 0.54/0.74  thf('72', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.54/0.74      inference('demod', [status(thm)], ['11', '18'])).
% 0.54/0.74  thf('73', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)),
% 0.54/0.74      inference('demod', [status(thm)], ['71', '72'])).
% 0.54/0.74  thf('74', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('75', plain,
% 0.54/0.74      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.54/0.74         (~ (v1_funct_1 @ X33)
% 0.54/0.74          | ~ (v3_funct_2 @ X33 @ X34 @ X35)
% 0.54/0.74          | (v2_funct_2 @ X33 @ X35)
% 0.54/0.74          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.54/0.74      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.54/0.74  thf('76', plain,
% 0.54/0.74      (((v2_funct_2 @ sk_C @ sk_A)
% 0.54/0.74        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.54/0.74        | ~ (v1_funct_1 @ sk_C))),
% 0.54/0.74      inference('sup-', [status(thm)], ['74', '75'])).
% 0.54/0.74  thf('77', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('79', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 0.54/0.74      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.54/0.74  thf('80', plain,
% 0.54/0.74      (![X36 : $i, X37 : $i]:
% 0.54/0.74         (~ (v2_funct_2 @ X37 @ X36)
% 0.54/0.74          | ((k2_relat_1 @ X37) = (X36))
% 0.54/0.74          | ~ (v5_relat_1 @ X37 @ X36)
% 0.54/0.74          | ~ (v1_relat_1 @ X37))),
% 0.54/0.74      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.54/0.74  thf('81', plain,
% 0.54/0.74      ((~ (v1_relat_1 @ sk_C)
% 0.54/0.74        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 0.54/0.74        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['79', '80'])).
% 0.54/0.74  thf('82', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.74      inference('demod', [status(thm)], ['33', '34'])).
% 0.54/0.74  thf('83', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('84', plain,
% 0.54/0.74      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.54/0.74         ((v5_relat_1 @ X22 @ X24)
% 0.54/0.74          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.54/0.74      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.74  thf('85', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.54/0.74      inference('sup-', [status(thm)], ['83', '84'])).
% 0.54/0.74  thf('86', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.54/0.74      inference('demod', [status(thm)], ['81', '82', '85'])).
% 0.54/0.74  thf(t147_funct_1, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.54/0.74       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.54/0.74         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.54/0.74  thf('87', plain,
% 0.54/0.74      (![X16 : $i, X17 : $i]:
% 0.54/0.74         (~ (r1_tarski @ X16 @ (k2_relat_1 @ X17))
% 0.54/0.74          | ((k9_relat_1 @ X17 @ (k10_relat_1 @ X17 @ X16)) = (X16))
% 0.54/0.74          | ~ (v1_funct_1 @ X17)
% 0.54/0.74          | ~ (v1_relat_1 @ X17))),
% 0.54/0.74      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.54/0.74  thf('88', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (r1_tarski @ X0 @ sk_A)
% 0.54/0.74          | ~ (v1_relat_1 @ sk_C)
% 0.54/0.74          | ~ (v1_funct_1 @ sk_C)
% 0.54/0.74          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['86', '87'])).
% 0.54/0.74  thf('89', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.74      inference('demod', [status(thm)], ['33', '34'])).
% 0.54/0.74  thf('90', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('91', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (r1_tarski @ X0 @ sk_A)
% 0.54/0.74          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.54/0.74      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.54/0.74  thf('92', plain,
% 0.54/0.74      (((k9_relat_1 @ sk_C @ 
% 0.54/0.74         (k10_relat_1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 0.54/0.74         = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['73', '91'])).
% 0.54/0.74  thf('93', plain,
% 0.54/0.74      (((k10_relat_1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ sk_C))) = (sk_A))),
% 0.54/0.74      inference('demod', [status(thm)], ['36', '63'])).
% 0.54/0.74  thf('94', plain,
% 0.54/0.74      (((k9_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.54/0.74      inference('demod', [status(thm)], ['92', '93'])).
% 0.54/0.74  thf('95', plain,
% 0.54/0.74      (![X11 : $i]:
% 0.54/0.74         (((k9_relat_1 @ X11 @ (k1_relat_1 @ X11)) = (k2_relat_1 @ X11))
% 0.54/0.74          | ~ (v1_relat_1 @ X11))),
% 0.54/0.74      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.54/0.74  thf('96', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('97', plain,
% 0.54/0.74      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.54/0.74         ((v4_relat_1 @ X22 @ X23)
% 0.54/0.74          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.54/0.74      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.74  thf('98', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.54/0.74      inference('sup-', [status(thm)], ['96', '97'])).
% 0.54/0.74  thf('99', plain,
% 0.54/0.74      (![X5 : $i, X6 : $i]:
% 0.54/0.74         (~ (v4_relat_1 @ X5 @ X6)
% 0.54/0.74          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 0.54/0.74          | ~ (v1_relat_1 @ X5))),
% 0.54/0.74      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.54/0.74  thf('100', plain,
% 0.54/0.74      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.54/0.74      inference('sup-', [status(thm)], ['98', '99'])).
% 0.54/0.74  thf('101', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.74      inference('demod', [status(thm)], ['33', '34'])).
% 0.54/0.74  thf('102', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.54/0.74      inference('demod', [status(thm)], ['100', '101'])).
% 0.54/0.74  thf(t156_relat_1, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( v1_relat_1 @ C ) =>
% 0.54/0.74       ( ( r1_tarski @ A @ B ) =>
% 0.54/0.74         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.54/0.74  thf('103', plain,
% 0.54/0.74      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.54/0.74         (~ (r1_tarski @ X12 @ X13)
% 0.54/0.74          | ~ (v1_relat_1 @ X14)
% 0.54/0.74          | (r1_tarski @ (k9_relat_1 @ X14 @ X12) @ (k9_relat_1 @ X14 @ X13)))),
% 0.54/0.74      inference('cnf', [status(esa)], [t156_relat_1])).
% 0.54/0.74  thf('104', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((r1_tarski @ (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_C)) @ 
% 0.54/0.74           (k9_relat_1 @ X0 @ sk_A))
% 0.54/0.74          | ~ (v1_relat_1 @ X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['102', '103'])).
% 0.54/0.74  thf('105', plain,
% 0.54/0.74      (((r1_tarski @ (k2_relat_1 @ sk_C) @ (k9_relat_1 @ sk_C @ sk_A))
% 0.54/0.74        | ~ (v1_relat_1 @ sk_C)
% 0.54/0.74        | ~ (v1_relat_1 @ sk_C))),
% 0.54/0.74      inference('sup+', [status(thm)], ['95', '104'])).
% 0.54/0.74  thf('106', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.74      inference('demod', [status(thm)], ['33', '34'])).
% 0.54/0.74  thf('107', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.74      inference('demod', [status(thm)], ['33', '34'])).
% 0.54/0.74  thf('108', plain,
% 0.54/0.74      ((r1_tarski @ (k2_relat_1 @ sk_C) @ (k9_relat_1 @ sk_C @ sk_A))),
% 0.54/0.74      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.54/0.74  thf(t144_relat_1, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( v1_relat_1 @ B ) =>
% 0.54/0.74       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.54/0.74  thf('109', plain,
% 0.54/0.74      (![X9 : $i, X10 : $i]:
% 0.54/0.74         ((r1_tarski @ (k9_relat_1 @ X9 @ X10) @ (k2_relat_1 @ X9))
% 0.54/0.74          | ~ (v1_relat_1 @ X9))),
% 0.54/0.74      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.54/0.74  thf(d10_xboole_0, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.54/0.74  thf('110', plain,
% 0.54/0.74      (![X0 : $i, X2 : $i]:
% 0.54/0.74         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.54/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.74  thf('111', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         (~ (v1_relat_1 @ X0)
% 0.54/0.74          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ (k9_relat_1 @ X0 @ X1))
% 0.54/0.74          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ X1)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['109', '110'])).
% 0.54/0.74  thf('112', plain,
% 0.54/0.74      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 0.54/0.74        | ~ (v1_relat_1 @ sk_C))),
% 0.54/0.74      inference('sup-', [status(thm)], ['108', '111'])).
% 0.54/0.74  thf('113', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.74      inference('demod', [status(thm)], ['33', '34'])).
% 0.54/0.74  thf('114', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.54/0.74      inference('demod', [status(thm)], ['112', '113'])).
% 0.54/0.74  thf('115', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.54/0.74      inference('demod', [status(thm)], ['81', '82', '85'])).
% 0.54/0.74  thf('116', plain, (((sk_A) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.54/0.74      inference('demod', [status(thm)], ['114', '115'])).
% 0.54/0.74  thf('117', plain, (((sk_A) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.54/0.74      inference('sup+', [status(thm)], ['94', '116'])).
% 0.54/0.74  thf('118', plain, (((k10_relat_1 @ sk_C @ sk_A) = (sk_A))),
% 0.54/0.74      inference('demod', [status(thm)], ['64', '117'])).
% 0.54/0.74  thf('119', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.54/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.74  thf('120', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.54/0.74      inference('simplify', [status(thm)], ['119'])).
% 0.54/0.74  thf('121', plain,
% 0.54/0.74      (![X16 : $i, X17 : $i]:
% 0.54/0.74         (~ (r1_tarski @ X16 @ (k2_relat_1 @ X17))
% 0.54/0.74          | ((k9_relat_1 @ X17 @ (k10_relat_1 @ X17 @ X16)) = (X16))
% 0.54/0.74          | ~ (v1_funct_1 @ X17)
% 0.54/0.74          | ~ (v1_relat_1 @ X17))),
% 0.54/0.74      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.54/0.74  thf('122', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (v1_relat_1 @ X0)
% 0.54/0.74          | ~ (v1_funct_1 @ X0)
% 0.54/0.74          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.54/0.74              = (k2_relat_1 @ X0)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['120', '121'])).
% 0.54/0.74  thf('123', plain,
% 0.54/0.74      (![X11 : $i]:
% 0.54/0.74         (((k9_relat_1 @ X11 @ (k1_relat_1 @ X11)) = (k2_relat_1 @ X11))
% 0.54/0.74          | ~ (v1_relat_1 @ X11))),
% 0.54/0.74      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.54/0.74  thf('124', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.54/0.74      inference('demod', [status(thm)], ['112', '113'])).
% 0.54/0.74  thf('125', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((r1_tarski @ (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_C)) @ 
% 0.54/0.74           (k9_relat_1 @ X0 @ sk_A))
% 0.54/0.74          | ~ (v1_relat_1 @ X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['102', '103'])).
% 0.54/0.74  thf('126', plain,
% 0.54/0.74      (((r1_tarski @ (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) @ 
% 0.54/0.74         (k2_relat_1 @ sk_C))
% 0.54/0.74        | ~ (v1_relat_1 @ sk_C))),
% 0.54/0.74      inference('sup+', [status(thm)], ['124', '125'])).
% 0.54/0.74  thf('127', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.74      inference('demod', [status(thm)], ['33', '34'])).
% 0.54/0.74  thf('128', plain,
% 0.54/0.74      ((r1_tarski @ (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) @ 
% 0.54/0.74        (k2_relat_1 @ sk_C))),
% 0.54/0.74      inference('demod', [status(thm)], ['126', '127'])).
% 0.54/0.74  thf('129', plain,
% 0.54/0.74      (![X16 : $i, X17 : $i]:
% 0.54/0.74         (~ (r1_tarski @ X16 @ (k2_relat_1 @ X17))
% 0.54/0.74          | ((k9_relat_1 @ X17 @ (k10_relat_1 @ X17 @ X16)) = (X16))
% 0.54/0.74          | ~ (v1_funct_1 @ X17)
% 0.54/0.74          | ~ (v1_relat_1 @ X17))),
% 0.54/0.74      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.54/0.74  thf('130', plain,
% 0.54/0.74      ((~ (v1_relat_1 @ sk_C)
% 0.54/0.74        | ~ (v1_funct_1 @ sk_C)
% 0.54/0.74        | ((k9_relat_1 @ sk_C @ 
% 0.54/0.74            (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))
% 0.54/0.74            = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['128', '129'])).
% 0.54/0.74  thf('131', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.74      inference('demod', [status(thm)], ['33', '34'])).
% 0.54/0.74  thf('132', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('133', plain,
% 0.54/0.74      (((k9_relat_1 @ sk_C @ 
% 0.54/0.74         (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))
% 0.54/0.74         = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.54/0.74      inference('demod', [status(thm)], ['130', '131', '132'])).
% 0.54/0.74  thf('134', plain,
% 0.54/0.74      ((((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.54/0.74          = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 0.54/0.74        | ~ (v1_relat_1 @ sk_C))),
% 0.54/0.74      inference('sup+', [status(thm)], ['123', '133'])).
% 0.54/0.74  thf('135', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.74      inference('demod', [status(thm)], ['33', '34'])).
% 0.54/0.74  thf('136', plain,
% 0.54/0.74      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.54/0.74         = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.54/0.74      inference('demod', [status(thm)], ['134', '135'])).
% 0.54/0.74  thf('137', plain,
% 0.54/0.74      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 0.54/0.74        | ~ (v1_funct_1 @ sk_C)
% 0.54/0.74        | ~ (v1_relat_1 @ sk_C))),
% 0.54/0.74      inference('sup+', [status(thm)], ['122', '136'])).
% 0.54/0.74  thf('138', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('139', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.74      inference('demod', [status(thm)], ['33', '34'])).
% 0.54/0.74  thf('140', plain,
% 0.54/0.74      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.54/0.74      inference('demod', [status(thm)], ['137', '138', '139'])).
% 0.54/0.74  thf('141', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.54/0.74      inference('simplify', [status(thm)], ['119'])).
% 0.54/0.74  thf(t164_funct_1, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.54/0.74       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.54/0.74         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.54/0.74  thf('142', plain,
% 0.54/0.74      (![X20 : $i, X21 : $i]:
% 0.54/0.74         (~ (r1_tarski @ X20 @ (k1_relat_1 @ X21))
% 0.54/0.74          | ~ (v2_funct_1 @ X21)
% 0.54/0.74          | ((k10_relat_1 @ X21 @ (k9_relat_1 @ X21 @ X20)) = (X20))
% 0.54/0.74          | ~ (v1_funct_1 @ X21)
% 0.54/0.74          | ~ (v1_relat_1 @ X21))),
% 0.54/0.74      inference('cnf', [status(esa)], [t164_funct_1])).
% 0.54/0.74  thf('143', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (v1_relat_1 @ X0)
% 0.54/0.74          | ~ (v1_funct_1 @ X0)
% 0.54/0.74          | ((k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.54/0.74              = (k1_relat_1 @ X0))
% 0.54/0.74          | ~ (v2_funct_1 @ X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['141', '142'])).
% 0.54/0.74  thf('144', plain,
% 0.54/0.74      ((((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))
% 0.54/0.74        | ~ (v2_funct_1 @ sk_C)
% 0.54/0.74        | ~ (v1_funct_1 @ sk_C)
% 0.54/0.74        | ~ (v1_relat_1 @ sk_C))),
% 0.54/0.74      inference('sup+', [status(thm)], ['140', '143'])).
% 0.54/0.74  thf('145', plain, ((v2_funct_1 @ sk_C)),
% 0.54/0.74      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.54/0.74  thf('146', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('147', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.74      inference('demod', [status(thm)], ['33', '34'])).
% 0.54/0.74  thf('148', plain,
% 0.54/0.74      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.54/0.74      inference('demod', [status(thm)], ['144', '145', '146', '147'])).
% 0.54/0.74  thf('149', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.54/0.74      inference('demod', [status(thm)], ['81', '82', '85'])).
% 0.54/0.74  thf('150', plain, (((k10_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.54/0.74      inference('demod', [status(thm)], ['148', '149'])).
% 0.54/0.74  thf('151', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.54/0.74      inference('sup+', [status(thm)], ['118', '150'])).
% 0.54/0.74  thf('152', plain,
% 0.54/0.74      (![X20 : $i, X21 : $i]:
% 0.54/0.74         (~ (r1_tarski @ X20 @ (k1_relat_1 @ X21))
% 0.54/0.74          | ~ (v2_funct_1 @ X21)
% 0.54/0.74          | ((k10_relat_1 @ X21 @ (k9_relat_1 @ X21 @ X20)) = (X20))
% 0.54/0.74          | ~ (v1_funct_1 @ X21)
% 0.54/0.74          | ~ (v1_relat_1 @ X21))),
% 0.54/0.74      inference('cnf', [status(esa)], [t164_funct_1])).
% 0.54/0.74  thf('153', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (r1_tarski @ X0 @ sk_A)
% 0.54/0.74          | ~ (v1_relat_1 @ sk_C)
% 0.54/0.74          | ~ (v1_funct_1 @ sk_C)
% 0.54/0.74          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0))
% 0.54/0.74          | ~ (v2_funct_1 @ sk_C))),
% 0.54/0.74      inference('sup-', [status(thm)], ['151', '152'])).
% 0.54/0.74  thf('154', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.74      inference('demod', [status(thm)], ['33', '34'])).
% 0.54/0.74  thf('155', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('156', plain, ((v2_funct_1 @ sk_C)),
% 0.54/0.74      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.54/0.74  thf('157', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (r1_tarski @ X0 @ sk_A)
% 0.54/0.74          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.54/0.74      inference('demod', [status(thm)], ['153', '154', '155', '156'])).
% 0.54/0.74  thf('158', plain,
% 0.54/0.74      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) = (sk_B))),
% 0.54/0.74      inference('sup-', [status(thm)], ['0', '157'])).
% 0.54/0.74  thf('159', plain,
% 0.54/0.74      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.54/0.74          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B))
% 0.54/0.74        | ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.54/0.74            (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('160', plain,
% 0.54/0.74      ((((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.54/0.74          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))
% 0.54/0.74         <= (~
% 0.54/0.74             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.54/0.74                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.54/0.74      inference('split', [status(esa)], ['159'])).
% 0.54/0.74  thf('161', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf(redefinition_k7_relset_1, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.74       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.54/0.74  thf('162', plain,
% 0.54/0.74      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.54/0.74         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.54/0.74          | ((k7_relset_1 @ X26 @ X27 @ X25 @ X28) = (k9_relat_1 @ X25 @ X28)))),
% 0.54/0.74      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.54/0.74  thf('163', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['161', '162'])).
% 0.54/0.74  thf('164', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf(redefinition_k8_relset_1, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.74       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.54/0.74  thf('165', plain,
% 0.54/0.74      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.54/0.74         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.54/0.74          | ((k8_relset_1 @ X30 @ X31 @ X29 @ X32) = (k10_relat_1 @ X29 @ X32)))),
% 0.54/0.74      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.54/0.74  thf('166', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['164', '165'])).
% 0.54/0.74  thf('167', plain,
% 0.54/0.74      ((((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) != (sk_B)))
% 0.54/0.74         <= (~
% 0.54/0.74             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.54/0.74                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.54/0.74      inference('demod', [status(thm)], ['160', '163', '166'])).
% 0.54/0.74  thf('168', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('169', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (r1_tarski @ X0 @ sk_A)
% 0.54/0.74          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.54/0.74      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.54/0.74  thf('170', plain,
% 0.54/0.74      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)) = (sk_B))),
% 0.54/0.74      inference('sup-', [status(thm)], ['168', '169'])).
% 0.54/0.74  thf('171', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['164', '165'])).
% 0.54/0.74  thf('172', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['161', '162'])).
% 0.54/0.74  thf('173', plain,
% 0.54/0.74      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.54/0.74          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))
% 0.54/0.74         <= (~
% 0.54/0.74             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.54/0.74                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.54/0.74      inference('split', [status(esa)], ['159'])).
% 0.54/0.74  thf('174', plain,
% 0.54/0.74      ((((k9_relat_1 @ sk_C @ (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B))
% 0.54/0.74          != (sk_B)))
% 0.54/0.74         <= (~
% 0.54/0.74             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.54/0.74                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['172', '173'])).
% 0.54/0.74  thf('175', plain,
% 0.54/0.74      ((((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)) != (sk_B)))
% 0.54/0.74         <= (~
% 0.54/0.74             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.54/0.74                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['171', '174'])).
% 0.54/0.74  thf('176', plain,
% 0.54/0.74      ((((sk_B) != (sk_B)))
% 0.54/0.74         <= (~
% 0.54/0.74             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.54/0.74                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['170', '175'])).
% 0.54/0.74  thf('177', plain,
% 0.54/0.74      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.54/0.74          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.54/0.74      inference('simplify', [status(thm)], ['176'])).
% 0.54/0.74  thf('178', plain,
% 0.54/0.74      (~
% 0.54/0.74       (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.54/0.74          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))) | 
% 0.54/0.74       ~
% 0.54/0.74       (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.54/0.74          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.54/0.74      inference('split', [status(esa)], ['159'])).
% 0.54/0.74  thf('179', plain,
% 0.54/0.74      (~
% 0.54/0.74       (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.54/0.74          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.54/0.74      inference('sat_resolution*', [status(thm)], ['177', '178'])).
% 0.54/0.74  thf('180', plain,
% 0.54/0.74      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) != (sk_B))),
% 0.54/0.74      inference('simpl_trail', [status(thm)], ['167', '179'])).
% 0.54/0.74  thf('181', plain, ($false),
% 0.54/0.74      inference('simplify_reflect-', [status(thm)], ['158', '180'])).
% 0.54/0.74  
% 0.54/0.74  % SZS output end Refutation
% 0.54/0.74  
% 0.54/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
