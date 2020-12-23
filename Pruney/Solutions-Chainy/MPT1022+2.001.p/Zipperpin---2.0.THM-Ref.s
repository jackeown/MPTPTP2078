%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0jkBjKuLfd

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:24 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  209 ( 744 expanded)
%              Number of leaves         :   46 ( 245 expanded)
%              Depth                    :   20
%              Number of atoms          : 1642 (14099 expanded)
%              Number of equality atoms :   91 ( 624 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X41: $i,X42: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X41 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) )
      | ~ ( v3_funct_2 @ X42 @ X41 @ X41 )
      | ~ ( v1_funct_2 @ X42 @ X41 @ X41 )
      | ~ ( v1_funct_1 @ X42 ) ) ),
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
    ! [X43: $i,X44: $i] :
      ( ( ( k2_funct_2 @ X44 @ X43 )
        = ( k2_funct_1 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X44 ) ) )
      | ~ ( v3_funct_2 @ X43 @ X44 @ X44 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X44 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('16',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v4_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k1_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5','6','13'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('20',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('21',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['18','21'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ( ( k7_relat_1 @ X14 @ X15 )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('26',plain,
    ( ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('28',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
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

thf('30',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_1 @ X36 )
      | ~ ( v3_funct_2 @ X36 @ X37 @ X38 )
      | ( v2_funct_2 @ X36 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('31',plain,
    ( ( v2_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X41: $i,X42: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X41 @ X42 ) @ X41 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) )
      | ~ ( v3_funct_2 @ X42 @ X41 @ X41 )
      | ~ ( v1_funct_2 @ X42 @ X41 @ X41 )
      | ~ ( v1_funct_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('34',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_C ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k2_funct_2 @ sk_A @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('39',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['34','35','36','37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X41: $i,X42: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X41 @ X42 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) )
      | ~ ( v3_funct_2 @ X42 @ X41 @ X41 )
      | ~ ( v1_funct_2 @ X42 @ X41 @ X41 )
      | ~ ( v1_funct_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('42',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_C ) ) ),
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
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,
    ( ( k2_funct_2 @ sk_A @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('48',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    v2_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['31','39','48'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('50',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( v2_funct_2 @ X40 @ X39 )
      | ( ( k2_relat_1 @ X40 )
        = X39 )
      | ~ ( v5_relat_1 @ X40 @ X39 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('53',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5','6','13'])).

thf('54',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v5_relat_1 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('55',plain,(
    v5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['51','52','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('59',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v4_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k1_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('63',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('65',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('66',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['61','66'])).

thf('68',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ( ( k7_relat_1 @ X14 @ X15 )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('69',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k7_relat_1 @ sk_C @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['64','65'])).

thf('71',plain,
    ( ( k7_relat_1 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('73',plain,(
    ! [X13: $i] :
      ( ( ( k10_relat_1 @ X13 @ ( k2_relat_1 @ X13 ) )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['64','65'])).

thf('77',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['64','65'])).

thf('78',plain,
    ( ( k7_relat_1 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['69','70'])).

thf('79',plain,
    ( ( k7_relat_1 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['69','70'])).

thf('80',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['75','76','77','78','79'])).

thf('81',plain,
    ( ( k7_relat_1 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['69','70'])).

thf('82',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('83',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['64','65'])).

thf('85',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['80','85'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('87',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('89',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('90',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('91',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('92',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X16 @ ( k2_relat_1 @ X17 ) )
      | ( ( k9_relat_1 @ X17 @ ( k10_relat_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['86','93'])).

thf('95',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['64','65'])).

thf('97',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_1 @ X36 )
      | ~ ( v3_funct_2 @ X36 @ X37 @ X38 )
      | ( v2_funct_2 @ X36 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('100',plain,
    ( ( v2_funct_2 @ sk_C @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v2_funct_2 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( v2_funct_2 @ X40 @ X39 )
      | ( ( k2_relat_1 @ X40 )
        = X39 )
      | ~ ( v5_relat_1 @ X40 @ X39 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('105',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v5_relat_1 @ sk_C @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['64','65'])).

thf('107',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v5_relat_1 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('109',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['105','106','109'])).

thf('111',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['97','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf(t177_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v2_funct_1 @ A )
            & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) )
         => ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) )
            = B ) ) ) )).

thf('113',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k1_relat_1 @ X21 ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X21 ) @ ( k9_relat_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( v2_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t177_funct_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['111','114'])).

thf('116',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_1 @ X36 )
      | ~ ( v3_funct_2 @ X36 @ X37 @ X38 )
      | ( v2_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('118',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('122',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['64','65'])).

thf('124',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['115','121','122','123'])).

thf('125',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('126',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['28','56','124','125'])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('127',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ~ ( v2_funct_1 @ X19 )
      | ( ( k10_relat_1 @ X19 @ ( k9_relat_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['64','65'])).

thf('130',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['128','129','130','131'])).

thf('133',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','132'])).

thf('134',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('135',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k8_relset_1 @ X33 @ X34 @ X32 @ X35 )
        = ( k10_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('138',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k7_relset_1 @ X29 @ X30 @ X28 @ X31 )
        = ( k9_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
    | ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['140'])).

thf('142',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['139','141'])).

thf('143',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['136','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('145',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['140'])).

thf('146',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('148',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['105','106','109'])).

thf('150',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X16 @ ( k2_relat_1 @ X17 ) )
      | ( ( k9_relat_1 @ X17 @ ( k10_relat_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['64','65'])).

thf('153',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['151','152','153'])).

thf('155',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['148','154'])).

thf('156',plain,
    ( ( sk_B != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(demod,[status(thm)],['146','147','155'])).

thf('157',plain,
    ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
    = sk_B ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
    | ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['140'])).

thf('159',plain,(
    ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['157','158'])).

thf('160',plain,(
    ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['143','159'])).

thf('161',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['133','160'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0jkBjKuLfd
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:36:54 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.49/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.49/0.68  % Solved by: fo/fo7.sh
% 0.49/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.68  % done 367 iterations in 0.221s
% 0.49/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.49/0.68  % SZS output start Refutation
% 0.49/0.68  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.49/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.49/0.68  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.49/0.68  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.49/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.68  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.49/0.68  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.49/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.68  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.49/0.68  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.49/0.68  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.49/0.68  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.49/0.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.49/0.68  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.49/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.49/0.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.49/0.68  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.49/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.49/0.68  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.49/0.68  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.49/0.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.49/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.49/0.68  thf(t92_funct_2, conjecture,
% 0.49/0.68    (![A:$i,B:$i,C:$i]:
% 0.49/0.68     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.49/0.68         ( v3_funct_2 @ C @ A @ A ) & 
% 0.49/0.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.49/0.68       ( ( r1_tarski @ B @ A ) =>
% 0.49/0.68         ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) ) =
% 0.49/0.68             ( B ) ) & 
% 0.49/0.68           ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) ) =
% 0.49/0.68             ( B ) ) ) ) ))).
% 0.49/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.68    (~( ![A:$i,B:$i,C:$i]:
% 0.49/0.68        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.49/0.68            ( v3_funct_2 @ C @ A @ A ) & 
% 0.49/0.68            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.49/0.68          ( ( r1_tarski @ B @ A ) =>
% 0.49/0.68            ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) ) =
% 0.49/0.68                ( B ) ) & 
% 0.49/0.68              ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) ) =
% 0.49/0.68                ( B ) ) ) ) ) )),
% 0.49/0.68    inference('cnf.neg', [status(esa)], [t92_funct_2])).
% 0.49/0.68  thf('0', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('1', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(dt_k2_funct_2, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.49/0.68         ( v3_funct_2 @ B @ A @ A ) & 
% 0.49/0.68         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.49/0.68       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.49/0.68         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.49/0.68         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.49/0.68         ( m1_subset_1 @
% 0.49/0.68           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.49/0.68  thf('2', plain,
% 0.49/0.68      (![X41 : $i, X42 : $i]:
% 0.49/0.68         ((m1_subset_1 @ (k2_funct_2 @ X41 @ X42) @ 
% 0.49/0.68           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))
% 0.49/0.68          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))
% 0.49/0.68          | ~ (v3_funct_2 @ X42 @ X41 @ X41)
% 0.49/0.68          | ~ (v1_funct_2 @ X42 @ X41 @ X41)
% 0.49/0.68          | ~ (v1_funct_1 @ X42))),
% 0.49/0.68      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.49/0.68  thf('3', plain,
% 0.49/0.68      ((~ (v1_funct_1 @ sk_C)
% 0.49/0.68        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.49/0.68        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.49/0.68        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_C) @ 
% 0.49/0.68           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.49/0.68  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('5', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('6', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('7', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(redefinition_k2_funct_2, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.49/0.68         ( v3_funct_2 @ B @ A @ A ) & 
% 0.49/0.68         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.49/0.68       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.49/0.68  thf('8', plain,
% 0.49/0.68      (![X43 : $i, X44 : $i]:
% 0.49/0.68         (((k2_funct_2 @ X44 @ X43) = (k2_funct_1 @ X43))
% 0.49/0.68          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X44)))
% 0.49/0.68          | ~ (v3_funct_2 @ X43 @ X44 @ X44)
% 0.49/0.68          | ~ (v1_funct_2 @ X43 @ X44 @ X44)
% 0.49/0.68          | ~ (v1_funct_1 @ X43))),
% 0.49/0.68      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.49/0.68  thf('9', plain,
% 0.49/0.68      ((~ (v1_funct_1 @ sk_C)
% 0.49/0.68        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.49/0.68        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.49/0.68        | ((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['7', '8'])).
% 0.49/0.68  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('11', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('12', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('13', plain, (((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.49/0.68      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.49/0.68  thf('14', plain,
% 0.49/0.68      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.68        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.68      inference('demod', [status(thm)], ['3', '4', '5', '6', '13'])).
% 0.49/0.68  thf(cc2_relset_1, axiom,
% 0.49/0.68    (![A:$i,B:$i,C:$i]:
% 0.49/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.68       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.49/0.68  thf('15', plain,
% 0.49/0.68      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.49/0.68         ((v4_relat_1 @ X25 @ X26)
% 0.49/0.68          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.49/0.68      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.49/0.68  thf('16', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)),
% 0.49/0.68      inference('sup-', [status(thm)], ['14', '15'])).
% 0.49/0.68  thf(d18_relat_1, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( v1_relat_1 @ B ) =>
% 0.49/0.68       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.49/0.68  thf('17', plain,
% 0.49/0.68      (![X7 : $i, X8 : $i]:
% 0.49/0.68         (~ (v4_relat_1 @ X7 @ X8)
% 0.49/0.68          | (r1_tarski @ (k1_relat_1 @ X7) @ X8)
% 0.49/0.68          | ~ (v1_relat_1 @ X7))),
% 0.49/0.68      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.49/0.68  thf('18', plain,
% 0.49/0.68      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.49/0.68        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['16', '17'])).
% 0.49/0.68  thf('19', plain,
% 0.49/0.68      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.68        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.68      inference('demod', [status(thm)], ['3', '4', '5', '6', '13'])).
% 0.49/0.68  thf(cc1_relset_1, axiom,
% 0.49/0.68    (![A:$i,B:$i,C:$i]:
% 0.49/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.68       ( v1_relat_1 @ C ) ))).
% 0.49/0.68  thf('20', plain,
% 0.49/0.68      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.49/0.68         ((v1_relat_1 @ X22)
% 0.49/0.68          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.49/0.68      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.49/0.68  thf('21', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.49/0.68      inference('sup-', [status(thm)], ['19', '20'])).
% 0.49/0.68  thf('22', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)),
% 0.49/0.68      inference('demod', [status(thm)], ['18', '21'])).
% 0.49/0.68  thf(t97_relat_1, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( v1_relat_1 @ B ) =>
% 0.49/0.68       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.49/0.68         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.49/0.68  thf('23', plain,
% 0.49/0.68      (![X14 : $i, X15 : $i]:
% 0.49/0.68         (~ (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 0.49/0.68          | ((k7_relat_1 @ X14 @ X15) = (X14))
% 0.49/0.68          | ~ (v1_relat_1 @ X14))),
% 0.49/0.68      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.49/0.68  thf('24', plain,
% 0.49/0.68      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.49/0.68        | ((k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A) = (k2_funct_1 @ sk_C)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['22', '23'])).
% 0.49/0.68  thf('25', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.49/0.68      inference('sup-', [status(thm)], ['19', '20'])).
% 0.49/0.68  thf('26', plain,
% 0.49/0.68      (((k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A) = (k2_funct_1 @ sk_C))),
% 0.49/0.68      inference('demod', [status(thm)], ['24', '25'])).
% 0.49/0.68  thf(t148_relat_1, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( v1_relat_1 @ B ) =>
% 0.49/0.68       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.49/0.68  thf('27', plain,
% 0.49/0.68      (![X11 : $i, X12 : $i]:
% 0.49/0.68         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.49/0.68          | ~ (v1_relat_1 @ X11))),
% 0.49/0.68      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.49/0.68  thf('28', plain,
% 0.49/0.68      ((((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 0.49/0.68          = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A))
% 0.49/0.68        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.49/0.68      inference('sup+', [status(thm)], ['26', '27'])).
% 0.49/0.68  thf('29', plain,
% 0.49/0.68      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.68        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.68      inference('demod', [status(thm)], ['3', '4', '5', '6', '13'])).
% 0.49/0.68  thf(cc2_funct_2, axiom,
% 0.49/0.68    (![A:$i,B:$i,C:$i]:
% 0.49/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.68       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.49/0.68         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.49/0.68  thf('30', plain,
% 0.49/0.68      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.49/0.68         (~ (v1_funct_1 @ X36)
% 0.49/0.68          | ~ (v3_funct_2 @ X36 @ X37 @ X38)
% 0.49/0.68          | (v2_funct_2 @ X36 @ X38)
% 0.49/0.68          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.49/0.68      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.49/0.68  thf('31', plain,
% 0.49/0.68      (((v2_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A)
% 0.49/0.68        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_A)
% 0.49/0.68        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['29', '30'])).
% 0.49/0.68  thf('32', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('33', plain,
% 0.49/0.68      (![X41 : $i, X42 : $i]:
% 0.49/0.68         ((v3_funct_2 @ (k2_funct_2 @ X41 @ X42) @ X41 @ X41)
% 0.49/0.68          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))
% 0.49/0.68          | ~ (v3_funct_2 @ X42 @ X41 @ X41)
% 0.49/0.68          | ~ (v1_funct_2 @ X42 @ X41 @ X41)
% 0.49/0.68          | ~ (v1_funct_1 @ X42))),
% 0.49/0.68      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.49/0.68  thf('34', plain,
% 0.49/0.68      ((~ (v1_funct_1 @ sk_C)
% 0.49/0.68        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.49/0.68        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.49/0.68        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_C) @ sk_A @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['32', '33'])).
% 0.49/0.68  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('36', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('37', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('38', plain, (((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.49/0.68      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.49/0.68  thf('39', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_A)),
% 0.49/0.68      inference('demod', [status(thm)], ['34', '35', '36', '37', '38'])).
% 0.49/0.68  thf('40', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('41', plain,
% 0.49/0.68      (![X41 : $i, X42 : $i]:
% 0.49/0.68         ((v1_funct_1 @ (k2_funct_2 @ X41 @ X42))
% 0.49/0.68          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))
% 0.49/0.68          | ~ (v3_funct_2 @ X42 @ X41 @ X41)
% 0.49/0.68          | ~ (v1_funct_2 @ X42 @ X41 @ X41)
% 0.49/0.68          | ~ (v1_funct_1 @ X42))),
% 0.49/0.68      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.49/0.68  thf('42', plain,
% 0.49/0.68      ((~ (v1_funct_1 @ sk_C)
% 0.49/0.68        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.49/0.68        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.49/0.68        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_C)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['40', '41'])).
% 0.49/0.68  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('44', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('45', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('46', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_C))),
% 0.49/0.68      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.49/0.68  thf('47', plain, (((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.49/0.68      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.49/0.68  thf('48', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.49/0.68      inference('demod', [status(thm)], ['46', '47'])).
% 0.49/0.68  thf('49', plain, ((v2_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A)),
% 0.49/0.68      inference('demod', [status(thm)], ['31', '39', '48'])).
% 0.49/0.68  thf(d3_funct_2, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.49/0.68       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.49/0.68  thf('50', plain,
% 0.49/0.68      (![X39 : $i, X40 : $i]:
% 0.49/0.68         (~ (v2_funct_2 @ X40 @ X39)
% 0.49/0.68          | ((k2_relat_1 @ X40) = (X39))
% 0.49/0.68          | ~ (v5_relat_1 @ X40 @ X39)
% 0.49/0.69          | ~ (v1_relat_1 @ X40))),
% 0.49/0.69      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.49/0.69  thf('51', plain,
% 0.49/0.69      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.49/0.69        | ~ (v5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)
% 0.49/0.69        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['49', '50'])).
% 0.49/0.69  thf('52', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.49/0.69      inference('sup-', [status(thm)], ['19', '20'])).
% 0.49/0.69  thf('53', plain,
% 0.49/0.69      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.69      inference('demod', [status(thm)], ['3', '4', '5', '6', '13'])).
% 0.49/0.69  thf('54', plain,
% 0.49/0.69      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.49/0.69         ((v5_relat_1 @ X25 @ X27)
% 0.49/0.69          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.49/0.69      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.49/0.69  thf('55', plain, ((v5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)),
% 0.49/0.69      inference('sup-', [status(thm)], ['53', '54'])).
% 0.49/0.69  thf('56', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A))),
% 0.49/0.69      inference('demod', [status(thm)], ['51', '52', '55'])).
% 0.49/0.69  thf('57', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('58', plain,
% 0.49/0.69      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.49/0.69         ((v4_relat_1 @ X25 @ X26)
% 0.49/0.69          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.49/0.69      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.49/0.69  thf('59', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.49/0.69      inference('sup-', [status(thm)], ['57', '58'])).
% 0.49/0.69  thf('60', plain,
% 0.49/0.69      (![X7 : $i, X8 : $i]:
% 0.49/0.69         (~ (v4_relat_1 @ X7 @ X8)
% 0.49/0.69          | (r1_tarski @ (k1_relat_1 @ X7) @ X8)
% 0.49/0.69          | ~ (v1_relat_1 @ X7))),
% 0.49/0.69      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.49/0.69  thf('61', plain,
% 0.49/0.69      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.49/0.69      inference('sup-', [status(thm)], ['59', '60'])).
% 0.49/0.69  thf('62', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf(cc2_relat_1, axiom,
% 0.49/0.69    (![A:$i]:
% 0.49/0.69     ( ( v1_relat_1 @ A ) =>
% 0.49/0.69       ( ![B:$i]:
% 0.49/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.49/0.69  thf('63', plain,
% 0.49/0.69      (![X5 : $i, X6 : $i]:
% 0.49/0.69         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.49/0.69          | (v1_relat_1 @ X5)
% 0.49/0.69          | ~ (v1_relat_1 @ X6))),
% 0.49/0.69      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.49/0.69  thf('64', plain,
% 0.49/0.69      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.49/0.69      inference('sup-', [status(thm)], ['62', '63'])).
% 0.49/0.69  thf(fc6_relat_1, axiom,
% 0.49/0.69    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.49/0.69  thf('65', plain,
% 0.49/0.69      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.49/0.69      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.49/0.69  thf('66', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.69      inference('demod', [status(thm)], ['64', '65'])).
% 0.49/0.69  thf('67', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.49/0.69      inference('demod', [status(thm)], ['61', '66'])).
% 0.49/0.69  thf('68', plain,
% 0.49/0.69      (![X14 : $i, X15 : $i]:
% 0.49/0.69         (~ (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 0.49/0.69          | ((k7_relat_1 @ X14 @ X15) = (X14))
% 0.49/0.69          | ~ (v1_relat_1 @ X14))),
% 0.49/0.69      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.49/0.69  thf('69', plain,
% 0.49/0.69      ((~ (v1_relat_1 @ sk_C) | ((k7_relat_1 @ sk_C @ sk_A) = (sk_C)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['67', '68'])).
% 0.49/0.69  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.69      inference('demod', [status(thm)], ['64', '65'])).
% 0.49/0.69  thf('71', plain, (((k7_relat_1 @ sk_C @ sk_A) = (sk_C))),
% 0.49/0.69      inference('demod', [status(thm)], ['69', '70'])).
% 0.49/0.69  thf('72', plain,
% 0.49/0.69      (![X11 : $i, X12 : $i]:
% 0.49/0.69         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.49/0.69          | ~ (v1_relat_1 @ X11))),
% 0.49/0.69      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.49/0.69  thf(t169_relat_1, axiom,
% 0.49/0.69    (![A:$i]:
% 0.49/0.69     ( ( v1_relat_1 @ A ) =>
% 0.49/0.69       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.49/0.69  thf('73', plain,
% 0.49/0.69      (![X13 : $i]:
% 0.49/0.69         (((k10_relat_1 @ X13 @ (k2_relat_1 @ X13)) = (k1_relat_1 @ X13))
% 0.49/0.69          | ~ (v1_relat_1 @ X13))),
% 0.49/0.69      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.49/0.69  thf('74', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]:
% 0.49/0.69         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.49/0.69            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.49/0.69          | ~ (v1_relat_1 @ X1)
% 0.49/0.69          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.49/0.69      inference('sup+', [status(thm)], ['72', '73'])).
% 0.49/0.69  thf('75', plain,
% 0.49/0.69      ((~ (v1_relat_1 @ sk_C)
% 0.49/0.69        | ~ (v1_relat_1 @ sk_C)
% 0.49/0.69        | ((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ 
% 0.49/0.69            (k9_relat_1 @ sk_C @ sk_A))
% 0.49/0.69            = (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['71', '74'])).
% 0.49/0.69  thf('76', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.69      inference('demod', [status(thm)], ['64', '65'])).
% 0.49/0.69  thf('77', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.69      inference('demod', [status(thm)], ['64', '65'])).
% 0.49/0.69  thf('78', plain, (((k7_relat_1 @ sk_C @ sk_A) = (sk_C))),
% 0.49/0.69      inference('demod', [status(thm)], ['69', '70'])).
% 0.49/0.69  thf('79', plain, (((k7_relat_1 @ sk_C @ sk_A) = (sk_C))),
% 0.49/0.69      inference('demod', [status(thm)], ['69', '70'])).
% 0.49/0.69  thf('80', plain,
% 0.49/0.69      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) = (k1_relat_1 @ sk_C))),
% 0.49/0.69      inference('demod', [status(thm)], ['75', '76', '77', '78', '79'])).
% 0.49/0.69  thf('81', plain, (((k7_relat_1 @ sk_C @ sk_A) = (sk_C))),
% 0.49/0.69      inference('demod', [status(thm)], ['69', '70'])).
% 0.49/0.69  thf('82', plain,
% 0.49/0.69      (![X11 : $i, X12 : $i]:
% 0.49/0.69         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.49/0.69          | ~ (v1_relat_1 @ X11))),
% 0.49/0.69      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.49/0.69  thf('83', plain,
% 0.49/0.69      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 0.49/0.69        | ~ (v1_relat_1 @ sk_C))),
% 0.49/0.69      inference('sup+', [status(thm)], ['81', '82'])).
% 0.49/0.69  thf('84', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.69      inference('demod', [status(thm)], ['64', '65'])).
% 0.49/0.69  thf('85', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.49/0.69      inference('demod', [status(thm)], ['83', '84'])).
% 0.49/0.69  thf('86', plain,
% 0.49/0.69      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.49/0.69      inference('demod', [status(thm)], ['80', '85'])).
% 0.49/0.69  thf(dt_k2_subset_1, axiom,
% 0.49/0.69    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.49/0.69  thf('87', plain,
% 0.49/0.69      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.49/0.69      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.49/0.69  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.49/0.69  thf('88', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.49/0.69      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.49/0.69  thf('89', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.49/0.69      inference('demod', [status(thm)], ['87', '88'])).
% 0.49/0.69  thf(t3_subset, axiom,
% 0.49/0.69    (![A:$i,B:$i]:
% 0.49/0.69     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.49/0.69  thf('90', plain,
% 0.49/0.69      (![X2 : $i, X3 : $i]:
% 0.49/0.69         ((r1_tarski @ X2 @ X3) | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.49/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.49/0.69  thf('91', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.49/0.69      inference('sup-', [status(thm)], ['89', '90'])).
% 0.49/0.69  thf(t147_funct_1, axiom,
% 0.49/0.69    (![A:$i,B:$i]:
% 0.49/0.69     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.49/0.69       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.49/0.69         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.49/0.69  thf('92', plain,
% 0.49/0.69      (![X16 : $i, X17 : $i]:
% 0.49/0.69         (~ (r1_tarski @ X16 @ (k2_relat_1 @ X17))
% 0.49/0.69          | ((k9_relat_1 @ X17 @ (k10_relat_1 @ X17 @ X16)) = (X16))
% 0.49/0.69          | ~ (v1_funct_1 @ X17)
% 0.49/0.69          | ~ (v1_relat_1 @ X17))),
% 0.49/0.69      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.49/0.69  thf('93', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (~ (v1_relat_1 @ X0)
% 0.49/0.69          | ~ (v1_funct_1 @ X0)
% 0.49/0.69          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.49/0.69              = (k2_relat_1 @ X0)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['91', '92'])).
% 0.49/0.69  thf('94', plain,
% 0.49/0.69      ((((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))
% 0.49/0.69        | ~ (v1_funct_1 @ sk_C)
% 0.49/0.69        | ~ (v1_relat_1 @ sk_C))),
% 0.49/0.69      inference('sup+', [status(thm)], ['86', '93'])).
% 0.49/0.69  thf('95', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('96', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.69      inference('demod', [status(thm)], ['64', '65'])).
% 0.49/0.69  thf('97', plain,
% 0.49/0.69      (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.49/0.69      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.49/0.69  thf('98', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('99', plain,
% 0.49/0.69      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.49/0.69         (~ (v1_funct_1 @ X36)
% 0.49/0.69          | ~ (v3_funct_2 @ X36 @ X37 @ X38)
% 0.49/0.69          | (v2_funct_2 @ X36 @ X38)
% 0.49/0.69          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.49/0.69      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.49/0.69  thf('100', plain,
% 0.49/0.69      (((v2_funct_2 @ sk_C @ sk_A)
% 0.49/0.69        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.49/0.69        | ~ (v1_funct_1 @ sk_C))),
% 0.49/0.69      inference('sup-', [status(thm)], ['98', '99'])).
% 0.49/0.69  thf('101', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('102', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('103', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 0.49/0.69      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.49/0.69  thf('104', plain,
% 0.49/0.69      (![X39 : $i, X40 : $i]:
% 0.49/0.69         (~ (v2_funct_2 @ X40 @ X39)
% 0.49/0.69          | ((k2_relat_1 @ X40) = (X39))
% 0.49/0.69          | ~ (v5_relat_1 @ X40 @ X39)
% 0.49/0.69          | ~ (v1_relat_1 @ X40))),
% 0.49/0.69      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.49/0.69  thf('105', plain,
% 0.49/0.69      ((~ (v1_relat_1 @ sk_C)
% 0.49/0.69        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 0.49/0.69        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['103', '104'])).
% 0.49/0.69  thf('106', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.69      inference('demod', [status(thm)], ['64', '65'])).
% 0.49/0.69  thf('107', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('108', plain,
% 0.49/0.69      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.49/0.69         ((v5_relat_1 @ X25 @ X27)
% 0.49/0.69          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.49/0.69      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.49/0.69  thf('109', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.49/0.69      inference('sup-', [status(thm)], ['107', '108'])).
% 0.49/0.69  thf('110', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.49/0.69      inference('demod', [status(thm)], ['105', '106', '109'])).
% 0.49/0.69  thf('111', plain, (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) = (sk_A))),
% 0.49/0.69      inference('demod', [status(thm)], ['97', '110'])).
% 0.49/0.69  thf('112', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.49/0.69      inference('sup-', [status(thm)], ['89', '90'])).
% 0.49/0.69  thf(t177_funct_1, axiom,
% 0.49/0.69    (![A:$i]:
% 0.49/0.69     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.69       ( ![B:$i]:
% 0.49/0.69         ( ( ( v2_funct_1 @ A ) & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.49/0.69           ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) ) =
% 0.49/0.69             ( B ) ) ) ) ))).
% 0.49/0.69  thf('113', plain,
% 0.49/0.69      (![X20 : $i, X21 : $i]:
% 0.49/0.69         (~ (r1_tarski @ X20 @ (k1_relat_1 @ X21))
% 0.49/0.69          | ((k9_relat_1 @ (k2_funct_1 @ X21) @ (k9_relat_1 @ X21 @ X20))
% 0.49/0.69              = (X20))
% 0.49/0.69          | ~ (v2_funct_1 @ X21)
% 0.49/0.69          | ~ (v1_funct_1 @ X21)
% 0.49/0.69          | ~ (v1_relat_1 @ X21))),
% 0.49/0.69      inference('cnf', [status(esa)], [t177_funct_1])).
% 0.49/0.69  thf('114', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (~ (v1_relat_1 @ X0)
% 0.49/0.69          | ~ (v1_funct_1 @ X0)
% 0.49/0.69          | ~ (v2_funct_1 @ X0)
% 0.49/0.69          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ 
% 0.49/0.69              (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))) = (k1_relat_1 @ X0)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['112', '113'])).
% 0.49/0.69  thf('115', plain,
% 0.49/0.69      ((((k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A) = (k1_relat_1 @ sk_C))
% 0.49/0.69        | ~ (v2_funct_1 @ sk_C)
% 0.49/0.69        | ~ (v1_funct_1 @ sk_C)
% 0.49/0.69        | ~ (v1_relat_1 @ sk_C))),
% 0.49/0.69      inference('sup+', [status(thm)], ['111', '114'])).
% 0.49/0.69  thf('116', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('117', plain,
% 0.49/0.69      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.49/0.69         (~ (v1_funct_1 @ X36)
% 0.49/0.69          | ~ (v3_funct_2 @ X36 @ X37 @ X38)
% 0.49/0.69          | (v2_funct_1 @ X36)
% 0.49/0.69          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.49/0.69      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.49/0.69  thf('118', plain,
% 0.49/0.69      (((v2_funct_1 @ sk_C)
% 0.49/0.69        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.49/0.69        | ~ (v1_funct_1 @ sk_C))),
% 0.49/0.69      inference('sup-', [status(thm)], ['116', '117'])).
% 0.49/0.69  thf('119', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('120', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('121', plain, ((v2_funct_1 @ sk_C)),
% 0.49/0.69      inference('demod', [status(thm)], ['118', '119', '120'])).
% 0.49/0.69  thf('122', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('123', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.69      inference('demod', [status(thm)], ['64', '65'])).
% 0.49/0.69  thf('124', plain,
% 0.49/0.69      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.49/0.69      inference('demod', [status(thm)], ['115', '121', '122', '123'])).
% 0.49/0.69  thf('125', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.49/0.69      inference('sup-', [status(thm)], ['19', '20'])).
% 0.49/0.69  thf('126', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.49/0.69      inference('demod', [status(thm)], ['28', '56', '124', '125'])).
% 0.49/0.69  thf(t164_funct_1, axiom,
% 0.49/0.69    (![A:$i,B:$i]:
% 0.49/0.69     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.49/0.69       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.49/0.69         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.49/0.69  thf('127', plain,
% 0.49/0.69      (![X18 : $i, X19 : $i]:
% 0.49/0.69         (~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 0.49/0.69          | ~ (v2_funct_1 @ X19)
% 0.49/0.69          | ((k10_relat_1 @ X19 @ (k9_relat_1 @ X19 @ X18)) = (X18))
% 0.49/0.69          | ~ (v1_funct_1 @ X19)
% 0.49/0.69          | ~ (v1_relat_1 @ X19))),
% 0.49/0.69      inference('cnf', [status(esa)], [t164_funct_1])).
% 0.49/0.69  thf('128', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (~ (r1_tarski @ X0 @ sk_A)
% 0.49/0.69          | ~ (v1_relat_1 @ sk_C)
% 0.49/0.69          | ~ (v1_funct_1 @ sk_C)
% 0.49/0.69          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0))
% 0.49/0.69          | ~ (v2_funct_1 @ sk_C))),
% 0.49/0.69      inference('sup-', [status(thm)], ['126', '127'])).
% 0.49/0.69  thf('129', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.69      inference('demod', [status(thm)], ['64', '65'])).
% 0.49/0.69  thf('130', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('131', plain, ((v2_funct_1 @ sk_C)),
% 0.49/0.69      inference('demod', [status(thm)], ['118', '119', '120'])).
% 0.49/0.69  thf('132', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (~ (r1_tarski @ X0 @ sk_A)
% 0.49/0.69          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.49/0.69      inference('demod', [status(thm)], ['128', '129', '130', '131'])).
% 0.49/0.69  thf('133', plain,
% 0.49/0.69      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) = (sk_B))),
% 0.49/0.69      inference('sup-', [status(thm)], ['0', '132'])).
% 0.49/0.69  thf('134', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf(redefinition_k8_relset_1, axiom,
% 0.49/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.69       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.49/0.69  thf('135', plain,
% 0.49/0.69      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.49/0.69         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.49/0.69          | ((k8_relset_1 @ X33 @ X34 @ X32 @ X35) = (k10_relat_1 @ X32 @ X35)))),
% 0.49/0.69      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.49/0.69  thf('136', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['134', '135'])).
% 0.49/0.69  thf('137', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf(redefinition_k7_relset_1, axiom,
% 0.49/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.69       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.49/0.69  thf('138', plain,
% 0.49/0.69      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.49/0.69         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.49/0.69          | ((k7_relset_1 @ X29 @ X30 @ X28 @ X31) = (k9_relat_1 @ X28 @ X31)))),
% 0.49/0.69      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.49/0.69  thf('139', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['137', '138'])).
% 0.49/0.69  thf('140', plain,
% 0.49/0.69      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.49/0.69          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B))
% 0.49/0.69        | ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.49/0.69            (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('141', plain,
% 0.49/0.69      ((((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.49/0.69          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))
% 0.49/0.69         <= (~
% 0.49/0.69             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.49/0.69                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.49/0.69      inference('split', [status(esa)], ['140'])).
% 0.49/0.69  thf('142', plain,
% 0.49/0.69      ((((k8_relset_1 @ sk_A @ sk_A @ sk_C @ (k9_relat_1 @ sk_C @ sk_B))
% 0.49/0.69          != (sk_B)))
% 0.49/0.69         <= (~
% 0.49/0.69             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.49/0.69                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['139', '141'])).
% 0.49/0.69  thf('143', plain,
% 0.49/0.69      ((((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) != (sk_B)))
% 0.49/0.69         <= (~
% 0.49/0.69             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.49/0.69                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['136', '142'])).
% 0.49/0.69  thf('144', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['134', '135'])).
% 0.49/0.69  thf('145', plain,
% 0.49/0.69      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.49/0.69          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))
% 0.49/0.69         <= (~
% 0.49/0.69             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.49/0.69                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.49/0.69      inference('split', [status(esa)], ['140'])).
% 0.49/0.69  thf('146', plain,
% 0.49/0.69      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ (k10_relat_1 @ sk_C @ sk_B))
% 0.49/0.69          != (sk_B)))
% 0.49/0.69         <= (~
% 0.49/0.69             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.49/0.69                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['144', '145'])).
% 0.49/0.69  thf('147', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['137', '138'])).
% 0.49/0.69  thf('148', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('149', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.49/0.69      inference('demod', [status(thm)], ['105', '106', '109'])).
% 0.49/0.69  thf('150', plain,
% 0.49/0.69      (![X16 : $i, X17 : $i]:
% 0.49/0.69         (~ (r1_tarski @ X16 @ (k2_relat_1 @ X17))
% 0.49/0.69          | ((k9_relat_1 @ X17 @ (k10_relat_1 @ X17 @ X16)) = (X16))
% 0.49/0.69          | ~ (v1_funct_1 @ X17)
% 0.49/0.69          | ~ (v1_relat_1 @ X17))),
% 0.49/0.69      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.49/0.69  thf('151', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (~ (r1_tarski @ X0 @ sk_A)
% 0.49/0.69          | ~ (v1_relat_1 @ sk_C)
% 0.49/0.69          | ~ (v1_funct_1 @ sk_C)
% 0.49/0.69          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['149', '150'])).
% 0.49/0.69  thf('152', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.69      inference('demod', [status(thm)], ['64', '65'])).
% 0.49/0.69  thf('153', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('154', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (~ (r1_tarski @ X0 @ sk_A)
% 0.49/0.69          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.49/0.69      inference('demod', [status(thm)], ['151', '152', '153'])).
% 0.49/0.69  thf('155', plain,
% 0.49/0.69      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)) = (sk_B))),
% 0.49/0.69      inference('sup-', [status(thm)], ['148', '154'])).
% 0.49/0.69  thf('156', plain,
% 0.49/0.69      ((((sk_B) != (sk_B)))
% 0.49/0.69         <= (~
% 0.49/0.69             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.49/0.69                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.49/0.69      inference('demod', [status(thm)], ['146', '147', '155'])).
% 0.49/0.69  thf('157', plain,
% 0.49/0.69      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.49/0.69          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.49/0.69      inference('simplify', [status(thm)], ['156'])).
% 0.49/0.69  thf('158', plain,
% 0.49/0.69      (~
% 0.49/0.69       (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.49/0.69          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))) | 
% 0.49/0.69       ~
% 0.49/0.69       (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.49/0.69          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.49/0.69      inference('split', [status(esa)], ['140'])).
% 0.49/0.69  thf('159', plain,
% 0.49/0.69      (~
% 0.49/0.69       (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.49/0.69          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.49/0.69      inference('sat_resolution*', [status(thm)], ['157', '158'])).
% 0.49/0.69  thf('160', plain,
% 0.49/0.69      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) != (sk_B))),
% 0.49/0.69      inference('simpl_trail', [status(thm)], ['143', '159'])).
% 0.49/0.69  thf('161', plain, ($false),
% 0.49/0.69      inference('simplify_reflect-', [status(thm)], ['133', '160'])).
% 0.49/0.69  
% 0.49/0.69  % SZS output end Refutation
% 0.49/0.69  
% 0.49/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
