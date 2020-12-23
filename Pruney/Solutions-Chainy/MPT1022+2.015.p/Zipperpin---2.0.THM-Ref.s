%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zywqLYNe11

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:27 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  210 (1027 expanded)
%              Number of leaves         :   42 ( 332 expanded)
%              Depth                    :   17
%              Number of atoms          : 1663 (19140 expanded)
%              Number of equality atoms :   95 ( 851 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X17 @ ( k2_relat_1 @ X18 ) )
      | ( ( k9_relat_1 @ X18 @ ( k10_relat_1 @ X18 @ X17 ) )
        = X17 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X39: $i,X40: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X39 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) )
      | ~ ( v3_funct_2 @ X40 @ X39 @ X39 )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X39 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('7',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k2_funct_2 @ X42 @ X41 )
        = ( k2_funct_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) )
      | ~ ( v3_funct_2 @ X41 @ X42 @ X42 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X42 )
      | ~ ( v1_funct_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k2_funct_2 @ sk_A @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('18',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8','9','10','17'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('22',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('23',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k9_relat_1 @ X19 @ X20 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X19 ) @ X20 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X15 @ ( k10_relat_1 @ X15 @ X16 ) ) @ X16 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ X1 ) @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X39 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) )
      | ~ ( v3_funct_2 @ X40 @ X39 @ X39 )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X39 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('29',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,
    ( ( k2_funct_2 @ sk_A @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('35',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
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

thf('37',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_1 @ X34 )
      | ~ ( v3_funct_2 @ X34 @ X35 @ X36 )
      | ( v2_funct_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('38',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('47',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['26','35','41','42','47'])).

thf('49',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) @ ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['4','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_1 @ X34 )
      | ~ ( v3_funct_2 @ X34 @ X35 @ X36 )
      | ( v2_funct_2 @ X34 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('52',plain,
    ( ( v2_funct_2 @ sk_C @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_funct_2 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['52','53','54'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('56',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v2_funct_2 @ X38 @ X37 )
      | ( ( k2_relat_1 @ X38 )
        = X37 )
      | ~ ( v5_relat_1 @ X38 @ X37 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('57',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v5_relat_1 @ sk_C @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('60',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v5_relat_1 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('61',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['57','58','61'])).

thf('63',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8','9','10','17'])).

thf('64',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('65',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['63','64'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('66',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13
        = ( k7_relat_1 @ X13 @ X14 ) )
      | ~ ( v4_relat_1 @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('67',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_funct_1 @ sk_C )
      = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('69',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('70',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k9_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('71',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8','9','10','17'])).

thf('73',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_1 @ X34 )
      | ~ ( v3_funct_2 @ X34 @ X35 @ X36 )
      | ( v2_funct_2 @ X34 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('74',plain,
    ( ( v2_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X39 @ X40 ) @ X39 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) )
      | ~ ( v3_funct_2 @ X40 @ X39 @ X39 )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X39 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('77',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_C ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k2_funct_2 @ sk_A @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('82',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['77','78','79','80','81'])).

thf('83',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('84',plain,(
    v2_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['74','82','83'])).

thf('85',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v2_funct_2 @ X38 @ X37 )
      | ( ( k2_relat_1 @ X38 )
        = X37 )
      | ~ ( v5_relat_1 @ X38 @ X37 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('86',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('88',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8','9','10','17'])).

thf('89',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v5_relat_1 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('90',plain,(
    v5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['86','87','90'])).

thf('92',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('93',plain,
    ( sk_A
    = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['71','91','92'])).

thf('94',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['57','58','61'])).

thf('95',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('97',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13
        = ( k7_relat_1 @ X13 @ X14 ) )
      | ~ ( v4_relat_1 @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('99',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('101',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k9_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('103',plain,(
    ! [X12: $i] :
      ( ( ( k10_relat_1 @ X12 @ ( k2_relat_1 @ X12 ) )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['101','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('107',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('108',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('109',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('110',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['105','106','107','108','109'])).

thf('111',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('112',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('113',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k9_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['111','114'])).

thf('116',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['110','115'])).

thf('117',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['57','58','61'])).

thf('118',plain,
    ( ( k10_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('121',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['49','62','93','94','118','119','120'])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('122',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X21 @ ( k1_relat_1 @ X22 ) )
      | ~ ( v2_funct_1 @ X22 )
      | ( ( k10_relat_1 @ X22 @ ( k9_relat_1 @ X22 @ X21 ) )
        = X21 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('123',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = sk_A )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('125',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['111','114'])).

thf('127',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['57','58','61'])).

thf('128',plain,
    ( sk_A
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k10_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('130',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('131',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['123','124','125','128','129','130'])).

thf('132',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X21 @ ( k1_relat_1 @ X22 ) )
      | ~ ( v2_funct_1 @ X22 )
      | ( ( k10_relat_1 @ X22 @ ( k9_relat_1 @ X22 @ X21 ) )
        = X21 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('135',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['133','134','135','136'])).

thf('138',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','137'])).

thf('139',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('140',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k8_relset_1 @ X31 @ X32 @ X30 @ X33 )
        = ( k10_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('143',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k7_relset_1 @ X27 @ X28 @ X26 @ X29 )
        = ( k9_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
    | ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['145'])).

thf('147',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['144','146'])).

thf('148',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['141','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('150',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['145'])).

thf('151',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('153',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['57','58','61'])).

thf('155',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X17 @ ( k2_relat_1 @ X18 ) )
      | ( ( k9_relat_1 @ X18 @ ( k10_relat_1 @ X18 @ X17 ) )
        = X17 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('158',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('160',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['153','159'])).

thf('161',plain,
    ( ( sk_B != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(demod,[status(thm)],['151','152','160'])).

thf('162',plain,
    ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
    = sk_B ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
    | ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['145'])).

thf('164',plain,(
    ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['162','163'])).

thf('165',plain,(
    ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['148','164'])).

thf('166',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['138','165'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zywqLYNe11
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:56:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.47/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.65  % Solved by: fo/fo7.sh
% 0.47/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.65  % done 329 iterations in 0.185s
% 0.47/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.65  % SZS output start Refutation
% 0.47/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.65  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.47/0.65  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.47/0.65  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.47/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.65  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.47/0.65  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.47/0.65  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.47/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.65  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.47/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.65  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.47/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.65  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.47/0.65  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.47/0.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.65  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.47/0.65  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.47/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.65  thf(t92_funct_2, conjecture,
% 0.47/0.65    (![A:$i,B:$i,C:$i]:
% 0.47/0.65     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.47/0.65         ( v3_funct_2 @ C @ A @ A ) & 
% 0.47/0.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.47/0.65       ( ( r1_tarski @ B @ A ) =>
% 0.47/0.65         ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) ) =
% 0.47/0.65             ( B ) ) & 
% 0.47/0.65           ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) ) =
% 0.47/0.65             ( B ) ) ) ) ))).
% 0.47/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.65    (~( ![A:$i,B:$i,C:$i]:
% 0.47/0.65        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.47/0.65            ( v3_funct_2 @ C @ A @ A ) & 
% 0.47/0.65            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.47/0.65          ( ( r1_tarski @ B @ A ) =>
% 0.47/0.65            ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) ) =
% 0.47/0.65                ( B ) ) & 
% 0.47/0.65              ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) ) =
% 0.47/0.65                ( B ) ) ) ) ) )),
% 0.47/0.65    inference('cnf.neg', [status(esa)], [t92_funct_2])).
% 0.47/0.65  thf('0', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(d10_xboole_0, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.65  thf('1', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.47/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.65  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.47/0.65      inference('simplify', [status(thm)], ['1'])).
% 0.47/0.65  thf(t147_funct_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.65       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.47/0.65         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.47/0.65  thf('3', plain,
% 0.47/0.65      (![X17 : $i, X18 : $i]:
% 0.47/0.65         (~ (r1_tarski @ X17 @ (k2_relat_1 @ X18))
% 0.47/0.65          | ((k9_relat_1 @ X18 @ (k10_relat_1 @ X18 @ X17)) = (X17))
% 0.47/0.65          | ~ (v1_funct_1 @ X18)
% 0.47/0.65          | ~ (v1_relat_1 @ X18))),
% 0.47/0.65      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.47/0.65  thf('4', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ X0)
% 0.47/0.65          | ~ (v1_funct_1 @ X0)
% 0.47/0.65          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.47/0.65              = (k2_relat_1 @ X0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['2', '3'])).
% 0.47/0.65  thf('5', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(dt_k2_funct_2, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.47/0.65         ( v3_funct_2 @ B @ A @ A ) & 
% 0.47/0.65         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.47/0.65       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.47/0.65         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.47/0.65         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.47/0.65         ( m1_subset_1 @
% 0.47/0.65           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.47/0.65  thf('6', plain,
% 0.47/0.65      (![X39 : $i, X40 : $i]:
% 0.47/0.65         ((m1_subset_1 @ (k2_funct_2 @ X39 @ X40) @ 
% 0.47/0.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))
% 0.47/0.65          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))
% 0.47/0.65          | ~ (v3_funct_2 @ X40 @ X39 @ X39)
% 0.47/0.65          | ~ (v1_funct_2 @ X40 @ X39 @ X39)
% 0.47/0.65          | ~ (v1_funct_1 @ X40))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.47/0.65  thf('7', plain,
% 0.47/0.65      ((~ (v1_funct_1 @ sk_C)
% 0.47/0.65        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.47/0.65        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.47/0.65        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_C) @ 
% 0.47/0.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['5', '6'])).
% 0.47/0.65  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('9', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('10', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('11', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(redefinition_k2_funct_2, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.47/0.65         ( v3_funct_2 @ B @ A @ A ) & 
% 0.47/0.65         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.47/0.65       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.47/0.65  thf('12', plain,
% 0.47/0.65      (![X41 : $i, X42 : $i]:
% 0.47/0.65         (((k2_funct_2 @ X42 @ X41) = (k2_funct_1 @ X41))
% 0.47/0.65          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))
% 0.47/0.65          | ~ (v3_funct_2 @ X41 @ X42 @ X42)
% 0.47/0.65          | ~ (v1_funct_2 @ X41 @ X42 @ X42)
% 0.47/0.65          | ~ (v1_funct_1 @ X41))),
% 0.47/0.65      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.47/0.65  thf('13', plain,
% 0.47/0.65      ((~ (v1_funct_1 @ sk_C)
% 0.47/0.65        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.47/0.65        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.47/0.65        | ((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['11', '12'])).
% 0.47/0.65  thf('14', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('15', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('16', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('17', plain, (((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 0.47/0.65  thf('18', plain,
% 0.47/0.65      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.47/0.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.65      inference('demod', [status(thm)], ['7', '8', '9', '10', '17'])).
% 0.47/0.65  thf(cc2_relat_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( v1_relat_1 @ A ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.47/0.65  thf('19', plain,
% 0.47/0.65      (![X6 : $i, X7 : $i]:
% 0.47/0.65         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.47/0.65          | (v1_relat_1 @ X6)
% 0.47/0.65          | ~ (v1_relat_1 @ X7))),
% 0.47/0.65      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.47/0.65  thf('20', plain,
% 0.47/0.65      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 0.47/0.65        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['18', '19'])).
% 0.47/0.65  thf(fc6_relat_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.47/0.65  thf('21', plain,
% 0.47/0.65      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.47/0.65      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.47/0.65  thf('22', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['20', '21'])).
% 0.47/0.65  thf(t154_funct_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.65       ( ( v2_funct_1 @ B ) =>
% 0.47/0.65         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.47/0.65  thf('23', plain,
% 0.47/0.65      (![X19 : $i, X20 : $i]:
% 0.47/0.65         (~ (v2_funct_1 @ X19)
% 0.47/0.65          | ((k9_relat_1 @ X19 @ X20)
% 0.47/0.65              = (k10_relat_1 @ (k2_funct_1 @ X19) @ X20))
% 0.47/0.65          | ~ (v1_funct_1 @ X19)
% 0.47/0.65          | ~ (v1_relat_1 @ X19))),
% 0.47/0.65      inference('cnf', [status(esa)], [t154_funct_1])).
% 0.47/0.65  thf(t145_funct_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.65       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.47/0.65  thf('24', plain,
% 0.47/0.65      (![X15 : $i, X16 : $i]:
% 0.47/0.65         ((r1_tarski @ (k9_relat_1 @ X15 @ (k10_relat_1 @ X15 @ X16)) @ X16)
% 0.47/0.65          | ~ (v1_funct_1 @ X15)
% 0.47/0.65          | ~ (v1_relat_1 @ X15))),
% 0.47/0.65      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.47/0.65  thf('25', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         ((r1_tarski @ 
% 0.47/0.65           (k9_relat_1 @ (k2_funct_1 @ X1) @ (k9_relat_1 @ X1 @ X0)) @ X0)
% 0.47/0.65          | ~ (v1_relat_1 @ X1)
% 0.47/0.65          | ~ (v1_funct_1 @ X1)
% 0.47/0.65          | ~ (v2_funct_1 @ X1)
% 0.47/0.65          | ~ (v1_relat_1 @ (k2_funct_1 @ X1))
% 0.47/0.65          | ~ (v1_funct_1 @ (k2_funct_1 @ X1)))),
% 0.47/0.65      inference('sup+', [status(thm)], ['23', '24'])).
% 0.47/0.65  thf('26', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.47/0.65          | ~ (v2_funct_1 @ sk_C)
% 0.47/0.65          | ~ (v1_funct_1 @ sk_C)
% 0.47/0.65          | ~ (v1_relat_1 @ sk_C)
% 0.47/0.65          | (r1_tarski @ 
% 0.47/0.65             (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k9_relat_1 @ sk_C @ X0)) @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['22', '25'])).
% 0.47/0.65  thf('27', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('28', plain,
% 0.47/0.65      (![X39 : $i, X40 : $i]:
% 0.47/0.65         ((v1_funct_1 @ (k2_funct_2 @ X39 @ X40))
% 0.47/0.65          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))
% 0.47/0.65          | ~ (v3_funct_2 @ X40 @ X39 @ X39)
% 0.47/0.65          | ~ (v1_funct_2 @ X40 @ X39 @ X39)
% 0.47/0.65          | ~ (v1_funct_1 @ X40))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.47/0.65  thf('29', plain,
% 0.47/0.65      ((~ (v1_funct_1 @ sk_C)
% 0.47/0.65        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.47/0.65        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.47/0.65        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_C)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['27', '28'])).
% 0.47/0.65  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('31', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('32', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('33', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.47/0.65  thf('34', plain, (((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 0.47/0.65  thf('35', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['33', '34'])).
% 0.47/0.65  thf('36', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(cc2_funct_2, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i]:
% 0.47/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.65       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.47/0.65         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.47/0.65  thf('37', plain,
% 0.47/0.65      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.47/0.65         (~ (v1_funct_1 @ X34)
% 0.47/0.65          | ~ (v3_funct_2 @ X34 @ X35 @ X36)
% 0.47/0.65          | (v2_funct_1 @ X34)
% 0.47/0.65          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.47/0.65      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.47/0.65  thf('38', plain,
% 0.47/0.65      (((v2_funct_1 @ sk_C)
% 0.47/0.65        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.47/0.65        | ~ (v1_funct_1 @ sk_C))),
% 0.47/0.65      inference('sup-', [status(thm)], ['36', '37'])).
% 0.47/0.65  thf('39', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('41', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.65      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.47/0.65  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('43', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('44', plain,
% 0.47/0.65      (![X6 : $i, X7 : $i]:
% 0.47/0.65         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.47/0.65          | (v1_relat_1 @ X6)
% 0.47/0.65          | ~ (v1_relat_1 @ X7))),
% 0.47/0.65      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.47/0.65  thf('45', plain,
% 0.47/0.65      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.47/0.65      inference('sup-', [status(thm)], ['43', '44'])).
% 0.47/0.65  thf('46', plain,
% 0.47/0.65      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.47/0.65      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.47/0.65  thf('47', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.65      inference('demod', [status(thm)], ['45', '46'])).
% 0.47/0.65  thf('48', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (r1_tarski @ 
% 0.47/0.65          (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k9_relat_1 @ sk_C @ X0)) @ X0)),
% 0.47/0.65      inference('demod', [status(thm)], ['26', '35', '41', '42', '47'])).
% 0.47/0.65  thf('49', plain,
% 0.47/0.65      (((r1_tarski @ 
% 0.47/0.65         (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C)) @ 
% 0.47/0.65         (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.47/0.65        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.65        | ~ (v1_relat_1 @ sk_C))),
% 0.47/0.65      inference('sup+', [status(thm)], ['4', '48'])).
% 0.47/0.65  thf('50', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('51', plain,
% 0.47/0.65      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.47/0.65         (~ (v1_funct_1 @ X34)
% 0.47/0.65          | ~ (v3_funct_2 @ X34 @ X35 @ X36)
% 0.47/0.65          | (v2_funct_2 @ X34 @ X36)
% 0.47/0.65          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.47/0.65      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.47/0.65  thf('52', plain,
% 0.47/0.65      (((v2_funct_2 @ sk_C @ sk_A)
% 0.47/0.65        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.47/0.65        | ~ (v1_funct_1 @ sk_C))),
% 0.47/0.65      inference('sup-', [status(thm)], ['50', '51'])).
% 0.47/0.65  thf('53', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('54', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('55', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 0.47/0.65      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.47/0.65  thf(d3_funct_2, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.47/0.65       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.47/0.65  thf('56', plain,
% 0.47/0.65      (![X37 : $i, X38 : $i]:
% 0.47/0.65         (~ (v2_funct_2 @ X38 @ X37)
% 0.47/0.65          | ((k2_relat_1 @ X38) = (X37))
% 0.47/0.65          | ~ (v5_relat_1 @ X38 @ X37)
% 0.47/0.65          | ~ (v1_relat_1 @ X38))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.47/0.65  thf('57', plain,
% 0.47/0.65      ((~ (v1_relat_1 @ sk_C)
% 0.47/0.65        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 0.47/0.65        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['55', '56'])).
% 0.47/0.65  thf('58', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.65      inference('demod', [status(thm)], ['45', '46'])).
% 0.47/0.65  thf('59', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(cc2_relset_1, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i]:
% 0.47/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.65       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.47/0.65  thf('60', plain,
% 0.47/0.65      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.47/0.65         ((v5_relat_1 @ X23 @ X25)
% 0.47/0.65          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.47/0.65      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.65  thf('61', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.47/0.65      inference('sup-', [status(thm)], ['59', '60'])).
% 0.47/0.65  thf('62', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['57', '58', '61'])).
% 0.47/0.65  thf('63', plain,
% 0.47/0.65      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.47/0.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.65      inference('demod', [status(thm)], ['7', '8', '9', '10', '17'])).
% 0.47/0.65  thf('64', plain,
% 0.47/0.65      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.47/0.65         ((v4_relat_1 @ X23 @ X24)
% 0.47/0.65          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.47/0.65      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.65  thf('65', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)),
% 0.47/0.65      inference('sup-', [status(thm)], ['63', '64'])).
% 0.47/0.65  thf(t209_relat_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.47/0.65       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.47/0.65  thf('66', plain,
% 0.47/0.65      (![X13 : $i, X14 : $i]:
% 0.47/0.65         (((X13) = (k7_relat_1 @ X13 @ X14))
% 0.47/0.65          | ~ (v4_relat_1 @ X13 @ X14)
% 0.47/0.65          | ~ (v1_relat_1 @ X13))),
% 0.47/0.65      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.47/0.65  thf('67', plain,
% 0.47/0.65      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.47/0.65        | ((k2_funct_1 @ sk_C) = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['65', '66'])).
% 0.47/0.65  thf('68', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['20', '21'])).
% 0.47/0.65  thf('69', plain,
% 0.47/0.65      (((k2_funct_1 @ sk_C) = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.65  thf(t148_relat_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( v1_relat_1 @ B ) =>
% 0.47/0.65       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.47/0.65  thf('70', plain,
% 0.47/0.65      (![X10 : $i, X11 : $i]:
% 0.47/0.65         (((k2_relat_1 @ (k7_relat_1 @ X10 @ X11)) = (k9_relat_1 @ X10 @ X11))
% 0.47/0.65          | ~ (v1_relat_1 @ X10))),
% 0.47/0.65      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.47/0.65  thf('71', plain,
% 0.47/0.65      ((((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 0.47/0.65          = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A))
% 0.47/0.65        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.47/0.65      inference('sup+', [status(thm)], ['69', '70'])).
% 0.47/0.65  thf('72', plain,
% 0.47/0.65      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.47/0.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.65      inference('demod', [status(thm)], ['7', '8', '9', '10', '17'])).
% 0.47/0.65  thf('73', plain,
% 0.47/0.65      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.47/0.65         (~ (v1_funct_1 @ X34)
% 0.47/0.65          | ~ (v3_funct_2 @ X34 @ X35 @ X36)
% 0.47/0.65          | (v2_funct_2 @ X34 @ X36)
% 0.47/0.65          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.47/0.65      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.47/0.65  thf('74', plain,
% 0.47/0.65      (((v2_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A)
% 0.47/0.65        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_A)
% 0.47/0.65        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['72', '73'])).
% 0.47/0.65  thf('75', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('76', plain,
% 0.47/0.65      (![X39 : $i, X40 : $i]:
% 0.47/0.65         ((v3_funct_2 @ (k2_funct_2 @ X39 @ X40) @ X39 @ X39)
% 0.47/0.65          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))
% 0.47/0.65          | ~ (v3_funct_2 @ X40 @ X39 @ X39)
% 0.47/0.65          | ~ (v1_funct_2 @ X40 @ X39 @ X39)
% 0.47/0.65          | ~ (v1_funct_1 @ X40))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.47/0.65  thf('77', plain,
% 0.47/0.65      ((~ (v1_funct_1 @ sk_C)
% 0.47/0.65        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.47/0.65        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.47/0.65        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_C) @ sk_A @ sk_A))),
% 0.47/0.65      inference('sup-', [status(thm)], ['75', '76'])).
% 0.47/0.65  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('79', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('80', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('81', plain, (((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 0.47/0.65  thf('82', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_A)),
% 0.47/0.65      inference('demod', [status(thm)], ['77', '78', '79', '80', '81'])).
% 0.47/0.65  thf('83', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['33', '34'])).
% 0.47/0.65  thf('84', plain, ((v2_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A)),
% 0.47/0.65      inference('demod', [status(thm)], ['74', '82', '83'])).
% 0.47/0.65  thf('85', plain,
% 0.47/0.65      (![X37 : $i, X38 : $i]:
% 0.47/0.65         (~ (v2_funct_2 @ X38 @ X37)
% 0.47/0.65          | ((k2_relat_1 @ X38) = (X37))
% 0.47/0.65          | ~ (v5_relat_1 @ X38 @ X37)
% 0.47/0.65          | ~ (v1_relat_1 @ X38))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.47/0.65  thf('86', plain,
% 0.47/0.65      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.47/0.65        | ~ (v5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)
% 0.47/0.65        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['84', '85'])).
% 0.47/0.65  thf('87', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['20', '21'])).
% 0.47/0.65  thf('88', plain,
% 0.47/0.65      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.47/0.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.65      inference('demod', [status(thm)], ['7', '8', '9', '10', '17'])).
% 0.47/0.65  thf('89', plain,
% 0.47/0.65      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.47/0.65         ((v5_relat_1 @ X23 @ X25)
% 0.47/0.65          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.47/0.65      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.65  thf('90', plain, ((v5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)),
% 0.47/0.65      inference('sup-', [status(thm)], ['88', '89'])).
% 0.47/0.65  thf('91', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['86', '87', '90'])).
% 0.47/0.65  thf('92', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['20', '21'])).
% 0.47/0.65  thf('93', plain, (((sk_A) = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['71', '91', '92'])).
% 0.47/0.65  thf('94', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['57', '58', '61'])).
% 0.47/0.65  thf('95', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('96', plain,
% 0.47/0.65      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.47/0.65         ((v4_relat_1 @ X23 @ X24)
% 0.47/0.65          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.47/0.65      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.65  thf('97', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.47/0.65      inference('sup-', [status(thm)], ['95', '96'])).
% 0.47/0.65  thf('98', plain,
% 0.47/0.65      (![X13 : $i, X14 : $i]:
% 0.47/0.65         (((X13) = (k7_relat_1 @ X13 @ X14))
% 0.47/0.65          | ~ (v4_relat_1 @ X13 @ X14)
% 0.47/0.65          | ~ (v1_relat_1 @ X13))),
% 0.47/0.65      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.47/0.65  thf('99', plain,
% 0.47/0.65      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['97', '98'])).
% 0.47/0.65  thf('100', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.65      inference('demod', [status(thm)], ['45', '46'])).
% 0.47/0.65  thf('101', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['99', '100'])).
% 0.47/0.65  thf('102', plain,
% 0.47/0.65      (![X10 : $i, X11 : $i]:
% 0.47/0.65         (((k2_relat_1 @ (k7_relat_1 @ X10 @ X11)) = (k9_relat_1 @ X10 @ X11))
% 0.47/0.65          | ~ (v1_relat_1 @ X10))),
% 0.47/0.65      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.47/0.65  thf(t169_relat_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( v1_relat_1 @ A ) =>
% 0.47/0.65       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.47/0.65  thf('103', plain,
% 0.47/0.65      (![X12 : $i]:
% 0.47/0.65         (((k10_relat_1 @ X12 @ (k2_relat_1 @ X12)) = (k1_relat_1 @ X12))
% 0.47/0.65          | ~ (v1_relat_1 @ X12))),
% 0.47/0.65      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.47/0.65  thf('104', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.47/0.65            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.47/0.65          | ~ (v1_relat_1 @ X1)
% 0.47/0.65          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.47/0.65      inference('sup+', [status(thm)], ['102', '103'])).
% 0.47/0.65  thf('105', plain,
% 0.47/0.65      ((~ (v1_relat_1 @ sk_C)
% 0.47/0.65        | ~ (v1_relat_1 @ sk_C)
% 0.47/0.65        | ((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ 
% 0.47/0.65            (k9_relat_1 @ sk_C @ sk_A))
% 0.47/0.65            = (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['101', '104'])).
% 0.47/0.65  thf('106', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.65      inference('demod', [status(thm)], ['45', '46'])).
% 0.47/0.65  thf('107', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.65      inference('demod', [status(thm)], ['45', '46'])).
% 0.47/0.65  thf('108', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['99', '100'])).
% 0.47/0.65  thf('109', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['99', '100'])).
% 0.47/0.65  thf('110', plain,
% 0.47/0.65      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) = (k1_relat_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['105', '106', '107', '108', '109'])).
% 0.47/0.65  thf('111', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['99', '100'])).
% 0.47/0.65  thf('112', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.65      inference('demod', [status(thm)], ['45', '46'])).
% 0.47/0.65  thf('113', plain,
% 0.47/0.65      (![X10 : $i, X11 : $i]:
% 0.47/0.65         (((k2_relat_1 @ (k7_relat_1 @ X10 @ X11)) = (k9_relat_1 @ X10 @ X11))
% 0.47/0.65          | ~ (v1_relat_1 @ X10))),
% 0.47/0.65      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.47/0.65  thf('114', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((k2_relat_1 @ (k7_relat_1 @ sk_C @ X0)) = (k9_relat_1 @ sk_C @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['112', '113'])).
% 0.47/0.65  thf('115', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.47/0.65      inference('sup+', [status(thm)], ['111', '114'])).
% 0.47/0.65  thf('116', plain,
% 0.47/0.65      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['110', '115'])).
% 0.47/0.65  thf('117', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['57', '58', '61'])).
% 0.47/0.65  thf('118', plain, (((k10_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['116', '117'])).
% 0.47/0.65  thf('119', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('120', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.65      inference('demod', [status(thm)], ['45', '46'])).
% 0.47/0.65  thf('121', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)],
% 0.47/0.65                ['49', '62', '93', '94', '118', '119', '120'])).
% 0.47/0.65  thf(t164_funct_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.65       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.47/0.65         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.47/0.65  thf('122', plain,
% 0.47/0.65      (![X21 : $i, X22 : $i]:
% 0.47/0.65         (~ (r1_tarski @ X21 @ (k1_relat_1 @ X22))
% 0.47/0.65          | ~ (v2_funct_1 @ X22)
% 0.47/0.65          | ((k10_relat_1 @ X22 @ (k9_relat_1 @ X22 @ X21)) = (X21))
% 0.47/0.65          | ~ (v1_funct_1 @ X22)
% 0.47/0.65          | ~ (v1_relat_1 @ X22))),
% 0.47/0.65      inference('cnf', [status(esa)], [t164_funct_1])).
% 0.47/0.65  thf('123', plain,
% 0.47/0.65      ((~ (v1_relat_1 @ sk_C)
% 0.47/0.65        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.65        | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) = (sk_A))
% 0.47/0.65        | ~ (v2_funct_1 @ sk_C))),
% 0.47/0.65      inference('sup-', [status(thm)], ['121', '122'])).
% 0.47/0.65  thf('124', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.65      inference('demod', [status(thm)], ['45', '46'])).
% 0.47/0.65  thf('125', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('126', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.47/0.65      inference('sup+', [status(thm)], ['111', '114'])).
% 0.47/0.65  thf('127', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['57', '58', '61'])).
% 0.47/0.65  thf('128', plain, (((sk_A) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['126', '127'])).
% 0.47/0.65  thf('129', plain, (((k10_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['116', '117'])).
% 0.47/0.65  thf('130', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.65      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.47/0.65  thf('131', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.47/0.65      inference('demod', [status(thm)],
% 0.47/0.65                ['123', '124', '125', '128', '129', '130'])).
% 0.47/0.65  thf('132', plain,
% 0.47/0.65      (![X21 : $i, X22 : $i]:
% 0.47/0.65         (~ (r1_tarski @ X21 @ (k1_relat_1 @ X22))
% 0.47/0.65          | ~ (v2_funct_1 @ X22)
% 0.47/0.65          | ((k10_relat_1 @ X22 @ (k9_relat_1 @ X22 @ X21)) = (X21))
% 0.47/0.65          | ~ (v1_funct_1 @ X22)
% 0.47/0.65          | ~ (v1_relat_1 @ X22))),
% 0.47/0.65      inference('cnf', [status(esa)], [t164_funct_1])).
% 0.47/0.65  thf('133', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (r1_tarski @ X0 @ sk_A)
% 0.47/0.65          | ~ (v1_relat_1 @ sk_C)
% 0.47/0.65          | ~ (v1_funct_1 @ sk_C)
% 0.47/0.65          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0))
% 0.47/0.65          | ~ (v2_funct_1 @ sk_C))),
% 0.47/0.65      inference('sup-', [status(thm)], ['131', '132'])).
% 0.47/0.65  thf('134', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.65      inference('demod', [status(thm)], ['45', '46'])).
% 0.47/0.65  thf('135', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('136', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.65      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.47/0.65  thf('137', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (r1_tarski @ X0 @ sk_A)
% 0.47/0.65          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.47/0.65      inference('demod', [status(thm)], ['133', '134', '135', '136'])).
% 0.47/0.65  thf('138', plain,
% 0.47/0.65      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) = (sk_B))),
% 0.47/0.65      inference('sup-', [status(thm)], ['0', '137'])).
% 0.47/0.65  thf('139', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(redefinition_k8_relset_1, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.65       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.47/0.65  thf('140', plain,
% 0.47/0.65      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.47/0.65         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.47/0.65          | ((k8_relset_1 @ X31 @ X32 @ X30 @ X33) = (k10_relat_1 @ X30 @ X33)))),
% 0.47/0.65      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.47/0.65  thf('141', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['139', '140'])).
% 0.47/0.65  thf('142', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(redefinition_k7_relset_1, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.65       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.47/0.65  thf('143', plain,
% 0.47/0.65      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.47/0.65         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.47/0.65          | ((k7_relset_1 @ X27 @ X28 @ X26 @ X29) = (k9_relat_1 @ X26 @ X29)))),
% 0.47/0.65      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.47/0.65  thf('144', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['142', '143'])).
% 0.47/0.65  thf('145', plain,
% 0.47/0.65      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.47/0.65          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B))
% 0.47/0.65        | ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.47/0.65            (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('146', plain,
% 0.47/0.65      ((((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.47/0.65          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))
% 0.47/0.65         <= (~
% 0.47/0.65             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.47/0.65                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.47/0.65      inference('split', [status(esa)], ['145'])).
% 0.47/0.65  thf('147', plain,
% 0.47/0.65      ((((k8_relset_1 @ sk_A @ sk_A @ sk_C @ (k9_relat_1 @ sk_C @ sk_B))
% 0.47/0.65          != (sk_B)))
% 0.47/0.65         <= (~
% 0.47/0.65             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.47/0.65                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['144', '146'])).
% 0.47/0.65  thf('148', plain,
% 0.47/0.65      ((((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) != (sk_B)))
% 0.47/0.65         <= (~
% 0.47/0.65             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.47/0.65                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['141', '147'])).
% 0.47/0.65  thf('149', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['139', '140'])).
% 0.47/0.65  thf('150', plain,
% 0.47/0.65      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.47/0.65          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))
% 0.47/0.65         <= (~
% 0.47/0.65             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.47/0.65                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.47/0.65      inference('split', [status(esa)], ['145'])).
% 0.47/0.65  thf('151', plain,
% 0.47/0.65      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ (k10_relat_1 @ sk_C @ sk_B))
% 0.47/0.65          != (sk_B)))
% 0.47/0.65         <= (~
% 0.47/0.65             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.47/0.65                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['149', '150'])).
% 0.47/0.65  thf('152', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['142', '143'])).
% 0.47/0.65  thf('153', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('154', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['57', '58', '61'])).
% 0.47/0.65  thf('155', plain,
% 0.47/0.65      (![X17 : $i, X18 : $i]:
% 0.47/0.65         (~ (r1_tarski @ X17 @ (k2_relat_1 @ X18))
% 0.47/0.65          | ((k9_relat_1 @ X18 @ (k10_relat_1 @ X18 @ X17)) = (X17))
% 0.47/0.65          | ~ (v1_funct_1 @ X18)
% 0.47/0.65          | ~ (v1_relat_1 @ X18))),
% 0.47/0.65      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.47/0.65  thf('156', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (r1_tarski @ X0 @ sk_A)
% 0.47/0.65          | ~ (v1_relat_1 @ sk_C)
% 0.47/0.65          | ~ (v1_funct_1 @ sk_C)
% 0.47/0.65          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['154', '155'])).
% 0.47/0.65  thf('157', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.65      inference('demod', [status(thm)], ['45', '46'])).
% 0.47/0.65  thf('158', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('159', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (r1_tarski @ X0 @ sk_A)
% 0.47/0.65          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.47/0.65      inference('demod', [status(thm)], ['156', '157', '158'])).
% 0.47/0.65  thf('160', plain,
% 0.47/0.65      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)) = (sk_B))),
% 0.47/0.65      inference('sup-', [status(thm)], ['153', '159'])).
% 0.47/0.65  thf('161', plain,
% 0.47/0.65      ((((sk_B) != (sk_B)))
% 0.47/0.65         <= (~
% 0.47/0.65             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.47/0.65                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.47/0.65      inference('demod', [status(thm)], ['151', '152', '160'])).
% 0.47/0.65  thf('162', plain,
% 0.47/0.65      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.47/0.65          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.47/0.65      inference('simplify', [status(thm)], ['161'])).
% 0.47/0.65  thf('163', plain,
% 0.47/0.65      (~
% 0.47/0.65       (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.47/0.65          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))) | 
% 0.47/0.65       ~
% 0.47/0.65       (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.47/0.65          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.47/0.65      inference('split', [status(esa)], ['145'])).
% 0.47/0.65  thf('164', plain,
% 0.47/0.65      (~
% 0.47/0.65       (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.47/0.65          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.47/0.65      inference('sat_resolution*', [status(thm)], ['162', '163'])).
% 0.47/0.65  thf('165', plain,
% 0.47/0.65      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) != (sk_B))),
% 0.47/0.65      inference('simpl_trail', [status(thm)], ['148', '164'])).
% 0.47/0.65  thf('166', plain, ($false),
% 0.47/0.65      inference('simplify_reflect-', [status(thm)], ['138', '165'])).
% 0.47/0.65  
% 0.47/0.65  % SZS output end Refutation
% 0.47/0.65  
% 0.47/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
