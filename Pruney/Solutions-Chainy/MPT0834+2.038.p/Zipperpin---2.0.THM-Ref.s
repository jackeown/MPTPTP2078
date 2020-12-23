%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.X0sqp6SheY

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 247 expanded)
%              Number of leaves         :   37 (  89 expanded)
%              Depth                    :   14
%              Number of atoms          :  795 (2668 expanded)
%              Number of equality atoms :   63 ( 178 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t38_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( ( ( k7_relset_1 @ A @ B @ C @ A )
            = ( k2_relset_1 @ A @ B @ C ) )
          & ( ( k8_relset_1 @ A @ B @ C @ B )
            = ( k1_relset_1 @ A @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_relset_1])).

thf('0',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('4',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('7',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k7_relset_1 @ X31 @ X32 @ X30 @ X33 )
        = ( k9_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ( ( k9_relat_1 @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('13',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12
        = ( k7_relat_1 @ X12 @ X13 ) )
      | ~ ( v4_relat_1 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['15','20'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) )
        = ( k9_relat_1 @ X8 @ X9 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('23',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('25',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('27',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('28',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['10','25','28'])).

thf('30',plain,
    ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
 != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['30','31'])).

thf('33',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['5','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('35',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( ( k8_relset_1 @ X35 @ X36 @ X34 @ X37 )
        = ( k10_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('38',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X21 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('39',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('41',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('43',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('45',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) )
        = ( k9_relat_1 @ X8 @ X9 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('46',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X16 ) @ X17 )
      | ( ( k5_relat_1 @ X16 @ ( k6_relat_1 @ X17 ) )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k6_relat_1 @ X2 ) )
        = ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k6_relat_1 @ X0 ) )
        = ( k7_relat_1 @ sk_C @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('50',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('51',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('52',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('53',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ X0 ) )
        = sk_C ) ) ),
    inference(demod,[status(thm)],['48','49','50','51','52','53'])).

thf('55',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
    = sk_C ),
    inference('sup-',[status(thm)],['43','54'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('56',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('57',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) )
        = ( k10_relat_1 @ X11 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('59',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['55','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('63',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['33','36','63'])).

thf('65',plain,(
    $false ),
    inference(simplify,[status(thm)],['64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.X0sqp6SheY
% 0.13/0.35  % Computer   : n001.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:22:15 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 57 iterations in 0.027s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.50  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.22/0.50  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.50  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.50  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.50  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.50  thf(t38_relset_1, conjecture,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.22/0.50         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.50        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50          ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.22/0.50            ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t38_relset_1])).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.22/0.50          != (k2_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.50        | ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.22/0.50            != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.22/0.50          != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.22/0.50         <= (~
% 0.22/0.50             (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.22/0.50                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(redefinition_k1_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.22/0.50         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 0.22/0.50          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.22/0.50  thf('4', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) != (k1_relat_1 @ sk_C)))
% 0.22/0.50         <= (~
% 0.22/0.50             (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.22/0.50                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.22/0.50      inference('demod', [status(thm)], ['1', '4'])).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(redefinition_k7_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.22/0.50          | ((k7_relset_1 @ X31 @ X32 @ X30 @ X33) = (k9_relat_1 @ X30 @ X33)))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.22/0.50          != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.22/0.50         <= (~
% 0.22/0.50             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.22/0.50                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      ((((k9_relat_1 @ sk_C @ sk_A) != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.22/0.50         <= (~
% 0.22/0.50             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.22/0.50                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(cc2_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.50         ((v4_relat_1 @ X18 @ X19)
% 0.22/0.50          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.50  thf('13', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.22/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.50  thf(t209_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.22/0.50       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (![X12 : $i, X13 : $i]:
% 0.22/0.50         (((X12) = (k7_relat_1 @ X12 @ X13))
% 0.22/0.50          | ~ (v4_relat_1 @ X12 @ X13)
% 0.22/0.50          | ~ (v1_relat_1 @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(cc2_relat_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (![X3 : $i, X4 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.22/0.50          | (v1_relat_1 @ X3)
% 0.22/0.50          | ~ (v1_relat_1 @ X4))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.50  thf(fc6_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.50  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.50      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.50  thf('21', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['15', '20'])).
% 0.22/0.50  thf(t148_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ B ) =>
% 0.22/0.50       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      (![X8 : $i, X9 : $i]:
% 0.22/0.50         (((k2_relat_1 @ (k7_relat_1 @ X8 @ X9)) = (k9_relat_1 @ X8 @ X9))
% 0.22/0.50          | ~ (v1_relat_1 @ X8))),
% 0.22/0.50      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 0.22/0.50        | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.50      inference('sup+', [status(thm)], ['21', '22'])).
% 0.22/0.50  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.50      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.50  thf('25', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['23', '24'])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(redefinition_k2_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.22/0.50         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 0.22/0.50          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.50  thf('29', plain,
% 0.22/0.50      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.22/0.50         <= (~
% 0.22/0.50             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.22/0.50                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.22/0.50      inference('demod', [status(thm)], ['10', '25', '28'])).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.22/0.50          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['29'])).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      (~
% 0.22/0.50       (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.22/0.50          = (k1_relset_1 @ sk_A @ sk_B @ sk_C))) | 
% 0.22/0.50       ~
% 0.22/0.50       (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.22/0.50          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      (~
% 0.22/0.50       (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.22/0.50          = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['30', '31'])).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) != (k1_relat_1 @ sk_C))),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['5', '32'])).
% 0.22/0.50  thf('34', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(redefinition_k8_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.22/0.50          | ((k8_relset_1 @ X35 @ X36 @ X34 @ X37) = (k10_relat_1 @ X34 @ X37)))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.22/0.50  thf('36', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.50  thf('37', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(dt_k2_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.22/0.50         ((m1_subset_1 @ (k2_relset_1 @ X21 @ X22 @ X23) @ (k1_zfmisc_1 @ X22))
% 0.22/0.50          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.22/0.50  thf('39', plain,
% 0.22/0.50      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.50  thf(t3_subset, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.50  thf('40', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.50  thf('41', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_C) @ sk_B)),
% 0.22/0.50      inference('sup-', [status(thm)], ['39', '40'])).
% 0.22/0.50  thf('42', plain,
% 0.22/0.50      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.50  thf('43', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.22/0.50      inference('demod', [status(thm)], ['41', '42'])).
% 0.22/0.50  thf('44', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['23', '24'])).
% 0.22/0.50  thf('45', plain,
% 0.22/0.50      (![X8 : $i, X9 : $i]:
% 0.22/0.50         (((k2_relat_1 @ (k7_relat_1 @ X8 @ X9)) = (k9_relat_1 @ X8 @ X9))
% 0.22/0.50          | ~ (v1_relat_1 @ X8))),
% 0.22/0.50      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.22/0.50  thf(t79_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ B ) =>
% 0.22/0.50       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.22/0.50         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.22/0.50  thf('46', plain,
% 0.22/0.50      (![X16 : $i, X17 : $i]:
% 0.22/0.50         (~ (r1_tarski @ (k2_relat_1 @ X16) @ X17)
% 0.22/0.50          | ((k5_relat_1 @ X16 @ (k6_relat_1 @ X17)) = (X16))
% 0.22/0.50          | ~ (v1_relat_1 @ X16))),
% 0.22/0.50      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.22/0.50  thf('47', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.22/0.50          | ~ (v1_relat_1 @ X1)
% 0.22/0.50          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.22/0.50          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k6_relat_1 @ X2))
% 0.22/0.50              = (k7_relat_1 @ X1 @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.50  thf('48', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (r1_tarski @ (k2_relat_1 @ sk_C) @ X0)
% 0.22/0.50          | ((k5_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ (k6_relat_1 @ X0))
% 0.22/0.50              = (k7_relat_1 @ sk_C @ sk_A))
% 0.22/0.50          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A))
% 0.22/0.50          | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['44', '47'])).
% 0.22/0.50  thf('49', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['15', '20'])).
% 0.22/0.50  thf('50', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['15', '20'])).
% 0.22/0.50  thf('51', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['15', '20'])).
% 0.22/0.50  thf('52', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.50      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.50  thf('53', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.50      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.50  thf('54', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (r1_tarski @ (k2_relat_1 @ sk_C) @ X0)
% 0.22/0.50          | ((k5_relat_1 @ sk_C @ (k6_relat_1 @ X0)) = (sk_C)))),
% 0.22/0.50      inference('demod', [status(thm)], ['48', '49', '50', '51', '52', '53'])).
% 0.22/0.50  thf('55', plain, (((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['43', '54'])).
% 0.22/0.50  thf(t71_relat_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.22/0.50       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.50  thf('56', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 0.22/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.50  thf(t182_relat_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( v1_relat_1 @ B ) =>
% 0.22/0.50           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.22/0.50             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.22/0.50  thf('57', plain,
% 0.22/0.50      (![X10 : $i, X11 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X10)
% 0.22/0.50          | ((k1_relat_1 @ (k5_relat_1 @ X11 @ X10))
% 0.22/0.50              = (k10_relat_1 @ X11 @ (k1_relat_1 @ X10)))
% 0.22/0.50          | ~ (v1_relat_1 @ X11))),
% 0.22/0.50      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.22/0.50  thf('58', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.22/0.50            = (k10_relat_1 @ X1 @ X0))
% 0.22/0.50          | ~ (v1_relat_1 @ X1)
% 0.22/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['56', '57'])).
% 0.22/0.50  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.22/0.50  thf('59', plain, (![X5 : $i]: (v1_relat_1 @ (k6_relat_1 @ X5))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.50  thf('60', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.22/0.50            = (k10_relat_1 @ X1 @ X0))
% 0.22/0.50          | ~ (v1_relat_1 @ X1))),
% 0.22/0.50      inference('demod', [status(thm)], ['58', '59'])).
% 0.22/0.50  thf('61', plain,
% 0.22/0.50      ((((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B))
% 0.22/0.50        | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.50      inference('sup+', [status(thm)], ['55', '60'])).
% 0.22/0.50  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.50      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.50  thf('63', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['61', '62'])).
% 0.22/0.50  thf('64', plain, (((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))),
% 0.22/0.50      inference('demod', [status(thm)], ['33', '36', '63'])).
% 0.22/0.50  thf('65', plain, ($false), inference('simplify', [status(thm)], ['64'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
