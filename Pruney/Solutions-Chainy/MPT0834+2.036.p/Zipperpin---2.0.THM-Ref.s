%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qJSbLEEjKh

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:43 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 173 expanded)
%              Number of leaves         :   40 (  67 expanded)
%              Depth                    :   18
%              Number of atoms          :  854 (1779 expanded)
%              Number of equality atoms :   66 ( 125 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( ( k7_relset_1 @ X35 @ X36 @ X34 @ X37 )
        = ( k9_relat_1 @ X34 @ X37 ) ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) )
        = ( k9_relat_1 @ X6 @ X7 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X33 @ X31 )
        = ( k2_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
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
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( ( k8_relset_1 @ X39 @ X40 @ X38 @ X41 )
        = ( k10_relat_1 @ X38 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('37',plain,(
    ! [X10: $i] :
      ( ( ( k10_relat_1 @ X10 @ ( k2_relat_1 @ X10 ) )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(fc24_relat_1,axiom,(
    ! [A: $i] :
      ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('38',plain,(
    ! [X21: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X21 ) @ X21 ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v5_relat_1 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('41',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['39','40'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('42',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v5_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k2_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('45',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['43','44'])).

thf(t217_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v4_relat_1 @ C @ A ) )
         => ( v4_relat_1 @ C @ B ) ) ) )).

thf('46',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v4_relat_1 @ X13 @ X14 )
      | ( v4_relat_1 @ X13 @ X15 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t217_relat_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ sk_B )
      | ~ ( v4_relat_1 @ X0 @ ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ( v4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['38','47'])).

thf('49',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('50',plain,(
    v4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ( ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('54',plain,
    ( ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) )
    = ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('55',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X24 ) @ ( k6_relat_1 @ X23 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('56',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k7_relat_1 @ X19 @ X18 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X18 ) @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('60',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    = ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup+',[status(thm)],['54','61'])).

thf('63',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('64',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['62','63'])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('65',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k10_relat_1 @ X8 @ X9 )
        = ( k10_relat_1 @ X8 @ ( k3_xboole_0 @ ( k2_relat_1 @ X8 ) @ X9 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('66',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('68',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['37','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('71',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['33','36','71'])).

thf('73',plain,(
    $false ),
    inference(simplify,[status(thm)],['72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qJSbLEEjKh
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:32:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.19/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.51  % Solved by: fo/fo7.sh
% 0.19/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.51  % done 95 iterations in 0.044s
% 0.19/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.51  % SZS output start Refutation
% 0.19/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.51  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.19/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.51  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.19/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.51  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.51  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.51  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.19/0.51  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.51  thf(t38_relset_1, conjecture,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.51       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.19/0.51         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.19/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.51        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.51          ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.19/0.51            ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) )),
% 0.19/0.51    inference('cnf.neg', [status(esa)], [t38_relset_1])).
% 0.19/0.51  thf('0', plain,
% 0.19/0.51      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.19/0.51          != (k2_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.19/0.51        | ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.19/0.51            != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('1', plain,
% 0.19/0.51      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.19/0.51          != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.19/0.51         <= (~
% 0.19/0.51             (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.19/0.51                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.19/0.51      inference('split', [status(esa)], ['0'])).
% 0.19/0.51  thf('2', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(redefinition_k1_relset_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.51       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.19/0.51  thf('3', plain,
% 0.19/0.51      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.19/0.51         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 0.19/0.51          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.19/0.51      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.19/0.51  thf('4', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.19/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.51  thf('5', plain,
% 0.19/0.51      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) != (k1_relat_1 @ sk_C)))
% 0.19/0.51         <= (~
% 0.19/0.51             (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.19/0.51                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.19/0.51      inference('demod', [status(thm)], ['1', '4'])).
% 0.19/0.51  thf('6', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(redefinition_k7_relset_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.51       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.19/0.51  thf('7', plain,
% 0.19/0.51      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.19/0.51         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.19/0.51          | ((k7_relset_1 @ X35 @ X36 @ X34 @ X37) = (k9_relat_1 @ X34 @ X37)))),
% 0.19/0.51      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.19/0.51  thf('8', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.51  thf('9', plain,
% 0.19/0.51      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.19/0.51          != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.19/0.51         <= (~
% 0.19/0.51             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.19/0.51                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.19/0.51      inference('split', [status(esa)], ['0'])).
% 0.19/0.51  thf('10', plain,
% 0.19/0.51      ((((k9_relat_1 @ sk_C @ sk_A) != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.19/0.51         <= (~
% 0.19/0.51             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.19/0.51                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.51  thf('11', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(cc2_relset_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.19/0.51  thf('12', plain,
% 0.19/0.51      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.19/0.51         ((v4_relat_1 @ X25 @ X26)
% 0.19/0.51          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.19/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.51  thf('13', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.19/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.51  thf(t209_relat_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.19/0.51       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.19/0.51  thf('14', plain,
% 0.19/0.51      (![X11 : $i, X12 : $i]:
% 0.19/0.51         (((X11) = (k7_relat_1 @ X11 @ X12))
% 0.19/0.51          | ~ (v4_relat_1 @ X11 @ X12)
% 0.19/0.51          | ~ (v1_relat_1 @ X11))),
% 0.19/0.51      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.19/0.51  thf('15', plain,
% 0.19/0.51      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.51  thf('16', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(cc2_relat_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ A ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.19/0.51  thf('17', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.19/0.51          | (v1_relat_1 @ X0)
% 0.19/0.51          | ~ (v1_relat_1 @ X1))),
% 0.19/0.51      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.19/0.51  thf('18', plain,
% 0.19/0.51      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.19/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.51  thf(fc6_relat_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.19/0.51  thf('19', plain,
% 0.19/0.51      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.19/0.51      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.19/0.51  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.51      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.51  thf('21', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['15', '20'])).
% 0.19/0.51  thf(t148_relat_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ B ) =>
% 0.19/0.51       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.19/0.51  thf('22', plain,
% 0.19/0.51      (![X6 : $i, X7 : $i]:
% 0.19/0.51         (((k2_relat_1 @ (k7_relat_1 @ X6 @ X7)) = (k9_relat_1 @ X6 @ X7))
% 0.19/0.51          | ~ (v1_relat_1 @ X6))),
% 0.19/0.51      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.19/0.51  thf('23', plain,
% 0.19/0.51      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 0.19/0.51        | ~ (v1_relat_1 @ sk_C))),
% 0.19/0.51      inference('sup+', [status(thm)], ['21', '22'])).
% 0.19/0.51  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.51      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.51  thf('25', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['23', '24'])).
% 0.19/0.51  thf('26', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(redefinition_k2_relset_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.51       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.19/0.51  thf('27', plain,
% 0.19/0.51      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.19/0.51         (((k2_relset_1 @ X32 @ X33 @ X31) = (k2_relat_1 @ X31))
% 0.19/0.51          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.19/0.51      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.19/0.51  thf('28', plain,
% 0.19/0.51      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.19/0.51      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.51  thf('29', plain,
% 0.19/0.51      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.19/0.51         <= (~
% 0.19/0.51             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.19/0.51                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.19/0.51      inference('demod', [status(thm)], ['10', '25', '28'])).
% 0.19/0.51  thf('30', plain,
% 0.19/0.51      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.19/0.51          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.19/0.51      inference('simplify', [status(thm)], ['29'])).
% 0.19/0.51  thf('31', plain,
% 0.19/0.51      (~
% 0.19/0.51       (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.19/0.51          = (k1_relset_1 @ sk_A @ sk_B @ sk_C))) | 
% 0.19/0.51       ~
% 0.19/0.51       (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.19/0.51          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.19/0.51      inference('split', [status(esa)], ['0'])).
% 0.19/0.51  thf('32', plain,
% 0.19/0.51      (~
% 0.19/0.51       (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.19/0.51          = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.19/0.51      inference('sat_resolution*', [status(thm)], ['30', '31'])).
% 0.19/0.51  thf('33', plain,
% 0.19/0.51      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) != (k1_relat_1 @ sk_C))),
% 0.19/0.51      inference('simpl_trail', [status(thm)], ['5', '32'])).
% 0.19/0.51  thf('34', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(redefinition_k8_relset_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.51       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.19/0.51  thf('35', plain,
% 0.19/0.51      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.19/0.51         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.19/0.51          | ((k8_relset_1 @ X39 @ X40 @ X38 @ X41) = (k10_relat_1 @ X38 @ X41)))),
% 0.19/0.51      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.19/0.51  thf('36', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['34', '35'])).
% 0.19/0.51  thf(t169_relat_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ A ) =>
% 0.19/0.51       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.19/0.51  thf('37', plain,
% 0.19/0.51      (![X10 : $i]:
% 0.19/0.51         (((k10_relat_1 @ X10 @ (k2_relat_1 @ X10)) = (k1_relat_1 @ X10))
% 0.19/0.51          | ~ (v1_relat_1 @ X10))),
% 0.19/0.51      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.19/0.51  thf(fc24_relat_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.19/0.51       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.19/0.51       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.19/0.51  thf('38', plain, (![X21 : $i]: (v4_relat_1 @ (k6_relat_1 @ X21) @ X21)),
% 0.19/0.51      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.19/0.51  thf('39', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('40', plain,
% 0.19/0.51      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.19/0.51         ((v5_relat_1 @ X25 @ X27)
% 0.19/0.51          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.19/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.51  thf('41', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.19/0.51      inference('sup-', [status(thm)], ['39', '40'])).
% 0.19/0.51  thf(d19_relat_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ B ) =>
% 0.19/0.51       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.51  thf('42', plain,
% 0.19/0.51      (![X2 : $i, X3 : $i]:
% 0.19/0.51         (~ (v5_relat_1 @ X2 @ X3)
% 0.19/0.51          | (r1_tarski @ (k2_relat_1 @ X2) @ X3)
% 0.19/0.51          | ~ (v1_relat_1 @ X2))),
% 0.19/0.51      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.19/0.51  thf('43', plain,
% 0.19/0.51      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.19/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.19/0.51  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.51      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.51  thf('45', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.19/0.51      inference('demod', [status(thm)], ['43', '44'])).
% 0.19/0.51  thf(t217_relat_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( r1_tarski @ A @ B ) =>
% 0.19/0.51       ( ![C:$i]:
% 0.19/0.51         ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ A ) ) =>
% 0.19/0.51           ( v4_relat_1 @ C @ B ) ) ) ))).
% 0.19/0.51  thf('46', plain,
% 0.19/0.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ X13)
% 0.19/0.51          | ~ (v4_relat_1 @ X13 @ X14)
% 0.19/0.51          | (v4_relat_1 @ X13 @ X15)
% 0.19/0.51          | ~ (r1_tarski @ X14 @ X15))),
% 0.19/0.51      inference('cnf', [status(esa)], [t217_relat_1])).
% 0.19/0.51  thf('47', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((v4_relat_1 @ X0 @ sk_B)
% 0.19/0.51          | ~ (v4_relat_1 @ X0 @ (k2_relat_1 @ sk_C))
% 0.19/0.51          | ~ (v1_relat_1 @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['45', '46'])).
% 0.19/0.51  thf('48', plain,
% 0.19/0.51      ((~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.19/0.51        | (v4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B))),
% 0.19/0.51      inference('sup-', [status(thm)], ['38', '47'])).
% 0.19/0.51  thf('49', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.19/0.51      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.19/0.51  thf('50', plain, ((v4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B)),
% 0.19/0.51      inference('demod', [status(thm)], ['48', '49'])).
% 0.19/0.51  thf('51', plain,
% 0.19/0.51      (![X11 : $i, X12 : $i]:
% 0.19/0.51         (((X11) = (k7_relat_1 @ X11 @ X12))
% 0.19/0.51          | ~ (v4_relat_1 @ X11 @ X12)
% 0.19/0.51          | ~ (v1_relat_1 @ X11))),
% 0.19/0.51      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.19/0.51  thf('52', plain,
% 0.19/0.51      ((~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.19/0.51        | ((k6_relat_1 @ (k2_relat_1 @ sk_C))
% 0.19/0.51            = (k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['50', '51'])).
% 0.19/0.51  thf('53', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.19/0.51      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.19/0.51  thf('54', plain,
% 0.19/0.51      (((k6_relat_1 @ (k2_relat_1 @ sk_C))
% 0.19/0.51         = (k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B))),
% 0.19/0.51      inference('demod', [status(thm)], ['52', '53'])).
% 0.19/0.51  thf(t43_funct_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.19/0.51       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.51  thf('55', plain,
% 0.19/0.51      (![X23 : $i, X24 : $i]:
% 0.19/0.51         ((k5_relat_1 @ (k6_relat_1 @ X24) @ (k6_relat_1 @ X23))
% 0.19/0.51           = (k6_relat_1 @ (k3_xboole_0 @ X23 @ X24)))),
% 0.19/0.51      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.19/0.51  thf(t94_relat_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ B ) =>
% 0.19/0.51       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.19/0.51  thf('56', plain,
% 0.19/0.51      (![X18 : $i, X19 : $i]:
% 0.19/0.51         (((k7_relat_1 @ X19 @ X18) = (k5_relat_1 @ (k6_relat_1 @ X18) @ X19))
% 0.19/0.51          | ~ (v1_relat_1 @ X19))),
% 0.19/0.51      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.19/0.51  thf('57', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.19/0.51            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.19/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.19/0.51      inference('sup+', [status(thm)], ['55', '56'])).
% 0.19/0.51  thf('58', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.19/0.51      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.19/0.51  thf('59', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.19/0.51           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.19/0.51      inference('demod', [status(thm)], ['57', '58'])).
% 0.19/0.51  thf(t71_relat_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.19/0.51       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.19/0.51  thf('60', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.19/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.51  thf('61', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.19/0.51           = (k3_xboole_0 @ X1 @ X0))),
% 0.19/0.51      inference('sup+', [status(thm)], ['59', '60'])).
% 0.19/0.51  thf('62', plain,
% 0.19/0.51      (((k1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.19/0.51         = (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.19/0.51      inference('sup+', [status(thm)], ['54', '61'])).
% 0.19/0.51  thf('63', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.19/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.51  thf('64', plain,
% 0.19/0.51      (((k2_relat_1 @ sk_C) = (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.19/0.51      inference('demod', [status(thm)], ['62', '63'])).
% 0.19/0.51  thf(t168_relat_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ B ) =>
% 0.19/0.51       ( ( k10_relat_1 @ B @ A ) =
% 0.19/0.51         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 0.19/0.51  thf('65', plain,
% 0.19/0.51      (![X8 : $i, X9 : $i]:
% 0.19/0.51         (((k10_relat_1 @ X8 @ X9)
% 0.19/0.51            = (k10_relat_1 @ X8 @ (k3_xboole_0 @ (k2_relat_1 @ X8) @ X9)))
% 0.19/0.51          | ~ (v1_relat_1 @ X8))),
% 0.19/0.51      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.19/0.51  thf('66', plain,
% 0.19/0.51      ((((k10_relat_1 @ sk_C @ sk_B)
% 0.19/0.51          = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.19/0.51        | ~ (v1_relat_1 @ sk_C))),
% 0.19/0.51      inference('sup+', [status(thm)], ['64', '65'])).
% 0.19/0.51  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.51      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.51  thf('68', plain,
% 0.19/0.51      (((k10_relat_1 @ sk_C @ sk_B)
% 0.19/0.51         = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 0.19/0.51      inference('demod', [status(thm)], ['66', '67'])).
% 0.19/0.51  thf('69', plain,
% 0.19/0.51      ((((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))
% 0.19/0.51        | ~ (v1_relat_1 @ sk_C))),
% 0.19/0.51      inference('sup+', [status(thm)], ['37', '68'])).
% 0.19/0.51  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.51      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.51  thf('71', plain, (((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))),
% 0.19/0.51      inference('demod', [status(thm)], ['69', '70'])).
% 0.19/0.51  thf('72', plain, (((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))),
% 0.19/0.51      inference('demod', [status(thm)], ['33', '36', '71'])).
% 0.19/0.51  thf('73', plain, ($false), inference('simplify', [status(thm)], ['72'])).
% 0.19/0.51  
% 0.19/0.51  % SZS output end Refutation
% 0.19/0.51  
% 0.19/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
