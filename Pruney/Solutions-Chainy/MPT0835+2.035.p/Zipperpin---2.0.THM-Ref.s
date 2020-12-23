%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jhyAHnFMlC

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:49 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 379 expanded)
%              Number of leaves         :   37 ( 128 expanded)
%              Depth                    :   16
%              Number of atoms          : 1039 (4604 expanded)
%              Number of equality atoms :   70 ( 247 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('9',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X38 ) @ X39 )
      | ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('13',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17
        = ( k7_relat_1 @ X17 @ X18 ) )
      | ~ ( v4_relat_1 @ X17 @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('23',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('25',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( r1_tarski @ X19 @ ( k10_relat_1 @ X20 @ ( k9_relat_1 @ X20 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X13 @ X14 ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('30',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['25','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('37',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('38',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v5_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('41',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['39','40'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('42',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('43',plain,
    ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_A )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('44',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k10_relat_1 @ X15 @ X16 )
        = ( k10_relat_1 @ X15 @ ( k3_xboole_0 @ ( k2_relat_1 @ X15 ) @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('45',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_A )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('47',plain,
    ( ( k10_relat_1 @ sk_C @ sk_A )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('49',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['34','47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('51',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k7_relset_1 @ X31 @ X32 @ X30 @ X33 )
        = ( k9_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('55',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('56',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['5','49','52','53','56'])).

thf('58',plain,
    ( $false
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('60',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('61',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('65',plain,(
    v4_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17
        = ( k7_relat_1 @ X17 @ X18 ) )
      | ~ ( v4_relat_1 @ X17 @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('67',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('69',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('71',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('73',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k10_relat_1 @ sk_C @ sk_A )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('75',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['34','47','48'])).

thf('76',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('78',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('79',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['61','62','73','76','79'])).

thf('81',plain,
    ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    = ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('83',plain,(
    ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
 != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['81','82'])).

thf('84',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['58','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jhyAHnFMlC
% 0.10/0.30  % Computer   : n004.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % DateTime   : Tue Dec  1 10:27:39 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.30  % Running portfolio for 600 s
% 0.10/0.30  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.10/0.30  % Number of cores: 8
% 0.10/0.31  % Python version: Python 3.6.8
% 0.10/0.31  % Running in FO mode
% 0.15/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.15/0.48  % Solved by: fo/fo7.sh
% 0.15/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.15/0.48  % done 124 iterations in 0.059s
% 0.15/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.15/0.48  % SZS output start Refutation
% 0.15/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.15/0.48  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.15/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.15/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.15/0.48  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.15/0.48  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.15/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.15/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.15/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.15/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.15/0.48  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.15/0.48  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.15/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.15/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.15/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.15/0.48  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.15/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.15/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.15/0.48  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.15/0.48  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.15/0.48  thf(t39_relset_1, conjecture,
% 0.15/0.48    (![A:$i,B:$i,C:$i]:
% 0.15/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.15/0.48       ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.15/0.48           ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.15/0.48         ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.15/0.48           ( k1_relset_1 @ B @ A @ C ) ) ) ))).
% 0.15/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.15/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.15/0.48        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.15/0.48          ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.15/0.48              ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.15/0.48            ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.15/0.48              ( k1_relset_1 @ B @ A @ C ) ) ) ) )),
% 0.15/0.48    inference('cnf.neg', [status(esa)], [t39_relset_1])).
% 0.15/0.48  thf('0', plain,
% 0.15/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.15/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.15/0.48  thf(redefinition_k8_relset_1, axiom,
% 0.15/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.15/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.15/0.48       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.15/0.48  thf('1', plain,
% 0.15/0.48      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.15/0.48         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.15/0.48          | ((k8_relset_1 @ X35 @ X36 @ X34 @ X37) = (k10_relat_1 @ X34 @ X37)))),
% 0.15/0.48      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.15/0.48  thf('2', plain,
% 0.15/0.48      (![X0 : $i]:
% 0.15/0.48         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.15/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.15/0.48  thf('3', plain,
% 0.15/0.48      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.15/0.48          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.15/0.48          != (k2_relset_1 @ sk_B @ sk_A @ sk_C))
% 0.15/0.48        | ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.15/0.48            (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.15/0.48            != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.15/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.15/0.48  thf('4', plain,
% 0.15/0.48      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.15/0.48          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.15/0.48          != (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.15/0.48         <= (~
% 0.15/0.48             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.15/0.48                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.15/0.48                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.15/0.48      inference('split', [status(esa)], ['3'])).
% 0.15/0.48  thf('5', plain,
% 0.15/0.48      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ (k10_relat_1 @ sk_C @ sk_A))
% 0.15/0.48          != (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.15/0.48         <= (~
% 0.15/0.48             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.15/0.48                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.15/0.48                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.15/0.48      inference('sup-', [status(thm)], ['2', '4'])).
% 0.15/0.48  thf(d10_xboole_0, axiom,
% 0.15/0.48    (![A:$i,B:$i]:
% 0.15/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.15/0.48  thf('6', plain,
% 0.15/0.48      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.15/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.15/0.48  thf('7', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.15/0.48      inference('simplify', [status(thm)], ['6'])).
% 0.15/0.48  thf('8', plain,
% 0.15/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.15/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.15/0.48  thf(t13_relset_1, axiom,
% 0.15/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.15/0.48     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.15/0.48       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.15/0.48         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.15/0.48  thf('9', plain,
% 0.15/0.48      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.15/0.48         (~ (r1_tarski @ (k1_relat_1 @ X38) @ X39)
% 0.15/0.48          | (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.15/0.48          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 0.15/0.48      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.15/0.48  thf('10', plain,
% 0.15/0.48      (![X0 : $i]:
% 0.15/0.48         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A)))
% 0.15/0.48          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.15/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.15/0.48  thf('11', plain,
% 0.15/0.48      ((m1_subset_1 @ sk_C @ 
% 0.15/0.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A)))),
% 0.15/0.48      inference('sup-', [status(thm)], ['7', '10'])).
% 0.15/0.48  thf(cc2_relset_1, axiom,
% 0.15/0.48    (![A:$i,B:$i,C:$i]:
% 0.15/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.15/0.48       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.15/0.48  thf('12', plain,
% 0.15/0.48      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.15/0.48         ((v4_relat_1 @ X21 @ X22)
% 0.15/0.48          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.15/0.48      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.15/0.48  thf('13', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.15/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.15/0.48  thf(t209_relat_1, axiom,
% 0.15/0.48    (![A:$i,B:$i]:
% 0.15/0.48     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.15/0.48       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.15/0.48  thf('14', plain,
% 0.15/0.48      (![X17 : $i, X18 : $i]:
% 0.15/0.48         (((X17) = (k7_relat_1 @ X17 @ X18))
% 0.15/0.48          | ~ (v4_relat_1 @ X17 @ X18)
% 0.15/0.48          | ~ (v1_relat_1 @ X17))),
% 0.15/0.48      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.15/0.48  thf('15', plain,
% 0.15/0.48      ((~ (v1_relat_1 @ sk_C)
% 0.15/0.48        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))),
% 0.15/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.15/0.48  thf('16', plain,
% 0.15/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.15/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.15/0.48  thf(cc2_relat_1, axiom,
% 0.15/0.48    (![A:$i]:
% 0.15/0.48     ( ( v1_relat_1 @ A ) =>
% 0.15/0.48       ( ![B:$i]:
% 0.15/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.15/0.48  thf('17', plain,
% 0.15/0.48      (![X5 : $i, X6 : $i]:
% 0.15/0.48         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.15/0.48          | (v1_relat_1 @ X5)
% 0.15/0.48          | ~ (v1_relat_1 @ X6))),
% 0.15/0.48      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.15/0.48  thf('18', plain,
% 0.15/0.48      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.15/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.15/0.48  thf(fc6_relat_1, axiom,
% 0.15/0.48    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.15/0.48  thf('19', plain,
% 0.15/0.48      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.15/0.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.15/0.48  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 0.15/0.48      inference('demod', [status(thm)], ['18', '19'])).
% 0.15/0.48  thf('21', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.15/0.48      inference('demod', [status(thm)], ['15', '20'])).
% 0.15/0.48  thf(t148_relat_1, axiom,
% 0.15/0.48    (![A:$i,B:$i]:
% 0.15/0.48     ( ( v1_relat_1 @ B ) =>
% 0.15/0.48       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.15/0.48  thf('22', plain,
% 0.15/0.48      (![X11 : $i, X12 : $i]:
% 0.15/0.48         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.15/0.48          | ~ (v1_relat_1 @ X11))),
% 0.15/0.48      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.15/0.48  thf('23', plain,
% 0.15/0.48      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 0.15/0.48        | ~ (v1_relat_1 @ sk_C))),
% 0.15/0.48      inference('sup+', [status(thm)], ['21', '22'])).
% 0.15/0.48  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 0.15/0.48      inference('demod', [status(thm)], ['18', '19'])).
% 0.15/0.48  thf('25', plain,
% 0.15/0.48      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.15/0.48      inference('demod', [status(thm)], ['23', '24'])).
% 0.15/0.48  thf('26', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.15/0.48      inference('simplify', [status(thm)], ['6'])).
% 0.15/0.48  thf(t146_funct_1, axiom,
% 0.15/0.48    (![A:$i,B:$i]:
% 0.15/0.48     ( ( v1_relat_1 @ B ) =>
% 0.15/0.48       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.15/0.48         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.15/0.48  thf('27', plain,
% 0.15/0.48      (![X19 : $i, X20 : $i]:
% 0.15/0.48         (~ (r1_tarski @ X19 @ (k1_relat_1 @ X20))
% 0.15/0.48          | (r1_tarski @ X19 @ (k10_relat_1 @ X20 @ (k9_relat_1 @ X20 @ X19)))
% 0.15/0.48          | ~ (v1_relat_1 @ X20))),
% 0.15/0.48      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.15/0.48  thf('28', plain,
% 0.15/0.48      (![X0 : $i]:
% 0.15/0.48         (~ (v1_relat_1 @ X0)
% 0.15/0.48          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.15/0.48             (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 0.15/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.15/0.48  thf(t167_relat_1, axiom,
% 0.15/0.48    (![A:$i,B:$i]:
% 0.15/0.48     ( ( v1_relat_1 @ B ) =>
% 0.15/0.48       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.15/0.48  thf('29', plain,
% 0.15/0.48      (![X13 : $i, X14 : $i]:
% 0.15/0.48         ((r1_tarski @ (k10_relat_1 @ X13 @ X14) @ (k1_relat_1 @ X13))
% 0.15/0.48          | ~ (v1_relat_1 @ X13))),
% 0.15/0.48      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.15/0.48  thf('30', plain,
% 0.15/0.48      (![X0 : $i, X2 : $i]:
% 0.15/0.48         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.15/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.15/0.48  thf('31', plain,
% 0.15/0.48      (![X0 : $i, X1 : $i]:
% 0.15/0.48         (~ (v1_relat_1 @ X0)
% 0.15/0.48          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.15/0.48          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 0.15/0.48      inference('sup-', [status(thm)], ['29', '30'])).
% 0.15/0.48  thf('32', plain,
% 0.15/0.48      (![X0 : $i]:
% 0.15/0.48         (~ (v1_relat_1 @ X0)
% 0.15/0.48          | ((k1_relat_1 @ X0)
% 0.15/0.48              = (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 0.15/0.48          | ~ (v1_relat_1 @ X0))),
% 0.15/0.48      inference('sup-', [status(thm)], ['28', '31'])).
% 0.15/0.48  thf('33', plain,
% 0.15/0.48      (![X0 : $i]:
% 0.15/0.48         (((k1_relat_1 @ X0)
% 0.15/0.48            = (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 0.15/0.48          | ~ (v1_relat_1 @ X0))),
% 0.15/0.48      inference('simplify', [status(thm)], ['32'])).
% 0.15/0.48  thf('34', plain,
% 0.15/0.48      ((((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.15/0.48        | ~ (v1_relat_1 @ sk_C))),
% 0.15/0.48      inference('sup+', [status(thm)], ['25', '33'])).
% 0.15/0.48  thf('35', plain,
% 0.15/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.15/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.15/0.48  thf('36', plain,
% 0.15/0.48      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.15/0.48         ((v5_relat_1 @ X21 @ X23)
% 0.15/0.48          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.15/0.48      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.15/0.48  thf('37', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.15/0.48      inference('sup-', [status(thm)], ['35', '36'])).
% 0.15/0.48  thf(d19_relat_1, axiom,
% 0.15/0.48    (![A:$i,B:$i]:
% 0.15/0.48     ( ( v1_relat_1 @ B ) =>
% 0.15/0.48       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.15/0.48  thf('38', plain,
% 0.15/0.48      (![X7 : $i, X8 : $i]:
% 0.15/0.48         (~ (v5_relat_1 @ X7 @ X8)
% 0.15/0.48          | (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 0.15/0.48          | ~ (v1_relat_1 @ X7))),
% 0.15/0.48      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.15/0.48  thf('39', plain,
% 0.15/0.48      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A))),
% 0.15/0.48      inference('sup-', [status(thm)], ['37', '38'])).
% 0.15/0.48  thf('40', plain, ((v1_relat_1 @ sk_C)),
% 0.15/0.48      inference('demod', [status(thm)], ['18', '19'])).
% 0.15/0.48  thf('41', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)),
% 0.15/0.48      inference('demod', [status(thm)], ['39', '40'])).
% 0.15/0.48  thf(t28_xboole_1, axiom,
% 0.15/0.48    (![A:$i,B:$i]:
% 0.15/0.48     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.15/0.48  thf('42', plain,
% 0.15/0.48      (![X3 : $i, X4 : $i]:
% 0.15/0.48         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.15/0.48      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.15/0.48  thf('43', plain,
% 0.15/0.48      (((k3_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_A) = (k2_relat_1 @ sk_C))),
% 0.15/0.48      inference('sup-', [status(thm)], ['41', '42'])).
% 0.15/0.48  thf(t168_relat_1, axiom,
% 0.15/0.48    (![A:$i,B:$i]:
% 0.15/0.48     ( ( v1_relat_1 @ B ) =>
% 0.15/0.48       ( ( k10_relat_1 @ B @ A ) =
% 0.15/0.48         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 0.15/0.48  thf('44', plain,
% 0.15/0.48      (![X15 : $i, X16 : $i]:
% 0.15/0.48         (((k10_relat_1 @ X15 @ X16)
% 0.15/0.48            = (k10_relat_1 @ X15 @ (k3_xboole_0 @ (k2_relat_1 @ X15) @ X16)))
% 0.15/0.48          | ~ (v1_relat_1 @ X15))),
% 0.15/0.48      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.15/0.48  thf('45', plain,
% 0.15/0.48      ((((k10_relat_1 @ sk_C @ sk_A)
% 0.15/0.48          = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.15/0.48        | ~ (v1_relat_1 @ sk_C))),
% 0.15/0.48      inference('sup+', [status(thm)], ['43', '44'])).
% 0.15/0.48  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 0.15/0.48      inference('demod', [status(thm)], ['18', '19'])).
% 0.15/0.48  thf('47', plain,
% 0.15/0.48      (((k10_relat_1 @ sk_C @ sk_A)
% 0.15/0.48         = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 0.15/0.48      inference('demod', [status(thm)], ['45', '46'])).
% 0.15/0.48  thf('48', plain, ((v1_relat_1 @ sk_C)),
% 0.15/0.48      inference('demod', [status(thm)], ['18', '19'])).
% 0.15/0.48  thf('49', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_A))),
% 0.15/0.48      inference('demod', [status(thm)], ['34', '47', '48'])).
% 0.15/0.48  thf('50', plain,
% 0.15/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.15/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.15/0.48  thf(redefinition_k7_relset_1, axiom,
% 0.15/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.15/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.15/0.48       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.15/0.48  thf('51', plain,
% 0.15/0.48      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.15/0.48         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.15/0.48          | ((k7_relset_1 @ X31 @ X32 @ X30 @ X33) = (k9_relat_1 @ X30 @ X33)))),
% 0.15/0.48      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.15/0.48  thf('52', plain,
% 0.15/0.48      (![X0 : $i]:
% 0.15/0.48         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.15/0.48      inference('sup-', [status(thm)], ['50', '51'])).
% 0.15/0.48  thf('53', plain,
% 0.15/0.48      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.15/0.48      inference('demod', [status(thm)], ['23', '24'])).
% 0.15/0.48  thf('54', plain,
% 0.15/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.15/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.15/0.48  thf(redefinition_k2_relset_1, axiom,
% 0.15/0.48    (![A:$i,B:$i,C:$i]:
% 0.15/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.15/0.48       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.15/0.48  thf('55', plain,
% 0.15/0.48      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.15/0.48         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 0.15/0.48          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.15/0.48      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.15/0.48  thf('56', plain,
% 0.15/0.48      (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.15/0.48      inference('sup-', [status(thm)], ['54', '55'])).
% 0.15/0.48  thf('57', plain,
% 0.15/0.48      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.15/0.48         <= (~
% 0.15/0.48             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.15/0.48                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.15/0.48                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.15/0.48      inference('demod', [status(thm)], ['5', '49', '52', '53', '56'])).
% 0.15/0.48  thf('58', plain,
% 0.15/0.48      (($false)
% 0.15/0.48         <= (~
% 0.15/0.48             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.15/0.48                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.15/0.48                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.15/0.48      inference('simplify', [status(thm)], ['57'])).
% 0.15/0.48  thf('59', plain,
% 0.15/0.48      (![X0 : $i]:
% 0.15/0.48         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.15/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.15/0.48  thf('60', plain,
% 0.15/0.48      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.15/0.48          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.15/0.48          != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.15/0.48         <= (~
% 0.15/0.48             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.15/0.48                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.15/0.48                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.15/0.48      inference('split', [status(esa)], ['3'])).
% 0.15/0.48  thf('61', plain,
% 0.15/0.48      ((((k10_relat_1 @ sk_C @ (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.15/0.48          != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.15/0.48         <= (~
% 0.15/0.48             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.15/0.48                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.15/0.48                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.15/0.48      inference('sup-', [status(thm)], ['59', '60'])).
% 0.15/0.48  thf('62', plain,
% 0.15/0.48      (![X0 : $i]:
% 0.15/0.48         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.15/0.48      inference('sup-', [status(thm)], ['50', '51'])).
% 0.15/0.48  thf('63', plain,
% 0.15/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.15/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.15/0.48  thf('64', plain,
% 0.15/0.48      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.15/0.48         ((v4_relat_1 @ X21 @ X22)
% 0.15/0.48          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.15/0.48      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.15/0.48  thf('65', plain, ((v4_relat_1 @ sk_C @ sk_B)),
% 0.15/0.48      inference('sup-', [status(thm)], ['63', '64'])).
% 0.15/0.48  thf('66', plain,
% 0.15/0.48      (![X17 : $i, X18 : $i]:
% 0.15/0.48         (((X17) = (k7_relat_1 @ X17 @ X18))
% 0.15/0.48          | ~ (v4_relat_1 @ X17 @ X18)
% 0.15/0.48          | ~ (v1_relat_1 @ X17))),
% 0.15/0.48      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.15/0.48  thf('67', plain,
% 0.15/0.48      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_B)))),
% 0.15/0.48      inference('sup-', [status(thm)], ['65', '66'])).
% 0.15/0.48  thf('68', plain, ((v1_relat_1 @ sk_C)),
% 0.15/0.48      inference('demod', [status(thm)], ['18', '19'])).
% 0.15/0.48  thf('69', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.15/0.48      inference('demod', [status(thm)], ['67', '68'])).
% 0.15/0.48  thf('70', plain,
% 0.15/0.48      (![X11 : $i, X12 : $i]:
% 0.15/0.48         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.15/0.48          | ~ (v1_relat_1 @ X11))),
% 0.15/0.48      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.15/0.48  thf('71', plain,
% 0.15/0.48      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))
% 0.15/0.48        | ~ (v1_relat_1 @ sk_C))),
% 0.15/0.48      inference('sup+', [status(thm)], ['69', '70'])).
% 0.15/0.48  thf('72', plain, ((v1_relat_1 @ sk_C)),
% 0.15/0.48      inference('demod', [status(thm)], ['18', '19'])).
% 0.15/0.48  thf('73', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))),
% 0.15/0.48      inference('demod', [status(thm)], ['71', '72'])).
% 0.15/0.48  thf('74', plain,
% 0.15/0.48      (((k10_relat_1 @ sk_C @ sk_A)
% 0.15/0.48         = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 0.15/0.48      inference('demod', [status(thm)], ['45', '46'])).
% 0.15/0.48  thf('75', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_A))),
% 0.15/0.48      inference('demod', [status(thm)], ['34', '47', '48'])).
% 0.15/0.48  thf('76', plain,
% 0.15/0.48      (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 0.15/0.48      inference('demod', [status(thm)], ['74', '75'])).
% 0.15/0.48  thf('77', plain,
% 0.15/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.15/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.15/0.48  thf(redefinition_k1_relset_1, axiom,
% 0.15/0.48    (![A:$i,B:$i,C:$i]:
% 0.15/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.15/0.48       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.15/0.48  thf('78', plain,
% 0.15/0.48      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.15/0.48         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 0.15/0.48          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.15/0.48      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.15/0.48  thf('79', plain,
% 0.15/0.48      (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.15/0.48      inference('sup-', [status(thm)], ['77', '78'])).
% 0.15/0.48  thf('80', plain,
% 0.15/0.48      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 0.15/0.48         <= (~
% 0.15/0.48             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.15/0.48                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.15/0.48                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.15/0.48      inference('demod', [status(thm)], ['61', '62', '73', '76', '79'])).
% 0.15/0.48  thf('81', plain,
% 0.15/0.48      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.15/0.48          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.15/0.48          = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.15/0.48      inference('simplify', [status(thm)], ['80'])).
% 0.15/0.48  thf('82', plain,
% 0.15/0.48      (~
% 0.15/0.48       (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.15/0.48          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.15/0.48          = (k2_relset_1 @ sk_B @ sk_A @ sk_C))) | 
% 0.15/0.48       ~
% 0.15/0.48       (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.15/0.48          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.15/0.48          = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.15/0.48      inference('split', [status(esa)], ['3'])).
% 0.15/0.48  thf('83', plain,
% 0.15/0.48      (~
% 0.15/0.48       (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.15/0.48          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.15/0.48          = (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.15/0.48      inference('sat_resolution*', [status(thm)], ['81', '82'])).
% 0.15/0.48  thf('84', plain, ($false),
% 0.15/0.48      inference('simpl_trail', [status(thm)], ['58', '83'])).
% 0.15/0.48  
% 0.15/0.48  % SZS output end Refutation
% 0.15/0.48  
% 0.15/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
