%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U2kpsm2kOF

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 194 expanded)
%              Number of leaves         :   37 (  71 expanded)
%              Depth                    :   13
%              Number of atoms          :  897 (2053 expanded)
%              Number of equality atoms :   63 ( 136 expanded)
%              Maximal formula depth    :   12 (   6 average)

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

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

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('3',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X38 ) @ X39 )
      | ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('7',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17
        = ( k7_relat_1 @ X17 @ X18 ) )
      | ~ ( v4_relat_1 @ X17 @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('14',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('17',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['12','13'])).

thf('19',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( r1_tarski @ X19 @ ( k10_relat_1 @ X20 @ ( k9_relat_1 @ X20 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X13 @ X14 ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('24',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['19','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('31',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['29','30'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v5_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['12','13'])).

thf('35',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['33','34'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('36',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('37',plain,
    ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_B )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('38',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k10_relat_1 @ X15 @ X16 )
        = ( k10_relat_1 @ X15 @ ( k3_xboole_0 @ ( k2_relat_1 @ X15 ) @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('39',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['12','13'])).

thf('41',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['12','13'])).

thf('43',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['28','41','42'])).

thf('44',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('47',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('48',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['44'])).

thf('54',plain,
    ( ( ( k9_relat_1 @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('57',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17
        = ( k7_relat_1 @ X17 @ X18 ) )
      | ~ ( v4_relat_1 @ X17 @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['12','13'])).

thf('61',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('63',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['12','13'])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('67',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('68',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['54','65','68'])).

thf('70',plain,
    ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['44'])).

thf('72',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
 != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['70','71'])).

thf('73',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['49','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('75',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( ( k8_relset_1 @ X35 @ X36 @ X34 @ X37 )
        = ( k10_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ( k10_relat_1 @ sk_C @ sk_B )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['43','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U2kpsm2kOF
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:39:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 102 iterations in 0.060s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.53  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.53  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.53  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(d10_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.53  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.53      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.53  thf(t38_relset_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.20/0.53         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.53        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53          ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.20/0.53            ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t38_relset_1])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t13_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.20/0.53       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.20/0.53         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.20/0.53         (~ (r1_tarski @ (k1_relat_1 @ X38) @ X39)
% 0.20/0.53          | (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.20/0.53          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 0.20/0.53      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.20/0.53          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ 
% 0.20/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.53  thf(cc2_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.53         ((v4_relat_1 @ X21 @ X22)
% 0.20/0.53          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.53  thf('7', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.53  thf(t209_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.53       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X17 : $i, X18 : $i]:
% 0.20/0.53         (((X17) = (k7_relat_1 @ X17 @ X18))
% 0.20/0.53          | ~ (v4_relat_1 @ X17 @ X18)
% 0.20/0.53          | ~ (v1_relat_1 @ X17))),
% 0.20/0.53      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.53        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(cc2_relat_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X5 : $i, X6 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.20/0.53          | (v1_relat_1 @ X5)
% 0.20/0.53          | ~ (v1_relat_1 @ X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.53  thf(fc6_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.53  thf('14', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.53  thf('15', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.20/0.53      inference('demod', [status(thm)], ['9', '14'])).
% 0.20/0.53  thf(t148_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ B ) =>
% 0.20/0.53       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i]:
% 0.20/0.53         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.20/0.53          | ~ (v1_relat_1 @ X11))),
% 0.20/0.53      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 0.20/0.53        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.53      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('18', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.20/0.53      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.53  thf('20', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.53      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.53  thf(t146_funct_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ B ) =>
% 0.20/0.53       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.53         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X19 @ (k1_relat_1 @ X20))
% 0.20/0.53          | (r1_tarski @ X19 @ (k10_relat_1 @ X20 @ (k9_relat_1 @ X20 @ X19)))
% 0.20/0.53          | ~ (v1_relat_1 @ X20))),
% 0.20/0.53      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.20/0.53             (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf(t167_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ B ) =>
% 0.20/0.53       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i]:
% 0.20/0.53         ((r1_tarski @ (k10_relat_1 @ X13 @ X14) @ (k1_relat_1 @ X13))
% 0.20/0.53          | ~ (v1_relat_1 @ X13))),
% 0.20/0.53      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X0 : $i, X2 : $i]:
% 0.20/0.53         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.20/0.53          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | ((k1_relat_1 @ X0)
% 0.20/0.53              = (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['22', '25'])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k1_relat_1 @ X0)
% 0.20/0.53            = (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      ((((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.20/0.53        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.53      inference('sup+', [status(thm)], ['19', '27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.53         ((v5_relat_1 @ X21 @ X23)
% 0.20/0.53          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.53  thf('31', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.20/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.53  thf(d19_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ B ) =>
% 0.20/0.53       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i]:
% 0.20/0.53         (~ (v5_relat_1 @ X7 @ X8)
% 0.20/0.53          | (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 0.20/0.53          | ~ (v1_relat_1 @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.53  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.53  thf('35', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.20/0.53      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf(t28_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i]:
% 0.20/0.53         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (((k3_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_B) = (k2_relat_1 @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.53  thf(t168_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ B ) =>
% 0.20/0.53       ( ( k10_relat_1 @ B @ A ) =
% 0.20/0.53         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i]:
% 0.20/0.53         (((k10_relat_1 @ X15 @ X16)
% 0.20/0.53            = (k10_relat_1 @ X15 @ (k3_xboole_0 @ (k2_relat_1 @ X15) @ X16)))
% 0.20/0.53          | ~ (v1_relat_1 @ X15))),
% 0.20/0.53      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      ((((k10_relat_1 @ sk_C @ sk_B)
% 0.20/0.53          = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.20/0.53        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.53      inference('sup+', [status(thm)], ['37', '38'])).
% 0.20/0.53  thf('40', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (((k10_relat_1 @ sk_C @ sk_B)
% 0.20/0.53         = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 0.20/0.53      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.53  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.53  thf('43', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['28', '41', '42'])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.53          != (k2_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.53        | ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.20/0.53            != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.20/0.53          != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.53         <= (~
% 0.20/0.53             (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.20/0.53                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.53      inference('split', [status(esa)], ['44'])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.53         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 0.20/0.53          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) != (k1_relat_1 @ sk_C)))
% 0.20/0.53         <= (~
% 0.20/0.53             (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.20/0.53                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.53      inference('demod', [status(thm)], ['45', '48'])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_k7_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.20/0.53          | ((k7_relset_1 @ X31 @ X32 @ X30 @ X33) = (k9_relat_1 @ X30 @ X33)))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.53  thf('53', plain,
% 0.20/0.53      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.53          != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.53         <= (~
% 0.20/0.53             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.53                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.53      inference('split', [status(esa)], ['44'])).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      ((((k9_relat_1 @ sk_C @ sk_A) != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.53         <= (~
% 0.20/0.53             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.53                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.53  thf('55', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('56', plain,
% 0.20/0.53      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.54         ((v4_relat_1 @ X21 @ X22)
% 0.20/0.54          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.20/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.54  thf('57', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.20/0.54      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.54  thf('58', plain,
% 0.20/0.54      (![X17 : $i, X18 : $i]:
% 0.20/0.54         (((X17) = (k7_relat_1 @ X17 @ X18))
% 0.20/0.54          | ~ (v4_relat_1 @ X17 @ X18)
% 0.20/0.54          | ~ (v1_relat_1 @ X17))),
% 0.20/0.54      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.20/0.54  thf('59', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.54  thf('60', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.54      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.54  thf('61', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['59', '60'])).
% 0.20/0.54  thf('62', plain,
% 0.20/0.54      (![X11 : $i, X12 : $i]:
% 0.20/0.54         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.20/0.54          | ~ (v1_relat_1 @ X11))),
% 0.20/0.54      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.54  thf('63', plain,
% 0.20/0.54      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 0.20/0.54        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.54      inference('sup+', [status(thm)], ['61', '62'])).
% 0.20/0.54  thf('64', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.54      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.54  thf('65', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['63', '64'])).
% 0.20/0.54  thf('66', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.54  thf('67', plain,
% 0.20/0.54      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.54         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 0.20/0.54          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.54  thf('68', plain,
% 0.20/0.54      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.20/0.54      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.54  thf('69', plain,
% 0.20/0.54      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.20/0.54         <= (~
% 0.20/0.54             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.54                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.54      inference('demod', [status(thm)], ['54', '65', '68'])).
% 0.20/0.54  thf('70', plain,
% 0.20/0.54      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.54          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['69'])).
% 0.20/0.54  thf('71', plain,
% 0.20/0.54      (~
% 0.20/0.54       (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.20/0.54          = (k1_relset_1 @ sk_A @ sk_B @ sk_C))) | 
% 0.20/0.54       ~
% 0.20/0.54       (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.54          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.54      inference('split', [status(esa)], ['44'])).
% 0.20/0.54  thf('72', plain,
% 0.20/0.54      (~
% 0.20/0.54       (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.20/0.54          = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['70', '71'])).
% 0.20/0.54  thf('73', plain,
% 0.20/0.54      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) != (k1_relat_1 @ sk_C))),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['49', '72'])).
% 0.20/0.54  thf('74', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(redefinition_k8_relset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.20/0.54  thf('75', plain,
% 0.20/0.54      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.20/0.54          | ((k8_relset_1 @ X35 @ X36 @ X34 @ X37) = (k10_relat_1 @ X34 @ X37)))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.54  thf('76', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['74', '75'])).
% 0.20/0.54  thf('77', plain, (((k10_relat_1 @ sk_C @ sk_B) != (k1_relat_1 @ sk_C))),
% 0.20/0.54      inference('demod', [status(thm)], ['73', '76'])).
% 0.20/0.54  thf('78', plain, ($false),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['43', '77'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
