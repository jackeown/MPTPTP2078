%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Nqcq2fey8I

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:03 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 202 expanded)
%              Number of leaves         :   43 (  78 expanded)
%              Depth                    :   24
%              Number of atoms          :  672 (1800 expanded)
%              Number of equality atoms :   52 (  87 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t49_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
             => ~ ( ( ( k1_relset_1 @ A @ B @ C )
                   != k1_xboole_0 )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ B )
                     => ~ ( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
               => ~ ( ( ( k1_relset_1 @ A @ B @ C )
                     != k1_xboole_0 )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ B )
                       => ~ ( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_relset_1])).

thf('1',plain,(
    ! [X41: $i] :
      ( ~ ( r2_hidden @ X41 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C ) )
      | ~ ( m1_subset_1 @ X41 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k2_relset_1 @ X39 @ X40 @ X38 )
        = ( k2_relat_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('4',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X41: $i] :
      ( ~ ( r2_hidden @ X41 @ ( k2_relat_1 @ sk_C ) )
      | ~ ( m1_subset_1 @ X41 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v5_relat_1 @ X32 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    v5_relat_1 @ sk_C @ sk_B_1 ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v5_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k2_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ),
    inference(demod,[status(thm)],['10','15'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('19',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( m1_subset_1 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X41: $i] :
      ~ ( r2_hidden @ X41 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['5','20'])).

thf('22',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','21'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('25',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X24 ) @ X25 )
      | ( ( k8_relat_1 @ X25 @ X24 )
        = X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k8_relat_1 @ k1_xboole_0 @ sk_C )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['22','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('29',plain,
    ( ( k8_relat_1 @ k1_xboole_0 @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf(t124_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('30',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k8_relat_1 @ X23 @ X22 )
        = ( k3_xboole_0 @ X22 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X22 ) @ X23 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t124_relat_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('31',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('32',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X0 @ ( k8_relat_1 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,
    ( ( ( k5_xboole_0 @ sk_C @ sk_C )
     != k1_xboole_0 )
    | ( r1_tarski @ sk_C @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('36',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('37',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('38',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_C @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v4_relat_1 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('43',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X30
        = ( k7_relat_1 @ X30 @ X31 ) )
      | ~ ( v4_relat_1 @ X30 @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('47',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X26 @ X27 ) )
        = ( k9_relat_1 @ X26 @ X27 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('49',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','21'])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('52',plain,
    ( k1_xboole_0
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t152_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf('54',plain,(
    ! [X28: $i,X29: $i] :
      ( ( X28 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X29 )
      | ~ ( r1_tarski @ X28 @ ( k1_relat_1 @ X29 ) )
      | ( ( k9_relat_1 @ X29 @ X28 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t152_relat_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('58',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('62',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k1_relset_1 @ X36 @ X37 @ X35 )
        = ( k1_relat_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('63',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ( k1_relat_1 @ sk_C )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['59','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Nqcq2fey8I
% 0.13/0.37  % Computer   : n020.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 18:36:37 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.46/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.70  % Solved by: fo/fo7.sh
% 0.46/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.70  % done 692 iterations in 0.215s
% 0.46/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.70  % SZS output start Refutation
% 0.46/0.70  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.70  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.46/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.70  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.46/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.70  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.46/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.70  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.70  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.70  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.70  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.70  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.70  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.46/0.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.70  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.70  thf(t7_xboole_0, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.70          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.46/0.70  thf('0', plain,
% 0.46/0.70      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.46/0.70      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.70  thf(t49_relset_1, conjecture,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.46/0.70           ( ![C:$i]:
% 0.46/0.70             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70               ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.46/0.70                    ( ![D:$i]:
% 0.46/0.70                      ( ( m1_subset_1 @ D @ B ) =>
% 0.46/0.70                        ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.70    (~( ![A:$i]:
% 0.46/0.70        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.70          ( ![B:$i]:
% 0.46/0.70            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.46/0.70              ( ![C:$i]:
% 0.46/0.70                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70                  ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.46/0.70                       ( ![D:$i]:
% 0.46/0.70                         ( ( m1_subset_1 @ D @ B ) =>
% 0.46/0.70                           ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.46/0.70    inference('cnf.neg', [status(esa)], [t49_relset_1])).
% 0.46/0.70  thf('1', plain,
% 0.46/0.70      (![X41 : $i]:
% 0.46/0.70         (~ (r2_hidden @ X41 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.46/0.70          | ~ (m1_subset_1 @ X41 @ sk_B_1))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('2', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(redefinition_k2_relset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.46/0.70  thf('3', plain,
% 0.46/0.70      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.46/0.70         (((k2_relset_1 @ X39 @ X40 @ X38) = (k2_relat_1 @ X38))
% 0.46/0.70          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.70  thf('4', plain,
% 0.46/0.70      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.70  thf('5', plain,
% 0.46/0.70      (![X41 : $i]:
% 0.46/0.70         (~ (r2_hidden @ X41 @ (k2_relat_1 @ sk_C))
% 0.46/0.70          | ~ (m1_subset_1 @ X41 @ sk_B_1))),
% 0.46/0.70      inference('demod', [status(thm)], ['1', '4'])).
% 0.46/0.70  thf('6', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(cc2_relset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.70  thf('7', plain,
% 0.46/0.70      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.46/0.70         ((v5_relat_1 @ X32 @ X34)
% 0.46/0.70          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.70  thf('8', plain, ((v5_relat_1 @ sk_C @ sk_B_1)),
% 0.46/0.70      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.70  thf(d19_relat_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( v1_relat_1 @ B ) =>
% 0.46/0.70       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.46/0.70  thf('9', plain,
% 0.46/0.70      (![X18 : $i, X19 : $i]:
% 0.46/0.70         (~ (v5_relat_1 @ X18 @ X19)
% 0.46/0.70          | (r1_tarski @ (k2_relat_1 @ X18) @ X19)
% 0.46/0.70          | ~ (v1_relat_1 @ X18))),
% 0.46/0.70      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.46/0.70  thf('10', plain,
% 0.46/0.70      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))),
% 0.46/0.70      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.70  thf('11', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(cc2_relat_1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( v1_relat_1 @ A ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.46/0.70  thf('12', plain,
% 0.46/0.70      (![X16 : $i, X17 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.46/0.70          | (v1_relat_1 @ X16)
% 0.46/0.70          | ~ (v1_relat_1 @ X17))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.46/0.70  thf('13', plain,
% 0.46/0.70      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.70  thf(fc6_relat_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.46/0.70  thf('14', plain,
% 0.46/0.70      (![X20 : $i, X21 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21))),
% 0.46/0.70      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.70  thf('15', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['13', '14'])).
% 0.46/0.70  thf('16', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)),
% 0.46/0.70      inference('demod', [status(thm)], ['10', '15'])).
% 0.46/0.70  thf(t3_subset, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.70  thf('17', plain,
% 0.46/0.70      (![X10 : $i, X12 : $i]:
% 0.46/0.70         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 0.46/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.70  thf('18', plain,
% 0.46/0.70      ((m1_subset_1 @ (k2_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.46/0.70      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.70  thf(t4_subset, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.46/0.70       ( m1_subset_1 @ A @ C ) ))).
% 0.46/0.70  thf('19', plain,
% 0.46/0.70      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.70         (~ (r2_hidden @ X13 @ X14)
% 0.46/0.70          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.46/0.70          | (m1_subset_1 @ X13 @ X15))),
% 0.46/0.70      inference('cnf', [status(esa)], [t4_subset])).
% 0.46/0.70  thf('20', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((m1_subset_1 @ X0 @ sk_B_1)
% 0.46/0.70          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.70  thf('21', plain, (![X41 : $i]: ~ (r2_hidden @ X41 @ (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('clc', [status(thm)], ['5', '20'])).
% 0.46/0.70  thf('22', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['0', '21'])).
% 0.46/0.70  thf(d10_xboole_0, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.70  thf('23', plain,
% 0.46/0.70      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.46/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.70  thf('24', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.46/0.70      inference('simplify', [status(thm)], ['23'])).
% 0.46/0.70  thf(t125_relat_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( v1_relat_1 @ B ) =>
% 0.46/0.70       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.46/0.70         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.46/0.70  thf('25', plain,
% 0.46/0.70      (![X24 : $i, X25 : $i]:
% 0.46/0.70         (~ (r1_tarski @ (k2_relat_1 @ X24) @ X25)
% 0.46/0.70          | ((k8_relat_1 @ X25 @ X24) = (X24))
% 0.46/0.70          | ~ (v1_relat_1 @ X24))),
% 0.46/0.70      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.46/0.70  thf('26', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v1_relat_1 @ X0) | ((k8_relat_1 @ (k2_relat_1 @ X0) @ X0) = (X0)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.70  thf('27', plain,
% 0.46/0.70      ((((k8_relat_1 @ k1_xboole_0 @ sk_C) = (sk_C)) | ~ (v1_relat_1 @ sk_C))),
% 0.46/0.70      inference('sup+', [status(thm)], ['22', '26'])).
% 0.46/0.70  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['13', '14'])).
% 0.46/0.70  thf('29', plain, (((k8_relat_1 @ k1_xboole_0 @ sk_C) = (sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['27', '28'])).
% 0.46/0.70  thf(t124_relat_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( v1_relat_1 @ B ) =>
% 0.46/0.70       ( ( k8_relat_1 @ A @ B ) =
% 0.46/0.70         ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.46/0.70  thf('30', plain,
% 0.46/0.70      (![X22 : $i, X23 : $i]:
% 0.46/0.70         (((k8_relat_1 @ X23 @ X22)
% 0.46/0.70            = (k3_xboole_0 @ X22 @ (k2_zfmisc_1 @ (k1_relat_1 @ X22) @ X23)))
% 0.46/0.70          | ~ (v1_relat_1 @ X22))),
% 0.46/0.70      inference('cnf', [status(esa)], [t124_relat_1])).
% 0.46/0.70  thf(t100_xboole_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.70  thf('31', plain,
% 0.46/0.70      (![X7 : $i, X8 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X7 @ X8)
% 0.46/0.70           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.70  thf(l32_xboole_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.70  thf('32', plain,
% 0.46/0.70      (![X4 : $i, X5 : $i]:
% 0.46/0.70         ((r1_tarski @ X4 @ X5) | ((k4_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 0.46/0.70      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.70  thf('33', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.46/0.70          | (r1_tarski @ X1 @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['31', '32'])).
% 0.46/0.70  thf('34', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (((k5_xboole_0 @ X0 @ (k8_relat_1 @ X1 @ X0)) != (k1_xboole_0))
% 0.46/0.70          | ~ (v1_relat_1 @ X0)
% 0.46/0.70          | (r1_tarski @ X0 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['30', '33'])).
% 0.46/0.70  thf('35', plain,
% 0.46/0.70      ((((k5_xboole_0 @ sk_C @ sk_C) != (k1_xboole_0))
% 0.46/0.70        | (r1_tarski @ sk_C @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ k1_xboole_0))
% 0.46/0.70        | ~ (v1_relat_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['29', '34'])).
% 0.46/0.70  thf(t92_xboole_1, axiom,
% 0.46/0.70    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.46/0.70  thf('36', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.46/0.70      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.46/0.70  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['13', '14'])).
% 0.46/0.70  thf('38', plain,
% 0.46/0.70      ((((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.70        | (r1_tarski @ sk_C @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ k1_xboole_0)))),
% 0.46/0.70      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.46/0.70  thf('39', plain,
% 0.46/0.70      ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ k1_xboole_0))),
% 0.46/0.70      inference('simplify', [status(thm)], ['38'])).
% 0.46/0.70  thf('40', plain,
% 0.46/0.70      (![X10 : $i, X12 : $i]:
% 0.46/0.70         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 0.46/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.70  thf('41', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ k1_xboole_0)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.70  thf('42', plain,
% 0.46/0.70      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.46/0.70         ((v4_relat_1 @ X32 @ X33)
% 0.46/0.70          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.70  thf('43', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.70  thf(t209_relat_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.46/0.70       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.46/0.70  thf('44', plain,
% 0.46/0.70      (![X30 : $i, X31 : $i]:
% 0.46/0.70         (((X30) = (k7_relat_1 @ X30 @ X31))
% 0.46/0.70          | ~ (v4_relat_1 @ X30 @ X31)
% 0.46/0.70          | ~ (v1_relat_1 @ X30))),
% 0.46/0.70      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.46/0.70  thf('45', plain,
% 0.46/0.70      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.70        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['43', '44'])).
% 0.46/0.70  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['13', '14'])).
% 0.46/0.70  thf('47', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['45', '46'])).
% 0.46/0.70  thf(t148_relat_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( v1_relat_1 @ B ) =>
% 0.46/0.70       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.46/0.70  thf('48', plain,
% 0.46/0.70      (![X26 : $i, X27 : $i]:
% 0.46/0.70         (((k2_relat_1 @ (k7_relat_1 @ X26 @ X27)) = (k9_relat_1 @ X26 @ X27))
% 0.46/0.70          | ~ (v1_relat_1 @ X26))),
% 0.46/0.70      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.46/0.70  thf('49', plain,
% 0.46/0.70      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 0.46/0.70        | ~ (v1_relat_1 @ sk_C))),
% 0.46/0.70      inference('sup+', [status(thm)], ['47', '48'])).
% 0.46/0.70  thf('50', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['0', '21'])).
% 0.46/0.70  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['13', '14'])).
% 0.46/0.70  thf('52', plain,
% 0.46/0.70      (((k1_xboole_0) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.46/0.70  thf('53', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.46/0.70      inference('simplify', [status(thm)], ['23'])).
% 0.46/0.70  thf(t152_relat_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( v1_relat_1 @ B ) =>
% 0.46/0.70       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.70            ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 0.46/0.70            ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.46/0.70  thf('54', plain,
% 0.46/0.70      (![X28 : $i, X29 : $i]:
% 0.46/0.70         (((X28) = (k1_xboole_0))
% 0.46/0.70          | ~ (v1_relat_1 @ X29)
% 0.46/0.70          | ~ (r1_tarski @ X28 @ (k1_relat_1 @ X29))
% 0.46/0.70          | ((k9_relat_1 @ X29 @ X28) != (k1_xboole_0)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t152_relat_1])).
% 0.46/0.70  thf('55', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) != (k1_xboole_0))
% 0.46/0.70          | ~ (v1_relat_1 @ X0)
% 0.46/0.70          | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['53', '54'])).
% 0.46/0.70  thf('56', plain,
% 0.46/0.70      ((((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.70        | ((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.46/0.70        | ~ (v1_relat_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['52', '55'])).
% 0.46/0.70  thf('57', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['13', '14'])).
% 0.46/0.70  thf('58', plain,
% 0.46/0.70      ((((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.70        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.46/0.70      inference('demod', [status(thm)], ['56', '57'])).
% 0.46/0.70  thf('59', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.46/0.70      inference('simplify', [status(thm)], ['58'])).
% 0.46/0.70  thf('60', plain, (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) != (k1_xboole_0))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('61', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(redefinition_k1_relset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.46/0.70  thf('62', plain,
% 0.46/0.70      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.46/0.70         (((k1_relset_1 @ X36 @ X37 @ X35) = (k1_relat_1 @ X35))
% 0.46/0.70          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.70  thf('63', plain,
% 0.46/0.70      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['61', '62'])).
% 0.46/0.70  thf('64', plain, (((k1_relat_1 @ sk_C) != (k1_xboole_0))),
% 0.46/0.70      inference('demod', [status(thm)], ['60', '63'])).
% 0.46/0.70  thf('65', plain, ($false),
% 0.46/0.70      inference('simplify_reflect-', [status(thm)], ['59', '64'])).
% 0.46/0.70  
% 0.46/0.70  % SZS output end Refutation
% 0.46/0.70  
% 0.55/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
