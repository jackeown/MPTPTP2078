%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sgGBrWxSjj

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 231 expanded)
%              Number of leaves         :   42 (  85 expanded)
%              Depth                    :   14
%              Number of atoms          :  864 (2611 expanded)
%              Number of equality atoms :   69 ( 184 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ( ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('4',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_B )
     != ( k1_relat_1 @ sk_C_1 ) )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('7',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( ( k7_relset_1 @ X37 @ X38 @ X36 @ X39 )
        = ( k9_relat_1 @ X36 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0 )
      = ( k9_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ( ( k9_relat_1 @ sk_C_1 @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('13',plain,(
    v4_relat_1 @ sk_C_1 @ sk_A ),
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
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1
      = ( k7_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('17',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('18',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','18'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) )
        = ( k9_relat_1 @ X13 @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('21',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k9_relat_1 @ sk_C_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('23',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k9_relat_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k2_relset_1 @ X34 @ X35 @ X33 )
        = ( k2_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('26',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != ( k2_relat_1 @ sk_C_1 ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['10','23','26'])).

thf('28',plain,
    ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_B )
 != ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['28','29'])).

thf('31',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_B )
 != ( k1_relat_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['5','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('33',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k8_relset_1 @ X41 @ X42 @ X40 @ X43 )
        = ( k10_relat_1 @ X40 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0 )
      = ( k10_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('36',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X27 @ X28 @ X29 ) @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('37',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('39',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('40',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r2_hidden @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('42',plain,(
    ! [X5: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('43',plain,(
    r2_hidden @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['41','42'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('44',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( r1_tarski @ X3 @ X1 )
      | ( X2
       != ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('45',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X3 @ X1 )
      | ~ ( r2_hidden @ X3 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k9_relat_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('48',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) )
        = ( k9_relat_1 @ X13 @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('49',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ( ( k8_relat_1 @ X12 @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ X0 )
      | ( ( k8_relat_1 @ X0 @ ( k7_relat_1 @ sk_C_1 @ sk_A ) )
        = ( k7_relat_1 @ sk_C_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('53',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('54',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('55',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('56',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ X0 )
      | ( ( k8_relat_1 @ X0 @ sk_C_1 )
        = sk_C_1 ) ) ),
    inference(demod,[status(thm)],['51','52','53','54','55','56'])).

thf('58',plain,
    ( ( k8_relat_1 @ sk_B @ sk_C_1 )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['46','57'])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('59',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k8_relat_1 @ X10 @ X9 )
        = ( k5_relat_1 @ X9 @ ( k6_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('60',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('61',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) )
        = ( k10_relat_1 @ X16 @ ( k1_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('63',plain,(
    ! [X8: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = ( k10_relat_1 @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['58','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('69',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k10_relat_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['31','34','69'])).

thf('71',plain,(
    $false ),
    inference(simplify,[status(thm)],['70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sgGBrWxSjj
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:55:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 88 iterations in 0.068s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.54  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.54  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.54  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.54  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.54  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.54  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.54  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(t38_relset_1, conjecture,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.21/0.54         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.54        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54          ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.21/0.54            ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t38_relset_1])).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_A)
% 0.21/0.54          != (k2_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 0.21/0.54        | ((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_B)
% 0.21/0.54            != (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_B)
% 0.21/0.54          != (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 0.21/0.54         <= (~
% 0.21/0.54             (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_B)
% 0.21/0.54                = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.21/0.54         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 0.21/0.54          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_B) != (k1_relat_1 @ sk_C_1)))
% 0.21/0.54         <= (~
% 0.21/0.54             (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_B)
% 0.21/0.54                = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.21/0.54      inference('demod', [status(thm)], ['1', '4'])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(redefinition_k7_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.21/0.54          | ((k7_relset_1 @ X37 @ X38 @ X36 @ X39) = (k9_relat_1 @ X36 @ X39)))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0)
% 0.21/0.54           = (k9_relat_1 @ sk_C_1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_A)
% 0.21/0.54          != (k2_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 0.21/0.54         <= (~
% 0.21/0.54             (((k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_A)
% 0.21/0.54                = (k2_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      ((((k9_relat_1 @ sk_C_1 @ sk_A) != (k2_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 0.21/0.54         <= (~
% 0.21/0.54             (((k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_A)
% 0.21/0.54                = (k2_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(cc2_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.54         ((v4_relat_1 @ X24 @ X25)
% 0.21/0.54          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.21/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.54  thf('13', plain, ((v4_relat_1 @ sk_C_1 @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.54  thf(t209_relat_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.54       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (![X17 : $i, X18 : $i]:
% 0.21/0.54         (((X17) = (k7_relat_1 @ X17 @ X18))
% 0.21/0.54          | ~ (v4_relat_1 @ X17 @ X18)
% 0.21/0.54          | ~ (v1_relat_1 @ X17))),
% 0.21/0.54      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      ((~ (v1_relat_1 @ sk_C_1) | ((sk_C_1) = (k7_relat_1 @ sk_C_1 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(cc1_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( v1_relat_1 @ C ) ))).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.54         ((v1_relat_1 @ X21)
% 0.21/0.54          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.21/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.54  thf('18', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.54  thf('19', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['15', '18'])).
% 0.21/0.54  thf(t148_relat_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ B ) =>
% 0.21/0.54       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      (![X13 : $i, X14 : $i]:
% 0.21/0.54         (((k2_relat_1 @ (k7_relat_1 @ X13 @ X14)) = (k9_relat_1 @ X13 @ X14))
% 0.21/0.54          | ~ (v1_relat_1 @ X13))),
% 0.21/0.54      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      ((((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ sk_A))
% 0.21/0.54        | ~ (v1_relat_1 @ sk_C_1))),
% 0.21/0.54      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.54  thf('22', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.54  thf('23', plain, (((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.21/0.54         (((k2_relset_1 @ X34 @ X35 @ X33) = (k2_relat_1 @ X33))
% 0.21/0.54          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      ((((k2_relat_1 @ sk_C_1) != (k2_relat_1 @ sk_C_1)))
% 0.21/0.54         <= (~
% 0.21/0.54             (((k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_A)
% 0.21/0.54                = (k2_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.21/0.54      inference('demod', [status(thm)], ['10', '23', '26'])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_A)
% 0.21/0.54          = (k2_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (~
% 0.21/0.54       (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_B)
% 0.21/0.54          = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) | 
% 0.21/0.54       ~
% 0.21/0.54       (((k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_A)
% 0.21/0.54          = (k2_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      (~
% 0.21/0.54       (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_B)
% 0.21/0.54          = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['28', '29'])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_B) != (k1_relat_1 @ sk_C_1))),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['5', '30'])).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(redefinition_k8_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.21/0.54          | ((k8_relset_1 @ X41 @ X42 @ X40 @ X43) = (k10_relat_1 @ X40 @ X43)))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.54  thf('34', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0)
% 0.21/0.54           = (k10_relat_1 @ sk_C_1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(dt_k2_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.54         ((m1_subset_1 @ (k2_relset_1 @ X27 @ X28 @ X29) @ (k1_zfmisc_1 @ X28))
% 0.21/0.54          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.21/0.54  thf('37', plain,
% 0.21/0.54      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.21/0.54        (k1_zfmisc_1 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.54  thf('38', plain,
% 0.21/0.54      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.54  thf('39', plain,
% 0.21/0.54      ((m1_subset_1 @ (k2_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.54  thf(t2_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.54       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      (![X6 : $i, X7 : $i]:
% 0.21/0.54         ((r2_hidden @ X6 @ X7)
% 0.21/0.54          | (v1_xboole_0 @ X7)
% 0.21/0.54          | ~ (m1_subset_1 @ X6 @ X7))),
% 0.21/0.54      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_B))
% 0.21/0.54        | (r2_hidden @ (k2_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.54  thf(fc1_subset_1, axiom,
% 0.21/0.54    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.54  thf('42', plain, (![X5 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.21/0.54      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      ((r2_hidden @ (k2_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.21/0.54      inference('clc', [status(thm)], ['41', '42'])).
% 0.21/0.54  thf(d1_zfmisc_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.54  thf('44', plain,
% 0.21/0.54      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X3 @ X2)
% 0.21/0.54          | (r1_tarski @ X3 @ X1)
% 0.21/0.54          | ((X2) != (k1_zfmisc_1 @ X1)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.54  thf('45', plain,
% 0.21/0.54      (![X1 : $i, X3 : $i]:
% 0.21/0.54         ((r1_tarski @ X3 @ X1) | ~ (r2_hidden @ X3 @ (k1_zfmisc_1 @ X1)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.54  thf('46', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)),
% 0.21/0.54      inference('sup-', [status(thm)], ['43', '45'])).
% 0.21/0.54  thf('47', plain, (((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.54  thf('48', plain,
% 0.21/0.54      (![X13 : $i, X14 : $i]:
% 0.21/0.54         (((k2_relat_1 @ (k7_relat_1 @ X13 @ X14)) = (k9_relat_1 @ X13 @ X14))
% 0.21/0.54          | ~ (v1_relat_1 @ X13))),
% 0.21/0.54      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.54  thf(t125_relat_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ B ) =>
% 0.21/0.54       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.21/0.54         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.21/0.54  thf('49', plain,
% 0.21/0.54      (![X11 : $i, X12 : $i]:
% 0.21/0.54         (~ (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 0.21/0.54          | ((k8_relat_1 @ X12 @ X11) = (X11))
% 0.21/0.54          | ~ (v1_relat_1 @ X11))),
% 0.21/0.54      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.21/0.54  thf('50', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.54          | ~ (v1_relat_1 @ X1)
% 0.21/0.54          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.54          | ((k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.54              = (k7_relat_1 @ X1 @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.54  thf('51', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ X0)
% 0.21/0.54          | ((k8_relat_1 @ X0 @ (k7_relat_1 @ sk_C_1 @ sk_A))
% 0.21/0.54              = (k7_relat_1 @ sk_C_1 @ sk_A))
% 0.21/0.54          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C_1 @ sk_A))
% 0.21/0.54          | ~ (v1_relat_1 @ sk_C_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['47', '50'])).
% 0.21/0.54  thf('52', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['15', '18'])).
% 0.21/0.54  thf('53', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['15', '18'])).
% 0.21/0.54  thf('54', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['15', '18'])).
% 0.21/0.54  thf('55', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.54  thf('56', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.54  thf('57', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ X0)
% 0.21/0.54          | ((k8_relat_1 @ X0 @ sk_C_1) = (sk_C_1)))),
% 0.21/0.54      inference('demod', [status(thm)], ['51', '52', '53', '54', '55', '56'])).
% 0.21/0.54  thf('58', plain, (((k8_relat_1 @ sk_B @ sk_C_1) = (sk_C_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['46', '57'])).
% 0.21/0.54  thf(t123_relat_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ B ) =>
% 0.21/0.54       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.21/0.54  thf('59', plain,
% 0.21/0.54      (![X9 : $i, X10 : $i]:
% 0.21/0.54         (((k8_relat_1 @ X10 @ X9) = (k5_relat_1 @ X9 @ (k6_relat_1 @ X10)))
% 0.21/0.54          | ~ (v1_relat_1 @ X9))),
% 0.21/0.54      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.21/0.54  thf(t71_relat_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.54       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.54  thf('60', plain, (![X19 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 0.21/0.54      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.54  thf(t182_relat_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( v1_relat_1 @ B ) =>
% 0.21/0.54           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.21/0.54             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.21/0.54  thf('61', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X15)
% 0.21/0.54          | ((k1_relat_1 @ (k5_relat_1 @ X16 @ X15))
% 0.21/0.54              = (k10_relat_1 @ X16 @ (k1_relat_1 @ X15)))
% 0.21/0.54          | ~ (v1_relat_1 @ X16))),
% 0.21/0.54      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.21/0.54  thf('62', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.21/0.54            = (k10_relat_1 @ X1 @ X0))
% 0.21/0.54          | ~ (v1_relat_1 @ X1)
% 0.21/0.54          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.54      inference('sup+', [status(thm)], ['60', '61'])).
% 0.21/0.54  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.21/0.54  thf('63', plain, (![X8 : $i]: (v1_relat_1 @ (k6_relat_1 @ X8))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.54  thf('64', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.21/0.54            = (k10_relat_1 @ X1 @ X0))
% 0.21/0.54          | ~ (v1_relat_1 @ X1))),
% 0.21/0.54      inference('demod', [status(thm)], ['62', '63'])).
% 0.21/0.54  thf('65', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (((k1_relat_1 @ (k8_relat_1 @ X1 @ X0)) = (k10_relat_1 @ X0 @ X1))
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['59', '64'])).
% 0.21/0.54  thf('66', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | ((k1_relat_1 @ (k8_relat_1 @ X1 @ X0)) = (k10_relat_1 @ X0 @ X1)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['65'])).
% 0.21/0.54  thf('67', plain,
% 0.21/0.54      ((((k1_relat_1 @ sk_C_1) = (k10_relat_1 @ sk_C_1 @ sk_B))
% 0.21/0.54        | ~ (v1_relat_1 @ sk_C_1))),
% 0.21/0.54      inference('sup+', [status(thm)], ['58', '66'])).
% 0.21/0.54  thf('68', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.54  thf('69', plain, (((k1_relat_1 @ sk_C_1) = (k10_relat_1 @ sk_C_1 @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['67', '68'])).
% 0.21/0.54  thf('70', plain, (((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_C_1))),
% 0.21/0.54      inference('demod', [status(thm)], ['31', '34', '69'])).
% 0.21/0.54  thf('71', plain, ($false), inference('simplify', [status(thm)], ['70'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
