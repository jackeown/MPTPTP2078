%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.E3c0Q7DwHW

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  220 ( 926 expanded)
%              Number of leaves         :   46 ( 310 expanded)
%              Depth                    :   32
%              Number of atoms          : 1668 (9184 expanded)
%              Number of equality atoms :  197 ( 831 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k1_relset_1 @ X39 @ X40 @ X38 )
        = ( k1_relat_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
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
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( ( k7_relset_1 @ X45 @ X46 @ X44 @ X47 )
        = ( k9_relat_1 @ X44 @ X47 ) ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v4_relat_1 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( X17
        = ( k7_relat_1 @ X17 @ X18 ) )
      | ~ ( v4_relat_1 @ X17 @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('17',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v1_relat_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('18',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['15','18'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('21',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf('23',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( ( k2_relset_1 @ X42 @ X43 @ X41 )
        = ( k2_relat_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('26',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['10','23','26'])).

thf('28',plain,
    ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
 != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['28','29'])).

thf('31',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['5','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('33',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ( ( k8_relset_1 @ X49 @ X50 @ X48 @ X51 )
        = ( k10_relat_1 @ X48 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ( k10_relat_1 @ sk_C @ sk_B )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['31','34'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('36',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('37',plain,(
    ! [X21: $i] :
      ( ( ( k1_relat_1 @ X21 )
       != k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('39',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['40'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('42',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k7_relat_1 @ X27 @ X26 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X26 ) @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('44',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) )
        = X16 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('46',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('48',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( r1_tarski @ ( k2_relat_1 @ X20 ) @ ( k2_relat_1 @ X19 ) )
      | ~ ( r1_tarski @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('51',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('52',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','52'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('54',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X24 ) @ X25 )
      | ( ( k5_relat_1 @ X24 @ ( k6_relat_1 @ X25 ) )
        = X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('55',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf('57',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
      = sk_C ) ),
    inference(demod,[status(thm)],['55','56'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('58',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) )
        = ( k10_relat_1 @ X14 @ ( k1_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('59',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('61',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf('62',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('63',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ sk_B ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,(
    ( k10_relat_1 @ sk_C @ sk_B )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('65',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('68',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( r1_tarski @ ( k1_relat_1 @ X20 ) @ ( k1_relat_1 @ X19 ) )
      | ~ ( r1_tarski @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('69',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf('71',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('72',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('73',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X28 ) @ X29 )
      | ( ( k7_relat_1 @ X28 @ X29 )
        = X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('74',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf('76',plain,
    ( ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    = sk_C ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) )
      = sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','76'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('78',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('79',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('80',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('81',plain,
    ( ( ( k7_relat_1 @ sk_C @ k1_xboole_0 )
      = sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','79','80'])).

thf('82',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_C )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf('84',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_C )
      = sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) )
        = ( k10_relat_1 @ X14 @ ( k1_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('86',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ k1_xboole_0 @ ( k1_relat_1 @ sk_C ) ) )
    | ( sk_A = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('88',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X24 ) @ X25 )
      | ( ( k5_relat_1 @ X24 @ ( k6_relat_1 @ X25 ) )
        = X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ ( k6_relat_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('90',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('92',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('93',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v1_relat_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('95',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ k1_xboole_0 @ ( k6_relat_1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','90','95'])).

thf('97',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) )
        = ( k10_relat_1 @ X14 @ ( k1_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k10_relat_1 @ k1_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('100',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('101',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['93','94'])).

thf('102',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['98','99','100','101','102'])).

thf('104',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['93','94'])).

thf('105',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf('106',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['86','103','104','105'])).

thf('107',plain,(
    ! [X21: $i] :
      ( ( ( k1_relat_1 @ X21 )
       != k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('108',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf('110',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('113',plain,
    ( ( r1_tarski @ sk_C @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('115',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['113','115'])).

thf('117',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('118',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X28 ) @ X29 )
      | ( ( k7_relat_1 @ X28 @ X29 )
        = X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_relat_1 @ ( k6_relat_1 @ sk_C ) @ k1_xboole_0 )
      = ( k6_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['116','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ k1_xboole_0 @ ( k6_relat_1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','90','95'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('125',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('126',plain,(
    ! [X21: $i] :
      ( ( ( k2_relat_1 @ X21 )
       != k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ k1_xboole_0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['124','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ k1_xboole_0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['123','129'])).

thf('131',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['93','94'])).

thf('132',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ k1_xboole_0 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ k1_xboole_0 @ ( k6_relat_1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','90','95'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('136',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k9_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k9_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['134','138'])).

thf('140',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('141',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('142',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['139','140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( k1_xboole_0 != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['133','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( k1_xboole_0
      = ( k6_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['122','144'])).

thf('146',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('148',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_C ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    = ( k6_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('150',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_C ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ sk_C ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X23: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('152',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('153',plain,
    ( sk_C
    = ( k9_relat_1 @ ( k6_relat_1 @ sk_C ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['150','151','152'])).

thf('154',plain,
    ( ( sk_C
      = ( k9_relat_1 @ k1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['145','153'])).

thf('155',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('156',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X28 ) @ X29 )
      | ( ( k7_relat_1 @ X28 @ X29 )
        = X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('159',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['93','94'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('164',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['93','94'])).

thf('165',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['162','163','164'])).

thf('166',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['154','165'])).

thf('167',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['98','99','100','101','102'])).

thf('169',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['166'])).

thf('170',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('171',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['35','167','168','169','170'])).

thf('172',plain,(
    $false ),
    inference(simplify,[status(thm)],['171'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.E3c0Q7DwHW
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:08:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 179 iterations in 0.089s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.54  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.54  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.54  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.54  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.54  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.54  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.54  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.54  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.54  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.54  thf(t38_relset_1, conjecture,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.20/0.54         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.54        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54          ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.20/0.54            ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t38_relset_1])).
% 0.20/0.54  thf('0', plain,
% 0.20/0.54      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.54          != (k2_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.54        | ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.20/0.54            != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.20/0.54          != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.54         <= (~
% 0.20/0.54             (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.20/0.54                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.54      inference('split', [status(esa)], ['0'])).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.20/0.54         (((k1_relset_1 @ X39 @ X40 @ X38) = (k1_relat_1 @ X38))
% 0.20/0.54          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.54  thf('4', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.20/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) != (k1_relat_1 @ sk_C)))
% 0.20/0.54         <= (~
% 0.20/0.54             (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.20/0.54                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.54      inference('demod', [status(thm)], ['1', '4'])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(redefinition_k7_relset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 0.20/0.54          | ((k7_relset_1 @ X45 @ X46 @ X44 @ X47) = (k9_relat_1 @ X44 @ X47)))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.54          != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.54         <= (~
% 0.20/0.54             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.54                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.54      inference('split', [status(esa)], ['0'])).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      ((((k9_relat_1 @ sk_C @ sk_A) != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.54         <= (~
% 0.20/0.54             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.54                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(cc2_relset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.20/0.54         ((v4_relat_1 @ X35 @ X36)
% 0.20/0.54          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.20/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.54  thf('13', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.20/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.54  thf(t209_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.54       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X17 : $i, X18 : $i]:
% 0.20/0.54         (((X17) = (k7_relat_1 @ X17 @ X18))
% 0.20/0.54          | ~ (v4_relat_1 @ X17 @ X18)
% 0.20/0.54          | ~ (v1_relat_1 @ X17))),
% 0.20/0.54      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(cc1_relset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54       ( v1_relat_1 @ C ) ))).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.54         ((v1_relat_1 @ X32)
% 0.20/0.54          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.20/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.54  thf('18', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.54  thf('19', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['15', '18'])).
% 0.20/0.54  thf(t148_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ B ) =>
% 0.20/0.54       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (![X9 : $i, X10 : $i]:
% 0.20/0.54         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.20/0.54          | ~ (v1_relat_1 @ X9))),
% 0.20/0.54      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 0.20/0.54        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.54      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.54  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.54  thf('23', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.20/0.54         (((k2_relset_1 @ X42 @ X43 @ X41) = (k2_relat_1 @ X41))
% 0.20/0.54          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43))))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.20/0.54      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.20/0.54         <= (~
% 0.20/0.54             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.54                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.54      inference('demod', [status(thm)], ['10', '23', '26'])).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.54          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.54  thf('29', plain,
% 0.20/0.54      (~
% 0.20/0.54       (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.20/0.54          = (k1_relset_1 @ sk_A @ sk_B @ sk_C))) | 
% 0.20/0.54       ~
% 0.20/0.54       (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.54          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.54      inference('split', [status(esa)], ['0'])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      (~
% 0.20/0.54       (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.20/0.54          = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['28', '29'])).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) != (k1_relat_1 @ sk_C))),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['5', '30'])).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(redefinition_k8_relset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.20/0.54  thf('33', plain,
% 0.20/0.54      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 0.20/0.54          | ((k8_relset_1 @ X49 @ X50 @ X48 @ X51) = (k10_relat_1 @ X48 @ X51)))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.54  thf('34', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.54  thf('35', plain, (((k10_relat_1 @ sk_C @ sk_B) != (k1_relat_1 @ sk_C))),
% 0.20/0.54      inference('demod', [status(thm)], ['31', '34'])).
% 0.20/0.54  thf(t71_relat_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.20/0.54       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.54  thf('36', plain, (![X22 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 0.20/0.54      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.54  thf(t64_relat_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ A ) =>
% 0.20/0.54       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.54           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.54         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.54  thf('37', plain,
% 0.20/0.54      (![X21 : $i]:
% 0.20/0.54         (((k1_relat_1 @ X21) != (k1_xboole_0))
% 0.20/0.54          | ((X21) = (k1_xboole_0))
% 0.20/0.54          | ~ (v1_relat_1 @ X21))),
% 0.20/0.54      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.20/0.54  thf('38', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((X0) != (k1_xboole_0))
% 0.20/0.54          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.54          | ((k6_relat_1 @ X0) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.54  thf(fc4_funct_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.54       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.54  thf('39', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.20/0.54      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.20/0.54  thf('40', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((X0) != (k1_xboole_0)) | ((k6_relat_1 @ X0) = (k1_xboole_0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.54  thf('41', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.54      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.54  thf(t94_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ B ) =>
% 0.20/0.54       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.20/0.54  thf('42', plain,
% 0.20/0.54      (![X26 : $i, X27 : $i]:
% 0.20/0.54         (((k7_relat_1 @ X27 @ X26) = (k5_relat_1 @ (k6_relat_1 @ X26) @ X27))
% 0.20/0.54          | ~ (v1_relat_1 @ X27))),
% 0.20/0.54      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.20/0.54  thf('43', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k7_relat_1 @ X0 @ k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.54          | ~ (v1_relat_1 @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['41', '42'])).
% 0.20/0.54  thf(t195_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.54          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.20/0.54               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.20/0.54  thf('44', plain,
% 0.20/0.54      (![X15 : $i, X16 : $i]:
% 0.20/0.54         (((X15) = (k1_xboole_0))
% 0.20/0.54          | ((k2_relat_1 @ (k2_zfmisc_1 @ X15 @ X16)) = (X16))
% 0.20/0.54          | ((X16) = (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.20/0.54  thf('45', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t3_subset, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.54  thf('46', plain,
% 0.20/0.54      (![X4 : $i, X5 : $i]:
% 0.20/0.54         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.54  thf('47', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.54  thf(t25_relat_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( v1_relat_1 @ B ) =>
% 0.20/0.54           ( ( r1_tarski @ A @ B ) =>
% 0.20/0.54             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.20/0.54               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.20/0.54  thf('48', plain,
% 0.20/0.54      (![X19 : $i, X20 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ X19)
% 0.20/0.54          | (r1_tarski @ (k2_relat_1 @ X20) @ (k2_relat_1 @ X19))
% 0.20/0.54          | ~ (r1_tarski @ X20 @ X19)
% 0.20/0.54          | ~ (v1_relat_1 @ X20))),
% 0.20/0.54      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.20/0.54  thf('49', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.54        | (r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.20/0.54           (k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.20/0.54        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.54  thf('50', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.54  thf(fc6_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.54  thf('51', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.20/0.54      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.54  thf('52', plain,
% 0.20/0.54      ((r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.20/0.54        (k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.20/0.54  thf('53', plain,
% 0.20/0.54      (((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)
% 0.20/0.54        | ((sk_B) = (k1_xboole_0))
% 0.20/0.54        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['44', '52'])).
% 0.20/0.54  thf(t79_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ B ) =>
% 0.20/0.54       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.20/0.54         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.20/0.54  thf('54', plain,
% 0.20/0.54      (![X24 : $i, X25 : $i]:
% 0.20/0.54         (~ (r1_tarski @ (k2_relat_1 @ X24) @ X25)
% 0.20/0.54          | ((k5_relat_1 @ X24 @ (k6_relat_1 @ X25)) = (X24))
% 0.20/0.54          | ~ (v1_relat_1 @ X24))),
% 0.20/0.54      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.20/0.54  thf('55', plain,
% 0.20/0.54      ((((sk_A) = (k1_xboole_0))
% 0.20/0.54        | ((sk_B) = (k1_xboole_0))
% 0.20/0.54        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.54        | ((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.54  thf('56', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.54  thf('57', plain,
% 0.20/0.54      ((((sk_A) = (k1_xboole_0))
% 0.20/0.54        | ((sk_B) = (k1_xboole_0))
% 0.20/0.54        | ((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C)))),
% 0.20/0.54      inference('demod', [status(thm)], ['55', '56'])).
% 0.20/0.54  thf(t182_relat_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( v1_relat_1 @ B ) =>
% 0.20/0.54           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.20/0.54             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.20/0.54  thf('58', plain,
% 0.20/0.54      (![X13 : $i, X14 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ X13)
% 0.20/0.54          | ((k1_relat_1 @ (k5_relat_1 @ X14 @ X13))
% 0.20/0.54              = (k10_relat_1 @ X14 @ (k1_relat_1 @ X13)))
% 0.20/0.54          | ~ (v1_relat_1 @ X14))),
% 0.20/0.54      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.20/0.54  thf('59', plain,
% 0.20/0.54      ((((k1_relat_1 @ sk_C)
% 0.20/0.54          = (k10_relat_1 @ sk_C @ (k1_relat_1 @ (k6_relat_1 @ sk_B))))
% 0.20/0.54        | ((sk_B) = (k1_xboole_0))
% 0.20/0.54        | ((sk_A) = (k1_xboole_0))
% 0.20/0.54        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.54        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['57', '58'])).
% 0.20/0.54  thf('60', plain, (![X22 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 0.20/0.54      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.54  thf('61', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.54  thf('62', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.20/0.54      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.20/0.54  thf('63', plain,
% 0.20/0.54      ((((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B))
% 0.20/0.54        | ((sk_B) = (k1_xboole_0))
% 0.20/0.54        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 0.20/0.54  thf('64', plain, (((k10_relat_1 @ sk_C @ sk_B) != (k1_relat_1 @ sk_C))),
% 0.20/0.54      inference('demod', [status(thm)], ['31', '34'])).
% 0.20/0.54  thf('65', plain,
% 0.20/0.54      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 0.20/0.54        | ((sk_A) = (k1_xboole_0))
% 0.20/0.54        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.54  thf('66', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['65'])).
% 0.20/0.54  thf('67', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.54  thf('68', plain,
% 0.20/0.54      (![X19 : $i, X20 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ X19)
% 0.20/0.54          | (r1_tarski @ (k1_relat_1 @ X20) @ (k1_relat_1 @ X19))
% 0.20/0.54          | ~ (r1_tarski @ X20 @ X19)
% 0.20/0.54          | ~ (v1_relat_1 @ X20))),
% 0.20/0.54      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.20/0.54  thf('69', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.54        | (r1_tarski @ (k1_relat_1 @ sk_C) @ 
% 0.20/0.54           (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.20/0.54        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['67', '68'])).
% 0.20/0.54  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.54  thf('71', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.20/0.54      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.54  thf('72', plain,
% 0.20/0.54      ((r1_tarski @ (k1_relat_1 @ sk_C) @ 
% 0.20/0.54        (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.20/0.54  thf(t97_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ B ) =>
% 0.20/0.54       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.20/0.54         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.20/0.54  thf('73', plain,
% 0.20/0.54      (![X28 : $i, X29 : $i]:
% 0.20/0.54         (~ (r1_tarski @ (k1_relat_1 @ X28) @ X29)
% 0.20/0.54          | ((k7_relat_1 @ X28 @ X29) = (X28))
% 0.20/0.54          | ~ (v1_relat_1 @ X28))),
% 0.20/0.54      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.20/0.54  thf('74', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.54        | ((k7_relat_1 @ sk_C @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.20/0.54            = (sk_C)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['72', '73'])).
% 0.20/0.54  thf('75', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.54  thf('76', plain,
% 0.20/0.54      (((k7_relat_1 @ sk_C @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.20/0.54         = (sk_C))),
% 0.20/0.54      inference('demod', [status(thm)], ['74', '75'])).
% 0.20/0.54  thf('77', plain,
% 0.20/0.54      ((((k7_relat_1 @ sk_C @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))
% 0.20/0.54          = (sk_C))
% 0.20/0.54        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['66', '76'])).
% 0.20/0.54  thf(t113_zfmisc_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.54       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.54  thf('78', plain,
% 0.20/0.54      (![X2 : $i, X3 : $i]:
% 0.20/0.54         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.54  thf('79', plain,
% 0.20/0.54      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.54      inference('simplify', [status(thm)], ['78'])).
% 0.20/0.54  thf(t60_relat_1, axiom,
% 0.20/0.54    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.54     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.54  thf('80', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.54  thf('81', plain,
% 0.20/0.54      ((((k7_relat_1 @ sk_C @ k1_xboole_0) = (sk_C)) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['77', '79', '80'])).
% 0.20/0.54  thf('82', plain,
% 0.20/0.54      ((((k5_relat_1 @ k1_xboole_0 @ sk_C) = (sk_C))
% 0.20/0.54        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.54        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['43', '81'])).
% 0.20/0.54  thf('83', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.54  thf('84', plain,
% 0.20/0.54      ((((k5_relat_1 @ k1_xboole_0 @ sk_C) = (sk_C)) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['82', '83'])).
% 0.20/0.54  thf('85', plain,
% 0.20/0.54      (![X13 : $i, X14 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ X13)
% 0.20/0.54          | ((k1_relat_1 @ (k5_relat_1 @ X14 @ X13))
% 0.20/0.54              = (k10_relat_1 @ X14 @ (k1_relat_1 @ X13)))
% 0.20/0.54          | ~ (v1_relat_1 @ X14))),
% 0.20/0.54      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.20/0.54  thf('86', plain,
% 0.20/0.54      ((((k1_relat_1 @ sk_C)
% 0.20/0.54          = (k10_relat_1 @ k1_xboole_0 @ (k1_relat_1 @ sk_C)))
% 0.20/0.54        | ((sk_A) = (k1_xboole_0))
% 0.20/0.54        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.54        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.54      inference('sup+', [status(thm)], ['84', '85'])).
% 0.20/0.54  thf('87', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.54  thf('88', plain,
% 0.20/0.54      (![X24 : $i, X25 : $i]:
% 0.20/0.54         (~ (r1_tarski @ (k2_relat_1 @ X24) @ X25)
% 0.20/0.54          | ((k5_relat_1 @ X24 @ (k6_relat_1 @ X25)) = (X24))
% 0.20/0.54          | ~ (v1_relat_1 @ X24))),
% 0.20/0.54      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.20/0.54  thf('89', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.20/0.54          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.54          | ((k5_relat_1 @ k1_xboole_0 @ (k6_relat_1 @ X0)) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['87', '88'])).
% 0.20/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.54  thf('90', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.54  thf('91', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.54  thf('92', plain,
% 0.20/0.54      (![X4 : $i, X6 : $i]:
% 0.20/0.54         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.20/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.54  thf('93', plain,
% 0.20/0.54      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['91', '92'])).
% 0.20/0.54  thf('94', plain,
% 0.20/0.54      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.54         ((v1_relat_1 @ X32)
% 0.20/0.54          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.20/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.54  thf('95', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.54      inference('sup-', [status(thm)], ['93', '94'])).
% 0.20/0.54  thf('96', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((k5_relat_1 @ k1_xboole_0 @ (k6_relat_1 @ X0)) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['89', '90', '95'])).
% 0.20/0.54  thf('97', plain,
% 0.20/0.54      (![X13 : $i, X14 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ X13)
% 0.20/0.54          | ((k1_relat_1 @ (k5_relat_1 @ X14 @ X13))
% 0.20/0.54              = (k10_relat_1 @ X14 @ (k1_relat_1 @ X13)))
% 0.20/0.54          | ~ (v1_relat_1 @ X14))),
% 0.20/0.54      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.20/0.54  thf('98', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k1_relat_1 @ k1_xboole_0)
% 0.20/0.54            = (k10_relat_1 @ k1_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X0))))
% 0.20/0.54          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.54          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['96', '97'])).
% 0.20/0.54  thf('99', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.54  thf('100', plain, (![X22 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 0.20/0.54      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.54  thf('101', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.54      inference('sup-', [status(thm)], ['93', '94'])).
% 0.20/0.54  thf('102', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.20/0.54      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.20/0.54  thf('103', plain,
% 0.20/0.54      (![X0 : $i]: ((k1_xboole_0) = (k10_relat_1 @ k1_xboole_0 @ X0))),
% 0.20/0.54      inference('demod', [status(thm)], ['98', '99', '100', '101', '102'])).
% 0.20/0.54  thf('104', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.54      inference('sup-', [status(thm)], ['93', '94'])).
% 0.20/0.54  thf('105', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.54  thf('106', plain,
% 0.20/0.54      ((((k1_relat_1 @ sk_C) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['86', '103', '104', '105'])).
% 0.20/0.54  thf('107', plain,
% 0.20/0.54      (![X21 : $i]:
% 0.20/0.54         (((k1_relat_1 @ X21) != (k1_xboole_0))
% 0.20/0.54          | ((X21) = (k1_xboole_0))
% 0.20/0.54          | ~ (v1_relat_1 @ X21))),
% 0.20/0.54      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.20/0.54  thf('108', plain,
% 0.20/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.54        | ((sk_A) = (k1_xboole_0))
% 0.20/0.54        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.54        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['106', '107'])).
% 0.20/0.54  thf('109', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.54  thf('110', plain,
% 0.20/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.54        | ((sk_A) = (k1_xboole_0))
% 0.20/0.54        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['108', '109'])).
% 0.20/0.54  thf('111', plain, ((((sk_C) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['110'])).
% 0.20/0.54  thf('112', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.54  thf('113', plain,
% 0.20/0.54      (((r1_tarski @ sk_C @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))
% 0.20/0.54        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['111', '112'])).
% 0.20/0.54  thf('114', plain,
% 0.20/0.54      (![X2 : $i, X3 : $i]:
% 0.20/0.54         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.54  thf('115', plain,
% 0.20/0.54      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.20/0.54      inference('simplify', [status(thm)], ['114'])).
% 0.20/0.54  thf('116', plain,
% 0.20/0.54      (((r1_tarski @ sk_C @ k1_xboole_0) | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['113', '115'])).
% 0.20/0.54  thf('117', plain, (![X22 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 0.20/0.54      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.54  thf('118', plain,
% 0.20/0.54      (![X28 : $i, X29 : $i]:
% 0.20/0.54         (~ (r1_tarski @ (k1_relat_1 @ X28) @ X29)
% 0.20/0.54          | ((k7_relat_1 @ X28 @ X29) = (X28))
% 0.20/0.54          | ~ (v1_relat_1 @ X28))),
% 0.20/0.54      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.20/0.54  thf('119', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.54          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.54          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['117', '118'])).
% 0.20/0.54  thf('120', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.20/0.54      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.20/0.54  thf('121', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.54          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['119', '120'])).
% 0.20/0.54  thf('122', plain,
% 0.20/0.54      ((((sk_C) = (k1_xboole_0))
% 0.20/0.54        | ((k7_relat_1 @ (k6_relat_1 @ sk_C) @ k1_xboole_0)
% 0.20/0.54            = (k6_relat_1 @ sk_C)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['116', '121'])).
% 0.20/0.54  thf('123', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((k5_relat_1 @ k1_xboole_0 @ (k6_relat_1 @ X0)) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['89', '90', '95'])).
% 0.20/0.54  thf('124', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k7_relat_1 @ X0 @ k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.54          | ~ (v1_relat_1 @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['41', '42'])).
% 0.20/0.54  thf('125', plain,
% 0.20/0.54      (![X9 : $i, X10 : $i]:
% 0.20/0.54         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.20/0.54          | ~ (v1_relat_1 @ X9))),
% 0.20/0.54      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.54  thf('126', plain,
% 0.20/0.54      (![X21 : $i]:
% 0.20/0.54         (((k2_relat_1 @ X21) != (k1_xboole_0))
% 0.20/0.54          | ((X21) = (k1_xboole_0))
% 0.20/0.54          | ~ (v1_relat_1 @ X21))),
% 0.20/0.54      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.20/0.54  thf('127', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((k9_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 0.20/0.54          | ~ (v1_relat_1 @ X1)
% 0.20/0.54          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.20/0.54          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['125', '126'])).
% 0.20/0.54  thf('128', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.54          | ~ (v1_relat_1 @ X0)
% 0.20/0.54          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.20/0.54          | ~ (v1_relat_1 @ X0)
% 0.20/0.54          | ((k9_relat_1 @ X0 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['124', '127'])).
% 0.20/0.54  thf('129', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k9_relat_1 @ X0 @ k1_xboole_0) != (k1_xboole_0))
% 0.20/0.54          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.20/0.54          | ~ (v1_relat_1 @ X0)
% 0.20/0.54          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['128'])).
% 0.20/0.54  thf('130', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.54          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.54          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.20/0.54          | ((k9_relat_1 @ (k6_relat_1 @ X0) @ k1_xboole_0) != (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['123', '129'])).
% 0.20/0.54  thf('131', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.54      inference('sup-', [status(thm)], ['93', '94'])).
% 0.20/0.54  thf('132', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.20/0.54      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.20/0.54  thf('133', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k7_relat_1 @ (k6_relat_1 @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.20/0.54          | ((k9_relat_1 @ (k6_relat_1 @ X0) @ k1_xboole_0) != (k1_xboole_0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['130', '131', '132'])).
% 0.20/0.54  thf('134', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((k5_relat_1 @ k1_xboole_0 @ (k6_relat_1 @ X0)) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['89', '90', '95'])).
% 0.20/0.54  thf('135', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k7_relat_1 @ X0 @ k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.54          | ~ (v1_relat_1 @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['41', '42'])).
% 0.20/0.54  thf('136', plain,
% 0.20/0.54      (![X9 : $i, X10 : $i]:
% 0.20/0.54         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.20/0.54          | ~ (v1_relat_1 @ X9))),
% 0.20/0.54      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.54  thf('137', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.54            = (k9_relat_1 @ X0 @ k1_xboole_0))
% 0.20/0.54          | ~ (v1_relat_1 @ X0)
% 0.20/0.54          | ~ (v1_relat_1 @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['135', '136'])).
% 0.20/0.54  thf('138', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ X0)
% 0.20/0.54          | ((k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.54              = (k9_relat_1 @ X0 @ k1_xboole_0)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['137'])).
% 0.20/0.54  thf('139', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k2_relat_1 @ k1_xboole_0)
% 0.20/0.54            = (k9_relat_1 @ (k6_relat_1 @ X0) @ k1_xboole_0))
% 0.20/0.54          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['134', '138'])).
% 0.20/0.54  thf('140', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.54  thf('141', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.20/0.54      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.20/0.54  thf('142', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((k1_xboole_0) = (k9_relat_1 @ (k6_relat_1 @ X0) @ k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['139', '140', '141'])).
% 0.20/0.54  thf('143', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k7_relat_1 @ (k6_relat_1 @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.20/0.54          | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['133', '142'])).
% 0.20/0.54  thf('144', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((k7_relat_1 @ (k6_relat_1 @ X0) @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.54      inference('simplify', [status(thm)], ['143'])).
% 0.20/0.54  thf('145', plain,
% 0.20/0.54      ((((sk_C) = (k1_xboole_0)) | ((k1_xboole_0) = (k6_relat_1 @ sk_C)))),
% 0.20/0.54      inference('demod', [status(thm)], ['122', '144'])).
% 0.20/0.54  thf('146', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.54  thf('147', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.54          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['119', '120'])).
% 0.20/0.54  thf('148', plain,
% 0.20/0.54      (((k7_relat_1 @ (k6_relat_1 @ sk_C) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.54         = (k6_relat_1 @ sk_C))),
% 0.20/0.54      inference('sup-', [status(thm)], ['146', '147'])).
% 0.20/0.54  thf('149', plain,
% 0.20/0.54      (![X9 : $i, X10 : $i]:
% 0.20/0.54         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.20/0.54          | ~ (v1_relat_1 @ X9))),
% 0.20/0.54      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.54  thf('150', plain,
% 0.20/0.54      ((((k2_relat_1 @ (k6_relat_1 @ sk_C))
% 0.20/0.54          = (k9_relat_1 @ (k6_relat_1 @ sk_C) @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.20/0.54        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_C)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['148', '149'])).
% 0.20/0.54  thf('151', plain, (![X23 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.20/0.54      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.54  thf('152', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.20/0.54      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.20/0.54  thf('153', plain,
% 0.20/0.54      (((sk_C)
% 0.20/0.54         = (k9_relat_1 @ (k6_relat_1 @ sk_C) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('demod', [status(thm)], ['150', '151', '152'])).
% 0.20/0.54  thf('154', plain,
% 0.20/0.54      ((((sk_C) = (k9_relat_1 @ k1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.20/0.54        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['145', '153'])).
% 0.20/0.54  thf('155', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.54  thf('156', plain,
% 0.20/0.54      (![X28 : $i, X29 : $i]:
% 0.20/0.54         (~ (r1_tarski @ (k1_relat_1 @ X28) @ X29)
% 0.20/0.54          | ((k7_relat_1 @ X28 @ X29) = (X28))
% 0.20/0.54          | ~ (v1_relat_1 @ X28))),
% 0.20/0.54      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.20/0.54  thf('157', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.20/0.54          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.54          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['155', '156'])).
% 0.20/0.54  thf('158', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.54  thf('159', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.54      inference('sup-', [status(thm)], ['93', '94'])).
% 0.20/0.54  thf('160', plain,
% 0.20/0.54      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['157', '158', '159'])).
% 0.20/0.54  thf('161', plain,
% 0.20/0.54      (![X9 : $i, X10 : $i]:
% 0.20/0.54         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.20/0.54          | ~ (v1_relat_1 @ X9))),
% 0.20/0.54      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.54  thf('162', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.54          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['160', '161'])).
% 0.20/0.54  thf('163', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.54  thf('164', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.54      inference('sup-', [status(thm)], ['93', '94'])).
% 0.20/0.54  thf('165', plain,
% 0.20/0.54      (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))),
% 0.20/0.54      inference('demod', [status(thm)], ['162', '163', '164'])).
% 0.20/0.54  thf('166', plain, ((((sk_C) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['154', '165'])).
% 0.20/0.54  thf('167', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.54      inference('simplify', [status(thm)], ['166'])).
% 0.20/0.54  thf('168', plain,
% 0.20/0.54      (![X0 : $i]: ((k1_xboole_0) = (k10_relat_1 @ k1_xboole_0 @ X0))),
% 0.20/0.54      inference('demod', [status(thm)], ['98', '99', '100', '101', '102'])).
% 0.20/0.54  thf('169', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.54      inference('simplify', [status(thm)], ['166'])).
% 0.20/0.54  thf('170', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.54  thf('171', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['35', '167', '168', '169', '170'])).
% 0.20/0.54  thf('172', plain, ($false), inference('simplify', [status(thm)], ['171'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
