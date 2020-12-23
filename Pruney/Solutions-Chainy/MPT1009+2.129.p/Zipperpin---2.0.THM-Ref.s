%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BO84FXBA2Y

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 363 expanded)
%              Number of leaves         :   33 ( 122 expanded)
%              Depth                    :   18
%              Number of atoms          :  670 (3281 expanded)
%              Number of equality atoms :   59 ( 222 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t64_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k7_relset_1 @ X33 @ X34 @ X32 @ X35 )
        = ( k9_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X24 @ X25 ) @ ( k2_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v4_relat_1 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v4_relat_1 @ X20 @ X21 )
      | ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X22: $i,X23: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['10','15'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('17',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X10
        = ( k1_tarski @ X9 ) )
      | ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('18',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k1_relat_1 @ X28 )
       != ( k1_tarski @ X27 ) )
      | ( ( k2_relat_1 @ X28 )
        = ( k1_tarski @ ( k1_funct_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['20'])).

thf('22',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('24',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('26',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('29',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['27','28'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('30',plain,(
    ! [X26: $i] :
      ( ( ( k1_relat_1 @ X26 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X26 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('31',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X24 @ X25 ) @ ( k2_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k9_relat_1 @ sk_D @ X0 ) )
      | ( ( k2_relat_1 @ sk_D )
        = ( k9_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('39',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_zfmisc_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('40',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['41'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('43',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v4_relat_1 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['40','46'])).

thf('48',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v4_relat_1 @ X20 @ X21 )
      | ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_zfmisc_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('51',plain,(
    ! [X14: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X14 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X22: $i,X23: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('53',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['49','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['49','53'])).

thf('56',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X10
        = ( k1_tarski @ X9 ) )
      | ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ ( k1_tarski @ X11 ) )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('59',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X11 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['49','53'])).

thf('62',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['54','64'])).

thf('66',plain,
    ( ( k2_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['33'])).

thf('67',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('68',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['38','65','66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['54','64'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['4','68','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BO84FXBA2Y
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:58:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 160 iterations in 0.048s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.50  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.50  thf(t64_funct_2, conjecture,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.20/0.50         ( m1_subset_1 @
% 0.20/0.50           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.20/0.50       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.50         ( r1_tarski @
% 0.20/0.50           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.20/0.50           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.20/0.50            ( m1_subset_1 @
% 0.20/0.50              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.20/0.50          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.50            ( r1_tarski @
% 0.20/0.50              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.20/0.50              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (~ (r1_tarski @ 
% 0.20/0.50          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.20/0.50          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_D @ 
% 0.20/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(redefinition_k7_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.20/0.50          | ((k7_relset_1 @ X33 @ X34 @ X32 @ X35) = (k9_relat_1 @ X32 @ X35)))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.20/0.50           = (k9_relat_1 @ sk_D @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.20/0.50          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.50  thf(t144_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X24 : $i, X25 : $i]:
% 0.20/0.50         ((r1_tarski @ (k9_relat_1 @ X24 @ X25) @ (k2_relat_1 @ X24))
% 0.20/0.50          | ~ (v1_relat_1 @ X24))),
% 0.20/0.50      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_D @ 
% 0.20/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(cc2_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.50         ((v4_relat_1 @ X29 @ X30)
% 0.20/0.50          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.50  thf('8', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf(d18_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X20 : $i, X21 : $i]:
% 0.20/0.50         (~ (v4_relat_1 @ X20 @ X21)
% 0.20/0.50          | (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.20/0.50          | ~ (v1_relat_1 @ X20))),
% 0.20/0.50      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ sk_D)
% 0.20/0.50        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_D @ 
% 0.20/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(cc2_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X18 : $i, X19 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.20/0.50          | (v1_relat_1 @ X18)
% 0.20/0.50          | ~ (v1_relat_1 @ X19))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.20/0.50        | (v1_relat_1 @ sk_D))),
% 0.20/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf(fc6_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X22 : $i, X23 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X22 @ X23))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.50  thf('15', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.50  thf('16', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['10', '15'])).
% 0.20/0.50  thf(l3_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.20/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X9 : $i, X10 : $i]:
% 0.20/0.50         (((X10) = (k1_tarski @ X9))
% 0.20/0.50          | ((X10) = (k1_xboole_0))
% 0.20/0.50          | ~ (r1_tarski @ X10 @ (k1_tarski @ X9)))),
% 0.20/0.50      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.20/0.50        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.50  thf(t14_funct_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.50       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.20/0.50         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X27 : $i, X28 : $i]:
% 0.20/0.50         (((k1_relat_1 @ X28) != (k1_tarski @ X27))
% 0.20/0.50          | ((k2_relat_1 @ X28) = (k1_tarski @ (k1_funct_1 @ X28 @ X27)))
% 0.20/0.50          | ~ (v1_funct_1 @ X28)
% 0.20/0.50          | ~ (v1_relat_1 @ X28))),
% 0.20/0.50      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.20/0.50          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.20/0.50          | ~ (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (v1_funct_1 @ X0)
% 0.20/0.50          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.20/0.50        | ~ (v1_funct_1 @ sk_D)
% 0.20/0.50        | ~ (v1_relat_1 @ sk_D)
% 0.20/0.50        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.20/0.50      inference('eq_res', [status(thm)], ['20'])).
% 0.20/0.50  thf('22', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('23', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.20/0.50        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.20/0.50          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.20/0.50        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['5', '26'])).
% 0.20/0.50  thf('28', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.50  thf('29', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.50  thf(t65_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.50         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (![X26 : $i]:
% 0.20/0.50         (((k1_relat_1 @ X26) != (k1_xboole_0))
% 0.20/0.50          | ((k2_relat_1 @ X26) = (k1_xboole_0))
% 0.20/0.50          | ~ (v1_relat_1 @ X26))),
% 0.20/0.50      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.50        | ~ (v1_relat_1 @ sk_D)
% 0.20/0.50        | ((k2_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.50  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.50        | ((k2_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.50  thf('34', plain, (((k2_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (![X24 : $i, X25 : $i]:
% 0.20/0.50         ((r1_tarski @ (k9_relat_1 @ X24 @ X25) @ (k2_relat_1 @ X24))
% 0.20/0.50          | ~ (v1_relat_1 @ X24))),
% 0.20/0.50      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.20/0.50  thf(d10_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (![X0 : $i, X2 : $i]:
% 0.20/0.50         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ (k9_relat_1 @ X0 @ X1))
% 0.20/0.50          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ X1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r1_tarski @ k1_xboole_0 @ (k9_relat_1 @ sk_D @ X0))
% 0.20/0.50          | ((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ X0))
% 0.20/0.50          | ~ (v1_relat_1 @ sk_D))),
% 0.20/0.50      inference('sup-', [status(thm)], ['34', '37'])).
% 0.20/0.50  thf(t113_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (![X13 : $i, X14 : $i]:
% 0.20/0.50         (((k2_zfmisc_1 @ X13 @ X14) = (k1_xboole_0))
% 0.20/0.50          | ((X14) != (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      (![X13 : $i]: ((k2_zfmisc_1 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.50  thf('42', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.50      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.50  thf(t3_subset, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (![X15 : $i, X17 : $i]:
% 0.20/0.50         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.50  thf('44', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.50         ((v4_relat_1 @ X29 @ X30)
% 0.20/0.50          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: (v4_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X1)),
% 0.20/0.50      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.50  thf('47', plain, (![X0 : $i]: (v4_relat_1 @ k1_xboole_0 @ X0)),
% 0.20/0.50      inference('sup+', [status(thm)], ['40', '46'])).
% 0.20/0.50  thf('48', plain,
% 0.20/0.50      (![X20 : $i, X21 : $i]:
% 0.20/0.50         (~ (v4_relat_1 @ X20 @ X21)
% 0.20/0.50          | (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.20/0.50          | ~ (v1_relat_1 @ X20))),
% 0.20/0.50      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.50          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      (![X13 : $i, X14 : $i]:
% 0.20/0.50         (((k2_zfmisc_1 @ X13 @ X14) = (k1_xboole_0))
% 0.20/0.50          | ((X13) != (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      (![X14 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X14) = (k1_xboole_0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.50  thf('52', plain,
% 0.20/0.50      (![X22 : $i, X23 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X22 @ X23))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.50  thf('53', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.50      inference('sup+', [status(thm)], ['51', '52'])).
% 0.20/0.50  thf('54', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.20/0.50      inference('demod', [status(thm)], ['49', '53'])).
% 0.20/0.50  thf('55', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.20/0.50      inference('demod', [status(thm)], ['49', '53'])).
% 0.20/0.50  thf('56', plain,
% 0.20/0.50      (![X9 : $i, X10 : $i]:
% 0.20/0.50         (((X10) = (k1_tarski @ X9))
% 0.20/0.50          | ((X10) = (k1_xboole_0))
% 0.20/0.50          | ~ (r1_tarski @ X10 @ (k1_tarski @ X9)))),
% 0.20/0.50      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.20/0.50  thf('57', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.20/0.50          | ((k1_relat_1 @ k1_xboole_0) = (k1_tarski @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.50  thf('58', plain,
% 0.20/0.50      (![X10 : $i, X11 : $i]:
% 0.20/0.50         ((r1_tarski @ X10 @ (k1_tarski @ X11)) | ((X10) != (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.20/0.50  thf('59', plain,
% 0.20/0.50      (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X11))),
% 0.20/0.50      inference('simplify', [status(thm)], ['58'])).
% 0.20/0.50  thf('60', plain,
% 0.20/0.50      (((r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))
% 0.20/0.50        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['57', '59'])).
% 0.20/0.50  thf('61', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.20/0.50      inference('demod', [status(thm)], ['49', '53'])).
% 0.20/0.50  thf('62', plain,
% 0.20/0.50      (![X0 : $i, X2 : $i]:
% 0.20/0.50         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.50  thf('63', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r1_tarski @ X0 @ (k1_relat_1 @ k1_xboole_0))
% 0.20/0.50          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.50  thf('64', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('clc', [status(thm)], ['60', '63'])).
% 0.20/0.50  thf('65', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.50      inference('demod', [status(thm)], ['54', '64'])).
% 0.20/0.50  thf('66', plain, (((k2_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.50  thf('67', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.50  thf('68', plain, (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ sk_D @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['38', '65', '66', '67'])).
% 0.20/0.50  thf('69', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.50      inference('demod', [status(thm)], ['54', '64'])).
% 0.20/0.50  thf('70', plain, ($false),
% 0.20/0.50      inference('demod', [status(thm)], ['4', '68', '69'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
