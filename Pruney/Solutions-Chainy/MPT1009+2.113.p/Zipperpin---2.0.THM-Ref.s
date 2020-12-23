%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.coSBpdTKfP

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 267 expanded)
%              Number of leaves         :   35 (  97 expanded)
%              Depth                    :   18
%              Number of atoms          :  652 (2641 expanded)
%              Number of equality atoms :   44 ( 133 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( ( k7_relset_1 @ X38 @ X39 @ X37 @ X40 )
        = ( k9_relat_1 @ X37 @ X40 ) ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X30 @ X31 ) @ ( k2_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v4_relat_1 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ~ ( v4_relat_1 @ X24 @ X25 )
      | ( r1_tarski @ ( k1_relat_1 @ X24 ) @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( v1_relat_1 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X28: $i,X29: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ( ( k1_relat_1 @ X33 )
       != ( k1_tarski @ X32 ) )
      | ( ( k2_relat_1 @ X33 )
        = ( k1_tarski @ ( k1_funct_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ X0 ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k2_relat_1 @ sk_D )
        = ( k1_tarski @ ( k1_funct_1 @ sk_D @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('22',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ X0 ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_D )
        = ( k1_tarski @ ( k1_funct_1 @ sk_D @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['23'])).

thf('25',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('28',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('31',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X41: $i] :
      ( ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X41 ) @ ( k2_relat_1 @ X41 ) ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('33',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ sk_D ) ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_zfmisc_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('35',plain,(
    ! [X14: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X14 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('37',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','35','36','37'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('39',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    r1_tarski @ sk_D @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('41',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('42',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    sk_D = k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('48',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v5_relat_1 @ X34 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('50',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v5_relat_1 @ X26 @ X27 )
      | ( r1_tarski @ ( k2_relat_1 @ X26 ) @ X27 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X14: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X14 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('53',plain,(
    ! [X28: $i,X29: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('54',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('57',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X30 @ X31 ) @ ( k2_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['52','53'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    sk_D = k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','45'])).

thf('65',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['4','46','63','64','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.coSBpdTKfP
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:53:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 143 iterations in 0.072s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.53  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.53  thf(t64_funct_2, conjecture,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.21/0.53         ( m1_subset_1 @
% 0.21/0.53           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.21/0.53       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.53         ( r1_tarski @
% 0.21/0.53           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.21/0.53           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.21/0.53            ( m1_subset_1 @
% 0.21/0.53              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.21/0.53          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.53            ( r1_tarski @
% 0.21/0.53              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.21/0.53              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      (~ (r1_tarski @ 
% 0.21/0.53          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.21/0.53          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_D @ 
% 0.21/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(redefinition_k7_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.21/0.53          | ((k7_relset_1 @ X38 @ X39 @ X37 @ X40) = (k9_relat_1 @ X37 @ X40)))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.21/0.53           = (k9_relat_1 @ sk_D @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.21/0.53          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['0', '3'])).
% 0.21/0.53  thf(t144_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ B ) =>
% 0.21/0.53       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X30 : $i, X31 : $i]:
% 0.21/0.53         ((r1_tarski @ (k9_relat_1 @ X30 @ X31) @ (k2_relat_1 @ X30))
% 0.21/0.53          | ~ (v1_relat_1 @ X30))),
% 0.21/0.53      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_D @ 
% 0.21/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(cc2_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.21/0.53         ((v4_relat_1 @ X34 @ X35)
% 0.21/0.53          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.53  thf('8', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf(d18_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ B ) =>
% 0.21/0.53       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X24 : $i, X25 : $i]:
% 0.21/0.53         (~ (v4_relat_1 @ X24 @ X25)
% 0.21/0.53          | (r1_tarski @ (k1_relat_1 @ X24) @ X25)
% 0.21/0.53          | ~ (v1_relat_1 @ X24))),
% 0.21/0.53      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ sk_D)
% 0.21/0.53        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_D @ 
% 0.21/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(cc2_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X22 : $i, X23 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.21/0.53          | (v1_relat_1 @ X22)
% 0.21/0.53          | ~ (v1_relat_1 @ X23))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.21/0.53        | (v1_relat_1 @ sk_D))),
% 0.21/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf(fc6_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X28 : $i, X29 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X28 @ X29))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.53  thf('15', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.53  thf('16', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['10', '15'])).
% 0.21/0.53  thf(l3_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.53       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X9 : $i, X10 : $i]:
% 0.21/0.53         (((X10) = (k1_tarski @ X9))
% 0.21/0.53          | ((X10) = (k1_xboole_0))
% 0.21/0.53          | ~ (r1_tarski @ X10 @ (k1_tarski @ X9)))),
% 0.21/0.53      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.21/0.53        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.53  thf(t14_funct_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.53       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.21/0.53         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X32 : $i, X33 : $i]:
% 0.21/0.53         (((k1_relat_1 @ X33) != (k1_tarski @ X32))
% 0.21/0.53          | ((k2_relat_1 @ X33) = (k1_tarski @ (k1_funct_1 @ X33 @ X32)))
% 0.21/0.53          | ~ (v1_funct_1 @ X33)
% 0.21/0.53          | ~ (v1_relat_1 @ X33))),
% 0.21/0.53      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k1_tarski @ sk_A) != (k1_tarski @ X0))
% 0.21/0.53          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.21/0.53          | ~ (v1_relat_1 @ sk_D)
% 0.21/0.53          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.53          | ((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ X0))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.53  thf('21', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.53  thf('22', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k1_tarski @ sk_A) != (k1_tarski @ X0))
% 0.21/0.53          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.21/0.53          | ((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ X0))))),
% 0.21/0.53      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.21/0.53        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.21/0.53      inference('eq_res', [status(thm)], ['23'])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (~ (r1_tarski @ 
% 0.21/0.53          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.21/0.53          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      ((~ (r1_tarski @ 
% 0.21/0.53           (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.21/0.53           (k2_relat_1 @ sk_D))
% 0.21/0.53        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.21/0.53           = (k9_relat_1 @ sk_D @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.21/0.53        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.21/0.53      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '28'])).
% 0.21/0.53  thf('30', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.53  thf('31', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.21/0.53      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf(t3_funct_2, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.53       ( ( v1_funct_1 @ A ) & 
% 0.21/0.53         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.21/0.53         ( m1_subset_1 @
% 0.21/0.53           A @ 
% 0.21/0.53           ( k1_zfmisc_1 @
% 0.21/0.53             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      (![X41 : $i]:
% 0.21/0.53         ((m1_subset_1 @ X41 @ 
% 0.21/0.53           (k1_zfmisc_1 @ 
% 0.21/0.53            (k2_zfmisc_1 @ (k1_relat_1 @ X41) @ (k2_relat_1 @ X41))))
% 0.21/0.53          | ~ (v1_funct_1 @ X41)
% 0.21/0.53          | ~ (v1_relat_1 @ X41))),
% 0.21/0.53      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      (((m1_subset_1 @ sk_D @ 
% 0.21/0.53         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_relat_1 @ sk_D))))
% 0.21/0.53        | ~ (v1_relat_1 @ sk_D)
% 0.21/0.53        | ~ (v1_funct_1 @ sk_D))),
% 0.21/0.53      inference('sup+', [status(thm)], ['31', '32'])).
% 0.21/0.53  thf(t113_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.53       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      (![X13 : $i, X14 : $i]:
% 0.21/0.53         (((k2_zfmisc_1 @ X13 @ X14) = (k1_xboole_0))
% 0.21/0.53          | ((X13) != (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      (![X14 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X14) = (k1_xboole_0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['34'])).
% 0.21/0.53  thf('36', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.53  thf('37', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('38', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.21/0.53      inference('demod', [status(thm)], ['33', '35', '36', '37'])).
% 0.21/0.53  thf(t3_subset, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (![X16 : $i, X17 : $i]:
% 0.21/0.53         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.53  thf('40', plain, ((r1_tarski @ sk_D @ k1_xboole_0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.53  thf(t4_subset_1, axiom,
% 0.21/0.53    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.21/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.53  thf('42', plain,
% 0.21/0.53      (![X16 : $i, X17 : $i]:
% 0.21/0.53         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.53  thf('43', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.53  thf(d10_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      (![X0 : $i, X2 : $i]:
% 0.21/0.53         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.53  thf('46', plain, (((sk_D) = (k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['40', '45'])).
% 0.21/0.53  thf('47', plain,
% 0.21/0.53      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.21/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.53  thf('48', plain,
% 0.21/0.53      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.21/0.53         ((v5_relat_1 @ X34 @ X36)
% 0.21/0.53          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.53  thf('49', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.53  thf(d19_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ B ) =>
% 0.21/0.53       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.53  thf('50', plain,
% 0.21/0.53      (![X26 : $i, X27 : $i]:
% 0.21/0.53         (~ (v5_relat_1 @ X26 @ X27)
% 0.21/0.53          | (r1_tarski @ (k2_relat_1 @ X26) @ X27)
% 0.21/0.53          | ~ (v1_relat_1 @ X26))),
% 0.21/0.53      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.53  thf('51', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.53          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.53  thf('52', plain,
% 0.21/0.53      (![X14 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X14) = (k1_xboole_0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['34'])).
% 0.21/0.53  thf('53', plain,
% 0.21/0.53      (![X28 : $i, X29 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X28 @ X29))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.53  thf('54', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.53      inference('sup+', [status(thm)], ['52', '53'])).
% 0.21/0.53  thf('55', plain, (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 0.21/0.53      inference('demod', [status(thm)], ['51', '54'])).
% 0.21/0.53  thf('56', plain,
% 0.21/0.53      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.53  thf('57', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.53  thf('58', plain,
% 0.21/0.53      (![X30 : $i, X31 : $i]:
% 0.21/0.53         ((r1_tarski @ (k9_relat_1 @ X30 @ X31) @ (k2_relat_1 @ X30))
% 0.21/0.53          | ~ (v1_relat_1 @ X30))),
% 0.21/0.53      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.21/0.53  thf('59', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.21/0.53          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['57', '58'])).
% 0.21/0.53  thf('60', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.53      inference('sup+', [status(thm)], ['52', '53'])).
% 0.21/0.53  thf('61', plain,
% 0.21/0.53      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)),
% 0.21/0.53      inference('demod', [status(thm)], ['59', '60'])).
% 0.21/0.53  thf('62', plain,
% 0.21/0.53      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.53  thf('63', plain,
% 0.21/0.53      (![X0 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.53  thf('64', plain, (((sk_D) = (k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['40', '45'])).
% 0.21/0.53  thf('65', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.53  thf('66', plain, ($false),
% 0.21/0.53      inference('demod', [status(thm)], ['4', '46', '63', '64', '65'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
