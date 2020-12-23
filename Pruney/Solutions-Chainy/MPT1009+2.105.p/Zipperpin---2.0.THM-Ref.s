%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PR8crnLc6d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:03 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  168 (2420 expanded)
%              Number of leaves         :   35 ( 728 expanded)
%              Depth                    :   22
%              Number of atoms          : 1122 (20455 expanded)
%              Number of equality atoms :  101 (1628 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ( X7
        = ( k1_tarski @ X6 ) )
      | ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ ( k1_tarski @ X6 ) ) ) ),
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

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X36: $i] :
      ( ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X36 ) @ ( k2_relat_1 @ X36 ) ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('31',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) @ X0 )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ sk_D ) ) @ sk_D )
    | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('36',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_zfmisc_1 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('37',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_zfmisc_1 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('39',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('43',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v4_relat_1 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['39','45'])).

thf('47',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v4_relat_1 @ X20 @ X21 )
      | ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('50',plain,(
    ! [X22: $i,X23: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('51',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('54',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X7
        = ( k1_tarski @ X6 ) )
      | ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('57',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('58',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('59',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_D ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k1_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('62',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','62'])).

thf('64',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('66',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('67',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ ( k1_tarski @ X8 ) )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('68',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X8 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','68'])).

thf('70',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('71',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('75',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','75'])).

thf('77',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['52','77'])).

thf('79',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['27','28'])).

thf('80',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('81',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('82',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['35','37','78','79','80','81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('85',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('86',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v4_relat_1 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('87',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v4_relat_1 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v4_relat_1 @ X20 @ X21 )
      | ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('90',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['49','50'])).

thf('92',plain,(
    r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('94',plain,(
    m1_subset_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf(cc5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) )
         => ( v4_relat_1 @ C @ A ) ) ) )).

thf('95',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v4_relat_1 @ X17 @ X19 )
      | ~ ( v4_relat_1 @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc5_relat_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v4_relat_1 @ k1_xboole_0 @ X0 )
      | ( v4_relat_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['49','50'])).

thf('98',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['39','45'])).

thf('99',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v4_relat_1 @ X20 @ X21 )
      | ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k1_relat_1 @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    m1_subset_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('103',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('104',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( v1_relat_1 @ ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['49','50'])).

thf('106',plain,(
    v1_relat_1 @ ( k1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k1_relat_1 @ k1_xboole_0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['101','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('109',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k1_relat_1 @ ( k1_relat_1 @ k1_xboole_0 ) )
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['107','110'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('112',plain,(
    ! [X26: $i] :
      ( ( ( k1_relat_1 @ X26 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X26 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('113',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ( ( k2_relat_1 @ ( k1_relat_1 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_relat_1 @ ( k1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('115',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ ( k1_relat_1 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['76'])).

thf('117',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['76'])).

thf('118',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X24 @ X25 ) @ ( k2_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['49','50'])).

thf('123',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('125',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['76'])).

thf('126',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['76'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['123','127'])).

thf('129',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['35','37','78','79','80','81','82'])).

thf('130',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['52','77'])).

thf('131',plain,(
    $false ),
    inference(demod,[status(thm)],['4','83','128','129','130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PR8crnLc6d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:14:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.60  % Solved by: fo/fo7.sh
% 0.39/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.60  % done 310 iterations in 0.151s
% 0.39/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.60  % SZS output start Refutation
% 0.39/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.60  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.39/0.60  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.39/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.39/0.60  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.39/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.60  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.39/0.60  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.39/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.60  thf(t64_funct_2, conjecture,
% 0.39/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.60     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.39/0.60         ( m1_subset_1 @
% 0.39/0.60           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.39/0.60       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.39/0.60         ( r1_tarski @
% 0.39/0.60           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.39/0.60           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.39/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.60    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.60        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.39/0.60            ( m1_subset_1 @
% 0.39/0.60              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.39/0.60          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.39/0.60            ( r1_tarski @
% 0.39/0.60              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.39/0.60              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.39/0.60    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.39/0.60  thf('0', plain,
% 0.39/0.60      (~ (r1_tarski @ 
% 0.39/0.60          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.39/0.60          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('1', plain,
% 0.39/0.60      ((m1_subset_1 @ sk_D @ 
% 0.39/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(redefinition_k7_relset_1, axiom,
% 0.39/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.60       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.39/0.60  thf('2', plain,
% 0.39/0.60      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.39/0.60         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.39/0.60          | ((k7_relset_1 @ X33 @ X34 @ X32 @ X35) = (k9_relat_1 @ X32 @ X35)))),
% 0.39/0.60      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.39/0.60  thf('3', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.39/0.60           = (k9_relat_1 @ sk_D @ X0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.60  thf('4', plain,
% 0.39/0.60      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.39/0.60          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.39/0.60      inference('demod', [status(thm)], ['0', '3'])).
% 0.39/0.60  thf(t144_relat_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( v1_relat_1 @ B ) =>
% 0.39/0.60       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.39/0.60  thf('5', plain,
% 0.39/0.60      (![X24 : $i, X25 : $i]:
% 0.39/0.60         ((r1_tarski @ (k9_relat_1 @ X24 @ X25) @ (k2_relat_1 @ X24))
% 0.39/0.60          | ~ (v1_relat_1 @ X24))),
% 0.39/0.60      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.39/0.60  thf('6', plain,
% 0.39/0.60      ((m1_subset_1 @ sk_D @ 
% 0.39/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(cc2_relset_1, axiom,
% 0.39/0.60    (![A:$i,B:$i,C:$i]:
% 0.39/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.60       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.39/0.60  thf('7', plain,
% 0.39/0.60      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.39/0.60         ((v4_relat_1 @ X29 @ X30)
% 0.39/0.60          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.39/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.60  thf('8', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.39/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.60  thf(d18_relat_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( v1_relat_1 @ B ) =>
% 0.39/0.60       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.39/0.60  thf('9', plain,
% 0.39/0.60      (![X20 : $i, X21 : $i]:
% 0.39/0.60         (~ (v4_relat_1 @ X20 @ X21)
% 0.39/0.60          | (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.39/0.60          | ~ (v1_relat_1 @ X20))),
% 0.39/0.60      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.39/0.60  thf('10', plain,
% 0.39/0.60      ((~ (v1_relat_1 @ sk_D)
% 0.39/0.60        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.60  thf('11', plain,
% 0.39/0.60      ((m1_subset_1 @ sk_D @ 
% 0.39/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(cc2_relat_1, axiom,
% 0.39/0.60    (![A:$i]:
% 0.39/0.60     ( ( v1_relat_1 @ A ) =>
% 0.39/0.60       ( ![B:$i]:
% 0.39/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.39/0.60  thf('12', plain,
% 0.39/0.60      (![X15 : $i, X16 : $i]:
% 0.39/0.60         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.39/0.60          | (v1_relat_1 @ X15)
% 0.39/0.60          | ~ (v1_relat_1 @ X16))),
% 0.39/0.60      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.39/0.60  thf('13', plain,
% 0.39/0.60      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.39/0.60        | (v1_relat_1 @ sk_D))),
% 0.39/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.39/0.60  thf(fc6_relat_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.39/0.60  thf('14', plain,
% 0.39/0.60      (![X22 : $i, X23 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X22 @ X23))),
% 0.39/0.60      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.39/0.60  thf('15', plain, ((v1_relat_1 @ sk_D)),
% 0.39/0.60      inference('demod', [status(thm)], ['13', '14'])).
% 0.39/0.60  thf('16', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.39/0.60      inference('demod', [status(thm)], ['10', '15'])).
% 0.39/0.60  thf(l3_zfmisc_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.39/0.60       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.39/0.60  thf('17', plain,
% 0.39/0.60      (![X6 : $i, X7 : $i]:
% 0.39/0.60         (((X7) = (k1_tarski @ X6))
% 0.39/0.60          | ((X7) = (k1_xboole_0))
% 0.39/0.60          | ~ (r1_tarski @ X7 @ (k1_tarski @ X6)))),
% 0.39/0.60      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.39/0.60  thf('18', plain,
% 0.39/0.60      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.39/0.60        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.39/0.60  thf(t14_funct_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.60       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.39/0.60         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.39/0.60  thf('19', plain,
% 0.39/0.60      (![X27 : $i, X28 : $i]:
% 0.39/0.60         (((k1_relat_1 @ X28) != (k1_tarski @ X27))
% 0.39/0.60          | ((k2_relat_1 @ X28) = (k1_tarski @ (k1_funct_1 @ X28 @ X27)))
% 0.39/0.60          | ~ (v1_funct_1 @ X28)
% 0.39/0.60          | ~ (v1_relat_1 @ X28))),
% 0.39/0.60      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.39/0.60  thf('20', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.39/0.60          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.39/0.60          | ~ (v1_relat_1 @ X0)
% 0.39/0.60          | ~ (v1_funct_1 @ X0)
% 0.39/0.60          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.39/0.60      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.60  thf('21', plain,
% 0.39/0.60      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.39/0.60        | ~ (v1_funct_1 @ sk_D)
% 0.39/0.60        | ~ (v1_relat_1 @ sk_D)
% 0.39/0.60        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.39/0.60      inference('eq_res', [status(thm)], ['20'])).
% 0.39/0.60  thf('22', plain, ((v1_funct_1 @ sk_D)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('23', plain, ((v1_relat_1 @ sk_D)),
% 0.39/0.60      inference('demod', [status(thm)], ['13', '14'])).
% 0.39/0.60  thf('24', plain,
% 0.39/0.60      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.39/0.60        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.39/0.60      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.39/0.60  thf('25', plain,
% 0.39/0.60      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.39/0.60          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.39/0.60      inference('demod', [status(thm)], ['0', '3'])).
% 0.39/0.60  thf('26', plain,
% 0.39/0.60      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.39/0.60        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.60  thf('27', plain,
% 0.39/0.60      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['5', '26'])).
% 0.39/0.60  thf('28', plain, ((v1_relat_1 @ sk_D)),
% 0.39/0.60      inference('demod', [status(thm)], ['13', '14'])).
% 0.39/0.60  thf('29', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['27', '28'])).
% 0.39/0.60  thf(t3_funct_2, axiom,
% 0.39/0.60    (![A:$i]:
% 0.39/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.60       ( ( v1_funct_1 @ A ) & 
% 0.39/0.60         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.39/0.60         ( m1_subset_1 @
% 0.39/0.60           A @ 
% 0.39/0.60           ( k1_zfmisc_1 @
% 0.39/0.60             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.39/0.60  thf('30', plain,
% 0.39/0.60      (![X36 : $i]:
% 0.39/0.60         ((m1_subset_1 @ X36 @ 
% 0.39/0.60           (k1_zfmisc_1 @ 
% 0.39/0.60            (k2_zfmisc_1 @ (k1_relat_1 @ X36) @ (k2_relat_1 @ X36))))
% 0.39/0.60          | ~ (v1_funct_1 @ X36)
% 0.39/0.60          | ~ (v1_relat_1 @ X36))),
% 0.39/0.60      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.39/0.60  thf(t3_subset, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.60  thf('31', plain,
% 0.39/0.60      (![X12 : $i, X13 : $i]:
% 0.39/0.60         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.39/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.60  thf('32', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (~ (v1_relat_1 @ X0)
% 0.39/0.60          | ~ (v1_funct_1 @ X0)
% 0.39/0.60          | (r1_tarski @ X0 @ 
% 0.39/0.60             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.39/0.60      inference('sup-', [status(thm)], ['30', '31'])).
% 0.39/0.60  thf(d10_xboole_0, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.60  thf('33', plain,
% 0.39/0.60      (![X0 : $i, X2 : $i]:
% 0.39/0.60         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.39/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.60  thf('34', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (~ (v1_funct_1 @ X0)
% 0.39/0.60          | ~ (v1_relat_1 @ X0)
% 0.39/0.60          | ~ (r1_tarski @ 
% 0.39/0.60               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ X0)
% 0.39/0.60          | ((k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) = (X0)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['32', '33'])).
% 0.39/0.60  thf('35', plain,
% 0.39/0.60      ((~ (r1_tarski @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_relat_1 @ sk_D)) @ sk_D)
% 0.39/0.60        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D)) = (sk_D))
% 0.39/0.60        | ~ (v1_relat_1 @ sk_D)
% 0.39/0.60        | ~ (v1_funct_1 @ sk_D))),
% 0.39/0.60      inference('sup-', [status(thm)], ['29', '34'])).
% 0.39/0.60  thf(t113_zfmisc_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.39/0.60       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.39/0.60  thf('36', plain,
% 0.39/0.60      (![X10 : $i, X11 : $i]:
% 0.39/0.60         (((k2_zfmisc_1 @ X10 @ X11) = (k1_xboole_0))
% 0.39/0.60          | ((X10) != (k1_xboole_0)))),
% 0.39/0.60      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.39/0.60  thf('37', plain,
% 0.39/0.60      (![X11 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['36'])).
% 0.39/0.60  thf('38', plain,
% 0.39/0.60      (![X10 : $i, X11 : $i]:
% 0.39/0.60         (((k2_zfmisc_1 @ X10 @ X11) = (k1_xboole_0))
% 0.39/0.60          | ((X11) != (k1_xboole_0)))),
% 0.39/0.60      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.39/0.60  thf('39', plain,
% 0.39/0.60      (![X10 : $i]: ((k2_zfmisc_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['38'])).
% 0.39/0.60  thf('40', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.39/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.60  thf('41', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.39/0.60      inference('simplify', [status(thm)], ['40'])).
% 0.39/0.60  thf('42', plain,
% 0.39/0.60      (![X12 : $i, X14 : $i]:
% 0.39/0.60         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.39/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.60  thf('43', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['41', '42'])).
% 0.39/0.60  thf('44', plain,
% 0.39/0.60      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.39/0.60         ((v4_relat_1 @ X29 @ X30)
% 0.39/0.60          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.39/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.60  thf('45', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]: (v4_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X1)),
% 0.39/0.60      inference('sup-', [status(thm)], ['43', '44'])).
% 0.39/0.60  thf('46', plain, (![X0 : $i]: (v4_relat_1 @ k1_xboole_0 @ X0)),
% 0.39/0.60      inference('sup+', [status(thm)], ['39', '45'])).
% 0.39/0.60  thf('47', plain,
% 0.39/0.60      (![X20 : $i, X21 : $i]:
% 0.39/0.60         (~ (v4_relat_1 @ X20 @ X21)
% 0.39/0.60          | (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.39/0.60          | ~ (v1_relat_1 @ X20))),
% 0.39/0.60      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.39/0.60  thf('48', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (~ (v1_relat_1 @ k1_xboole_0)
% 0.39/0.60          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['46', '47'])).
% 0.39/0.60  thf('49', plain,
% 0.39/0.60      (![X11 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['36'])).
% 0.39/0.60  thf('50', plain,
% 0.39/0.60      (![X22 : $i, X23 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X22 @ X23))),
% 0.39/0.60      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.39/0.60  thf('51', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.39/0.60      inference('sup+', [status(thm)], ['49', '50'])).
% 0.39/0.60  thf('52', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.39/0.60      inference('demod', [status(thm)], ['48', '51'])).
% 0.39/0.60  thf('53', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.39/0.60      inference('demod', [status(thm)], ['48', '51'])).
% 0.39/0.60  thf('54', plain,
% 0.39/0.60      (![X6 : $i, X7 : $i]:
% 0.39/0.60         (((X7) = (k1_tarski @ X6))
% 0.39/0.60          | ((X7) = (k1_xboole_0))
% 0.39/0.60          | ~ (r1_tarski @ X7 @ (k1_tarski @ X6)))),
% 0.39/0.60      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.39/0.60  thf('55', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.39/0.60          | ((k1_relat_1 @ k1_xboole_0) = (k1_tarski @ X0)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['53', '54'])).
% 0.39/0.60  thf('56', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.39/0.60          | ((k1_relat_1 @ k1_xboole_0) = (k1_tarski @ X0)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['53', '54'])).
% 0.39/0.60  thf('57', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.39/0.60      inference('demod', [status(thm)], ['10', '15'])).
% 0.39/0.60  thf('58', plain,
% 0.39/0.60      (![X0 : $i, X2 : $i]:
% 0.39/0.60         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.39/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.60  thf('59', plain,
% 0.39/0.60      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_D))
% 0.39/0.60        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['57', '58'])).
% 0.39/0.60  thf('60', plain,
% 0.39/0.60      ((~ (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ (k1_relat_1 @ sk_D))
% 0.39/0.60        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.39/0.60        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['56', '59'])).
% 0.39/0.60  thf('61', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.39/0.60      inference('demod', [status(thm)], ['48', '51'])).
% 0.39/0.60  thf('62', plain,
% 0.39/0.60      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.39/0.60        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D)))),
% 0.39/0.60      inference('demod', [status(thm)], ['60', '61'])).
% 0.39/0.60  thf('63', plain,
% 0.39/0.60      ((((k1_relat_1 @ k1_xboole_0) = (k1_relat_1 @ sk_D))
% 0.39/0.60        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.39/0.60        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['55', '62'])).
% 0.39/0.60  thf('64', plain,
% 0.39/0.60      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.39/0.60        | ((k1_relat_1 @ k1_xboole_0) = (k1_relat_1 @ sk_D)))),
% 0.39/0.60      inference('simplify', [status(thm)], ['63'])).
% 0.39/0.60  thf('65', plain,
% 0.39/0.60      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.39/0.60        | ((k1_relat_1 @ k1_xboole_0) = (k1_relat_1 @ sk_D)))),
% 0.39/0.60      inference('simplify', [status(thm)], ['63'])).
% 0.39/0.60  thf('66', plain,
% 0.39/0.60      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.39/0.60        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.39/0.60  thf('67', plain,
% 0.39/0.60      (![X7 : $i, X8 : $i]:
% 0.39/0.60         ((r1_tarski @ X7 @ (k1_tarski @ X8)) | ((X7) != (k1_xboole_0)))),
% 0.39/0.60      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.39/0.60  thf('68', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X8))),
% 0.39/0.60      inference('simplify', [status(thm)], ['67'])).
% 0.39/0.60  thf('69', plain,
% 0.39/0.60      (((r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ sk_D))
% 0.39/0.60        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['66', '68'])).
% 0.39/0.60  thf('70', plain,
% 0.39/0.60      (![X0 : $i, X2 : $i]:
% 0.39/0.60         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.39/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.60  thf('71', plain,
% 0.39/0.60      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.39/0.60        | ~ (r1_tarski @ (k1_relat_1 @ sk_D) @ k1_xboole_0)
% 0.39/0.60        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['69', '70'])).
% 0.39/0.60  thf('72', plain,
% 0.39/0.60      ((~ (r1_tarski @ (k1_relat_1 @ sk_D) @ k1_xboole_0)
% 0.39/0.60        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.39/0.60      inference('simplify', [status(thm)], ['71'])).
% 0.39/0.60  thf('73', plain,
% 0.39/0.60      ((~ (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)
% 0.39/0.60        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.39/0.60        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['65', '72'])).
% 0.39/0.60  thf('74', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.39/0.60      inference('demod', [status(thm)], ['48', '51'])).
% 0.39/0.60  thf('75', plain,
% 0.39/0.60      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.39/0.60        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.39/0.60      inference('demod', [status(thm)], ['73', '74'])).
% 0.39/0.60  thf('76', plain,
% 0.39/0.60      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.39/0.60        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.39/0.60        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['64', '75'])).
% 0.39/0.60  thf('77', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['76'])).
% 0.39/0.60  thf('78', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.39/0.60      inference('demod', [status(thm)], ['52', '77'])).
% 0.39/0.60  thf('79', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['27', '28'])).
% 0.39/0.60  thf('80', plain,
% 0.39/0.60      (![X11 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['36'])).
% 0.39/0.60  thf('81', plain, ((v1_relat_1 @ sk_D)),
% 0.39/0.60      inference('demod', [status(thm)], ['13', '14'])).
% 0.39/0.60  thf('82', plain, ((v1_funct_1 @ sk_D)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('83', plain, (((k1_xboole_0) = (sk_D))),
% 0.39/0.60      inference('demod', [status(thm)],
% 0.39/0.60                ['35', '37', '78', '79', '80', '81', '82'])).
% 0.39/0.60  thf('84', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['41', '42'])).
% 0.39/0.60  thf('85', plain,
% 0.39/0.60      (![X11 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['36'])).
% 0.39/0.60  thf('86', plain,
% 0.39/0.60      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.39/0.60         ((v4_relat_1 @ X29 @ X30)
% 0.39/0.60          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.39/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.60  thf('87', plain,
% 0.39/0.60      (![X1 : $i]:
% 0.39/0.60         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.39/0.60          | (v4_relat_1 @ X1 @ k1_xboole_0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['85', '86'])).
% 0.39/0.60  thf('88', plain, ((v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.39/0.60      inference('sup-', [status(thm)], ['84', '87'])).
% 0.39/0.60  thf('89', plain,
% 0.39/0.60      (![X20 : $i, X21 : $i]:
% 0.39/0.60         (~ (v4_relat_1 @ X20 @ X21)
% 0.39/0.60          | (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.39/0.60          | ~ (v1_relat_1 @ X20))),
% 0.39/0.60      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.39/0.60  thf('90', plain,
% 0.39/0.60      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.39/0.60        | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['88', '89'])).
% 0.39/0.60  thf('91', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.39/0.60      inference('sup+', [status(thm)], ['49', '50'])).
% 0.39/0.60  thf('92', plain, ((r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.39/0.60      inference('demod', [status(thm)], ['90', '91'])).
% 0.39/0.60  thf('93', plain,
% 0.39/0.60      (![X12 : $i, X14 : $i]:
% 0.39/0.60         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.39/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.60  thf('94', plain,
% 0.39/0.60      ((m1_subset_1 @ (k1_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['92', '93'])).
% 0.39/0.60  thf(cc5_relat_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.39/0.60       ( ![C:$i]:
% 0.39/0.60         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) ) => ( v4_relat_1 @ C @ A ) ) ) ))).
% 0.39/0.60  thf('95', plain,
% 0.39/0.60      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.39/0.60         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.39/0.60          | (v4_relat_1 @ X17 @ X19)
% 0.39/0.60          | ~ (v4_relat_1 @ X18 @ X19)
% 0.39/0.60          | ~ (v1_relat_1 @ X18))),
% 0.39/0.60      inference('cnf', [status(esa)], [cc5_relat_1])).
% 0.39/0.60  thf('96', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (~ (v1_relat_1 @ k1_xboole_0)
% 0.39/0.60          | ~ (v4_relat_1 @ k1_xboole_0 @ X0)
% 0.39/0.60          | (v4_relat_1 @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['94', '95'])).
% 0.39/0.60  thf('97', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.39/0.60      inference('sup+', [status(thm)], ['49', '50'])).
% 0.39/0.60  thf('98', plain, (![X0 : $i]: (v4_relat_1 @ k1_xboole_0 @ X0)),
% 0.39/0.60      inference('sup+', [status(thm)], ['39', '45'])).
% 0.39/0.60  thf('99', plain,
% 0.39/0.60      (![X0 : $i]: (v4_relat_1 @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.39/0.60      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.39/0.60  thf('100', plain,
% 0.39/0.60      (![X20 : $i, X21 : $i]:
% 0.39/0.60         (~ (v4_relat_1 @ X20 @ X21)
% 0.39/0.60          | (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.39/0.60          | ~ (v1_relat_1 @ X20))),
% 0.39/0.60      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.39/0.60  thf('101', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (~ (v1_relat_1 @ (k1_relat_1 @ k1_xboole_0))
% 0.39/0.60          | (r1_tarski @ (k1_relat_1 @ (k1_relat_1 @ k1_xboole_0)) @ X0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['99', '100'])).
% 0.39/0.60  thf('102', plain,
% 0.39/0.60      ((m1_subset_1 @ (k1_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['92', '93'])).
% 0.39/0.60  thf('103', plain,
% 0.39/0.60      (![X15 : $i, X16 : $i]:
% 0.39/0.60         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.39/0.60          | (v1_relat_1 @ X15)
% 0.39/0.60          | ~ (v1_relat_1 @ X16))),
% 0.39/0.60      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.39/0.60  thf('104', plain,
% 0.39/0.60      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.39/0.60        | (v1_relat_1 @ (k1_relat_1 @ k1_xboole_0)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['102', '103'])).
% 0.39/0.60  thf('105', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.39/0.60      inference('sup+', [status(thm)], ['49', '50'])).
% 0.39/0.60  thf('106', plain, ((v1_relat_1 @ (k1_relat_1 @ k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['104', '105'])).
% 0.39/0.60  thf('107', plain,
% 0.39/0.60      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k1_relat_1 @ k1_xboole_0)) @ X0)),
% 0.39/0.60      inference('demod', [status(thm)], ['101', '106'])).
% 0.39/0.60  thf('108', plain,
% 0.39/0.60      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.39/0.60      inference('demod', [status(thm)], ['48', '51'])).
% 0.39/0.60  thf('109', plain,
% 0.39/0.60      (![X0 : $i, X2 : $i]:
% 0.39/0.60         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.39/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.60  thf('110', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (~ (r1_tarski @ X0 @ (k1_relat_1 @ k1_xboole_0))
% 0.39/0.60          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['108', '109'])).
% 0.39/0.60  thf('111', plain,
% 0.39/0.60      (((k1_relat_1 @ (k1_relat_1 @ k1_xboole_0)) = (k1_relat_1 @ k1_xboole_0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['107', '110'])).
% 0.39/0.60  thf(t65_relat_1, axiom,
% 0.39/0.60    (![A:$i]:
% 0.39/0.60     ( ( v1_relat_1 @ A ) =>
% 0.39/0.60       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.39/0.60         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.39/0.60  thf('112', plain,
% 0.39/0.60      (![X26 : $i]:
% 0.39/0.60         (((k1_relat_1 @ X26) != (k1_xboole_0))
% 0.39/0.60          | ((k2_relat_1 @ X26) = (k1_xboole_0))
% 0.39/0.60          | ~ (v1_relat_1 @ X26))),
% 0.39/0.60      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.39/0.60  thf('113', plain,
% 0.39/0.60      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.39/0.60        | ~ (v1_relat_1 @ (k1_relat_1 @ k1_xboole_0))
% 0.39/0.60        | ((k2_relat_1 @ (k1_relat_1 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['111', '112'])).
% 0.39/0.60  thf('114', plain, ((v1_relat_1 @ (k1_relat_1 @ k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['104', '105'])).
% 0.39/0.60  thf('115', plain,
% 0.39/0.60      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.39/0.60        | ((k2_relat_1 @ (k1_relat_1 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.39/0.60      inference('demod', [status(thm)], ['113', '114'])).
% 0.39/0.60  thf('116', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['76'])).
% 0.39/0.60  thf('117', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['76'])).
% 0.39/0.60  thf('118', plain,
% 0.39/0.60      ((((k1_xboole_0) != (k1_xboole_0))
% 0.39/0.60        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.39/0.60      inference('demod', [status(thm)], ['115', '116', '117'])).
% 0.39/0.60  thf('119', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['118'])).
% 0.39/0.60  thf('120', plain,
% 0.39/0.60      (![X24 : $i, X25 : $i]:
% 0.39/0.60         ((r1_tarski @ (k9_relat_1 @ X24 @ X25) @ (k2_relat_1 @ X24))
% 0.39/0.60          | ~ (v1_relat_1 @ X24))),
% 0.39/0.60      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.39/0.60  thf('121', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         ((r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.39/0.60          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['119', '120'])).
% 0.39/0.60  thf('122', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.39/0.60      inference('sup+', [status(thm)], ['49', '50'])).
% 0.39/0.60  thf('123', plain,
% 0.39/0.60      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)),
% 0.39/0.60      inference('demod', [status(thm)], ['121', '122'])).
% 0.39/0.60  thf('124', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (~ (r1_tarski @ X0 @ (k1_relat_1 @ k1_xboole_0))
% 0.39/0.60          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['108', '109'])).
% 0.39/0.60  thf('125', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['76'])).
% 0.39/0.60  thf('126', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['76'])).
% 0.39/0.60  thf('127', plain,
% 0.39/0.60      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.39/0.60      inference('demod', [status(thm)], ['124', '125', '126'])).
% 0.39/0.60  thf('128', plain,
% 0.39/0.60      (![X0 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['123', '127'])).
% 0.39/0.60  thf('129', plain, (((k1_xboole_0) = (sk_D))),
% 0.39/0.60      inference('demod', [status(thm)],
% 0.39/0.60                ['35', '37', '78', '79', '80', '81', '82'])).
% 0.39/0.60  thf('130', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.39/0.60      inference('demod', [status(thm)], ['52', '77'])).
% 0.39/0.60  thf('131', plain, ($false),
% 0.39/0.60      inference('demod', [status(thm)], ['4', '83', '128', '129', '130'])).
% 0.39/0.60  
% 0.39/0.60  % SZS output end Refutation
% 0.39/0.60  
% 0.39/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
