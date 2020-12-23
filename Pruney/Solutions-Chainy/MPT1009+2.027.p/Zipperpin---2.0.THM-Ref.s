%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1qAr4Muict

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:52 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 334 expanded)
%              Number of leaves         :   36 ( 114 expanded)
%              Depth                    :   16
%              Number of atoms          :  645 (4073 expanded)
%              Number of equality atoms :   61 ( 281 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

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
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k7_relset_1 @ X34 @ X35 @ X33 @ X36 )
        = ( k9_relat_1 @ X33 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('8',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X37 ) @ X38 )
      | ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) @ sk_D )
    | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B )
      = sk_D ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('15',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X22 @ X23 ) @ ( k2_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v4_relat_1 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('18',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('19',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v4_relat_1 @ X20 @ X21 )
      | ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('22',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v1_relat_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('23',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['20','23'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('25',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('26',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X12
        = ( k2_tarski @ X10 @ X11 ) )
      | ( X12
        = ( k1_tarski @ X11 ) )
      | ( X12
        = ( k1_tarski @ X10 ) )
      | ( X12 = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ ( k2_tarski @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k2_tarski @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('31',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('33',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k1_relat_1 @ X26 )
       != ( k1_tarski @ X25 ) )
      | ( ( k2_relat_1 @ X26 )
        = ( k1_tarski @ ( k1_funct_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['34'])).

thf('36',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['21','22'])).

thf('38',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('40',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['21','22'])).

thf('43',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['41','42'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('44',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_zfmisc_1 @ X15 @ X16 )
        = k1_xboole_0 )
      | ( X15 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('45',plain,(
    ! [X16: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('46',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('47',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['41','42'])).

thf('48',plain,(
    ! [X16: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('49',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['14','43','45','46','47','48'])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('50',plain,(
    ! [X24: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X24 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('51',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['14','43','45','46','47','48'])).

thf('52',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['4','49','50','51','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1qAr4Muict
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:28:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.48/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.48/0.68  % Solved by: fo/fo7.sh
% 0.48/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.68  % done 599 iterations in 0.226s
% 0.48/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.48/0.68  % SZS output start Refutation
% 0.48/0.68  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.48/0.68  thf(sk_D_type, type, sk_D: $i).
% 0.48/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.68  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.48/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.48/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.48/0.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.48/0.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.48/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.48/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.48/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.48/0.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.48/0.68  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.48/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.68  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.48/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.48/0.68  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.48/0.68  thf(t64_funct_2, conjecture,
% 0.48/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.68     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.48/0.68         ( m1_subset_1 @
% 0.48/0.68           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.48/0.68       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.48/0.68         ( r1_tarski @
% 0.48/0.68           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.48/0.68           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.48/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.68    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.68        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.48/0.68            ( m1_subset_1 @
% 0.48/0.68              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.48/0.68          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.48/0.68            ( r1_tarski @
% 0.48/0.68              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.48/0.68              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.48/0.68    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.48/0.68  thf('0', plain,
% 0.48/0.68      (~ (r1_tarski @ 
% 0.48/0.68          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.48/0.68          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('1', plain,
% 0.48/0.68      ((m1_subset_1 @ sk_D @ 
% 0.48/0.68        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf(redefinition_k7_relset_1, axiom,
% 0.48/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.68       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.48/0.68  thf('2', plain,
% 0.48/0.68      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.48/0.68          | ((k7_relset_1 @ X34 @ X35 @ X33 @ X36) = (k9_relat_1 @ X33 @ X36)))),
% 0.48/0.68      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.48/0.68  thf('3', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.48/0.68           = (k9_relat_1 @ sk_D @ X0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.48/0.68  thf('4', plain,
% 0.48/0.68      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.48/0.68          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.48/0.68      inference('demod', [status(thm)], ['0', '3'])).
% 0.48/0.68  thf(d10_xboole_0, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.48/0.68  thf('5', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.48/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.48/0.68  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.48/0.68      inference('simplify', [status(thm)], ['5'])).
% 0.48/0.68  thf('7', plain,
% 0.48/0.68      ((m1_subset_1 @ sk_D @ 
% 0.48/0.68        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf(t13_relset_1, axiom,
% 0.48/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.68     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.48/0.68       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.48/0.68         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.48/0.68  thf('8', plain,
% 0.48/0.68      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.48/0.68         (~ (r1_tarski @ (k1_relat_1 @ X37) @ X38)
% 0.48/0.68          | (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.48/0.68          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39))))),
% 0.48/0.68      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.48/0.68  thf('9', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.48/0.68          | ~ (r1_tarski @ (k1_relat_1 @ sk_D) @ X0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['7', '8'])).
% 0.48/0.68  thf('10', plain,
% 0.48/0.68      ((m1_subset_1 @ sk_D @ 
% 0.48/0.68        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['6', '9'])).
% 0.48/0.68  thf(t3_subset, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.48/0.68  thf('11', plain,
% 0.48/0.68      (![X17 : $i, X18 : $i]:
% 0.48/0.68         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.48/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.68  thf('12', plain,
% 0.48/0.68      ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B))),
% 0.48/0.68      inference('sup-', [status(thm)], ['10', '11'])).
% 0.48/0.68  thf('13', plain,
% 0.48/0.68      (![X0 : $i, X2 : $i]:
% 0.48/0.68         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.48/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.48/0.68  thf('14', plain,
% 0.48/0.68      ((~ (r1_tarski @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B) @ sk_D)
% 0.48/0.68        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B) = (sk_D)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['12', '13'])).
% 0.48/0.68  thf(t144_relat_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( v1_relat_1 @ B ) =>
% 0.48/0.68       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.48/0.68  thf('15', plain,
% 0.48/0.68      (![X22 : $i, X23 : $i]:
% 0.48/0.68         ((r1_tarski @ (k9_relat_1 @ X22 @ X23) @ (k2_relat_1 @ X22))
% 0.48/0.68          | ~ (v1_relat_1 @ X22))),
% 0.48/0.68      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.48/0.68  thf('16', plain,
% 0.48/0.68      ((m1_subset_1 @ sk_D @ 
% 0.48/0.68        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf(cc2_relset_1, axiom,
% 0.48/0.68    (![A:$i,B:$i,C:$i]:
% 0.48/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.68       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.48/0.68  thf('17', plain,
% 0.48/0.68      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.48/0.68         ((v4_relat_1 @ X30 @ X31)
% 0.48/0.68          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.48/0.68      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.48/0.68  thf('18', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.48/0.68      inference('sup-', [status(thm)], ['16', '17'])).
% 0.48/0.68  thf(d18_relat_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( v1_relat_1 @ B ) =>
% 0.48/0.68       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.48/0.68  thf('19', plain,
% 0.48/0.68      (![X20 : $i, X21 : $i]:
% 0.48/0.68         (~ (v4_relat_1 @ X20 @ X21)
% 0.48/0.68          | (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.48/0.68          | ~ (v1_relat_1 @ X20))),
% 0.48/0.68      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.48/0.68  thf('20', plain,
% 0.48/0.68      ((~ (v1_relat_1 @ sk_D)
% 0.48/0.68        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['18', '19'])).
% 0.48/0.68  thf('21', plain,
% 0.48/0.68      ((m1_subset_1 @ sk_D @ 
% 0.48/0.68        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf(cc1_relset_1, axiom,
% 0.48/0.68    (![A:$i,B:$i,C:$i]:
% 0.48/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.68       ( v1_relat_1 @ C ) ))).
% 0.48/0.68  thf('22', plain,
% 0.48/0.68      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.48/0.68         ((v1_relat_1 @ X27)
% 0.48/0.68          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.48/0.68      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.48/0.68  thf('23', plain, ((v1_relat_1 @ sk_D)),
% 0.48/0.68      inference('sup-', [status(thm)], ['21', '22'])).
% 0.48/0.68  thf('24', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.48/0.68      inference('demod', [status(thm)], ['20', '23'])).
% 0.48/0.68  thf(t69_enumset1, axiom,
% 0.48/0.68    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.48/0.68  thf('25', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.48/0.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.48/0.68  thf(l45_zfmisc_1, axiom,
% 0.48/0.68    (![A:$i,B:$i,C:$i]:
% 0.48/0.68     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.48/0.68       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.48/0.68            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.48/0.68  thf('26', plain,
% 0.48/0.68      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.48/0.68         (((X12) = (k2_tarski @ X10 @ X11))
% 0.48/0.68          | ((X12) = (k1_tarski @ X11))
% 0.48/0.68          | ((X12) = (k1_tarski @ X10))
% 0.48/0.68          | ((X12) = (k1_xboole_0))
% 0.48/0.68          | ~ (r1_tarski @ X12 @ (k2_tarski @ X10 @ X11)))),
% 0.48/0.68      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.48/0.68  thf('27', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.48/0.68          | ((X1) = (k1_xboole_0))
% 0.48/0.68          | ((X1) = (k1_tarski @ X0))
% 0.48/0.68          | ((X1) = (k1_tarski @ X0))
% 0.48/0.68          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['25', '26'])).
% 0.48/0.68  thf('28', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (((X1) = (k2_tarski @ X0 @ X0))
% 0.48/0.68          | ((X1) = (k1_tarski @ X0))
% 0.48/0.68          | ((X1) = (k1_xboole_0))
% 0.48/0.68          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.48/0.68      inference('simplify', [status(thm)], ['27'])).
% 0.48/0.68  thf('29', plain,
% 0.48/0.68      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.48/0.68        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.48/0.68        | ((k1_relat_1 @ sk_D) = (k2_tarski @ sk_A @ sk_A)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['24', '28'])).
% 0.48/0.68  thf('30', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.48/0.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.48/0.68  thf('31', plain,
% 0.48/0.68      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.48/0.68        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.48/0.68        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.48/0.68      inference('demod', [status(thm)], ['29', '30'])).
% 0.48/0.68  thf('32', plain,
% 0.48/0.68      ((((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.48/0.68        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.48/0.68      inference('simplify', [status(thm)], ['31'])).
% 0.48/0.68  thf(t14_funct_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.48/0.68       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.48/0.68         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.48/0.68  thf('33', plain,
% 0.48/0.68      (![X25 : $i, X26 : $i]:
% 0.48/0.68         (((k1_relat_1 @ X26) != (k1_tarski @ X25))
% 0.48/0.68          | ((k2_relat_1 @ X26) = (k1_tarski @ (k1_funct_1 @ X26 @ X25)))
% 0.48/0.68          | ~ (v1_funct_1 @ X26)
% 0.48/0.68          | ~ (v1_relat_1 @ X26))),
% 0.48/0.68      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.48/0.68  thf('34', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.48/0.68          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.48/0.68          | ~ (v1_relat_1 @ X0)
% 0.48/0.68          | ~ (v1_funct_1 @ X0)
% 0.48/0.68          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['32', '33'])).
% 0.48/0.68  thf('35', plain,
% 0.48/0.68      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.48/0.68        | ~ (v1_funct_1 @ sk_D)
% 0.48/0.68        | ~ (v1_relat_1 @ sk_D)
% 0.48/0.68        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.48/0.68      inference('eq_res', [status(thm)], ['34'])).
% 0.48/0.68  thf('36', plain, ((v1_funct_1 @ sk_D)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('37', plain, ((v1_relat_1 @ sk_D)),
% 0.48/0.68      inference('sup-', [status(thm)], ['21', '22'])).
% 0.48/0.68  thf('38', plain,
% 0.48/0.68      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.48/0.68        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.48/0.68      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.48/0.68  thf('39', plain,
% 0.48/0.68      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.48/0.68          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.48/0.68      inference('demod', [status(thm)], ['0', '3'])).
% 0.48/0.68  thf('40', plain,
% 0.48/0.68      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.48/0.68        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['38', '39'])).
% 0.48/0.68  thf('41', plain,
% 0.48/0.68      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['15', '40'])).
% 0.48/0.68  thf('42', plain, ((v1_relat_1 @ sk_D)),
% 0.48/0.68      inference('sup-', [status(thm)], ['21', '22'])).
% 0.48/0.68  thf('43', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.48/0.68      inference('demod', [status(thm)], ['41', '42'])).
% 0.48/0.68  thf(t113_zfmisc_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.48/0.68       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.48/0.68  thf('44', plain,
% 0.48/0.68      (![X15 : $i, X16 : $i]:
% 0.48/0.68         (((k2_zfmisc_1 @ X15 @ X16) = (k1_xboole_0))
% 0.48/0.68          | ((X15) != (k1_xboole_0)))),
% 0.48/0.68      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.48/0.68  thf('45', plain,
% 0.48/0.68      (![X16 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 0.48/0.68      inference('simplify', [status(thm)], ['44'])).
% 0.48/0.68  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.48/0.68  thf('46', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.48/0.68      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.48/0.68  thf('47', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.48/0.68      inference('demod', [status(thm)], ['41', '42'])).
% 0.48/0.68  thf('48', plain,
% 0.48/0.68      (![X16 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 0.48/0.68      inference('simplify', [status(thm)], ['44'])).
% 0.48/0.68  thf('49', plain, (((k1_xboole_0) = (sk_D))),
% 0.48/0.68      inference('demod', [status(thm)], ['14', '43', '45', '46', '47', '48'])).
% 0.48/0.68  thf(t150_relat_1, axiom,
% 0.48/0.68    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.48/0.68  thf('50', plain,
% 0.48/0.68      (![X24 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X24) = (k1_xboole_0))),
% 0.48/0.68      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.48/0.68  thf('51', plain, (((k1_xboole_0) = (sk_D))),
% 0.48/0.68      inference('demod', [status(thm)], ['14', '43', '45', '46', '47', '48'])).
% 0.48/0.68  thf('52', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.48/0.68      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.48/0.68  thf('53', plain, ($false),
% 0.48/0.68      inference('demod', [status(thm)], ['4', '49', '50', '51', '52'])).
% 0.48/0.68  
% 0.48/0.68  % SZS output end Refutation
% 0.48/0.68  
% 0.48/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
