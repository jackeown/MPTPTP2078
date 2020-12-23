%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pCndvjJ2by

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:49 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 129 expanded)
%              Number of leaves         :   39 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :  675 (1275 expanded)
%              Number of equality atoms :   54 (  76 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['0'])).

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

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('3',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X41 ) @ X42 )
      | ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('6',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X36 ) ) )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X25: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('12',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ~ ( v1_xboole_0 @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('19',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( ( k7_relset_1 @ X38 @ X39 @ X37 @ X40 )
        = ( k9_relat_1 @ X37 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( v1_xboole_0 @ ( k9_relat_1 @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_D ) ) ),
    inference(clc,[status(thm)],['7','24'])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('26',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X23 @ X24 ) @ ( k2_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('28',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v4_relat_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('29',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('30',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v4_relat_1 @ X21 @ X22 )
      | ( r1_tarski @ ( k1_relat_1 @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('33',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('34',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['31','34'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('36',plain,(
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

thf('37',plain,(
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

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k2_tarski @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','39'])).

thf('41',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('42',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('44',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k1_relat_1 @ X27 )
       != ( k1_tarski @ X26 ) )
      | ( ( k2_relat_1 @ X27 )
        = ( k1_tarski @ ( k1_funct_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['45'])).

thf('47',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['32','33'])).

thf('49',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('52',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['32','33'])).

thf('56',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['25','56','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pCndvjJ2by
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:53:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.51/1.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.51/1.72  % Solved by: fo/fo7.sh
% 1.51/1.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.51/1.72  % done 2306 iterations in 1.264s
% 1.51/1.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.51/1.72  % SZS output start Refutation
% 1.51/1.72  thf(sk_C_type, type, sk_C: $i).
% 1.51/1.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.51/1.72  thf(sk_A_type, type, sk_A: $i).
% 1.51/1.72  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.51/1.72  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.51/1.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.51/1.72  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.51/1.72  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.51/1.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.51/1.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.51/1.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.51/1.72  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.51/1.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.51/1.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.51/1.72  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.51/1.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.51/1.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.51/1.72  thf(sk_B_type, type, sk_B: $i).
% 1.51/1.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.51/1.72  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.51/1.72  thf(sk_D_type, type, sk_D: $i).
% 1.51/1.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.51/1.72  thf(d10_xboole_0, axiom,
% 1.51/1.72    (![A:$i,B:$i]:
% 1.51/1.72     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.51/1.72  thf('0', plain,
% 1.51/1.72      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 1.51/1.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.51/1.72  thf('1', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 1.51/1.72      inference('simplify', [status(thm)], ['0'])).
% 1.51/1.72  thf(t64_funct_2, conjecture,
% 1.51/1.72    (![A:$i,B:$i,C:$i,D:$i]:
% 1.51/1.72     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 1.51/1.72         ( m1_subset_1 @
% 1.51/1.72           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 1.51/1.72       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.51/1.72         ( r1_tarski @
% 1.51/1.72           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 1.51/1.72           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 1.51/1.72  thf(zf_stmt_0, negated_conjecture,
% 1.51/1.72    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.51/1.72        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 1.51/1.72            ( m1_subset_1 @
% 1.51/1.72              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 1.51/1.72          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.51/1.72            ( r1_tarski @
% 1.51/1.72              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 1.51/1.72              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 1.51/1.72    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 1.51/1.72  thf('2', plain,
% 1.51/1.72      ((m1_subset_1 @ sk_D @ 
% 1.51/1.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf(t13_relset_1, axiom,
% 1.51/1.72    (![A:$i,B:$i,C:$i,D:$i]:
% 1.51/1.72     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 1.51/1.72       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 1.51/1.72         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 1.51/1.72  thf('3', plain,
% 1.51/1.72      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 1.51/1.72         (~ (r1_tarski @ (k1_relat_1 @ X41) @ X42)
% 1.51/1.72          | (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 1.51/1.72          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43))))),
% 1.51/1.72      inference('cnf', [status(esa)], [t13_relset_1])).
% 1.51/1.72  thf('4', plain,
% 1.51/1.72      (![X0 : $i]:
% 1.51/1.72         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 1.51/1.72          | ~ (r1_tarski @ (k1_relat_1 @ sk_D) @ X0))),
% 1.51/1.72      inference('sup-', [status(thm)], ['2', '3'])).
% 1.51/1.72  thf('5', plain,
% 1.51/1.72      ((m1_subset_1 @ sk_D @ 
% 1.51/1.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 1.51/1.72      inference('sup-', [status(thm)], ['1', '4'])).
% 1.51/1.72  thf(cc3_relset_1, axiom,
% 1.51/1.72    (![A:$i,B:$i]:
% 1.51/1.72     ( ( v1_xboole_0 @ A ) =>
% 1.51/1.72       ( ![C:$i]:
% 1.51/1.72         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.72           ( v1_xboole_0 @ C ) ) ) ))).
% 1.51/1.72  thf('6', plain,
% 1.51/1.72      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.51/1.72         (~ (v1_xboole_0 @ X34)
% 1.51/1.72          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X36)))
% 1.51/1.72          | (v1_xboole_0 @ X35))),
% 1.51/1.72      inference('cnf', [status(esa)], [cc3_relset_1])).
% 1.51/1.72  thf('7', plain,
% 1.51/1.72      (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ (k1_relat_1 @ sk_D)))),
% 1.51/1.72      inference('sup-', [status(thm)], ['5', '6'])).
% 1.51/1.72  thf(l13_xboole_0, axiom,
% 1.51/1.72    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.51/1.72  thf('8', plain,
% 1.51/1.72      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.51/1.72      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.51/1.72  thf(t150_relat_1, axiom,
% 1.51/1.72    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 1.51/1.72  thf('9', plain,
% 1.51/1.72      (![X25 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X25) = (k1_xboole_0))),
% 1.51/1.72      inference('cnf', [status(esa)], [t150_relat_1])).
% 1.51/1.72  thf('10', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i]:
% 1.51/1.72         (((k9_relat_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.51/1.72      inference('sup+', [status(thm)], ['8', '9'])).
% 1.51/1.72  thf('11', plain,
% 1.51/1.72      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.51/1.72      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.51/1.72  thf(t4_subset_1, axiom,
% 1.51/1.72    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.51/1.72  thf('12', plain,
% 1.51/1.72      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 1.51/1.72      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.51/1.72  thf('13', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i]:
% 1.51/1.72         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 1.51/1.72      inference('sup+', [status(thm)], ['11', '12'])).
% 1.51/1.72  thf(t3_subset, axiom,
% 1.51/1.72    (![A:$i,B:$i]:
% 1.51/1.72     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.51/1.72  thf('14', plain,
% 1.51/1.72      (![X15 : $i, X16 : $i]:
% 1.51/1.72         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 1.51/1.72      inference('cnf', [status(esa)], [t3_subset])).
% 1.51/1.72  thf('15', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X1) | (r1_tarski @ X1 @ X0))),
% 1.51/1.72      inference('sup-', [status(thm)], ['13', '14'])).
% 1.51/1.72  thf('16', plain,
% 1.51/1.72      (~ (r1_tarski @ 
% 1.51/1.72          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 1.51/1.72          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('17', plain,
% 1.51/1.72      (~ (v1_xboole_0 @ (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C))),
% 1.51/1.72      inference('sup-', [status(thm)], ['15', '16'])).
% 1.51/1.72  thf('18', plain,
% 1.51/1.72      ((m1_subset_1 @ sk_D @ 
% 1.51/1.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf(redefinition_k7_relset_1, axiom,
% 1.51/1.72    (![A:$i,B:$i,C:$i,D:$i]:
% 1.51/1.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.72       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 1.51/1.72  thf('19', plain,
% 1.51/1.72      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.51/1.72         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 1.51/1.72          | ((k7_relset_1 @ X38 @ X39 @ X37 @ X40) = (k9_relat_1 @ X37 @ X40)))),
% 1.51/1.72      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.51/1.72  thf('20', plain,
% 1.51/1.72      (![X0 : $i]:
% 1.51/1.72         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 1.51/1.72           = (k9_relat_1 @ sk_D @ X0))),
% 1.51/1.72      inference('sup-', [status(thm)], ['18', '19'])).
% 1.51/1.72  thf('21', plain, (~ (v1_xboole_0 @ (k9_relat_1 @ sk_D @ sk_C))),
% 1.51/1.72      inference('demod', [status(thm)], ['17', '20'])).
% 1.51/1.72  thf('22', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_D))),
% 1.51/1.72      inference('sup-', [status(thm)], ['10', '21'])).
% 1.51/1.72  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.51/1.72  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.51/1.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.51/1.72  thf('24', plain, (~ (v1_xboole_0 @ sk_D)),
% 1.51/1.72      inference('demod', [status(thm)], ['22', '23'])).
% 1.51/1.72  thf('25', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_D))),
% 1.51/1.72      inference('clc', [status(thm)], ['7', '24'])).
% 1.51/1.72  thf(t144_relat_1, axiom,
% 1.51/1.72    (![A:$i,B:$i]:
% 1.51/1.72     ( ( v1_relat_1 @ B ) =>
% 1.51/1.72       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 1.51/1.72  thf('26', plain,
% 1.51/1.72      (![X23 : $i, X24 : $i]:
% 1.51/1.72         ((r1_tarski @ (k9_relat_1 @ X23 @ X24) @ (k2_relat_1 @ X23))
% 1.51/1.72          | ~ (v1_relat_1 @ X23))),
% 1.51/1.72      inference('cnf', [status(esa)], [t144_relat_1])).
% 1.51/1.72  thf('27', plain,
% 1.51/1.72      ((m1_subset_1 @ sk_D @ 
% 1.51/1.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf(cc2_relset_1, axiom,
% 1.51/1.72    (![A:$i,B:$i,C:$i]:
% 1.51/1.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.72       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.51/1.72  thf('28', plain,
% 1.51/1.72      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.51/1.72         ((v4_relat_1 @ X31 @ X32)
% 1.51/1.72          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 1.51/1.72      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.51/1.72  thf('29', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 1.51/1.72      inference('sup-', [status(thm)], ['27', '28'])).
% 1.51/1.72  thf(d18_relat_1, axiom,
% 1.51/1.72    (![A:$i,B:$i]:
% 1.51/1.72     ( ( v1_relat_1 @ B ) =>
% 1.51/1.72       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.51/1.72  thf('30', plain,
% 1.51/1.72      (![X21 : $i, X22 : $i]:
% 1.51/1.72         (~ (v4_relat_1 @ X21 @ X22)
% 1.51/1.72          | (r1_tarski @ (k1_relat_1 @ X21) @ X22)
% 1.51/1.72          | ~ (v1_relat_1 @ X21))),
% 1.51/1.72      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.51/1.72  thf('31', plain,
% 1.51/1.72      ((~ (v1_relat_1 @ sk_D)
% 1.51/1.72        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 1.51/1.72      inference('sup-', [status(thm)], ['29', '30'])).
% 1.51/1.72  thf('32', plain,
% 1.51/1.72      ((m1_subset_1 @ sk_D @ 
% 1.51/1.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf(cc1_relset_1, axiom,
% 1.51/1.72    (![A:$i,B:$i,C:$i]:
% 1.51/1.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.72       ( v1_relat_1 @ C ) ))).
% 1.51/1.72  thf('33', plain,
% 1.51/1.72      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.51/1.72         ((v1_relat_1 @ X28)
% 1.51/1.72          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.51/1.72      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.51/1.72  thf('34', plain, ((v1_relat_1 @ sk_D)),
% 1.51/1.72      inference('sup-', [status(thm)], ['32', '33'])).
% 1.51/1.72  thf('35', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 1.51/1.72      inference('demod', [status(thm)], ['31', '34'])).
% 1.51/1.72  thf(t69_enumset1, axiom,
% 1.51/1.72    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.51/1.72  thf('36', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 1.51/1.72      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.51/1.72  thf(l45_zfmisc_1, axiom,
% 1.51/1.72    (![A:$i,B:$i,C:$i]:
% 1.51/1.72     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 1.51/1.72       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 1.51/1.72            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 1.51/1.72  thf('37', plain,
% 1.51/1.72      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.51/1.72         (((X12) = (k2_tarski @ X10 @ X11))
% 1.51/1.72          | ((X12) = (k1_tarski @ X11))
% 1.51/1.72          | ((X12) = (k1_tarski @ X10))
% 1.51/1.72          | ((X12) = (k1_xboole_0))
% 1.51/1.72          | ~ (r1_tarski @ X12 @ (k2_tarski @ X10 @ X11)))),
% 1.51/1.72      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 1.51/1.72  thf('38', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i]:
% 1.51/1.72         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 1.51/1.72          | ((X1) = (k1_xboole_0))
% 1.51/1.72          | ((X1) = (k1_tarski @ X0))
% 1.51/1.72          | ((X1) = (k1_tarski @ X0))
% 1.51/1.72          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 1.51/1.72      inference('sup-', [status(thm)], ['36', '37'])).
% 1.51/1.72  thf('39', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i]:
% 1.51/1.72         (((X1) = (k2_tarski @ X0 @ X0))
% 1.51/1.72          | ((X1) = (k1_tarski @ X0))
% 1.51/1.72          | ((X1) = (k1_xboole_0))
% 1.51/1.72          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 1.51/1.72      inference('simplify', [status(thm)], ['38'])).
% 1.51/1.72  thf('40', plain,
% 1.51/1.72      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 1.51/1.72        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 1.51/1.72        | ((k1_relat_1 @ sk_D) = (k2_tarski @ sk_A @ sk_A)))),
% 1.51/1.72      inference('sup-', [status(thm)], ['35', '39'])).
% 1.51/1.72  thf('41', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 1.51/1.72      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.51/1.72  thf('42', plain,
% 1.51/1.72      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 1.51/1.72        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 1.51/1.72        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 1.51/1.72      inference('demod', [status(thm)], ['40', '41'])).
% 1.51/1.72  thf('43', plain,
% 1.51/1.72      ((((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 1.51/1.72        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 1.51/1.72      inference('simplify', [status(thm)], ['42'])).
% 1.51/1.72  thf(t14_funct_1, axiom,
% 1.51/1.72    (![A:$i,B:$i]:
% 1.51/1.72     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.51/1.72       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 1.51/1.72         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 1.51/1.72  thf('44', plain,
% 1.51/1.72      (![X26 : $i, X27 : $i]:
% 1.51/1.72         (((k1_relat_1 @ X27) != (k1_tarski @ X26))
% 1.51/1.72          | ((k2_relat_1 @ X27) = (k1_tarski @ (k1_funct_1 @ X27 @ X26)))
% 1.51/1.72          | ~ (v1_funct_1 @ X27)
% 1.51/1.72          | ~ (v1_relat_1 @ X27))),
% 1.51/1.72      inference('cnf', [status(esa)], [t14_funct_1])).
% 1.51/1.72  thf('45', plain,
% 1.51/1.72      (![X0 : $i]:
% 1.51/1.72         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 1.51/1.72          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 1.51/1.72          | ~ (v1_relat_1 @ X0)
% 1.51/1.72          | ~ (v1_funct_1 @ X0)
% 1.51/1.72          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 1.51/1.72      inference('sup-', [status(thm)], ['43', '44'])).
% 1.51/1.72  thf('46', plain,
% 1.51/1.72      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 1.51/1.72        | ~ (v1_funct_1 @ sk_D)
% 1.51/1.72        | ~ (v1_relat_1 @ sk_D)
% 1.51/1.72        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 1.51/1.72      inference('eq_res', [status(thm)], ['45'])).
% 1.51/1.72  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('48', plain, ((v1_relat_1 @ sk_D)),
% 1.51/1.72      inference('sup-', [status(thm)], ['32', '33'])).
% 1.51/1.72  thf('49', plain,
% 1.51/1.72      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 1.51/1.72        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 1.51/1.72      inference('demod', [status(thm)], ['46', '47', '48'])).
% 1.51/1.72  thf('50', plain,
% 1.51/1.72      (~ (r1_tarski @ 
% 1.51/1.72          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 1.51/1.72          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('51', plain,
% 1.51/1.72      (![X0 : $i]:
% 1.51/1.72         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 1.51/1.72           = (k9_relat_1 @ sk_D @ X0))),
% 1.51/1.72      inference('sup-', [status(thm)], ['18', '19'])).
% 1.51/1.72  thf('52', plain,
% 1.51/1.72      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 1.51/1.72          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 1.51/1.72      inference('demod', [status(thm)], ['50', '51'])).
% 1.51/1.72  thf('53', plain,
% 1.51/1.72      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 1.51/1.72        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 1.51/1.72      inference('sup-', [status(thm)], ['49', '52'])).
% 1.51/1.72  thf('54', plain,
% 1.51/1.72      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 1.51/1.72      inference('sup-', [status(thm)], ['26', '53'])).
% 1.51/1.72  thf('55', plain, ((v1_relat_1 @ sk_D)),
% 1.51/1.72      inference('sup-', [status(thm)], ['32', '33'])).
% 1.51/1.72  thf('56', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 1.51/1.72      inference('demod', [status(thm)], ['54', '55'])).
% 1.51/1.72  thf('57', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.51/1.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.51/1.72  thf('58', plain, ($false),
% 1.51/1.72      inference('demod', [status(thm)], ['25', '56', '57'])).
% 1.51/1.72  
% 1.51/1.72  % SZS output end Refutation
% 1.51/1.72  
% 1.51/1.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
