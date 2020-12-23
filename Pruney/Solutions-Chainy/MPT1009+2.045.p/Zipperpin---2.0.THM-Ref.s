%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2ktu6ftf8m

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:55 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 375 expanded)
%              Number of leaves         :   38 ( 127 expanded)
%              Depth                    :   18
%              Number of atoms          :  679 (4525 expanded)
%              Number of equality atoms :   65 ( 305 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( ( k7_relset_1 @ X40 @ X41 @ X39 @ X42 )
        = ( k9_relat_1 @ X39 @ X42 ) ) ) ),
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
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X43 ) @ X44 )
      | ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X24 @ X25 ) @ ( k2_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( v4_relat_1 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('18',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X27: $i,X28: $i] :
      ( ( X27
        = ( k7_relat_1 @ X27 @ X28 ) )
      | ~ ( v4_relat_1 @ X27 @ X28 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('22',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v1_relat_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('23',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('25',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X29 @ X30 ) ) @ X30 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('26',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['21','22'])).

thf('28',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('29',plain,(
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

thf('30',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X16
        = ( k2_tarski @ X14 @ X15 ) )
      | ( X16
        = ( k1_tarski @ X15 ) )
      | ( X16
        = ( k1_tarski @ X14 ) )
      | ( X16 = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ ( k2_tarski @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k2_tarski @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('34',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('35',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('37',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k1_relat_1 @ X32 )
       != ( k1_tarski @ X31 ) )
      | ( ( k2_relat_1 @ X32 )
        = ( k1_tarski @ ( k1_funct_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['38'])).

thf('40',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['21','22'])).

thf('42',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('44',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['21','22'])).

thf('47',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['45','46'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('48',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_zfmisc_1 @ X19 @ X20 )
        = k1_xboole_0 )
      | ( X19 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('49',plain,(
    ! [X20: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X20 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('50',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['45','46'])).

thf('52',plain,(
    ! [X20: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X20 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('53',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['14','47','49','50','51','52'])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('54',plain,(
    ! [X26: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X26 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('55',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['14','47','49','50','51','52'])).

thf('56',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['4','53','54','55','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2ktu6ftf8m
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:39:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.54/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.72  % Solved by: fo/fo7.sh
% 0.54/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.72  % done 731 iterations in 0.272s
% 0.54/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.72  % SZS output start Refutation
% 0.54/0.72  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.54/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.72  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.54/0.72  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.54/0.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.54/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.72  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.54/0.72  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.54/0.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.54/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.54/0.72  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.54/0.72  thf(sk_D_type, type, sk_D: $i).
% 0.54/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.72  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.72  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.54/0.72  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.54/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.54/0.72  thf(t64_funct_2, conjecture,
% 0.54/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.72     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.54/0.72         ( m1_subset_1 @
% 0.54/0.72           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.54/0.72       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.54/0.72         ( r1_tarski @
% 0.54/0.72           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.54/0.72           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.54/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.72    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.72        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.54/0.72            ( m1_subset_1 @
% 0.54/0.72              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.54/0.72          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.54/0.72            ( r1_tarski @
% 0.54/0.72              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.54/0.72              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.54/0.72    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.54/0.72  thf('0', plain,
% 0.54/0.72      (~ (r1_tarski @ 
% 0.54/0.72          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.54/0.72          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('1', plain,
% 0.54/0.72      ((m1_subset_1 @ sk_D @ 
% 0.54/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf(redefinition_k7_relset_1, axiom,
% 0.54/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.72       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.54/0.72  thf('2', plain,
% 0.54/0.72      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.54/0.72         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.54/0.72          | ((k7_relset_1 @ X40 @ X41 @ X39 @ X42) = (k9_relat_1 @ X39 @ X42)))),
% 0.54/0.72      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.54/0.72  thf('3', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.54/0.72           = (k9_relat_1 @ sk_D @ X0))),
% 0.54/0.72      inference('sup-', [status(thm)], ['1', '2'])).
% 0.54/0.72  thf('4', plain,
% 0.54/0.72      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.54/0.72          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.54/0.72      inference('demod', [status(thm)], ['0', '3'])).
% 0.54/0.72  thf(d10_xboole_0, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.54/0.72  thf('5', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.54/0.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.72  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.54/0.72      inference('simplify', [status(thm)], ['5'])).
% 0.54/0.72  thf('7', plain,
% 0.54/0.72      ((m1_subset_1 @ sk_D @ 
% 0.54/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf(t13_relset_1, axiom,
% 0.54/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.72     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.54/0.72       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.54/0.72         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.54/0.72  thf('8', plain,
% 0.54/0.72      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.54/0.72         (~ (r1_tarski @ (k1_relat_1 @ X43) @ X44)
% 0.54/0.72          | (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 0.54/0.72          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45))))),
% 0.54/0.72      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.54/0.72  thf('9', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.54/0.72          | ~ (r1_tarski @ (k1_relat_1 @ sk_D) @ X0))),
% 0.54/0.72      inference('sup-', [status(thm)], ['7', '8'])).
% 0.54/0.72  thf('10', plain,
% 0.54/0.72      ((m1_subset_1 @ sk_D @ 
% 0.54/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['6', '9'])).
% 0.54/0.72  thf(t3_subset, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.54/0.72  thf('11', plain,
% 0.54/0.72      (![X21 : $i, X22 : $i]:
% 0.54/0.72         ((r1_tarski @ X21 @ X22) | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 0.54/0.72      inference('cnf', [status(esa)], [t3_subset])).
% 0.54/0.72  thf('12', plain,
% 0.54/0.72      ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B))),
% 0.54/0.72      inference('sup-', [status(thm)], ['10', '11'])).
% 0.54/0.72  thf('13', plain,
% 0.54/0.72      (![X0 : $i, X2 : $i]:
% 0.54/0.72         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.54/0.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.72  thf('14', plain,
% 0.54/0.72      ((~ (r1_tarski @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B) @ sk_D)
% 0.54/0.72        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B) = (sk_D)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['12', '13'])).
% 0.54/0.72  thf(t144_relat_1, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( v1_relat_1 @ B ) =>
% 0.54/0.72       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.54/0.72  thf('15', plain,
% 0.54/0.72      (![X24 : $i, X25 : $i]:
% 0.54/0.72         ((r1_tarski @ (k9_relat_1 @ X24 @ X25) @ (k2_relat_1 @ X24))
% 0.54/0.72          | ~ (v1_relat_1 @ X24))),
% 0.54/0.72      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.54/0.72  thf('16', plain,
% 0.54/0.72      ((m1_subset_1 @ sk_D @ 
% 0.54/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf(cc2_relset_1, axiom,
% 0.54/0.72    (![A:$i,B:$i,C:$i]:
% 0.54/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.72       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.54/0.72  thf('17', plain,
% 0.54/0.72      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.54/0.72         ((v4_relat_1 @ X36 @ X37)
% 0.54/0.72          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.54/0.72      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.72  thf('18', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.54/0.72      inference('sup-', [status(thm)], ['16', '17'])).
% 0.54/0.72  thf(t209_relat_1, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.54/0.72       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.54/0.72  thf('19', plain,
% 0.54/0.72      (![X27 : $i, X28 : $i]:
% 0.54/0.72         (((X27) = (k7_relat_1 @ X27 @ X28))
% 0.54/0.72          | ~ (v4_relat_1 @ X27 @ X28)
% 0.54/0.72          | ~ (v1_relat_1 @ X27))),
% 0.54/0.72      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.54/0.72  thf('20', plain,
% 0.54/0.72      ((~ (v1_relat_1 @ sk_D)
% 0.54/0.72        | ((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A))))),
% 0.54/0.72      inference('sup-', [status(thm)], ['18', '19'])).
% 0.54/0.72  thf('21', plain,
% 0.54/0.72      ((m1_subset_1 @ sk_D @ 
% 0.54/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf(cc1_relset_1, axiom,
% 0.54/0.72    (![A:$i,B:$i,C:$i]:
% 0.54/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.72       ( v1_relat_1 @ C ) ))).
% 0.54/0.72  thf('22', plain,
% 0.54/0.72      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.54/0.72         ((v1_relat_1 @ X33)
% 0.54/0.72          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.54/0.72      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.54/0.72  thf('23', plain, ((v1_relat_1 @ sk_D)),
% 0.54/0.72      inference('sup-', [status(thm)], ['21', '22'])).
% 0.54/0.72  thf('24', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.54/0.72      inference('demod', [status(thm)], ['20', '23'])).
% 0.54/0.72  thf(t87_relat_1, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( v1_relat_1 @ B ) =>
% 0.54/0.72       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.54/0.72  thf('25', plain,
% 0.54/0.72      (![X29 : $i, X30 : $i]:
% 0.54/0.72         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X29 @ X30)) @ X30)
% 0.54/0.72          | ~ (v1_relat_1 @ X29))),
% 0.54/0.72      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.54/0.72  thf('26', plain,
% 0.54/0.72      (((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))
% 0.54/0.72        | ~ (v1_relat_1 @ sk_D))),
% 0.54/0.72      inference('sup+', [status(thm)], ['24', '25'])).
% 0.54/0.72  thf('27', plain, ((v1_relat_1 @ sk_D)),
% 0.54/0.72      inference('sup-', [status(thm)], ['21', '22'])).
% 0.54/0.72  thf('28', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.54/0.72      inference('demod', [status(thm)], ['26', '27'])).
% 0.54/0.72  thf(t69_enumset1, axiom,
% 0.54/0.72    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.54/0.72  thf('29', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.54/0.72      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.54/0.72  thf(l45_zfmisc_1, axiom,
% 0.54/0.72    (![A:$i,B:$i,C:$i]:
% 0.54/0.72     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.54/0.72       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.54/0.72            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.54/0.72  thf('30', plain,
% 0.54/0.72      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.54/0.72         (((X16) = (k2_tarski @ X14 @ X15))
% 0.54/0.72          | ((X16) = (k1_tarski @ X15))
% 0.54/0.72          | ((X16) = (k1_tarski @ X14))
% 0.54/0.72          | ((X16) = (k1_xboole_0))
% 0.54/0.72          | ~ (r1_tarski @ X16 @ (k2_tarski @ X14 @ X15)))),
% 0.54/0.72      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.54/0.72  thf('31', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]:
% 0.54/0.72         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.54/0.72          | ((X1) = (k1_xboole_0))
% 0.54/0.72          | ((X1) = (k1_tarski @ X0))
% 0.54/0.72          | ((X1) = (k1_tarski @ X0))
% 0.54/0.72          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['29', '30'])).
% 0.54/0.72  thf('32', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]:
% 0.54/0.72         (((X1) = (k2_tarski @ X0 @ X0))
% 0.54/0.72          | ((X1) = (k1_tarski @ X0))
% 0.54/0.72          | ((X1) = (k1_xboole_0))
% 0.54/0.72          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.54/0.72      inference('simplify', [status(thm)], ['31'])).
% 0.54/0.72  thf('33', plain,
% 0.54/0.72      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.54/0.72        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.54/0.72        | ((k1_relat_1 @ sk_D) = (k2_tarski @ sk_A @ sk_A)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['28', '32'])).
% 0.54/0.72  thf('34', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.54/0.72      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.54/0.72  thf('35', plain,
% 0.54/0.72      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.54/0.72        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.54/0.72        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.54/0.72      inference('demod', [status(thm)], ['33', '34'])).
% 0.54/0.72  thf('36', plain,
% 0.54/0.72      ((((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.54/0.72        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.54/0.72      inference('simplify', [status(thm)], ['35'])).
% 0.54/0.72  thf(t14_funct_1, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.54/0.72       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.54/0.72         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.54/0.72  thf('37', plain,
% 0.54/0.72      (![X31 : $i, X32 : $i]:
% 0.54/0.72         (((k1_relat_1 @ X32) != (k1_tarski @ X31))
% 0.54/0.72          | ((k2_relat_1 @ X32) = (k1_tarski @ (k1_funct_1 @ X32 @ X31)))
% 0.54/0.72          | ~ (v1_funct_1 @ X32)
% 0.54/0.72          | ~ (v1_relat_1 @ X32))),
% 0.54/0.72      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.54/0.72  thf('38', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.54/0.72          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.54/0.72          | ~ (v1_relat_1 @ X0)
% 0.54/0.72          | ~ (v1_funct_1 @ X0)
% 0.54/0.72          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.54/0.72      inference('sup-', [status(thm)], ['36', '37'])).
% 0.54/0.72  thf('39', plain,
% 0.54/0.72      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.54/0.72        | ~ (v1_funct_1 @ sk_D)
% 0.54/0.72        | ~ (v1_relat_1 @ sk_D)
% 0.54/0.72        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.54/0.72      inference('eq_res', [status(thm)], ['38'])).
% 0.54/0.72  thf('40', plain, ((v1_funct_1 @ sk_D)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('41', plain, ((v1_relat_1 @ sk_D)),
% 0.54/0.72      inference('sup-', [status(thm)], ['21', '22'])).
% 0.54/0.72  thf('42', plain,
% 0.54/0.72      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.54/0.72        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.54/0.72      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.54/0.72  thf('43', plain,
% 0.54/0.72      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.54/0.72          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.54/0.72      inference('demod', [status(thm)], ['0', '3'])).
% 0.54/0.72  thf('44', plain,
% 0.54/0.72      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.54/0.72        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['42', '43'])).
% 0.54/0.72  thf('45', plain,
% 0.54/0.72      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['15', '44'])).
% 0.54/0.72  thf('46', plain, ((v1_relat_1 @ sk_D)),
% 0.54/0.72      inference('sup-', [status(thm)], ['21', '22'])).
% 0.54/0.72  thf('47', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.54/0.72      inference('demod', [status(thm)], ['45', '46'])).
% 0.54/0.72  thf(t113_zfmisc_1, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.54/0.72       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.54/0.72  thf('48', plain,
% 0.54/0.72      (![X19 : $i, X20 : $i]:
% 0.54/0.72         (((k2_zfmisc_1 @ X19 @ X20) = (k1_xboole_0))
% 0.54/0.72          | ((X19) != (k1_xboole_0)))),
% 0.54/0.72      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.54/0.72  thf('49', plain,
% 0.54/0.72      (![X20 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X20) = (k1_xboole_0))),
% 0.54/0.72      inference('simplify', [status(thm)], ['48'])).
% 0.54/0.72  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.54/0.72  thf('50', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.54/0.72      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.54/0.72  thf('51', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.54/0.72      inference('demod', [status(thm)], ['45', '46'])).
% 0.54/0.72  thf('52', plain,
% 0.54/0.72      (![X20 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X20) = (k1_xboole_0))),
% 0.54/0.72      inference('simplify', [status(thm)], ['48'])).
% 0.54/0.72  thf('53', plain, (((k1_xboole_0) = (sk_D))),
% 0.54/0.72      inference('demod', [status(thm)], ['14', '47', '49', '50', '51', '52'])).
% 0.54/0.72  thf(t150_relat_1, axiom,
% 0.54/0.72    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.54/0.72  thf('54', plain,
% 0.54/0.72      (![X26 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X26) = (k1_xboole_0))),
% 0.54/0.72      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.54/0.72  thf('55', plain, (((k1_xboole_0) = (sk_D))),
% 0.54/0.72      inference('demod', [status(thm)], ['14', '47', '49', '50', '51', '52'])).
% 0.54/0.72  thf('56', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.54/0.72      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.54/0.72  thf('57', plain, ($false),
% 0.54/0.72      inference('demod', [status(thm)], ['4', '53', '54', '55', '56'])).
% 0.54/0.72  
% 0.54/0.72  % SZS output end Refutation
% 0.54/0.72  
% 0.54/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
