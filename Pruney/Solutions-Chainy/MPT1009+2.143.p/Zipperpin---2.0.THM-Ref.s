%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B1kzPwAaYc

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:09 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 232 expanded)
%              Number of leaves         :   38 (  86 expanded)
%              Depth                    :   19
%              Number of atoms          :  762 (2723 expanded)
%              Number of equality atoms :   94 ( 225 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ( ( k7_relset_1 @ X50 @ X51 @ X49 @ X52 )
        = ( k9_relat_1 @ X49 @ X52 ) ) ) ),
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
    ! [X40: $i,X41: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X40 @ X41 ) @ ( k2_relat_1 @ X40 ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
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
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( v4_relat_1 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) ) ) ),
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
    ! [X36: $i,X37: $i] :
      ( ~ ( v4_relat_1 @ X36 @ X37 )
      | ( r1_tarski @ ( k1_relat_1 @ X36 ) @ X37 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
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
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ( v1_relat_1 @ X34 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X38: $i,X39: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['10','15'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X4 @ X4 @ X5 @ X6 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('20',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X4 @ X4 @ X5 @ X6 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t142_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) )
    <=> ~ ( ( D != k1_xboole_0 )
          & ( D
           != ( k1_tarski @ A ) )
          & ( D
           != ( k1_tarski @ B ) )
          & ( D
           != ( k1_tarski @ C ) )
          & ( D
           != ( k2_tarski @ A @ B ) )
          & ( D
           != ( k2_tarski @ B @ C ) )
          & ( D
           != ( k2_tarski @ A @ C ) )
          & ( D
           != ( k1_enumset1 @ A @ B @ C ) ) ) ) )).

thf('23',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( X32
        = ( k1_enumset1 @ X29 @ X30 @ X31 ) )
      | ( X32
        = ( k2_tarski @ X29 @ X31 ) )
      | ( X32
        = ( k2_tarski @ X30 @ X31 ) )
      | ( X32
        = ( k2_tarski @ X29 @ X30 ) )
      | ( X32
        = ( k1_tarski @ X31 ) )
      | ( X32
        = ( k1_tarski @ X30 ) )
      | ( X32
        = ( k1_tarski @ X29 ) )
      | ( X32 = k1_xboole_0 )
      | ~ ( r1_tarski @ X32 @ ( k1_enumset1 @ X29 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X3
        = ( k1_tarski @ X2 ) )
      | ( X3
        = ( k1_tarski @ X1 ) )
      | ( X3
        = ( k1_tarski @ X0 ) )
      | ( X3
        = ( k2_tarski @ X2 @ X1 ) )
      | ( X3
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X3
        = ( k2_tarski @ X2 @ X0 ) )
      | ( X3
        = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_enumset1 @ X0 @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k2_tarski @ sk_A @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','28'])).

thf('30',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('31',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
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
    ! [X44: $i,X45: $i] :
      ( ( ( k1_relat_1 @ X45 )
       != ( k1_tarski @ X44 ) )
      | ( ( k2_relat_1 @ X45 )
        = ( k1_tarski @ ( k1_funct_1 @ X45 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
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
    inference(demod,[status(thm)],['13','14'])).

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
    inference('sup-',[status(thm)],['5','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('43',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['41','42'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('44',plain,(
    ! [X43: $i] :
      ( ( ( k1_relat_1 @ X43 )
       != k1_xboole_0 )
      | ( X43 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('45',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('47',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['47'])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('49',plain,(
    ! [X42: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X42 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('50',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['47'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['4','48','49','50','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B1kzPwAaYc
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:47:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 405 iterations in 0.122s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.38/0.57  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.38/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.57  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.38/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.57  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.38/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.57  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.38/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.57  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.38/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.57  thf(t64_funct_2, conjecture,
% 0.38/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.57     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.38/0.57         ( m1_subset_1 @
% 0.38/0.57           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.38/0.57       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.38/0.57         ( r1_tarski @
% 0.38/0.57           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.38/0.57           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.57        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.38/0.57            ( m1_subset_1 @
% 0.38/0.57              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.38/0.57          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.38/0.57            ( r1_tarski @
% 0.38/0.57              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.38/0.57              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.38/0.57  thf('0', plain,
% 0.38/0.57      (~ (r1_tarski @ 
% 0.38/0.57          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.38/0.57          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('1', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_D @ 
% 0.38/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(redefinition_k7_relset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.38/0.57  thf('2', plain,
% 0.38/0.57      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 0.38/0.57          | ((k7_relset_1 @ X50 @ X51 @ X49 @ X52) = (k9_relat_1 @ X49 @ X52)))),
% 0.38/0.57      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.38/0.57  thf('3', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.38/0.57           = (k9_relat_1 @ sk_D @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.57  thf('4', plain,
% 0.38/0.57      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.38/0.57          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['0', '3'])).
% 0.38/0.57  thf(t144_relat_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( v1_relat_1 @ B ) =>
% 0.38/0.57       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.38/0.57  thf('5', plain,
% 0.38/0.57      (![X40 : $i, X41 : $i]:
% 0.38/0.57         ((r1_tarski @ (k9_relat_1 @ X40 @ X41) @ (k2_relat_1 @ X40))
% 0.38/0.57          | ~ (v1_relat_1 @ X40))),
% 0.38/0.57      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.38/0.57  thf('6', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_D @ 
% 0.38/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(cc2_relset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.38/0.57  thf('7', plain,
% 0.38/0.57      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.38/0.57         ((v4_relat_1 @ X46 @ X47)
% 0.38/0.57          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48))))),
% 0.38/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.57  thf('8', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.57  thf(d18_relat_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( v1_relat_1 @ B ) =>
% 0.38/0.57       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.38/0.57  thf('9', plain,
% 0.38/0.57      (![X36 : $i, X37 : $i]:
% 0.38/0.57         (~ (v4_relat_1 @ X36 @ X37)
% 0.38/0.57          | (r1_tarski @ (k1_relat_1 @ X36) @ X37)
% 0.38/0.57          | ~ (v1_relat_1 @ X36))),
% 0.38/0.57      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.38/0.57  thf('10', plain,
% 0.38/0.57      ((~ (v1_relat_1 @ sk_D)
% 0.38/0.57        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.38/0.57  thf('11', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_D @ 
% 0.38/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(cc2_relat_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( v1_relat_1 @ A ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.38/0.57  thf('12', plain,
% 0.38/0.57      (![X34 : $i, X35 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.38/0.57          | (v1_relat_1 @ X34)
% 0.38/0.57          | ~ (v1_relat_1 @ X35))),
% 0.38/0.57      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.38/0.57  thf('13', plain,
% 0.38/0.57      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.38/0.57        | (v1_relat_1 @ sk_D))),
% 0.38/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.57  thf(fc6_relat_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.38/0.57  thf('14', plain,
% 0.38/0.57      (![X38 : $i, X39 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X38 @ X39))),
% 0.38/0.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.38/0.57  thf('15', plain, ((v1_relat_1 @ sk_D)),
% 0.38/0.57      inference('demod', [status(thm)], ['13', '14'])).
% 0.38/0.57  thf('16', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['10', '15'])).
% 0.38/0.57  thf(t71_enumset1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.38/0.57  thf('17', plain,
% 0.38/0.57      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.38/0.57         ((k2_enumset1 @ X4 @ X4 @ X5 @ X6) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 0.38/0.57      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.38/0.57  thf(t70_enumset1, axiom,
% 0.38/0.57    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.38/0.57  thf('18', plain,
% 0.38/0.57      (![X2 : $i, X3 : $i]:
% 0.38/0.57         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 0.38/0.57      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.38/0.57  thf('19', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['17', '18'])).
% 0.38/0.57  thf(t69_enumset1, axiom,
% 0.38/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.38/0.57  thf('20', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.38/0.57  thf('21', plain,
% 0.38/0.57      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['19', '20'])).
% 0.38/0.57  thf('22', plain,
% 0.38/0.57      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.38/0.57         ((k2_enumset1 @ X4 @ X4 @ X5 @ X6) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 0.38/0.57      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.38/0.57  thf(t142_zfmisc_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.57     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.38/0.57       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 0.38/0.57            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 0.38/0.57            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 0.38/0.57            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 0.38/0.57            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 0.38/0.57            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 0.38/0.57  thf('23', plain,
% 0.38/0.57      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.38/0.57         (((X32) = (k1_enumset1 @ X29 @ X30 @ X31))
% 0.38/0.57          | ((X32) = (k2_tarski @ X29 @ X31))
% 0.38/0.57          | ((X32) = (k2_tarski @ X30 @ X31))
% 0.38/0.57          | ((X32) = (k2_tarski @ X29 @ X30))
% 0.38/0.57          | ((X32) = (k1_tarski @ X31))
% 0.38/0.57          | ((X32) = (k1_tarski @ X30))
% 0.38/0.57          | ((X32) = (k1_tarski @ X29))
% 0.38/0.57          | ((X32) = (k1_xboole_0))
% 0.38/0.57          | ~ (r1_tarski @ X32 @ (k1_enumset1 @ X29 @ X30 @ X31)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 0.38/0.57  thf('24', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.57         (~ (r1_tarski @ X3 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0))
% 0.38/0.57          | ((X3) = (k1_xboole_0))
% 0.38/0.57          | ((X3) = (k1_tarski @ X2))
% 0.38/0.57          | ((X3) = (k1_tarski @ X1))
% 0.38/0.57          | ((X3) = (k1_tarski @ X0))
% 0.38/0.57          | ((X3) = (k2_tarski @ X2 @ X1))
% 0.38/0.57          | ((X3) = (k2_tarski @ X1 @ X0))
% 0.38/0.57          | ((X3) = (k2_tarski @ X2 @ X0))
% 0.38/0.57          | ((X3) = (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.57  thf('25', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.38/0.57          | ((X1) = (k1_enumset1 @ X0 @ X0 @ X0))
% 0.38/0.57          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.38/0.57          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.38/0.57          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.38/0.57          | ((X1) = (k1_tarski @ X0))
% 0.38/0.57          | ((X1) = (k1_tarski @ X0))
% 0.38/0.57          | ((X1) = (k1_tarski @ X0))
% 0.38/0.57          | ((X1) = (k1_xboole_0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['21', '24'])).
% 0.38/0.57  thf('26', plain,
% 0.38/0.57      (![X2 : $i, X3 : $i]:
% 0.38/0.57         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 0.38/0.57      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.38/0.57  thf('27', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.38/0.57          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.38/0.57          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.38/0.57          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.38/0.57          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.38/0.57          | ((X1) = (k1_tarski @ X0))
% 0.38/0.57          | ((X1) = (k1_tarski @ X0))
% 0.38/0.57          | ((X1) = (k1_tarski @ X0))
% 0.38/0.57          | ((X1) = (k1_xboole_0)))),
% 0.38/0.57      inference('demod', [status(thm)], ['25', '26'])).
% 0.38/0.57  thf('28', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (((X1) = (k1_xboole_0))
% 0.38/0.57          | ((X1) = (k1_tarski @ X0))
% 0.38/0.57          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.38/0.57          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['27'])).
% 0.38/0.57  thf('29', plain,
% 0.38/0.57      ((((k1_relat_1 @ sk_D) = (k2_tarski @ sk_A @ sk_A))
% 0.38/0.57        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.38/0.57        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['16', '28'])).
% 0.38/0.57  thf('30', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.38/0.57  thf('31', plain,
% 0.38/0.57      ((((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.38/0.57        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.38/0.57        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.38/0.57      inference('demod', [status(thm)], ['29', '30'])).
% 0.38/0.57  thf('32', plain,
% 0.38/0.57      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.38/0.57        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['31'])).
% 0.38/0.57  thf(t14_funct_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.57       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.38/0.57         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.38/0.57  thf('33', plain,
% 0.38/0.57      (![X44 : $i, X45 : $i]:
% 0.38/0.57         (((k1_relat_1 @ X45) != (k1_tarski @ X44))
% 0.38/0.57          | ((k2_relat_1 @ X45) = (k1_tarski @ (k1_funct_1 @ X45 @ X44)))
% 0.38/0.57          | ~ (v1_funct_1 @ X45)
% 0.38/0.57          | ~ (v1_relat_1 @ X45))),
% 0.38/0.57      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.38/0.57  thf('34', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.38/0.57          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['32', '33'])).
% 0.38/0.57  thf('35', plain,
% 0.38/0.57      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.38/0.57        | ~ (v1_funct_1 @ sk_D)
% 0.38/0.57        | ~ (v1_relat_1 @ sk_D)
% 0.38/0.57        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.38/0.57      inference('eq_res', [status(thm)], ['34'])).
% 0.38/0.57  thf('36', plain, ((v1_funct_1 @ sk_D)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('37', plain, ((v1_relat_1 @ sk_D)),
% 0.38/0.57      inference('demod', [status(thm)], ['13', '14'])).
% 0.38/0.57  thf('38', plain,
% 0.38/0.57      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.38/0.57        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.38/0.57      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.38/0.57  thf('39', plain,
% 0.38/0.57      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.38/0.57          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['0', '3'])).
% 0.38/0.57  thf('40', plain,
% 0.38/0.57      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.38/0.57        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['38', '39'])).
% 0.38/0.57  thf('41', plain,
% 0.38/0.57      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['5', '40'])).
% 0.38/0.57  thf('42', plain, ((v1_relat_1 @ sk_D)),
% 0.38/0.57      inference('demod', [status(thm)], ['13', '14'])).
% 0.38/0.57  thf('43', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.38/0.57      inference('demod', [status(thm)], ['41', '42'])).
% 0.38/0.57  thf(t64_relat_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( v1_relat_1 @ A ) =>
% 0.38/0.57       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.38/0.57           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.57         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.38/0.57  thf('44', plain,
% 0.38/0.57      (![X43 : $i]:
% 0.38/0.57         (((k1_relat_1 @ X43) != (k1_xboole_0))
% 0.38/0.57          | ((X43) = (k1_xboole_0))
% 0.38/0.57          | ~ (v1_relat_1 @ X43))),
% 0.38/0.57      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.38/0.57  thf('45', plain,
% 0.38/0.57      ((((k1_xboole_0) != (k1_xboole_0))
% 0.38/0.57        | ~ (v1_relat_1 @ sk_D)
% 0.38/0.57        | ((sk_D) = (k1_xboole_0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['43', '44'])).
% 0.38/0.57  thf('46', plain, ((v1_relat_1 @ sk_D)),
% 0.38/0.57      inference('demod', [status(thm)], ['13', '14'])).
% 0.38/0.57  thf('47', plain,
% 0.38/0.57      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 0.38/0.57      inference('demod', [status(thm)], ['45', '46'])).
% 0.38/0.57  thf('48', plain, (((sk_D) = (k1_xboole_0))),
% 0.38/0.57      inference('simplify', [status(thm)], ['47'])).
% 0.38/0.57  thf(t150_relat_1, axiom,
% 0.38/0.57    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.38/0.57  thf('49', plain,
% 0.38/0.57      (![X42 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X42) = (k1_xboole_0))),
% 0.38/0.57      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.38/0.57  thf('50', plain, (((sk_D) = (k1_xboole_0))),
% 0.38/0.57      inference('simplify', [status(thm)], ['47'])).
% 0.38/0.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.38/0.57  thf('51', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.38/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.57  thf('52', plain, ($false),
% 0.38/0.57      inference('demod', [status(thm)], ['4', '48', '49', '50', '51'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.38/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
