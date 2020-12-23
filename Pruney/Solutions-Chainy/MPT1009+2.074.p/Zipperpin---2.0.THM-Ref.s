%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Q9E0Vr86AV

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:59 EST 2020

% Result     : Theorem 1.94s
% Output     : Refutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 221 expanded)
%              Number of leaves         :   38 (  81 expanded)
%              Depth                    :   20
%              Number of atoms          :  763 (2754 expanded)
%              Number of equality atoms :   95 ( 229 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( ( k7_relset_1 @ X35 @ X36 @ X34 @ X37 )
        = ( k9_relat_1 @ X34 @ X37 ) ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X18 @ X19 ) @ ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v4_relat_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X21
        = ( k7_relat_1 @ X21 @ X22 ) )
      | ~ ( v4_relat_1 @ X21 @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('12',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('15',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X24 @ X25 ) ) @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('16',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('18',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

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

thf('21',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X9
        = ( k1_enumset1 @ X6 @ X7 @ X8 ) )
      | ( X9
        = ( k2_tarski @ X6 @ X8 ) )
      | ( X9
        = ( k2_tarski @ X7 @ X8 ) )
      | ( X9
        = ( k2_tarski @ X6 @ X7 ) )
      | ( X9
        = ( k1_tarski @ X8 ) )
      | ( X9
        = ( k1_tarski @ X7 ) )
      | ( X9
        = ( k1_tarski @ X6 ) )
      | ( X9 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X1 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X1 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X1 ) )
      | ( X2
        = ( k1_tarski @ X0 ) )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2 = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k2_tarski @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('30',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('32',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k1_relat_1 @ X27 )
       != ( k1_tarski @ X26 ) )
      | ( ( k2_relat_1 @ X27 )
        = ( k1_tarski @ ( k1_funct_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['33'])).

thf('35',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('37',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('39',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('42',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['40','41'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('43',plain,(
    ! [X23: $i] :
      ( ( ( k1_relat_1 @ X23 )
       != k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('44',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('46',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['46'])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('48',plain,(
    ! [X20: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('49',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['46'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('50',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('51',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['4','47','48','49','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Q9E0Vr86AV
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:53:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.94/2.18  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.94/2.18  % Solved by: fo/fo7.sh
% 1.94/2.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.94/2.18  % done 1111 iterations in 1.744s
% 1.94/2.18  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.94/2.18  % SZS output start Refutation
% 1.94/2.18  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.94/2.18  thf(sk_A_type, type, sk_A: $i).
% 1.94/2.18  thf(sk_D_type, type, sk_D: $i).
% 1.94/2.18  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.94/2.18  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.94/2.18  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.94/2.18  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.94/2.18  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.94/2.18  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.94/2.18  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.94/2.18  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.94/2.18  thf(sk_B_type, type, sk_B: $i).
% 1.94/2.18  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.94/2.18  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.94/2.18  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.94/2.18  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.94/2.18  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.94/2.18  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.94/2.18  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.94/2.18  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.94/2.18  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.94/2.18  thf(sk_C_type, type, sk_C: $i).
% 1.94/2.18  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.94/2.18  thf(t64_funct_2, conjecture,
% 1.94/2.18    (![A:$i,B:$i,C:$i,D:$i]:
% 1.94/2.18     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 1.94/2.18         ( m1_subset_1 @
% 1.94/2.18           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 1.94/2.18       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.94/2.18         ( r1_tarski @
% 1.94/2.18           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 1.94/2.18           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 1.94/2.18  thf(zf_stmt_0, negated_conjecture,
% 1.94/2.18    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.94/2.18        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 1.94/2.18            ( m1_subset_1 @
% 1.94/2.18              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 1.94/2.18          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.94/2.18            ( r1_tarski @
% 1.94/2.18              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 1.94/2.18              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 1.94/2.18    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 1.94/2.18  thf('0', plain,
% 1.94/2.18      (~ (r1_tarski @ 
% 1.94/2.18          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 1.94/2.18          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 1.94/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.18  thf('1', plain,
% 1.94/2.18      ((m1_subset_1 @ sk_D @ 
% 1.94/2.18        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.94/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.18  thf(redefinition_k7_relset_1, axiom,
% 1.94/2.18    (![A:$i,B:$i,C:$i,D:$i]:
% 1.94/2.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.94/2.18       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 1.94/2.18  thf('2', plain,
% 1.94/2.18      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.94/2.18         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 1.94/2.18          | ((k7_relset_1 @ X35 @ X36 @ X34 @ X37) = (k9_relat_1 @ X34 @ X37)))),
% 1.94/2.18      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.94/2.18  thf('3', plain,
% 1.94/2.18      (![X0 : $i]:
% 1.94/2.18         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 1.94/2.18           = (k9_relat_1 @ sk_D @ X0))),
% 1.94/2.18      inference('sup-', [status(thm)], ['1', '2'])).
% 1.94/2.18  thf('4', plain,
% 1.94/2.18      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 1.94/2.18          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 1.94/2.18      inference('demod', [status(thm)], ['0', '3'])).
% 1.94/2.18  thf(t144_relat_1, axiom,
% 1.94/2.18    (![A:$i,B:$i]:
% 1.94/2.18     ( ( v1_relat_1 @ B ) =>
% 1.94/2.18       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 1.94/2.18  thf('5', plain,
% 1.94/2.18      (![X18 : $i, X19 : $i]:
% 1.94/2.18         ((r1_tarski @ (k9_relat_1 @ X18 @ X19) @ (k2_relat_1 @ X18))
% 1.94/2.18          | ~ (v1_relat_1 @ X18))),
% 1.94/2.18      inference('cnf', [status(esa)], [t144_relat_1])).
% 1.94/2.18  thf('6', plain,
% 1.94/2.18      ((m1_subset_1 @ sk_D @ 
% 1.94/2.18        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.94/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.18  thf(cc2_relset_1, axiom,
% 1.94/2.18    (![A:$i,B:$i,C:$i]:
% 1.94/2.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.94/2.18       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.94/2.18  thf('7', plain,
% 1.94/2.18      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.94/2.18         ((v4_relat_1 @ X31 @ X32)
% 1.94/2.18          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 1.94/2.18      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.94/2.18  thf('8', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 1.94/2.18      inference('sup-', [status(thm)], ['6', '7'])).
% 1.94/2.18  thf(t209_relat_1, axiom,
% 1.94/2.18    (![A:$i,B:$i]:
% 1.94/2.18     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.94/2.18       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 1.94/2.18  thf('9', plain,
% 1.94/2.18      (![X21 : $i, X22 : $i]:
% 1.94/2.18         (((X21) = (k7_relat_1 @ X21 @ X22))
% 1.94/2.18          | ~ (v4_relat_1 @ X21 @ X22)
% 1.94/2.18          | ~ (v1_relat_1 @ X21))),
% 1.94/2.18      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.94/2.18  thf('10', plain,
% 1.94/2.18      ((~ (v1_relat_1 @ sk_D)
% 1.94/2.18        | ((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A))))),
% 1.94/2.18      inference('sup-', [status(thm)], ['8', '9'])).
% 1.94/2.18  thf('11', plain,
% 1.94/2.18      ((m1_subset_1 @ sk_D @ 
% 1.94/2.18        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.94/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.18  thf(cc1_relset_1, axiom,
% 1.94/2.18    (![A:$i,B:$i,C:$i]:
% 1.94/2.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.94/2.18       ( v1_relat_1 @ C ) ))).
% 1.94/2.18  thf('12', plain,
% 1.94/2.18      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.94/2.18         ((v1_relat_1 @ X28)
% 1.94/2.18          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.94/2.18      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.94/2.18  thf('13', plain, ((v1_relat_1 @ sk_D)),
% 1.94/2.18      inference('sup-', [status(thm)], ['11', '12'])).
% 1.94/2.18  thf('14', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 1.94/2.18      inference('demod', [status(thm)], ['10', '13'])).
% 1.94/2.18  thf(t87_relat_1, axiom,
% 1.94/2.18    (![A:$i,B:$i]:
% 1.94/2.18     ( ( v1_relat_1 @ B ) =>
% 1.94/2.18       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 1.94/2.18  thf('15', plain,
% 1.94/2.18      (![X24 : $i, X25 : $i]:
% 1.94/2.18         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X24 @ X25)) @ X25)
% 1.94/2.18          | ~ (v1_relat_1 @ X24))),
% 1.94/2.18      inference('cnf', [status(esa)], [t87_relat_1])).
% 1.94/2.18  thf('16', plain,
% 1.94/2.18      (((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))
% 1.94/2.18        | ~ (v1_relat_1 @ sk_D))),
% 1.94/2.18      inference('sup+', [status(thm)], ['14', '15'])).
% 1.94/2.18  thf('17', plain, ((v1_relat_1 @ sk_D)),
% 1.94/2.18      inference('sup-', [status(thm)], ['11', '12'])).
% 1.94/2.18  thf('18', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 1.94/2.18      inference('demod', [status(thm)], ['16', '17'])).
% 1.94/2.18  thf(t69_enumset1, axiom,
% 1.94/2.18    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.94/2.18  thf('19', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 1.94/2.18      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.94/2.18  thf(t70_enumset1, axiom,
% 1.94/2.18    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.94/2.18  thf('20', plain,
% 1.94/2.18      (![X1 : $i, X2 : $i]:
% 1.94/2.18         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 1.94/2.18      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.94/2.18  thf(t142_zfmisc_1, axiom,
% 1.94/2.18    (![A:$i,B:$i,C:$i,D:$i]:
% 1.94/2.18     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.94/2.18       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 1.94/2.18            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 1.94/2.18            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 1.94/2.18            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 1.94/2.18            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 1.94/2.18            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 1.94/2.18  thf('21', plain,
% 1.94/2.18      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 1.94/2.18         (((X9) = (k1_enumset1 @ X6 @ X7 @ X8))
% 1.94/2.18          | ((X9) = (k2_tarski @ X6 @ X8))
% 1.94/2.18          | ((X9) = (k2_tarski @ X7 @ X8))
% 1.94/2.18          | ((X9) = (k2_tarski @ X6 @ X7))
% 1.94/2.18          | ((X9) = (k1_tarski @ X8))
% 1.94/2.18          | ((X9) = (k1_tarski @ X7))
% 1.94/2.18          | ((X9) = (k1_tarski @ X6))
% 1.94/2.18          | ((X9) = (k1_xboole_0))
% 1.94/2.18          | ~ (r1_tarski @ X9 @ (k1_enumset1 @ X6 @ X7 @ X8)))),
% 1.94/2.18      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 1.94/2.18  thf('22', plain,
% 1.94/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.18         (~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0))
% 1.94/2.18          | ((X2) = (k1_xboole_0))
% 1.94/2.18          | ((X2) = (k1_tarski @ X1))
% 1.94/2.18          | ((X2) = (k1_tarski @ X1))
% 1.94/2.18          | ((X2) = (k1_tarski @ X0))
% 1.94/2.18          | ((X2) = (k2_tarski @ X1 @ X1))
% 1.94/2.18          | ((X2) = (k2_tarski @ X1 @ X0))
% 1.94/2.18          | ((X2) = (k2_tarski @ X1 @ X0))
% 1.94/2.18          | ((X2) = (k1_enumset1 @ X1 @ X1 @ X0)))),
% 1.94/2.18      inference('sup-', [status(thm)], ['20', '21'])).
% 1.94/2.18  thf('23', plain,
% 1.94/2.18      (![X1 : $i, X2 : $i]:
% 1.94/2.18         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 1.94/2.18      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.94/2.18  thf('24', plain,
% 1.94/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.18         (~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0))
% 1.94/2.18          | ((X2) = (k1_xboole_0))
% 1.94/2.18          | ((X2) = (k1_tarski @ X1))
% 1.94/2.18          | ((X2) = (k1_tarski @ X1))
% 1.94/2.18          | ((X2) = (k1_tarski @ X0))
% 1.94/2.18          | ((X2) = (k2_tarski @ X1 @ X1))
% 1.94/2.18          | ((X2) = (k2_tarski @ X1 @ X0))
% 1.94/2.18          | ((X2) = (k2_tarski @ X1 @ X0))
% 1.94/2.18          | ((X2) = (k2_tarski @ X1 @ X0)))),
% 1.94/2.18      inference('demod', [status(thm)], ['22', '23'])).
% 1.94/2.18  thf('25', plain,
% 1.94/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.18         (((X2) = (k2_tarski @ X1 @ X0))
% 1.94/2.18          | ((X2) = (k2_tarski @ X1 @ X1))
% 1.94/2.18          | ((X2) = (k1_tarski @ X0))
% 1.94/2.18          | ((X2) = (k1_tarski @ X1))
% 1.94/2.18          | ((X2) = (k1_xboole_0))
% 1.94/2.18          | ~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0)))),
% 1.94/2.18      inference('simplify', [status(thm)], ['24'])).
% 1.94/2.18  thf('26', plain,
% 1.94/2.18      (![X0 : $i, X1 : $i]:
% 1.94/2.18         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 1.94/2.18          | ((X1) = (k1_xboole_0))
% 1.94/2.18          | ((X1) = (k1_tarski @ X0))
% 1.94/2.18          | ((X1) = (k1_tarski @ X0))
% 1.94/2.18          | ((X1) = (k2_tarski @ X0 @ X0))
% 1.94/2.18          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 1.94/2.18      inference('sup-', [status(thm)], ['19', '25'])).
% 1.94/2.18  thf('27', plain,
% 1.94/2.18      (![X0 : $i, X1 : $i]:
% 1.94/2.18         (((X1) = (k2_tarski @ X0 @ X0))
% 1.94/2.18          | ((X1) = (k1_tarski @ X0))
% 1.94/2.18          | ((X1) = (k1_xboole_0))
% 1.94/2.18          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 1.94/2.18      inference('simplify', [status(thm)], ['26'])).
% 1.94/2.18  thf('28', plain,
% 1.94/2.18      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 1.94/2.18        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 1.94/2.18        | ((k1_relat_1 @ sk_D) = (k2_tarski @ sk_A @ sk_A)))),
% 1.94/2.18      inference('sup-', [status(thm)], ['18', '27'])).
% 1.94/2.18  thf('29', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 1.94/2.18      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.94/2.18  thf('30', plain,
% 1.94/2.18      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 1.94/2.18        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 1.94/2.18        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 1.94/2.18      inference('demod', [status(thm)], ['28', '29'])).
% 1.94/2.18  thf('31', plain,
% 1.94/2.18      ((((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 1.94/2.18        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 1.94/2.18      inference('simplify', [status(thm)], ['30'])).
% 1.94/2.18  thf(t14_funct_1, axiom,
% 1.94/2.18    (![A:$i,B:$i]:
% 1.94/2.18     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.94/2.18       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 1.94/2.18         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 1.94/2.18  thf('32', plain,
% 1.94/2.18      (![X26 : $i, X27 : $i]:
% 1.94/2.18         (((k1_relat_1 @ X27) != (k1_tarski @ X26))
% 1.94/2.18          | ((k2_relat_1 @ X27) = (k1_tarski @ (k1_funct_1 @ X27 @ X26)))
% 1.94/2.18          | ~ (v1_funct_1 @ X27)
% 1.94/2.18          | ~ (v1_relat_1 @ X27))),
% 1.94/2.18      inference('cnf', [status(esa)], [t14_funct_1])).
% 1.94/2.18  thf('33', plain,
% 1.94/2.18      (![X0 : $i]:
% 1.94/2.18         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 1.94/2.18          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 1.94/2.18          | ~ (v1_relat_1 @ X0)
% 1.94/2.18          | ~ (v1_funct_1 @ X0)
% 1.94/2.18          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 1.94/2.18      inference('sup-', [status(thm)], ['31', '32'])).
% 1.94/2.18  thf('34', plain,
% 1.94/2.18      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 1.94/2.18        | ~ (v1_funct_1 @ sk_D)
% 1.94/2.18        | ~ (v1_relat_1 @ sk_D)
% 1.94/2.18        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 1.94/2.18      inference('eq_res', [status(thm)], ['33'])).
% 1.94/2.18  thf('35', plain, ((v1_funct_1 @ sk_D)),
% 1.94/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.18  thf('36', plain, ((v1_relat_1 @ sk_D)),
% 1.94/2.18      inference('sup-', [status(thm)], ['11', '12'])).
% 1.94/2.18  thf('37', plain,
% 1.94/2.18      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 1.94/2.18        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 1.94/2.18      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.94/2.18  thf('38', plain,
% 1.94/2.18      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 1.94/2.18          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 1.94/2.18      inference('demod', [status(thm)], ['0', '3'])).
% 1.94/2.18  thf('39', plain,
% 1.94/2.18      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 1.94/2.18        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 1.94/2.18      inference('sup-', [status(thm)], ['37', '38'])).
% 1.94/2.18  thf('40', plain,
% 1.94/2.18      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 1.94/2.18      inference('sup-', [status(thm)], ['5', '39'])).
% 1.94/2.18  thf('41', plain, ((v1_relat_1 @ sk_D)),
% 1.94/2.18      inference('sup-', [status(thm)], ['11', '12'])).
% 1.94/2.18  thf('42', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 1.94/2.18      inference('demod', [status(thm)], ['40', '41'])).
% 1.94/2.18  thf(t64_relat_1, axiom,
% 1.94/2.18    (![A:$i]:
% 1.94/2.18     ( ( v1_relat_1 @ A ) =>
% 1.94/2.18       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 1.94/2.18           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 1.94/2.18         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 1.94/2.18  thf('43', plain,
% 1.94/2.18      (![X23 : $i]:
% 1.94/2.18         (((k1_relat_1 @ X23) != (k1_xboole_0))
% 1.94/2.18          | ((X23) = (k1_xboole_0))
% 1.94/2.18          | ~ (v1_relat_1 @ X23))),
% 1.94/2.18      inference('cnf', [status(esa)], [t64_relat_1])).
% 1.94/2.18  thf('44', plain,
% 1.94/2.18      ((((k1_xboole_0) != (k1_xboole_0))
% 1.94/2.18        | ~ (v1_relat_1 @ sk_D)
% 1.94/2.18        | ((sk_D) = (k1_xboole_0)))),
% 1.94/2.18      inference('sup-', [status(thm)], ['42', '43'])).
% 1.94/2.18  thf('45', plain, ((v1_relat_1 @ sk_D)),
% 1.94/2.18      inference('sup-', [status(thm)], ['11', '12'])).
% 1.94/2.18  thf('46', plain,
% 1.94/2.18      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 1.94/2.18      inference('demod', [status(thm)], ['44', '45'])).
% 1.94/2.18  thf('47', plain, (((sk_D) = (k1_xboole_0))),
% 1.94/2.18      inference('simplify', [status(thm)], ['46'])).
% 1.94/2.18  thf(t150_relat_1, axiom,
% 1.94/2.18    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 1.94/2.18  thf('48', plain,
% 1.94/2.18      (![X20 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X20) = (k1_xboole_0))),
% 1.94/2.18      inference('cnf', [status(esa)], [t150_relat_1])).
% 1.94/2.18  thf('49', plain, (((sk_D) = (k1_xboole_0))),
% 1.94/2.18      inference('simplify', [status(thm)], ['46'])).
% 1.94/2.18  thf(t4_subset_1, axiom,
% 1.94/2.18    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.94/2.18  thf('50', plain,
% 1.94/2.18      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 1.94/2.18      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.94/2.18  thf(t3_subset, axiom,
% 1.94/2.18    (![A:$i,B:$i]:
% 1.94/2.18     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.94/2.18  thf('51', plain,
% 1.94/2.18      (![X12 : $i, X13 : $i]:
% 1.94/2.18         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 1.94/2.18      inference('cnf', [status(esa)], [t3_subset])).
% 1.94/2.18  thf('52', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.94/2.18      inference('sup-', [status(thm)], ['50', '51'])).
% 1.94/2.18  thf('53', plain, ($false),
% 1.94/2.18      inference('demod', [status(thm)], ['4', '47', '48', '49', '52'])).
% 1.94/2.18  
% 1.94/2.18  % SZS output end Refutation
% 1.94/2.18  
% 1.94/2.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
