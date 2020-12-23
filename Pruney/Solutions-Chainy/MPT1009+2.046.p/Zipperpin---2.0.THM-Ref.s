%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BIf0vSQaAz

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:55 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 257 expanded)
%              Number of leaves         :   42 (  95 expanded)
%              Depth                    :   20
%              Number of atoms          :  869 (3123 expanded)
%              Number of equality atoms :   99 ( 243 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

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
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( ( k7_relset_1 @ X37 @ X38 @ X36 @ X39 )
        = ( k9_relat_1 @ X36 @ X39 ) ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X21 @ X22 ) @ ( k2_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v4_relat_1 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ( X24
        = ( k7_relat_1 @ X24 @ X25 ) )
      | ~ ( v4_relat_1 @ X24 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_relat_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X26 @ X27 ) ) @ X27 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
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

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X7 @ X7 @ X8 @ X9 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('22',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X7 @ X7 @ X8 @ X9 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
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

thf('25',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X16
        = ( k1_enumset1 @ X13 @ X14 @ X15 ) )
      | ( X16
        = ( k2_tarski @ X13 @ X15 ) )
      | ( X16
        = ( k2_tarski @ X14 @ X15 ) )
      | ( X16
        = ( k2_tarski @ X13 @ X14 ) )
      | ( X16
        = ( k1_tarski @ X15 ) )
      | ( X16
        = ( k1_tarski @ X14 ) )
      | ( X16
        = ( k1_tarski @ X13 ) )
      | ( X16 = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ ( k1_enumset1 @ X13 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('26',plain,(
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
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
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
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('29',plain,(
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
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k2_tarski @ sk_A @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','30'])).

thf('32',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('33',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('35',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k1_relat_1 @ X29 )
       != ( k1_tarski @ X28 ) )
      | ( ( k2_relat_1 @ X29 )
        = ( k1_tarski @ ( k1_funct_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ X0 ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k2_relat_1 @ sk_D )
        = ( k1_tarski @ ( k1_funct_1 @ sk_D @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('38',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ X0 ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_D )
        = ( k1_tarski @ ( k1_funct_1 @ sk_D @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['39'])).

thf('41',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('42',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('45',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['43','44'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('46',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X40 ) @ ( k2_relat_1 @ X40 ) ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('47',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( r1_tarski @ sk_D @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('50',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('51',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('54',plain,(
    r1_tarski @ sk_D @ k1_xboole_0 ),
    inference(demod,[status(thm)],['49','51','52','53'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('55',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('56',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    sk_D = k1_xboole_0 ),
    inference('sup-',[status(thm)],['54','57'])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('59',plain,(
    ! [X23: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('60',plain,(
    sk_D = k1_xboole_0 ),
    inference('sup-',[status(thm)],['54','57'])).

thf('61',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['4','58','59','60','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BIf0vSQaAz
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:35:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.45/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.64  % Solved by: fo/fo7.sh
% 0.45/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.64  % done 479 iterations in 0.190s
% 0.45/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.64  % SZS output start Refutation
% 0.45/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.64  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.45/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.64  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.45/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.64  thf(sk_D_type, type, sk_D: $i).
% 0.45/0.64  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.45/0.64  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.45/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.64  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.45/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.64  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.45/0.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.64  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.45/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.64  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.45/0.64  thf(t64_funct_2, conjecture,
% 0.45/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.64     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.45/0.64         ( m1_subset_1 @
% 0.45/0.64           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.45/0.64       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.45/0.64         ( r1_tarski @
% 0.45/0.64           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.45/0.64           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.45/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.64    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.64        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.45/0.64            ( m1_subset_1 @
% 0.45/0.64              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.45/0.64          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.45/0.64            ( r1_tarski @
% 0.45/0.64              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.45/0.64              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.45/0.64    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.45/0.64  thf('0', plain,
% 0.45/0.64      (~ (r1_tarski @ 
% 0.45/0.64          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.45/0.64          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('1', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_D @ 
% 0.45/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(redefinition_k7_relset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.45/0.64  thf('2', plain,
% 0.45/0.64      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.45/0.64          | ((k7_relset_1 @ X37 @ X38 @ X36 @ X39) = (k9_relat_1 @ X36 @ X39)))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.45/0.64  thf('3', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.45/0.64           = (k9_relat_1 @ sk_D @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.64  thf('4', plain,
% 0.45/0.64      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.45/0.64          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['0', '3'])).
% 0.45/0.64  thf(t144_relat_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( v1_relat_1 @ B ) =>
% 0.45/0.64       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.45/0.64  thf('5', plain,
% 0.45/0.64      (![X21 : $i, X22 : $i]:
% 0.45/0.64         ((r1_tarski @ (k9_relat_1 @ X21 @ X22) @ (k2_relat_1 @ X21))
% 0.45/0.64          | ~ (v1_relat_1 @ X21))),
% 0.45/0.64      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.45/0.64  thf('6', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_D @ 
% 0.45/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(cc2_relset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.45/0.64  thf('7', plain,
% 0.45/0.64      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.45/0.64         ((v4_relat_1 @ X33 @ X34)
% 0.45/0.64          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.64  thf('8', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.64  thf(t209_relat_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.45/0.64       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.45/0.64  thf('9', plain,
% 0.45/0.64      (![X24 : $i, X25 : $i]:
% 0.45/0.64         (((X24) = (k7_relat_1 @ X24 @ X25))
% 0.45/0.64          | ~ (v4_relat_1 @ X24 @ X25)
% 0.45/0.64          | ~ (v1_relat_1 @ X24))),
% 0.45/0.64      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.45/0.64  thf('10', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ sk_D)
% 0.45/0.64        | ((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.64  thf('11', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_D @ 
% 0.45/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(cc1_relset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64       ( v1_relat_1 @ C ) ))).
% 0.45/0.64  thf('12', plain,
% 0.45/0.64      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.45/0.64         ((v1_relat_1 @ X30)
% 0.45/0.64          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.64  thf('13', plain, ((v1_relat_1 @ sk_D)),
% 0.45/0.64      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.64  thf('14', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['10', '13'])).
% 0.45/0.64  thf(t87_relat_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( v1_relat_1 @ B ) =>
% 0.45/0.64       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.45/0.64  thf('15', plain,
% 0.45/0.64      (![X26 : $i, X27 : $i]:
% 0.45/0.64         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X26 @ X27)) @ X27)
% 0.45/0.64          | ~ (v1_relat_1 @ X26))),
% 0.45/0.64      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.45/0.64  thf('16', plain,
% 0.45/0.64      (((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))
% 0.45/0.64        | ~ (v1_relat_1 @ sk_D))),
% 0.45/0.64      inference('sup+', [status(thm)], ['14', '15'])).
% 0.45/0.64  thf('17', plain, ((v1_relat_1 @ sk_D)),
% 0.45/0.64      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.64  thf('18', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['16', '17'])).
% 0.45/0.64  thf(t71_enumset1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.45/0.64  thf('19', plain,
% 0.45/0.64      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.45/0.64         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 0.45/0.64      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.45/0.64  thf(t70_enumset1, axiom,
% 0.45/0.64    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.45/0.64  thf('20', plain,
% 0.45/0.64      (![X5 : $i, X6 : $i]:
% 0.45/0.64         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 0.45/0.64      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.64  thf('21', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['19', '20'])).
% 0.45/0.64  thf(t69_enumset1, axiom,
% 0.45/0.64    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.64  thf('22', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.45/0.64      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.64  thf('23', plain,
% 0.45/0.64      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['21', '22'])).
% 0.45/0.64  thf('24', plain,
% 0.45/0.64      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.45/0.64         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 0.45/0.64      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.45/0.64  thf(t142_zfmisc_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.64     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.45/0.64       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 0.45/0.64            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 0.45/0.64            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 0.45/0.64            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 0.45/0.64            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 0.45/0.64            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 0.45/0.64  thf('25', plain,
% 0.45/0.64      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.64         (((X16) = (k1_enumset1 @ X13 @ X14 @ X15))
% 0.45/0.64          | ((X16) = (k2_tarski @ X13 @ X15))
% 0.45/0.64          | ((X16) = (k2_tarski @ X14 @ X15))
% 0.45/0.64          | ((X16) = (k2_tarski @ X13 @ X14))
% 0.45/0.64          | ((X16) = (k1_tarski @ X15))
% 0.45/0.64          | ((X16) = (k1_tarski @ X14))
% 0.45/0.64          | ((X16) = (k1_tarski @ X13))
% 0.45/0.64          | ((X16) = (k1_xboole_0))
% 0.45/0.64          | ~ (r1_tarski @ X16 @ (k1_enumset1 @ X13 @ X14 @ X15)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 0.45/0.64  thf('26', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.64         (~ (r1_tarski @ X3 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0))
% 0.45/0.64          | ((X3) = (k1_xboole_0))
% 0.45/0.64          | ((X3) = (k1_tarski @ X2))
% 0.45/0.64          | ((X3) = (k1_tarski @ X1))
% 0.45/0.64          | ((X3) = (k1_tarski @ X0))
% 0.45/0.64          | ((X3) = (k2_tarski @ X2 @ X1))
% 0.45/0.64          | ((X3) = (k2_tarski @ X1 @ X0))
% 0.45/0.64          | ((X3) = (k2_tarski @ X2 @ X0))
% 0.45/0.64          | ((X3) = (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.64  thf('27', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.45/0.64          | ((X1) = (k1_enumset1 @ X0 @ X0 @ X0))
% 0.45/0.64          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.45/0.64          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.45/0.64          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.45/0.64          | ((X1) = (k1_tarski @ X0))
% 0.45/0.64          | ((X1) = (k1_tarski @ X0))
% 0.45/0.64          | ((X1) = (k1_tarski @ X0))
% 0.45/0.64          | ((X1) = (k1_xboole_0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['23', '26'])).
% 0.45/0.64  thf('28', plain,
% 0.45/0.64      (![X5 : $i, X6 : $i]:
% 0.45/0.64         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 0.45/0.64      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.64  thf('29', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.45/0.64          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.45/0.64          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.45/0.64          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.45/0.64          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.45/0.64          | ((X1) = (k1_tarski @ X0))
% 0.45/0.64          | ((X1) = (k1_tarski @ X0))
% 0.45/0.64          | ((X1) = (k1_tarski @ X0))
% 0.45/0.64          | ((X1) = (k1_xboole_0)))),
% 0.45/0.64      inference('demod', [status(thm)], ['27', '28'])).
% 0.45/0.64  thf('30', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (((X1) = (k1_xboole_0))
% 0.45/0.64          | ((X1) = (k1_tarski @ X0))
% 0.45/0.64          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.45/0.64          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.45/0.64      inference('simplify', [status(thm)], ['29'])).
% 0.45/0.64  thf('31', plain,
% 0.45/0.64      ((((k1_relat_1 @ sk_D) = (k2_tarski @ sk_A @ sk_A))
% 0.45/0.64        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.45/0.64        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['18', '30'])).
% 0.45/0.64  thf('32', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.45/0.64      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.64  thf('33', plain,
% 0.45/0.64      ((((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.45/0.64        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.45/0.64        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.45/0.64      inference('demod', [status(thm)], ['31', '32'])).
% 0.45/0.64  thf('34', plain,
% 0.45/0.64      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.45/0.64        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.45/0.64      inference('simplify', [status(thm)], ['33'])).
% 0.45/0.64  thf(t14_funct_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.45/0.64       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.45/0.64         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.45/0.64  thf('35', plain,
% 0.45/0.64      (![X28 : $i, X29 : $i]:
% 0.45/0.64         (((k1_relat_1 @ X29) != (k1_tarski @ X28))
% 0.45/0.64          | ((k2_relat_1 @ X29) = (k1_tarski @ (k1_funct_1 @ X29 @ X28)))
% 0.45/0.64          | ~ (v1_funct_1 @ X29)
% 0.45/0.64          | ~ (v1_relat_1 @ X29))),
% 0.45/0.64      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.45/0.64  thf('36', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (((k1_tarski @ sk_A) != (k1_tarski @ X0))
% 0.45/0.64          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.45/0.64          | ~ (v1_relat_1 @ sk_D)
% 0.45/0.64          | ~ (v1_funct_1 @ sk_D)
% 0.45/0.64          | ((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ X0))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['34', '35'])).
% 0.45/0.64  thf('37', plain, ((v1_relat_1 @ sk_D)),
% 0.45/0.64      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.64  thf('38', plain, ((v1_funct_1 @ sk_D)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('39', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (((k1_tarski @ sk_A) != (k1_tarski @ X0))
% 0.45/0.64          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.45/0.64          | ((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ X0))))),
% 0.45/0.64      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.45/0.64  thf('40', plain,
% 0.45/0.64      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.45/0.64        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.45/0.64      inference('eq_res', [status(thm)], ['39'])).
% 0.45/0.64  thf('41', plain,
% 0.45/0.64      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.45/0.64          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['0', '3'])).
% 0.45/0.64  thf('42', plain,
% 0.45/0.64      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.45/0.64        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['40', '41'])).
% 0.45/0.64  thf('43', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['5', '42'])).
% 0.45/0.64  thf('44', plain, ((v1_relat_1 @ sk_D)),
% 0.45/0.64      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.64  thf('45', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.45/0.64      inference('demod', [status(thm)], ['43', '44'])).
% 0.45/0.64  thf(t3_funct_2, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.64       ( ( v1_funct_1 @ A ) & 
% 0.45/0.64         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.45/0.64         ( m1_subset_1 @
% 0.45/0.64           A @ 
% 0.45/0.64           ( k1_zfmisc_1 @
% 0.45/0.64             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.45/0.64  thf('46', plain,
% 0.45/0.64      (![X40 : $i]:
% 0.45/0.64         ((m1_subset_1 @ X40 @ 
% 0.45/0.64           (k1_zfmisc_1 @ 
% 0.45/0.64            (k2_zfmisc_1 @ (k1_relat_1 @ X40) @ (k2_relat_1 @ X40))))
% 0.45/0.64          | ~ (v1_funct_1 @ X40)
% 0.45/0.64          | ~ (v1_relat_1 @ X40))),
% 0.45/0.64      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.45/0.64  thf(t3_subset, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.64  thf('47', plain,
% 0.45/0.64      (![X18 : $i, X19 : $i]:
% 0.45/0.64         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.64  thf('48', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | (r1_tarski @ X0 @ 
% 0.45/0.64             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['46', '47'])).
% 0.45/0.64  thf('49', plain,
% 0.45/0.64      (((r1_tarski @ sk_D @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_relat_1 @ sk_D)))
% 0.45/0.64        | ~ (v1_funct_1 @ sk_D)
% 0.45/0.64        | ~ (v1_relat_1 @ sk_D))),
% 0.45/0.64      inference('sup+', [status(thm)], ['45', '48'])).
% 0.45/0.64  thf(t113_zfmisc_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.45/0.64       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.45/0.64  thf('50', plain,
% 0.45/0.64      (![X11 : $i, X12 : $i]:
% 0.45/0.64         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 0.45/0.64          | ((X11) != (k1_xboole_0)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.45/0.64  thf('51', plain,
% 0.45/0.64      (![X12 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 0.45/0.64      inference('simplify', [status(thm)], ['50'])).
% 0.45/0.64  thf('52', plain, ((v1_funct_1 @ sk_D)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('53', plain, ((v1_relat_1 @ sk_D)),
% 0.45/0.64      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.64  thf('54', plain, ((r1_tarski @ sk_D @ k1_xboole_0)),
% 0.45/0.64      inference('demod', [status(thm)], ['49', '51', '52', '53'])).
% 0.45/0.64  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.45/0.64  thf('55', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.45/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.64  thf(d10_xboole_0, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.64  thf('56', plain,
% 0.45/0.64      (![X0 : $i, X2 : $i]:
% 0.45/0.64         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.45/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.64  thf('57', plain,
% 0.45/0.64      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['55', '56'])).
% 0.45/0.64  thf('58', plain, (((sk_D) = (k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['54', '57'])).
% 0.45/0.64  thf(t150_relat_1, axiom,
% 0.45/0.64    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.45/0.64  thf('59', plain,
% 0.45/0.64      (![X23 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X23) = (k1_xboole_0))),
% 0.45/0.64      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.45/0.64  thf('60', plain, (((sk_D) = (k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['54', '57'])).
% 0.45/0.64  thf('61', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.45/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.64  thf('62', plain, ($false),
% 0.45/0.64      inference('demod', [status(thm)], ['4', '58', '59', '60', '61'])).
% 0.45/0.64  
% 0.45/0.64  % SZS output end Refutation
% 0.45/0.64  
% 0.50/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
