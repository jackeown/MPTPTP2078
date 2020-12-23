%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lY1Kk4o1hU

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:38 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 463 expanded)
%              Number of leaves         :   36 ( 148 expanded)
%              Depth                    :   19
%              Number of atoms          :  837 (5877 expanded)
%              Number of equality atoms :   95 ( 554 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(t62_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
          = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
            = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k8_relset_1 @ A @ B @ C @ B )
          = A ) ) ) )).

thf('1',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( X61 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X60 )
      | ~ ( v1_funct_2 @ X60 @ X59 @ X61 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X61 ) ) )
      | ( ( k8_relset_1 @ X59 @ X61 @ X60 @ X61 )
        = X59 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_2])).

thf('2',plain,
    ( ( ( k8_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C @ sk_B )
      = ( k1_tarski @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('4',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) )
      | ( ( k8_relset_1 @ X56 @ X57 @ X55 @ X58 )
        = ( k10_relat_1 @ X55 @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k1_tarski @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','5','6','7'])).

thf('9',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( v4_relat_1 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('13',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('14',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v4_relat_1 @ X37 @ X38 )
      | ( r1_tarski @ ( k1_relat_1 @ X37 ) @ X38 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('17',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( v1_relat_1 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('18',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['15','18'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('20',plain,(
    ! [X2: $i] :
      ( ( k2_tarski @ X2 @ X2 )
      = ( k1_tarski @ X2 ) ) ),
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

thf('21',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X32
        = ( k2_tarski @ X30 @ X31 ) )
      | ( X32
        = ( k1_tarski @ X31 ) )
      | ( X32
        = ( k1_tarski @ X30 ) )
      | ( X32 = k1_xboole_0 )
      | ~ ( r1_tarski @ X32 @ ( k2_tarski @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_tarski @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,(
    ! [X2: $i] :
      ( ( k2_tarski @ X2 @ X2 )
      = ( k1_tarski @ X2 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('26',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('28',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k1_relat_1 @ X41 )
       != ( k1_tarski @ X40 ) )
      | ( ( k2_relat_1 @ X41 )
        = ( k1_tarski @ ( k1_funct_1 @ X41 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf('33',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('36',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( ( k2_relset_1 @ X53 @ X54 @ X52 )
        = ( k2_relat_1 @ X52 ) )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('37',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['33','38'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('40',plain,(
    ! [X39: $i] :
      ( ( ( k1_relat_1 @ X39 )
       != k1_xboole_0 )
      | ( X39 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('41',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf('43',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['43'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('46',plain,(
    ! [X34: $i,X36: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( r1_tarski @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('48',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X49 @ X50 @ X48 @ X51 ) @ ( k1_zfmisc_1 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('51',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) )
      | ( ( k8_relset_1 @ X56 @ X57 @ X55 @ X58 )
        = ( k10_relat_1 @ X55 @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k10_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k10_relat_1 @ k1_xboole_0 @ X2 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ k1_xboole_0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('56',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['10','44','57'])).

thf('59',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['33','38'])).

thf('60',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k1_relat_1 @ X41 )
       != ( k1_tarski @ X40 ) )
      | ( ( k2_relat_1 @ X41 )
        = ( k1_tarski @ ( k1_funct_1 @ X41 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k2_relat_1 @ sk_C )
        = ( k1_tarski @ ( k1_funct_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf('63',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_C )
        = ( k1_tarski @ ( k1_funct_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['43'])).

thf('66',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['43'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','67'])).

thf('69',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('71',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['43'])).

thf('72',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['43'])).

thf('73',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['69','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lY1Kk4o1hU
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:42:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.41/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.58  % Solved by: fo/fo7.sh
% 0.41/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.58  % done 514 iterations in 0.132s
% 0.41/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.58  % SZS output start Refutation
% 0.41/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.41/0.58  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.41/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.58  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.41/0.58  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.41/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.58  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.41/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.58  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.41/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.41/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.58  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.41/0.58  thf(t62_funct_2, conjecture,
% 0.41/0.58    (![A:$i,B:$i,C:$i]:
% 0.41/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.41/0.58         ( m1_subset_1 @
% 0.41/0.58           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.41/0.58       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.41/0.58         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.41/0.58           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.41/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.41/0.58        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.41/0.58            ( m1_subset_1 @
% 0.41/0.58              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.41/0.58          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.41/0.58            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.41/0.58              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.41/0.58    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.41/0.58  thf('0', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_C @ 
% 0.41/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(t48_funct_2, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i]:
% 0.41/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.41/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.58       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.58         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ))).
% 0.41/0.58  thf('1', plain,
% 0.41/0.58      (![X59 : $i, X60 : $i, X61 : $i]:
% 0.41/0.58         (((X61) = (k1_xboole_0))
% 0.41/0.58          | ~ (v1_funct_1 @ X60)
% 0.41/0.58          | ~ (v1_funct_2 @ X60 @ X59 @ X61)
% 0.41/0.58          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X61)))
% 0.41/0.58          | ((k8_relset_1 @ X59 @ X61 @ X60 @ X61) = (X59)))),
% 0.41/0.58      inference('cnf', [status(esa)], [t48_funct_2])).
% 0.41/0.58  thf('2', plain,
% 0.41/0.58      ((((k8_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C @ sk_B)
% 0.41/0.58          = (k1_tarski @ sk_A))
% 0.41/0.58        | ~ (v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)
% 0.41/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.41/0.58        | ((sk_B) = (k1_xboole_0)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.41/0.58  thf('3', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_C @ 
% 0.41/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(redefinition_k8_relset_1, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.58       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.41/0.58  thf('4', plain,
% 0.41/0.58      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 0.41/0.58         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57)))
% 0.41/0.58          | ((k8_relset_1 @ X56 @ X57 @ X55 @ X58) = (k10_relat_1 @ X55 @ X58)))),
% 0.41/0.58      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.41/0.58  thf('5', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         ((k8_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C @ X0)
% 0.41/0.58           = (k10_relat_1 @ sk_C @ X0))),
% 0.41/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.41/0.58  thf('6', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('8', plain,
% 0.41/0.58      ((((k10_relat_1 @ sk_C @ sk_B) = (k1_tarski @ sk_A))
% 0.41/0.58        | ((sk_B) = (k1_xboole_0)))),
% 0.41/0.58      inference('demod', [status(thm)], ['2', '5', '6', '7'])).
% 0.41/0.58  thf('9', plain, (((sk_B) != (k1_xboole_0))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('10', plain, (((k10_relat_1 @ sk_C @ sk_B) = (k1_tarski @ sk_A))),
% 0.41/0.58      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.41/0.58  thf('11', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_C @ 
% 0.41/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(cc2_relset_1, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i]:
% 0.41/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.58       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.41/0.58  thf('12', plain,
% 0.41/0.58      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.41/0.58         ((v4_relat_1 @ X45 @ X46)
% 0.41/0.58          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47))))),
% 0.41/0.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.41/0.58  thf('13', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 0.41/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.58  thf(d18_relat_1, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( v1_relat_1 @ B ) =>
% 0.41/0.58       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.41/0.58  thf('14', plain,
% 0.41/0.58      (![X37 : $i, X38 : $i]:
% 0.41/0.58         (~ (v4_relat_1 @ X37 @ X38)
% 0.41/0.58          | (r1_tarski @ (k1_relat_1 @ X37) @ X38)
% 0.41/0.58          | ~ (v1_relat_1 @ X37))),
% 0.41/0.58      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.41/0.58  thf('15', plain,
% 0.41/0.58      ((~ (v1_relat_1 @ sk_C)
% 0.41/0.58        | (r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.41/0.58  thf('16', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_C @ 
% 0.41/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(cc1_relset_1, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i]:
% 0.41/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.58       ( v1_relat_1 @ C ) ))).
% 0.41/0.58  thf('17', plain,
% 0.41/0.58      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.41/0.58         ((v1_relat_1 @ X42)
% 0.41/0.58          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44))))),
% 0.41/0.58      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.41/0.58  thf('18', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.41/0.58  thf('19', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A))),
% 0.41/0.58      inference('demod', [status(thm)], ['15', '18'])).
% 0.41/0.58  thf(t69_enumset1, axiom,
% 0.41/0.58    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.41/0.58  thf('20', plain, (![X2 : $i]: ((k2_tarski @ X2 @ X2) = (k1_tarski @ X2))),
% 0.41/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.41/0.58  thf(l45_zfmisc_1, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i]:
% 0.41/0.58     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.41/0.58       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.41/0.58            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.41/0.58  thf('21', plain,
% 0.41/0.58      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.41/0.58         (((X32) = (k2_tarski @ X30 @ X31))
% 0.41/0.58          | ((X32) = (k1_tarski @ X31))
% 0.41/0.58          | ((X32) = (k1_tarski @ X30))
% 0.41/0.58          | ((X32) = (k1_xboole_0))
% 0.41/0.58          | ~ (r1_tarski @ X32 @ (k2_tarski @ X30 @ X31)))),
% 0.41/0.58      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.41/0.58  thf('22', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]:
% 0.41/0.58         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.41/0.58          | ((X1) = (k1_xboole_0))
% 0.41/0.58          | ((X1) = (k1_tarski @ X0))
% 0.41/0.58          | ((X1) = (k1_tarski @ X0))
% 0.41/0.58          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.41/0.58  thf('23', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]:
% 0.41/0.58         (((X1) = (k2_tarski @ X0 @ X0))
% 0.41/0.58          | ((X1) = (k1_tarski @ X0))
% 0.41/0.58          | ((X1) = (k1_xboole_0))
% 0.41/0.58          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.41/0.58      inference('simplify', [status(thm)], ['22'])).
% 0.41/0.58  thf('24', plain,
% 0.41/0.58      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.41/0.58        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.41/0.58        | ((k1_relat_1 @ sk_C) = (k2_tarski @ sk_A @ sk_A)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['19', '23'])).
% 0.41/0.58  thf('25', plain, (![X2 : $i]: ((k2_tarski @ X2 @ X2) = (k1_tarski @ X2))),
% 0.41/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.41/0.58  thf('26', plain,
% 0.41/0.58      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.41/0.58        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.41/0.58        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A)))),
% 0.41/0.58      inference('demod', [status(thm)], ['24', '25'])).
% 0.41/0.58  thf('27', plain,
% 0.41/0.58      ((((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.41/0.58        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.41/0.58      inference('simplify', [status(thm)], ['26'])).
% 0.41/0.58  thf(t14_funct_1, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.41/0.58       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.41/0.58         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.41/0.58  thf('28', plain,
% 0.41/0.58      (![X40 : $i, X41 : $i]:
% 0.41/0.58         (((k1_relat_1 @ X41) != (k1_tarski @ X40))
% 0.41/0.58          | ((k2_relat_1 @ X41) = (k1_tarski @ (k1_funct_1 @ X41 @ X40)))
% 0.41/0.58          | ~ (v1_funct_1 @ X41)
% 0.41/0.58          | ~ (v1_relat_1 @ X41))),
% 0.41/0.58      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.41/0.58  thf('29', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 0.41/0.58          | ((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.41/0.58          | ~ (v1_relat_1 @ X0)
% 0.41/0.58          | ~ (v1_funct_1 @ X0)
% 0.41/0.58          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.41/0.58      inference('sup-', [status(thm)], ['27', '28'])).
% 0.41/0.58  thf('30', plain,
% 0.41/0.58      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.41/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.41/0.58        | ~ (v1_relat_1 @ sk_C)
% 0.41/0.58        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.41/0.58      inference('eq_res', [status(thm)], ['29'])).
% 0.41/0.58  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('32', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.41/0.58  thf('33', plain,
% 0.41/0.58      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.41/0.58        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.41/0.58      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.41/0.58  thf('34', plain,
% 0.41/0.58      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)
% 0.41/0.58         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('35', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_C @ 
% 0.41/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(redefinition_k2_relset_1, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i]:
% 0.41/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.58       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.41/0.58  thf('36', plain,
% 0.41/0.58      (![X52 : $i, X53 : $i, X54 : $i]:
% 0.41/0.58         (((k2_relset_1 @ X53 @ X54 @ X52) = (k2_relat_1 @ X52))
% 0.41/0.58          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54))))),
% 0.41/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.41/0.58  thf('37', plain,
% 0.41/0.58      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.41/0.58      inference('sup-', [status(thm)], ['35', '36'])).
% 0.41/0.58  thf('38', plain,
% 0.41/0.58      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.41/0.58      inference('demod', [status(thm)], ['34', '37'])).
% 0.41/0.58  thf('39', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.41/0.58      inference('simplify_reflect-', [status(thm)], ['33', '38'])).
% 0.41/0.58  thf(t64_relat_1, axiom,
% 0.41/0.58    (![A:$i]:
% 0.41/0.58     ( ( v1_relat_1 @ A ) =>
% 0.41/0.58       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.41/0.58           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.58         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.41/0.58  thf('40', plain,
% 0.41/0.58      (![X39 : $i]:
% 0.41/0.58         (((k1_relat_1 @ X39) != (k1_xboole_0))
% 0.41/0.58          | ((X39) = (k1_xboole_0))
% 0.41/0.58          | ~ (v1_relat_1 @ X39))),
% 0.41/0.58      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.41/0.58  thf('41', plain,
% 0.41/0.58      ((((k1_xboole_0) != (k1_xboole_0))
% 0.41/0.58        | ~ (v1_relat_1 @ sk_C)
% 0.41/0.58        | ((sk_C) = (k1_xboole_0)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['39', '40'])).
% 0.41/0.58  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.41/0.58  thf('43', plain,
% 0.41/0.58      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.41/0.58      inference('demod', [status(thm)], ['41', '42'])).
% 0.41/0.58  thf('44', plain, (((sk_C) = (k1_xboole_0))),
% 0.41/0.58      inference('simplify', [status(thm)], ['43'])).
% 0.41/0.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.41/0.58  thf('45', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.41/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.41/0.58  thf(t3_subset, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.41/0.58  thf('46', plain,
% 0.41/0.58      (![X34 : $i, X36 : $i]:
% 0.41/0.58         ((m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X36)) | ~ (r1_tarski @ X34 @ X36))),
% 0.41/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.41/0.58  thf('47', plain,
% 0.41/0.58      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.41/0.58      inference('sup-', [status(thm)], ['45', '46'])).
% 0.41/0.58  thf(dt_k8_relset_1, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.58       ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.41/0.58  thf('48', plain,
% 0.41/0.58      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 0.41/0.58         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 0.41/0.58          | (m1_subset_1 @ (k8_relset_1 @ X49 @ X50 @ X48 @ X51) @ 
% 0.41/0.58             (k1_zfmisc_1 @ X49)))),
% 0.41/0.58      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 0.41/0.58  thf('49', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.58         (m1_subset_1 @ (k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2) @ 
% 0.41/0.58          (k1_zfmisc_1 @ X1))),
% 0.41/0.58      inference('sup-', [status(thm)], ['47', '48'])).
% 0.41/0.58  thf('50', plain,
% 0.41/0.58      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.41/0.58      inference('sup-', [status(thm)], ['45', '46'])).
% 0.41/0.58  thf('51', plain,
% 0.41/0.58      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 0.41/0.58         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57)))
% 0.41/0.58          | ((k8_relset_1 @ X56 @ X57 @ X55 @ X58) = (k10_relat_1 @ X55 @ X58)))),
% 0.41/0.58      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.41/0.58  thf('52', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.58         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 0.41/0.58           = (k10_relat_1 @ k1_xboole_0 @ X2))),
% 0.41/0.58      inference('sup-', [status(thm)], ['50', '51'])).
% 0.41/0.58  thf('53', plain,
% 0.41/0.58      (![X1 : $i, X2 : $i]:
% 0.41/0.58         (m1_subset_1 @ (k10_relat_1 @ k1_xboole_0 @ X2) @ (k1_zfmisc_1 @ X1))),
% 0.41/0.58      inference('demod', [status(thm)], ['49', '52'])).
% 0.41/0.58  thf('54', plain,
% 0.41/0.58      (![X34 : $i, X35 : $i]:
% 0.41/0.58         ((r1_tarski @ X34 @ X35) | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35)))),
% 0.41/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.41/0.58  thf('55', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]: (r1_tarski @ (k10_relat_1 @ k1_xboole_0 @ X1) @ X0)),
% 0.41/0.58      inference('sup-', [status(thm)], ['53', '54'])).
% 0.41/0.58  thf(t3_xboole_1, axiom,
% 0.41/0.58    (![A:$i]:
% 0.41/0.58     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.41/0.58  thf('56', plain,
% 0.41/0.58      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ k1_xboole_0))),
% 0.41/0.58      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.41/0.58  thf('57', plain,
% 0.41/0.58      (![X0 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.41/0.58      inference('sup-', [status(thm)], ['55', '56'])).
% 0.41/0.58  thf('58', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.41/0.58      inference('demod', [status(thm)], ['10', '44', '57'])).
% 0.41/0.58  thf('59', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.41/0.58      inference('simplify_reflect-', [status(thm)], ['33', '38'])).
% 0.41/0.58  thf('60', plain,
% 0.41/0.58      (![X40 : $i, X41 : $i]:
% 0.41/0.58         (((k1_relat_1 @ X41) != (k1_tarski @ X40))
% 0.41/0.58          | ((k2_relat_1 @ X41) = (k1_tarski @ (k1_funct_1 @ X41 @ X40)))
% 0.41/0.58          | ~ (v1_funct_1 @ X41)
% 0.41/0.58          | ~ (v1_relat_1 @ X41))),
% 0.41/0.58      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.41/0.58  thf('61', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.41/0.58          | ~ (v1_relat_1 @ sk_C)
% 0.41/0.58          | ~ (v1_funct_1 @ sk_C)
% 0.41/0.58          | ((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ X0))))),
% 0.41/0.58      inference('sup-', [status(thm)], ['59', '60'])).
% 0.41/0.58  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.41/0.58  thf('63', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('64', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.41/0.58          | ((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ X0))))),
% 0.41/0.58      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.41/0.58  thf('65', plain, (((sk_C) = (k1_xboole_0))),
% 0.41/0.58      inference('simplify', [status(thm)], ['43'])).
% 0.41/0.58  thf('66', plain, (((sk_C) = (k1_xboole_0))),
% 0.41/0.58      inference('simplify', [status(thm)], ['43'])).
% 0.41/0.58  thf('67', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.41/0.58          | ((k2_relat_1 @ k1_xboole_0)
% 0.41/0.58              = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.41/0.58      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.41/0.58  thf('68', plain,
% 0.41/0.58      ((((k1_xboole_0) != (k1_xboole_0))
% 0.41/0.58        | ((k2_relat_1 @ k1_xboole_0)
% 0.41/0.58            = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A))))),
% 0.41/0.58      inference('sup-', [status(thm)], ['58', '67'])).
% 0.41/0.58  thf('69', plain,
% 0.41/0.58      (((k2_relat_1 @ k1_xboole_0)
% 0.41/0.58         = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 0.41/0.58      inference('simplify', [status(thm)], ['68'])).
% 0.41/0.58  thf('70', plain,
% 0.41/0.58      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.41/0.58      inference('demod', [status(thm)], ['34', '37'])).
% 0.41/0.58  thf('71', plain, (((sk_C) = (k1_xboole_0))),
% 0.41/0.58      inference('simplify', [status(thm)], ['43'])).
% 0.41/0.58  thf('72', plain, (((sk_C) = (k1_xboole_0))),
% 0.41/0.58      inference('simplify', [status(thm)], ['43'])).
% 0.41/0.58  thf('73', plain,
% 0.41/0.58      (((k2_relat_1 @ k1_xboole_0)
% 0.41/0.58         != (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 0.41/0.58      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.41/0.58  thf('74', plain, ($false),
% 0.41/0.58      inference('simplify_reflect-', [status(thm)], ['69', '73'])).
% 0.41/0.58  
% 0.41/0.58  % SZS output end Refutation
% 0.41/0.58  
% 0.41/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
