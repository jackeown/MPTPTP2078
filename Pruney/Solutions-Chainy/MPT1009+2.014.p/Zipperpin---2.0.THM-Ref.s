%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lA9lAcEVKc

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:50 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 393 expanded)
%              Number of leaves         :   33 ( 135 expanded)
%              Depth                    :   16
%              Number of atoms          :  793 (4955 expanded)
%              Number of equality atoms :   49 ( 229 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X58 ) ) )
      | ( ( k7_relset_1 @ X57 @ X58 @ X56 @ X59 )
        = ( k9_relat_1 @ X56 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X60: $i] :
      ( ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X60 ) @ ( k2_relat_1 @ X60 ) ) ) )
      | ~ ( v1_funct_1 @ X60 )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('6',plain,(
    ! [X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X58 ) ) )
      | ( ( k7_relset_1 @ X57 @ X58 @ X56 @ X59 )
        = ( k9_relat_1 @ X56 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X60: $i] :
      ( ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X60 ) @ ( k2_relat_1 @ X60 ) ) ) )
      | ~ ( v1_funct_1 @ X60 )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('9',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X53 @ X54 @ X52 @ X55 ) @ ( k1_zfmisc_1 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k9_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( m1_subset_1 @ ( k9_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_tarski @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( v4_relat_1 @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('17',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( v4_relat_1 @ X41 @ X42 )
      | ( r1_tarski @ ( k1_relat_1 @ X41 ) @ X42 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('21',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( v1_relat_1 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('22',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['19','22'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('24',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X33
        = ( k1_tarski @ X32 ) )
      | ( X33 = k1_xboole_0 )
      | ~ ( r1_tarski @ X33 @ ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('25',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('26',plain,(
    ! [X44: $i,X45: $i] :
      ( ( ( k1_relat_1 @ X45 )
       != ( k1_tarski @ X44 ) )
      | ( ( k2_relat_1 @ X45 )
        = ( k1_tarski @ ( k1_funct_1 @ X45 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['27'])).

thf('29',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['20','21'])).

thf('31',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['20','21'])).

thf('38',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X60: $i] :
      ( ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X60 ) @ ( k2_relat_1 @ X60 ) ) ) )
      | ~ ( v1_funct_1 @ X60 )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('41',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_tarski @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) @ X0 )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ sk_D ) ) @ sk_D )
    | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('46',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k2_zfmisc_1 @ X36 @ X37 )
        = k1_xboole_0 )
      | ( X36 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('47',plain,(
    ! [X37: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X37 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('48',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('49',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('50',plain,(
    ! [X37: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X37 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('51',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['20','21'])).

thf('52',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['45','47','48','49','50','51','52'])).

thf('54',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('55',plain,(
    ! [X38: $i,X40: $i] :
      ( ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X40 ) )
      | ~ ( r1_tarski @ X38 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('56',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X53 @ X54 @ X52 @ X55 ) @ ( k1_zfmisc_1 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_tarski @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k7_relset_1 @ X2 @ X0 @ k1_xboole_0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relset_1 @ X1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('66',plain,(
    ! [X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X58 ) ) )
      | ( ( k7_relset_1 @ X57 @ X58 @ X56 @ X59 )
        = ( k9_relat_1 @ X56 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k9_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['45','47','48','49','50','51','52'])).

thf('70',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['4','53','68','69','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lA9lAcEVKc
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:00:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.47/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.66  % Solved by: fo/fo7.sh
% 0.47/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.66  % done 345 iterations in 0.195s
% 0.47/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.66  % SZS output start Refutation
% 0.47/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.66  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.47/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.66  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.47/0.66  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.47/0.66  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.47/0.66  thf(sk_D_type, type, sk_D: $i).
% 0.47/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.66  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.47/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.66  thf(t64_funct_2, conjecture,
% 0.47/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.66     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.47/0.66         ( m1_subset_1 @
% 0.47/0.66           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.47/0.66       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.47/0.66         ( r1_tarski @
% 0.47/0.66           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.47/0.66           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.47/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.66    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.66        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.47/0.66            ( m1_subset_1 @
% 0.47/0.66              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.47/0.66          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.47/0.66            ( r1_tarski @
% 0.47/0.66              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.47/0.66              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.47/0.66    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.47/0.66  thf('0', plain,
% 0.47/0.66      (~ (r1_tarski @ 
% 0.47/0.66          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.47/0.66          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('1', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_D @ 
% 0.47/0.66        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(redefinition_k7_relset_1, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.66       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.47/0.66  thf('2', plain,
% 0.47/0.66      (![X56 : $i, X57 : $i, X58 : $i, X59 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X58)))
% 0.47/0.66          | ((k7_relset_1 @ X57 @ X58 @ X56 @ X59) = (k9_relat_1 @ X56 @ X59)))),
% 0.47/0.66      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.47/0.66  thf('3', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.47/0.66           = (k9_relat_1 @ sk_D @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.66  thf('4', plain,
% 0.47/0.66      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.47/0.66          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['0', '3'])).
% 0.47/0.66  thf(t3_funct_2, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.66       ( ( v1_funct_1 @ A ) & 
% 0.47/0.66         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.47/0.66         ( m1_subset_1 @
% 0.47/0.66           A @ 
% 0.47/0.66           ( k1_zfmisc_1 @
% 0.47/0.66             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.47/0.66  thf('5', plain,
% 0.47/0.66      (![X60 : $i]:
% 0.47/0.66         ((m1_subset_1 @ X60 @ 
% 0.47/0.66           (k1_zfmisc_1 @ 
% 0.47/0.66            (k2_zfmisc_1 @ (k1_relat_1 @ X60) @ (k2_relat_1 @ X60))))
% 0.47/0.66          | ~ (v1_funct_1 @ X60)
% 0.47/0.66          | ~ (v1_relat_1 @ X60))),
% 0.47/0.66      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.47/0.66  thf('6', plain,
% 0.47/0.66      (![X56 : $i, X57 : $i, X58 : $i, X59 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X58)))
% 0.47/0.66          | ((k7_relset_1 @ X57 @ X58 @ X56 @ X59) = (k9_relat_1 @ X56 @ X59)))),
% 0.47/0.66      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.47/0.66  thf('7', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ X0)
% 0.47/0.66          | ~ (v1_funct_1 @ X0)
% 0.47/0.66          | ((k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1)
% 0.47/0.66              = (k9_relat_1 @ X0 @ X1)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['5', '6'])).
% 0.47/0.66  thf('8', plain,
% 0.47/0.66      (![X60 : $i]:
% 0.47/0.66         ((m1_subset_1 @ X60 @ 
% 0.47/0.66           (k1_zfmisc_1 @ 
% 0.47/0.66            (k2_zfmisc_1 @ (k1_relat_1 @ X60) @ (k2_relat_1 @ X60))))
% 0.47/0.66          | ~ (v1_funct_1 @ X60)
% 0.47/0.66          | ~ (v1_relat_1 @ X60))),
% 0.47/0.66      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.47/0.66  thf(dt_k7_relset_1, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.66       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.47/0.66  thf('9', plain,
% 0.47/0.66      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54)))
% 0.47/0.66          | (m1_subset_1 @ (k7_relset_1 @ X53 @ X54 @ X52 @ X55) @ 
% 0.47/0.66             (k1_zfmisc_1 @ X54)))),
% 0.47/0.66      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.47/0.66  thf('10', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ X0)
% 0.47/0.66          | ~ (v1_funct_1 @ X0)
% 0.47/0.66          | (m1_subset_1 @ 
% 0.47/0.66             (k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1) @ 
% 0.47/0.66             (k1_zfmisc_1 @ (k2_relat_1 @ X0))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['8', '9'])).
% 0.47/0.66  thf('11', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((m1_subset_1 @ (k9_relat_1 @ X1 @ X0) @ 
% 0.47/0.66           (k1_zfmisc_1 @ (k2_relat_1 @ X1)))
% 0.47/0.66          | ~ (v1_funct_1 @ X1)
% 0.47/0.66          | ~ (v1_relat_1 @ X1)
% 0.47/0.66          | ~ (v1_funct_1 @ X1)
% 0.47/0.66          | ~ (v1_relat_1 @ X1))),
% 0.47/0.66      inference('sup+', [status(thm)], ['7', '10'])).
% 0.47/0.66  thf('12', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ X1)
% 0.47/0.66          | ~ (v1_funct_1 @ X1)
% 0.47/0.66          | (m1_subset_1 @ (k9_relat_1 @ X1 @ X0) @ 
% 0.47/0.66             (k1_zfmisc_1 @ (k2_relat_1 @ X1))))),
% 0.47/0.66      inference('simplify', [status(thm)], ['11'])).
% 0.47/0.66  thf(t3_subset, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.47/0.66  thf('13', plain,
% 0.47/0.66      (![X38 : $i, X39 : $i]:
% 0.47/0.66         ((r1_tarski @ X38 @ X39) | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39)))),
% 0.47/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.66  thf('14', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (v1_funct_1 @ X0)
% 0.47/0.66          | ~ (v1_relat_1 @ X0)
% 0.47/0.66          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ (k2_relat_1 @ X0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['12', '13'])).
% 0.47/0.66  thf('15', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_D @ 
% 0.47/0.66        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(cc2_relset_1, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.66       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.47/0.66  thf('16', plain,
% 0.47/0.66      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.47/0.66         ((v4_relat_1 @ X49 @ X50)
% 0.47/0.66          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51))))),
% 0.47/0.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.66  thf('17', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['15', '16'])).
% 0.47/0.66  thf(d18_relat_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( v1_relat_1 @ B ) =>
% 0.47/0.66       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.47/0.66  thf('18', plain,
% 0.47/0.66      (![X41 : $i, X42 : $i]:
% 0.47/0.66         (~ (v4_relat_1 @ X41 @ X42)
% 0.47/0.66          | (r1_tarski @ (k1_relat_1 @ X41) @ X42)
% 0.47/0.66          | ~ (v1_relat_1 @ X41))),
% 0.47/0.66      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.47/0.66  thf('19', plain,
% 0.47/0.66      ((~ (v1_relat_1 @ sk_D)
% 0.47/0.66        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['17', '18'])).
% 0.47/0.66  thf('20', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_D @ 
% 0.47/0.66        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(cc1_relset_1, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.66       ( v1_relat_1 @ C ) ))).
% 0.47/0.66  thf('21', plain,
% 0.47/0.66      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.47/0.66         ((v1_relat_1 @ X46)
% 0.47/0.66          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48))))),
% 0.47/0.66      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.47/0.66  thf('22', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.66      inference('sup-', [status(thm)], ['20', '21'])).
% 0.47/0.66  thf('23', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.47/0.66      inference('demod', [status(thm)], ['19', '22'])).
% 0.47/0.66  thf(l3_zfmisc_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.47/0.66       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.47/0.66  thf('24', plain,
% 0.47/0.66      (![X32 : $i, X33 : $i]:
% 0.47/0.66         (((X33) = (k1_tarski @ X32))
% 0.47/0.66          | ((X33) = (k1_xboole_0))
% 0.47/0.66          | ~ (r1_tarski @ X33 @ (k1_tarski @ X32)))),
% 0.47/0.66      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.47/0.66  thf('25', plain,
% 0.47/0.66      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.47/0.66        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['23', '24'])).
% 0.47/0.66  thf(t14_funct_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.66       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.47/0.66         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.47/0.66  thf('26', plain,
% 0.47/0.66      (![X44 : $i, X45 : $i]:
% 0.47/0.66         (((k1_relat_1 @ X45) != (k1_tarski @ X44))
% 0.47/0.66          | ((k2_relat_1 @ X45) = (k1_tarski @ (k1_funct_1 @ X45 @ X44)))
% 0.47/0.66          | ~ (v1_funct_1 @ X45)
% 0.47/0.66          | ~ (v1_relat_1 @ X45))),
% 0.47/0.66      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.47/0.66  thf('27', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.47/0.66          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.47/0.66          | ~ (v1_relat_1 @ X0)
% 0.47/0.66          | ~ (v1_funct_1 @ X0)
% 0.47/0.66          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['25', '26'])).
% 0.47/0.66  thf('28', plain,
% 0.47/0.66      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.47/0.66        | ~ (v1_funct_1 @ sk_D)
% 0.47/0.66        | ~ (v1_relat_1 @ sk_D)
% 0.47/0.66        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.47/0.66      inference('eq_res', [status(thm)], ['27'])).
% 0.47/0.66  thf('29', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('30', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.66      inference('sup-', [status(thm)], ['20', '21'])).
% 0.47/0.66  thf('31', plain,
% 0.47/0.66      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.47/0.66        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.47/0.66      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.47/0.66  thf('32', plain,
% 0.47/0.66      (~ (r1_tarski @ 
% 0.47/0.66          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.47/0.66          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('33', plain,
% 0.47/0.66      ((~ (r1_tarski @ 
% 0.47/0.66           (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.47/0.66           (k2_relat_1 @ sk_D))
% 0.47/0.66        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['31', '32'])).
% 0.47/0.66  thf('34', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.47/0.66           = (k9_relat_1 @ sk_D @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.66  thf('35', plain,
% 0.47/0.66      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.47/0.66        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.47/0.66      inference('demod', [status(thm)], ['33', '34'])).
% 0.47/0.66  thf('36', plain,
% 0.47/0.66      ((~ (v1_relat_1 @ sk_D)
% 0.47/0.66        | ~ (v1_funct_1 @ sk_D)
% 0.47/0.66        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['14', '35'])).
% 0.47/0.66  thf('37', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.66      inference('sup-', [status(thm)], ['20', '21'])).
% 0.47/0.66  thf('38', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('39', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.47/0.66      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.47/0.66  thf('40', plain,
% 0.47/0.66      (![X60 : $i]:
% 0.47/0.66         ((m1_subset_1 @ X60 @ 
% 0.47/0.66           (k1_zfmisc_1 @ 
% 0.47/0.66            (k2_zfmisc_1 @ (k1_relat_1 @ X60) @ (k2_relat_1 @ X60))))
% 0.47/0.66          | ~ (v1_funct_1 @ X60)
% 0.47/0.66          | ~ (v1_relat_1 @ X60))),
% 0.47/0.66      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.47/0.66  thf('41', plain,
% 0.47/0.66      (![X38 : $i, X39 : $i]:
% 0.47/0.66         ((r1_tarski @ X38 @ X39) | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39)))),
% 0.47/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.66  thf('42', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ X0)
% 0.47/0.66          | ~ (v1_funct_1 @ X0)
% 0.47/0.66          | (r1_tarski @ X0 @ 
% 0.47/0.66             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['40', '41'])).
% 0.47/0.66  thf(d10_xboole_0, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.66  thf('43', plain,
% 0.47/0.66      (![X0 : $i, X2 : $i]:
% 0.47/0.66         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.47/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.66  thf('44', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v1_funct_1 @ X0)
% 0.47/0.66          | ~ (v1_relat_1 @ X0)
% 0.47/0.66          | ~ (r1_tarski @ 
% 0.47/0.66               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ X0)
% 0.47/0.66          | ((k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) = (X0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['42', '43'])).
% 0.47/0.66  thf('45', plain,
% 0.47/0.66      ((~ (r1_tarski @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_relat_1 @ sk_D)) @ sk_D)
% 0.47/0.66        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D)) = (sk_D))
% 0.47/0.66        | ~ (v1_relat_1 @ sk_D)
% 0.47/0.66        | ~ (v1_funct_1 @ sk_D))),
% 0.47/0.66      inference('sup-', [status(thm)], ['39', '44'])).
% 0.47/0.66  thf(t113_zfmisc_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.47/0.66       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.47/0.66  thf('46', plain,
% 0.47/0.66      (![X36 : $i, X37 : $i]:
% 0.47/0.66         (((k2_zfmisc_1 @ X36 @ X37) = (k1_xboole_0))
% 0.47/0.66          | ((X36) != (k1_xboole_0)))),
% 0.47/0.66      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.47/0.66  thf('47', plain,
% 0.47/0.66      (![X37 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X37) = (k1_xboole_0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['46'])).
% 0.47/0.66  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.47/0.66  thf('48', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.47/0.66      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.47/0.66  thf('49', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.47/0.66      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.47/0.66  thf('50', plain,
% 0.47/0.66      (![X37 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X37) = (k1_xboole_0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['46'])).
% 0.47/0.66  thf('51', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.66      inference('sup-', [status(thm)], ['20', '21'])).
% 0.47/0.66  thf('52', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('53', plain, (((k1_xboole_0) = (sk_D))),
% 0.47/0.66      inference('demod', [status(thm)],
% 0.47/0.66                ['45', '47', '48', '49', '50', '51', '52'])).
% 0.47/0.66  thf('54', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.47/0.66      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.47/0.66  thf('55', plain,
% 0.47/0.66      (![X38 : $i, X40 : $i]:
% 0.47/0.66         ((m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X40)) | ~ (r1_tarski @ X38 @ X40))),
% 0.47/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.66  thf('56', plain,
% 0.47/0.66      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['54', '55'])).
% 0.47/0.66  thf('57', plain,
% 0.47/0.66      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54)))
% 0.47/0.66          | (m1_subset_1 @ (k7_relset_1 @ X53 @ X54 @ X52 @ X55) @ 
% 0.47/0.66             (k1_zfmisc_1 @ X54)))),
% 0.47/0.66      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.47/0.66  thf('58', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         (m1_subset_1 @ (k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2) @ 
% 0.47/0.66          (k1_zfmisc_1 @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['56', '57'])).
% 0.47/0.66  thf('59', plain,
% 0.47/0.66      (![X38 : $i, X39 : $i]:
% 0.47/0.66         ((r1_tarski @ X38 @ X39) | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39)))),
% 0.47/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.66  thf('60', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         (r1_tarski @ (k7_relset_1 @ X2 @ X0 @ k1_xboole_0 @ X1) @ X0)),
% 0.47/0.66      inference('sup-', [status(thm)], ['58', '59'])).
% 0.47/0.66  thf('61', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.47/0.66      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.47/0.66  thf('62', plain,
% 0.47/0.66      (![X0 : $i, X2 : $i]:
% 0.47/0.66         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.47/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.66  thf('63', plain,
% 0.47/0.66      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['61', '62'])).
% 0.47/0.66  thf('64', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((k7_relset_1 @ X1 @ k1_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['60', '63'])).
% 0.47/0.66  thf('65', plain,
% 0.47/0.66      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['54', '55'])).
% 0.47/0.66  thf('66', plain,
% 0.47/0.66      (![X56 : $i, X57 : $i, X58 : $i, X59 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X58)))
% 0.47/0.66          | ((k7_relset_1 @ X57 @ X58 @ X56 @ X59) = (k9_relat_1 @ X56 @ X59)))),
% 0.47/0.66      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.47/0.66  thf('67', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         ((k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 0.47/0.66           = (k9_relat_1 @ k1_xboole_0 @ X2))),
% 0.47/0.66      inference('sup-', [status(thm)], ['65', '66'])).
% 0.47/0.66  thf('68', plain,
% 0.47/0.66      (![X0 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.47/0.66      inference('demod', [status(thm)], ['64', '67'])).
% 0.47/0.66  thf('69', plain, (((k1_xboole_0) = (sk_D))),
% 0.47/0.66      inference('demod', [status(thm)],
% 0.47/0.66                ['45', '47', '48', '49', '50', '51', '52'])).
% 0.47/0.66  thf('70', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.47/0.66      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.47/0.66  thf('71', plain, ($false),
% 0.47/0.66      inference('demod', [status(thm)], ['4', '53', '68', '69', '70'])).
% 0.47/0.66  
% 0.47/0.66  % SZS output end Refutation
% 0.47/0.66  
% 0.47/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
