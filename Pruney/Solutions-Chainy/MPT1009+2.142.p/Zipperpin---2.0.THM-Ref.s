%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zTr30rDNQa

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:09 EST 2020

% Result     : Theorem 1.10s
% Output     : Refutation 1.10s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 246 expanded)
%              Number of leaves         :   38 (  88 expanded)
%              Depth                    :   18
%              Number of atoms          :  712 (2612 expanded)
%              Number of equality atoms :   60 ( 153 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X60 ) ) )
      | ( ( k7_relset_1 @ X59 @ X60 @ X58 @ X61 )
        = ( k9_relat_1 @ X58 @ X61 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X45 @ X46 ) )
        = ( k9_relat_1 @ X45 @ X46 ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('6',plain,(
    ! [X51: $i,X52: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X51 @ X52 ) @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v1_relat_1 @ X48 )
      | ( r1_tarski @ ( k2_relat_1 @ X49 ) @ ( k2_relat_1 @ X48 ) )
      | ~ ( r1_tarski @ X49 @ X48 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X51: $i,X52: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X51 @ X52 ) @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X33: $i,X35: $i] :
      ( ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( r1_tarski @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('13',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ( v1_relat_1 @ X39 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['9','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ( v4_relat_1 @ X55 @ X56 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('21',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('22',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( v4_relat_1 @ X41 @ X42 )
      | ( r1_tarski @ ( k1_relat_1 @ X41 ) @ X42 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ( v1_relat_1 @ X39 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('27',plain,(
    ! [X43: $i,X44: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('28',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['23','28'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
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

thf('31',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X30
        = ( k2_tarski @ X28 @ X29 ) )
      | ( X30
        = ( k1_tarski @ X29 ) )
      | ( X30
        = ( k1_tarski @ X28 ) )
      | ( X30 = k1_xboole_0 )
      | ~ ( r1_tarski @ X30 @ ( k2_tarski @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k2_tarski @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('36',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('38',plain,(
    ! [X53: $i,X54: $i] :
      ( ( ( k1_relat_1 @ X54 )
       != ( k1_tarski @ X53 ) )
      | ( ( k2_relat_1 @ X54 )
        = ( k1_tarski @ ( k1_funct_1 @ X54 @ X53 ) ) )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['39'])).

thf('41',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['26','27'])).

thf('43',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('45',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['26','27'])).

thf('48',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['46','47'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('49',plain,(
    ! [X50: $i] :
      ( ( ( k1_relat_1 @ X50 )
       != k1_xboole_0 )
      | ( X50 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('50',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['26','27'])).

thf('52',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['52'])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('54',plain,(
    ! [X47: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X47 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('55',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['52'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('56',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('57',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_tarski @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['4','53','54','55','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zTr30rDNQa
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:50:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.10/1.31  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.10/1.31  % Solved by: fo/fo7.sh
% 1.10/1.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.10/1.31  % done 2514 iterations in 0.859s
% 1.10/1.31  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.10/1.31  % SZS output start Refutation
% 1.10/1.31  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.10/1.31  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.10/1.31  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.10/1.31  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.10/1.31  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.10/1.31  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.10/1.31  thf(sk_A_type, type, sk_A: $i).
% 1.10/1.31  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.10/1.31  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.10/1.31  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.10/1.31  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.10/1.31  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.10/1.31  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.10/1.31  thf(sk_C_type, type, sk_C: $i).
% 1.10/1.31  thf(sk_D_type, type, sk_D: $i).
% 1.10/1.31  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.10/1.31  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.10/1.31  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.10/1.31  thf(sk_B_type, type, sk_B: $i).
% 1.10/1.31  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.10/1.31  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.10/1.31  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.10/1.31  thf(t64_funct_2, conjecture,
% 1.10/1.31    (![A:$i,B:$i,C:$i,D:$i]:
% 1.10/1.31     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 1.10/1.31         ( m1_subset_1 @
% 1.10/1.31           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 1.10/1.31       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.10/1.31         ( r1_tarski @
% 1.10/1.31           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 1.10/1.31           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 1.10/1.31  thf(zf_stmt_0, negated_conjecture,
% 1.10/1.31    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.10/1.31        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 1.10/1.31            ( m1_subset_1 @
% 1.10/1.31              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 1.10/1.31          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.10/1.31            ( r1_tarski @
% 1.10/1.31              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 1.10/1.31              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 1.10/1.31    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 1.10/1.31  thf('0', plain,
% 1.10/1.31      (~ (r1_tarski @ 
% 1.10/1.31          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 1.10/1.31          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('1', plain,
% 1.10/1.31      ((m1_subset_1 @ sk_D @ 
% 1.10/1.31        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf(redefinition_k7_relset_1, axiom,
% 1.10/1.31    (![A:$i,B:$i,C:$i,D:$i]:
% 1.10/1.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.10/1.31       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 1.10/1.31  thf('2', plain,
% 1.10/1.31      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i]:
% 1.10/1.31         (~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X60)))
% 1.10/1.31          | ((k7_relset_1 @ X59 @ X60 @ X58 @ X61) = (k9_relat_1 @ X58 @ X61)))),
% 1.10/1.31      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.10/1.31  thf('3', plain,
% 1.10/1.31      (![X0 : $i]:
% 1.10/1.31         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 1.10/1.31           = (k9_relat_1 @ sk_D @ X0))),
% 1.10/1.31      inference('sup-', [status(thm)], ['1', '2'])).
% 1.10/1.31  thf('4', plain,
% 1.10/1.31      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 1.10/1.31          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 1.10/1.31      inference('demod', [status(thm)], ['0', '3'])).
% 1.10/1.31  thf(t148_relat_1, axiom,
% 1.10/1.31    (![A:$i,B:$i]:
% 1.10/1.31     ( ( v1_relat_1 @ B ) =>
% 1.10/1.31       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 1.10/1.31  thf('5', plain,
% 1.10/1.31      (![X45 : $i, X46 : $i]:
% 1.10/1.31         (((k2_relat_1 @ (k7_relat_1 @ X45 @ X46)) = (k9_relat_1 @ X45 @ X46))
% 1.10/1.31          | ~ (v1_relat_1 @ X45))),
% 1.10/1.31      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.10/1.31  thf(t88_relat_1, axiom,
% 1.10/1.31    (![A:$i,B:$i]:
% 1.10/1.31     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 1.10/1.31  thf('6', plain,
% 1.10/1.31      (![X51 : $i, X52 : $i]:
% 1.10/1.31         ((r1_tarski @ (k7_relat_1 @ X51 @ X52) @ X51) | ~ (v1_relat_1 @ X51))),
% 1.10/1.31      inference('cnf', [status(esa)], [t88_relat_1])).
% 1.10/1.31  thf(t25_relat_1, axiom,
% 1.10/1.31    (![A:$i]:
% 1.10/1.31     ( ( v1_relat_1 @ A ) =>
% 1.10/1.31       ( ![B:$i]:
% 1.10/1.31         ( ( v1_relat_1 @ B ) =>
% 1.10/1.31           ( ( r1_tarski @ A @ B ) =>
% 1.10/1.31             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 1.10/1.31               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 1.10/1.31  thf('7', plain,
% 1.10/1.31      (![X48 : $i, X49 : $i]:
% 1.10/1.31         (~ (v1_relat_1 @ X48)
% 1.10/1.31          | (r1_tarski @ (k2_relat_1 @ X49) @ (k2_relat_1 @ X48))
% 1.10/1.31          | ~ (r1_tarski @ X49 @ X48)
% 1.10/1.31          | ~ (v1_relat_1 @ X49))),
% 1.10/1.31      inference('cnf', [status(esa)], [t25_relat_1])).
% 1.10/1.31  thf('8', plain,
% 1.10/1.31      (![X0 : $i, X1 : $i]:
% 1.10/1.31         (~ (v1_relat_1 @ X0)
% 1.10/1.31          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 1.10/1.31          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 1.10/1.31             (k2_relat_1 @ X0))
% 1.10/1.31          | ~ (v1_relat_1 @ X0))),
% 1.10/1.31      inference('sup-', [status(thm)], ['6', '7'])).
% 1.10/1.31  thf('9', plain,
% 1.10/1.31      (![X0 : $i, X1 : $i]:
% 1.10/1.31         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 1.10/1.31           (k2_relat_1 @ X0))
% 1.10/1.31          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 1.10/1.31          | ~ (v1_relat_1 @ X0))),
% 1.10/1.31      inference('simplify', [status(thm)], ['8'])).
% 1.10/1.31  thf('10', plain,
% 1.10/1.31      (![X51 : $i, X52 : $i]:
% 1.10/1.31         ((r1_tarski @ (k7_relat_1 @ X51 @ X52) @ X51) | ~ (v1_relat_1 @ X51))),
% 1.10/1.31      inference('cnf', [status(esa)], [t88_relat_1])).
% 1.10/1.31  thf(t3_subset, axiom,
% 1.10/1.31    (![A:$i,B:$i]:
% 1.10/1.31     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.10/1.31  thf('11', plain,
% 1.10/1.31      (![X33 : $i, X35 : $i]:
% 1.10/1.31         ((m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X35)) | ~ (r1_tarski @ X33 @ X35))),
% 1.10/1.31      inference('cnf', [status(esa)], [t3_subset])).
% 1.10/1.31  thf('12', plain,
% 1.10/1.31      (![X0 : $i, X1 : $i]:
% 1.10/1.31         (~ (v1_relat_1 @ X0)
% 1.10/1.31          | (m1_subset_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 1.10/1.31      inference('sup-', [status(thm)], ['10', '11'])).
% 1.10/1.31  thf(cc2_relat_1, axiom,
% 1.10/1.31    (![A:$i]:
% 1.10/1.31     ( ( v1_relat_1 @ A ) =>
% 1.10/1.31       ( ![B:$i]:
% 1.10/1.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.10/1.31  thf('13', plain,
% 1.10/1.31      (![X39 : $i, X40 : $i]:
% 1.10/1.31         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40))
% 1.10/1.31          | (v1_relat_1 @ X39)
% 1.10/1.31          | ~ (v1_relat_1 @ X40))),
% 1.10/1.31      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.10/1.31  thf('14', plain,
% 1.10/1.31      (![X0 : $i, X1 : $i]:
% 1.10/1.31         (~ (v1_relat_1 @ X0)
% 1.10/1.31          | ~ (v1_relat_1 @ X0)
% 1.10/1.31          | (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 1.10/1.31      inference('sup-', [status(thm)], ['12', '13'])).
% 1.10/1.31  thf('15', plain,
% 1.10/1.31      (![X0 : $i, X1 : $i]:
% 1.10/1.31         ((v1_relat_1 @ (k7_relat_1 @ X0 @ X1)) | ~ (v1_relat_1 @ X0))),
% 1.10/1.31      inference('simplify', [status(thm)], ['14'])).
% 1.10/1.31  thf('16', plain,
% 1.10/1.31      (![X0 : $i, X1 : $i]:
% 1.10/1.31         (~ (v1_relat_1 @ X0)
% 1.10/1.31          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 1.10/1.31             (k2_relat_1 @ X0)))),
% 1.10/1.31      inference('clc', [status(thm)], ['9', '15'])).
% 1.10/1.31  thf('17', plain,
% 1.10/1.31      (![X0 : $i, X1 : $i]:
% 1.10/1.31         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1))
% 1.10/1.31          | ~ (v1_relat_1 @ X1)
% 1.10/1.31          | ~ (v1_relat_1 @ X1))),
% 1.10/1.31      inference('sup+', [status(thm)], ['5', '16'])).
% 1.10/1.31  thf('18', plain,
% 1.10/1.31      (![X0 : $i, X1 : $i]:
% 1.10/1.31         (~ (v1_relat_1 @ X1)
% 1.10/1.31          | (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1)))),
% 1.10/1.31      inference('simplify', [status(thm)], ['17'])).
% 1.10/1.31  thf('19', plain,
% 1.10/1.31      ((m1_subset_1 @ sk_D @ 
% 1.10/1.31        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf(cc2_relset_1, axiom,
% 1.10/1.31    (![A:$i,B:$i,C:$i]:
% 1.10/1.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.10/1.31       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.10/1.31  thf('20', plain,
% 1.10/1.31      (![X55 : $i, X56 : $i, X57 : $i]:
% 1.10/1.31         ((v4_relat_1 @ X55 @ X56)
% 1.10/1.31          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57))))),
% 1.10/1.31      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.10/1.31  thf('21', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 1.10/1.31      inference('sup-', [status(thm)], ['19', '20'])).
% 1.10/1.31  thf(d18_relat_1, axiom,
% 1.10/1.31    (![A:$i,B:$i]:
% 1.10/1.31     ( ( v1_relat_1 @ B ) =>
% 1.10/1.31       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.10/1.31  thf('22', plain,
% 1.10/1.31      (![X41 : $i, X42 : $i]:
% 1.10/1.31         (~ (v4_relat_1 @ X41 @ X42)
% 1.10/1.31          | (r1_tarski @ (k1_relat_1 @ X41) @ X42)
% 1.10/1.31          | ~ (v1_relat_1 @ X41))),
% 1.10/1.31      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.10/1.31  thf('23', plain,
% 1.10/1.31      ((~ (v1_relat_1 @ sk_D)
% 1.10/1.31        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 1.10/1.31      inference('sup-', [status(thm)], ['21', '22'])).
% 1.10/1.31  thf('24', plain,
% 1.10/1.31      ((m1_subset_1 @ sk_D @ 
% 1.10/1.31        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('25', plain,
% 1.10/1.31      (![X39 : $i, X40 : $i]:
% 1.10/1.31         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40))
% 1.10/1.31          | (v1_relat_1 @ X39)
% 1.10/1.31          | ~ (v1_relat_1 @ X40))),
% 1.10/1.31      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.10/1.31  thf('26', plain,
% 1.10/1.31      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 1.10/1.31        | (v1_relat_1 @ sk_D))),
% 1.10/1.31      inference('sup-', [status(thm)], ['24', '25'])).
% 1.10/1.31  thf(fc6_relat_1, axiom,
% 1.10/1.31    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.10/1.31  thf('27', plain,
% 1.10/1.31      (![X43 : $i, X44 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X43 @ X44))),
% 1.10/1.31      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.10/1.31  thf('28', plain, ((v1_relat_1 @ sk_D)),
% 1.10/1.31      inference('demod', [status(thm)], ['26', '27'])).
% 1.10/1.31  thf('29', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 1.10/1.31      inference('demod', [status(thm)], ['23', '28'])).
% 1.10/1.31  thf(t69_enumset1, axiom,
% 1.10/1.31    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.10/1.31  thf('30', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 1.10/1.31      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.10/1.31  thf(l45_zfmisc_1, axiom,
% 1.10/1.31    (![A:$i,B:$i,C:$i]:
% 1.10/1.31     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 1.10/1.31       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 1.10/1.31            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 1.10/1.31  thf('31', plain,
% 1.10/1.31      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.10/1.31         (((X30) = (k2_tarski @ X28 @ X29))
% 1.10/1.31          | ((X30) = (k1_tarski @ X29))
% 1.10/1.31          | ((X30) = (k1_tarski @ X28))
% 1.10/1.31          | ((X30) = (k1_xboole_0))
% 1.10/1.31          | ~ (r1_tarski @ X30 @ (k2_tarski @ X28 @ X29)))),
% 1.10/1.31      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 1.10/1.31  thf('32', plain,
% 1.10/1.31      (![X0 : $i, X1 : $i]:
% 1.10/1.31         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 1.10/1.31          | ((X1) = (k1_xboole_0))
% 1.10/1.31          | ((X1) = (k1_tarski @ X0))
% 1.10/1.31          | ((X1) = (k1_tarski @ X0))
% 1.10/1.31          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 1.10/1.31      inference('sup-', [status(thm)], ['30', '31'])).
% 1.10/1.31  thf('33', plain,
% 1.10/1.31      (![X0 : $i, X1 : $i]:
% 1.10/1.31         (((X1) = (k2_tarski @ X0 @ X0))
% 1.10/1.31          | ((X1) = (k1_tarski @ X0))
% 1.10/1.31          | ((X1) = (k1_xboole_0))
% 1.10/1.31          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 1.10/1.31      inference('simplify', [status(thm)], ['32'])).
% 1.10/1.31  thf('34', plain,
% 1.10/1.31      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 1.10/1.31        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 1.10/1.31        | ((k1_relat_1 @ sk_D) = (k2_tarski @ sk_A @ sk_A)))),
% 1.10/1.31      inference('sup-', [status(thm)], ['29', '33'])).
% 1.10/1.31  thf('35', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 1.10/1.31      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.10/1.31  thf('36', plain,
% 1.10/1.31      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 1.10/1.31        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 1.10/1.31        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 1.10/1.31      inference('demod', [status(thm)], ['34', '35'])).
% 1.10/1.31  thf('37', plain,
% 1.10/1.31      ((((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 1.10/1.31        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 1.10/1.31      inference('simplify', [status(thm)], ['36'])).
% 1.10/1.31  thf(t14_funct_1, axiom,
% 1.10/1.31    (![A:$i,B:$i]:
% 1.10/1.31     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.10/1.31       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 1.10/1.31         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 1.10/1.31  thf('38', plain,
% 1.10/1.31      (![X53 : $i, X54 : $i]:
% 1.10/1.31         (((k1_relat_1 @ X54) != (k1_tarski @ X53))
% 1.10/1.31          | ((k2_relat_1 @ X54) = (k1_tarski @ (k1_funct_1 @ X54 @ X53)))
% 1.10/1.31          | ~ (v1_funct_1 @ X54)
% 1.10/1.31          | ~ (v1_relat_1 @ X54))),
% 1.10/1.31      inference('cnf', [status(esa)], [t14_funct_1])).
% 1.10/1.31  thf('39', plain,
% 1.10/1.31      (![X0 : $i]:
% 1.10/1.31         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 1.10/1.31          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 1.10/1.31          | ~ (v1_relat_1 @ X0)
% 1.10/1.31          | ~ (v1_funct_1 @ X0)
% 1.10/1.31          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 1.10/1.31      inference('sup-', [status(thm)], ['37', '38'])).
% 1.10/1.31  thf('40', plain,
% 1.10/1.31      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 1.10/1.31        | ~ (v1_funct_1 @ sk_D)
% 1.10/1.31        | ~ (v1_relat_1 @ sk_D)
% 1.10/1.31        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 1.10/1.31      inference('eq_res', [status(thm)], ['39'])).
% 1.10/1.31  thf('41', plain, ((v1_funct_1 @ sk_D)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('42', plain, ((v1_relat_1 @ sk_D)),
% 1.10/1.31      inference('demod', [status(thm)], ['26', '27'])).
% 1.10/1.31  thf('43', plain,
% 1.10/1.31      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 1.10/1.31        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 1.10/1.31      inference('demod', [status(thm)], ['40', '41', '42'])).
% 1.10/1.31  thf('44', plain,
% 1.10/1.31      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 1.10/1.31          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 1.10/1.31      inference('demod', [status(thm)], ['0', '3'])).
% 1.10/1.31  thf('45', plain,
% 1.10/1.31      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 1.10/1.31        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 1.10/1.31      inference('sup-', [status(thm)], ['43', '44'])).
% 1.10/1.31  thf('46', plain,
% 1.10/1.31      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 1.10/1.31      inference('sup-', [status(thm)], ['18', '45'])).
% 1.10/1.31  thf('47', plain, ((v1_relat_1 @ sk_D)),
% 1.10/1.31      inference('demod', [status(thm)], ['26', '27'])).
% 1.10/1.31  thf('48', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 1.10/1.31      inference('demod', [status(thm)], ['46', '47'])).
% 1.10/1.31  thf(t64_relat_1, axiom,
% 1.10/1.31    (![A:$i]:
% 1.10/1.31     ( ( v1_relat_1 @ A ) =>
% 1.10/1.31       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 1.10/1.31           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 1.10/1.31         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 1.10/1.31  thf('49', plain,
% 1.10/1.31      (![X50 : $i]:
% 1.10/1.31         (((k1_relat_1 @ X50) != (k1_xboole_0))
% 1.10/1.31          | ((X50) = (k1_xboole_0))
% 1.10/1.31          | ~ (v1_relat_1 @ X50))),
% 1.10/1.31      inference('cnf', [status(esa)], [t64_relat_1])).
% 1.10/1.31  thf('50', plain,
% 1.10/1.31      ((((k1_xboole_0) != (k1_xboole_0))
% 1.10/1.31        | ~ (v1_relat_1 @ sk_D)
% 1.10/1.31        | ((sk_D) = (k1_xboole_0)))),
% 1.10/1.31      inference('sup-', [status(thm)], ['48', '49'])).
% 1.10/1.31  thf('51', plain, ((v1_relat_1 @ sk_D)),
% 1.10/1.31      inference('demod', [status(thm)], ['26', '27'])).
% 1.10/1.31  thf('52', plain,
% 1.10/1.31      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 1.10/1.31      inference('demod', [status(thm)], ['50', '51'])).
% 1.10/1.31  thf('53', plain, (((sk_D) = (k1_xboole_0))),
% 1.10/1.31      inference('simplify', [status(thm)], ['52'])).
% 1.10/1.31  thf(t150_relat_1, axiom,
% 1.10/1.31    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 1.10/1.31  thf('54', plain,
% 1.10/1.31      (![X47 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X47) = (k1_xboole_0))),
% 1.10/1.31      inference('cnf', [status(esa)], [t150_relat_1])).
% 1.10/1.31  thf('55', plain, (((sk_D) = (k1_xboole_0))),
% 1.10/1.31      inference('simplify', [status(thm)], ['52'])).
% 1.10/1.31  thf(t4_subset_1, axiom,
% 1.10/1.31    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.10/1.31  thf('56', plain,
% 1.10/1.31      (![X32 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X32))),
% 1.10/1.31      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.10/1.31  thf('57', plain,
% 1.10/1.31      (![X33 : $i, X34 : $i]:
% 1.10/1.31         ((r1_tarski @ X33 @ X34) | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34)))),
% 1.10/1.31      inference('cnf', [status(esa)], [t3_subset])).
% 1.10/1.31  thf('58', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.10/1.31      inference('sup-', [status(thm)], ['56', '57'])).
% 1.10/1.31  thf('59', plain, ($false),
% 1.10/1.31      inference('demod', [status(thm)], ['4', '53', '54', '55', '58'])).
% 1.10/1.31  
% 1.10/1.31  % SZS output end Refutation
% 1.10/1.31  
% 1.10/1.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
