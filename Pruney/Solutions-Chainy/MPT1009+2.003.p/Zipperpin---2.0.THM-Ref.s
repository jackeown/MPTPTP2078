%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nbrY1BnZFG

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:48 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 395 expanded)
%              Number of leaves         :   42 ( 134 expanded)
%              Depth                    :   14
%              Number of atoms          :  770 (4414 expanded)
%              Number of equality atoms :   53 ( 218 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

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
    ! [X61: $i,X62: $i,X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X63 ) ) )
      | ( ( k7_relset_1 @ X62 @ X63 @ X61 @ X64 )
        = ( k9_relat_1 @ X61 @ X64 ) ) ) ),
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
    ! [X65: $i,X66: $i,X67: $i,X68: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X65 ) @ X66 )
      | ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X66 @ X67 ) ) )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X68 @ X67 ) ) ) ) ),
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
    ! [X39: $i,X40: $i] :
      ( ( r1_tarski @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
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

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X47: $i,X48: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X47 @ X48 ) )
        = ( k9_relat_1 @ X47 @ X48 ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('16',plain,(
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

thf('17',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( v1_relat_1 @ X49 )
      | ( r1_tarski @ ( k2_relat_1 @ X50 ) @ ( k2_relat_1 @ X49 ) )
      | ~ ( r1_tarski @ X50 @ X49 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X51: $i,X52: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X51 @ X52 ) @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('21',plain,(
    ! [X39: $i,X41: $i] :
      ( ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( r1_tarski @ X39 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) )
      | ( v1_relat_1 @ X42 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('30',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( v4_relat_1 @ X58 @ X59 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X60 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('31',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('32',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( v4_relat_1 @ X44 @ X45 )
      | ( r1_tarski @ ( k1_relat_1 @ X44 ) @ X45 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('35',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ( v1_relat_1 @ X55 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('36',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['33','36'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('38',plain,(
    ! [X33: $i,X34: $i] :
      ( ( X34
        = ( k1_tarski @ X33 ) )
      | ( X34 = k1_xboole_0 )
      | ~ ( r1_tarski @ X34 @ ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('39',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('40',plain,(
    ! [X53: $i,X54: $i] :
      ( ( ( k1_relat_1 @ X54 )
       != ( k1_tarski @ X53 ) )
      | ( ( k2_relat_1 @ X54 )
        = ( k1_tarski @ ( k1_funct_1 @ X54 @ X53 ) ) )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['41'])).

thf('43',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['34','35'])).

thf('45',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('47',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['34','35'])).

thf('50',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['48','49'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('51',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k2_zfmisc_1 @ X37 @ X38 )
        = k1_xboole_0 )
      | ( X37 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('52',plain,(
    ! [X38: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X38 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['51'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('53',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('54',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['48','49'])).

thf('55',plain,(
    ! [X38: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X38 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('56',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['14','50','52','53','54','55'])).

thf('57',plain,(
    ! [X51: $i,X52: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X51 @ X52 ) @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('58',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('60',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('61',plain,(
    ! [X46: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('62',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X47: $i,X48: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X47 @ X48 ) )
        = ( k9_relat_1 @ X47 @ X48 ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('66',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('67',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['60','61'])).

thf('68',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['14','50','52','53','54','55'])).

thf('70',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['4','56','68','69','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nbrY1BnZFG
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:38:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.77/1.02  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.77/1.02  % Solved by: fo/fo7.sh
% 0.77/1.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/1.02  % done 744 iterations in 0.556s
% 0.77/1.02  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.77/1.02  % SZS output start Refutation
% 0.77/1.02  thf(sk_B_type, type, sk_B: $i).
% 0.77/1.02  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.77/1.02  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.77/1.02  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.77/1.02  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.77/1.02  thf(sk_C_type, type, sk_C: $i).
% 0.77/1.02  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.77/1.02  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.77/1.02  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.77/1.02  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.77/1.02  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.77/1.02  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.77/1.02  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.77/1.02  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.77/1.02  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/1.02  thf(sk_A_type, type, sk_A: $i).
% 0.77/1.02  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.77/1.02  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.77/1.02  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.77/1.02  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.77/1.02  thf(sk_D_type, type, sk_D: $i).
% 0.77/1.02  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.77/1.02  thf(t64_funct_2, conjecture,
% 0.77/1.02    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/1.02     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.77/1.02         ( m1_subset_1 @
% 0.77/1.02           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.77/1.02       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.77/1.02         ( r1_tarski @
% 0.77/1.02           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.77/1.02           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.77/1.02  thf(zf_stmt_0, negated_conjecture,
% 0.77/1.02    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.77/1.02        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.77/1.02            ( m1_subset_1 @
% 0.77/1.02              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.77/1.02          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.77/1.02            ( r1_tarski @
% 0.77/1.02              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.77/1.02              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.77/1.02    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.77/1.02  thf('0', plain,
% 0.77/1.02      (~ (r1_tarski @ 
% 0.77/1.02          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.77/1.02          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.77/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.02  thf('1', plain,
% 0.77/1.02      ((m1_subset_1 @ sk_D @ 
% 0.77/1.02        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.77/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.02  thf(redefinition_k7_relset_1, axiom,
% 0.77/1.02    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/1.02     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/1.02       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.77/1.02  thf('2', plain,
% 0.77/1.02      (![X61 : $i, X62 : $i, X63 : $i, X64 : $i]:
% 0.77/1.02         (~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X63)))
% 0.77/1.02          | ((k7_relset_1 @ X62 @ X63 @ X61 @ X64) = (k9_relat_1 @ X61 @ X64)))),
% 0.77/1.02      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.77/1.02  thf('3', plain,
% 0.77/1.02      (![X0 : $i]:
% 0.77/1.02         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.77/1.02           = (k9_relat_1 @ sk_D @ X0))),
% 0.77/1.02      inference('sup-', [status(thm)], ['1', '2'])).
% 0.77/1.02  thf('4', plain,
% 0.77/1.02      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.77/1.02          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.77/1.02      inference('demod', [status(thm)], ['0', '3'])).
% 0.77/1.02  thf(d10_xboole_0, axiom,
% 0.77/1.02    (![A:$i,B:$i]:
% 0.77/1.02     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.77/1.02  thf('5', plain,
% 0.77/1.02      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.77/1.02      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.77/1.02  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.77/1.02      inference('simplify', [status(thm)], ['5'])).
% 0.77/1.02  thf('7', plain,
% 0.77/1.02      ((m1_subset_1 @ sk_D @ 
% 0.77/1.02        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.77/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.02  thf(t13_relset_1, axiom,
% 0.77/1.02    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/1.02     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.77/1.02       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.77/1.02         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.77/1.02  thf('8', plain,
% 0.77/1.02      (![X65 : $i, X66 : $i, X67 : $i, X68 : $i]:
% 0.77/1.02         (~ (r1_tarski @ (k1_relat_1 @ X65) @ X66)
% 0.77/1.02          | (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X66 @ X67)))
% 0.77/1.02          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X68 @ X67))))),
% 0.77/1.02      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.77/1.02  thf('9', plain,
% 0.77/1.02      (![X0 : $i]:
% 0.77/1.02         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.77/1.02          | ~ (r1_tarski @ (k1_relat_1 @ sk_D) @ X0))),
% 0.77/1.02      inference('sup-', [status(thm)], ['7', '8'])).
% 0.77/1.02  thf('10', plain,
% 0.77/1.02      ((m1_subset_1 @ sk_D @ 
% 0.77/1.02        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.77/1.02      inference('sup-', [status(thm)], ['6', '9'])).
% 0.77/1.02  thf(t3_subset, axiom,
% 0.77/1.02    (![A:$i,B:$i]:
% 0.77/1.02     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.77/1.02  thf('11', plain,
% 0.77/1.02      (![X39 : $i, X40 : $i]:
% 0.77/1.02         ((r1_tarski @ X39 @ X40) | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40)))),
% 0.77/1.02      inference('cnf', [status(esa)], [t3_subset])).
% 0.77/1.02  thf('12', plain,
% 0.77/1.02      ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B))),
% 0.77/1.02      inference('sup-', [status(thm)], ['10', '11'])).
% 0.77/1.02  thf('13', plain,
% 0.77/1.02      (![X0 : $i, X2 : $i]:
% 0.77/1.02         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.77/1.02      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.77/1.02  thf('14', plain,
% 0.77/1.02      ((~ (r1_tarski @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B) @ sk_D)
% 0.77/1.02        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B) = (sk_D)))),
% 0.77/1.02      inference('sup-', [status(thm)], ['12', '13'])).
% 0.77/1.02  thf(t148_relat_1, axiom,
% 0.77/1.02    (![A:$i,B:$i]:
% 0.77/1.02     ( ( v1_relat_1 @ B ) =>
% 0.77/1.02       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.77/1.02  thf('15', plain,
% 0.77/1.02      (![X47 : $i, X48 : $i]:
% 0.77/1.02         (((k2_relat_1 @ (k7_relat_1 @ X47 @ X48)) = (k9_relat_1 @ X47 @ X48))
% 0.77/1.02          | ~ (v1_relat_1 @ X47))),
% 0.77/1.02      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.77/1.02  thf(t88_relat_1, axiom,
% 0.77/1.02    (![A:$i,B:$i]:
% 0.77/1.02     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.77/1.02  thf('16', plain,
% 0.77/1.02      (![X51 : $i, X52 : $i]:
% 0.77/1.02         ((r1_tarski @ (k7_relat_1 @ X51 @ X52) @ X51) | ~ (v1_relat_1 @ X51))),
% 0.77/1.02      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.77/1.02  thf(t25_relat_1, axiom,
% 0.77/1.02    (![A:$i]:
% 0.77/1.02     ( ( v1_relat_1 @ A ) =>
% 0.77/1.02       ( ![B:$i]:
% 0.77/1.02         ( ( v1_relat_1 @ B ) =>
% 0.77/1.02           ( ( r1_tarski @ A @ B ) =>
% 0.77/1.02             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.77/1.02               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.77/1.02  thf('17', plain,
% 0.77/1.02      (![X49 : $i, X50 : $i]:
% 0.77/1.02         (~ (v1_relat_1 @ X49)
% 0.77/1.02          | (r1_tarski @ (k2_relat_1 @ X50) @ (k2_relat_1 @ X49))
% 0.77/1.02          | ~ (r1_tarski @ X50 @ X49)
% 0.77/1.02          | ~ (v1_relat_1 @ X50))),
% 0.77/1.02      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.77/1.02  thf('18', plain,
% 0.77/1.02      (![X0 : $i, X1 : $i]:
% 0.77/1.02         (~ (v1_relat_1 @ X0)
% 0.77/1.02          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.77/1.02          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 0.77/1.02             (k2_relat_1 @ X0))
% 0.77/1.02          | ~ (v1_relat_1 @ X0))),
% 0.77/1.02      inference('sup-', [status(thm)], ['16', '17'])).
% 0.77/1.02  thf('19', plain,
% 0.77/1.02      (![X0 : $i, X1 : $i]:
% 0.77/1.02         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 0.77/1.02           (k2_relat_1 @ X0))
% 0.77/1.02          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.77/1.02          | ~ (v1_relat_1 @ X0))),
% 0.77/1.02      inference('simplify', [status(thm)], ['18'])).
% 0.77/1.02  thf('20', plain,
% 0.77/1.02      (![X51 : $i, X52 : $i]:
% 0.77/1.02         ((r1_tarski @ (k7_relat_1 @ X51 @ X52) @ X51) | ~ (v1_relat_1 @ X51))),
% 0.77/1.02      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.77/1.02  thf('21', plain,
% 0.77/1.02      (![X39 : $i, X41 : $i]:
% 0.77/1.02         ((m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X41)) | ~ (r1_tarski @ X39 @ X41))),
% 0.77/1.02      inference('cnf', [status(esa)], [t3_subset])).
% 0.77/1.02  thf('22', plain,
% 0.77/1.02      (![X0 : $i, X1 : $i]:
% 0.77/1.02         (~ (v1_relat_1 @ X0)
% 0.77/1.02          | (m1_subset_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 0.77/1.02      inference('sup-', [status(thm)], ['20', '21'])).
% 0.77/1.02  thf(cc2_relat_1, axiom,
% 0.77/1.02    (![A:$i]:
% 0.77/1.02     ( ( v1_relat_1 @ A ) =>
% 0.77/1.02       ( ![B:$i]:
% 0.77/1.02         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.77/1.02  thf('23', plain,
% 0.77/1.02      (![X42 : $i, X43 : $i]:
% 0.77/1.02         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43))
% 0.77/1.02          | (v1_relat_1 @ X42)
% 0.77/1.02          | ~ (v1_relat_1 @ X43))),
% 0.77/1.02      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.77/1.02  thf('24', plain,
% 0.77/1.02      (![X0 : $i, X1 : $i]:
% 0.77/1.02         (~ (v1_relat_1 @ X0)
% 0.77/1.02          | ~ (v1_relat_1 @ X0)
% 0.77/1.02          | (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 0.77/1.02      inference('sup-', [status(thm)], ['22', '23'])).
% 0.77/1.02  thf('25', plain,
% 0.77/1.02      (![X0 : $i, X1 : $i]:
% 0.77/1.02         ((v1_relat_1 @ (k7_relat_1 @ X0 @ X1)) | ~ (v1_relat_1 @ X0))),
% 0.77/1.02      inference('simplify', [status(thm)], ['24'])).
% 0.77/1.02  thf('26', plain,
% 0.77/1.02      (![X0 : $i, X1 : $i]:
% 0.77/1.02         (~ (v1_relat_1 @ X0)
% 0.77/1.02          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 0.77/1.02             (k2_relat_1 @ X0)))),
% 0.77/1.02      inference('clc', [status(thm)], ['19', '25'])).
% 0.77/1.02  thf('27', plain,
% 0.77/1.02      (![X0 : $i, X1 : $i]:
% 0.77/1.02         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1))
% 0.77/1.02          | ~ (v1_relat_1 @ X1)
% 0.77/1.02          | ~ (v1_relat_1 @ X1))),
% 0.77/1.02      inference('sup+', [status(thm)], ['15', '26'])).
% 0.77/1.02  thf('28', plain,
% 0.77/1.02      (![X0 : $i, X1 : $i]:
% 0.77/1.02         (~ (v1_relat_1 @ X1)
% 0.77/1.02          | (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1)))),
% 0.77/1.02      inference('simplify', [status(thm)], ['27'])).
% 0.77/1.02  thf('29', plain,
% 0.77/1.02      ((m1_subset_1 @ sk_D @ 
% 0.77/1.02        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.77/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.02  thf(cc2_relset_1, axiom,
% 0.77/1.02    (![A:$i,B:$i,C:$i]:
% 0.77/1.02     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/1.02       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.77/1.02  thf('30', plain,
% 0.77/1.02      (![X58 : $i, X59 : $i, X60 : $i]:
% 0.77/1.02         ((v4_relat_1 @ X58 @ X59)
% 0.77/1.02          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X60))))),
% 0.77/1.02      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.77/1.02  thf('31', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.77/1.02      inference('sup-', [status(thm)], ['29', '30'])).
% 0.77/1.02  thf(d18_relat_1, axiom,
% 0.77/1.02    (![A:$i,B:$i]:
% 0.77/1.02     ( ( v1_relat_1 @ B ) =>
% 0.77/1.02       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.77/1.02  thf('32', plain,
% 0.77/1.02      (![X44 : $i, X45 : $i]:
% 0.77/1.02         (~ (v4_relat_1 @ X44 @ X45)
% 0.77/1.02          | (r1_tarski @ (k1_relat_1 @ X44) @ X45)
% 0.77/1.02          | ~ (v1_relat_1 @ X44))),
% 0.77/1.02      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.77/1.02  thf('33', plain,
% 0.77/1.02      ((~ (v1_relat_1 @ sk_D)
% 0.77/1.02        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.77/1.02      inference('sup-', [status(thm)], ['31', '32'])).
% 0.77/1.02  thf('34', plain,
% 0.77/1.02      ((m1_subset_1 @ sk_D @ 
% 0.77/1.02        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.77/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.02  thf(cc1_relset_1, axiom,
% 0.77/1.02    (![A:$i,B:$i,C:$i]:
% 0.77/1.02     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/1.02       ( v1_relat_1 @ C ) ))).
% 0.77/1.02  thf('35', plain,
% 0.77/1.02      (![X55 : $i, X56 : $i, X57 : $i]:
% 0.77/1.02         ((v1_relat_1 @ X55)
% 0.77/1.02          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57))))),
% 0.77/1.02      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.77/1.02  thf('36', plain, ((v1_relat_1 @ sk_D)),
% 0.77/1.02      inference('sup-', [status(thm)], ['34', '35'])).
% 0.77/1.02  thf('37', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.77/1.02      inference('demod', [status(thm)], ['33', '36'])).
% 0.77/1.02  thf(l3_zfmisc_1, axiom,
% 0.77/1.02    (![A:$i,B:$i]:
% 0.77/1.02     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.77/1.02       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.77/1.02  thf('38', plain,
% 0.77/1.02      (![X33 : $i, X34 : $i]:
% 0.77/1.02         (((X34) = (k1_tarski @ X33))
% 0.77/1.02          | ((X34) = (k1_xboole_0))
% 0.77/1.02          | ~ (r1_tarski @ X34 @ (k1_tarski @ X33)))),
% 0.77/1.02      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.77/1.02  thf('39', plain,
% 0.77/1.02      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.77/1.02        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.77/1.02      inference('sup-', [status(thm)], ['37', '38'])).
% 0.77/1.02  thf(t14_funct_1, axiom,
% 0.77/1.02    (![A:$i,B:$i]:
% 0.77/1.02     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.77/1.02       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.77/1.02         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.77/1.02  thf('40', plain,
% 0.77/1.02      (![X53 : $i, X54 : $i]:
% 0.77/1.02         (((k1_relat_1 @ X54) != (k1_tarski @ X53))
% 0.77/1.02          | ((k2_relat_1 @ X54) = (k1_tarski @ (k1_funct_1 @ X54 @ X53)))
% 0.77/1.02          | ~ (v1_funct_1 @ X54)
% 0.77/1.02          | ~ (v1_relat_1 @ X54))),
% 0.77/1.02      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.77/1.02  thf('41', plain,
% 0.77/1.02      (![X0 : $i]:
% 0.77/1.02         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.77/1.02          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.77/1.02          | ~ (v1_relat_1 @ X0)
% 0.77/1.02          | ~ (v1_funct_1 @ X0)
% 0.77/1.02          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.77/1.02      inference('sup-', [status(thm)], ['39', '40'])).
% 0.77/1.02  thf('42', plain,
% 0.77/1.02      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.77/1.02        | ~ (v1_funct_1 @ sk_D)
% 0.77/1.02        | ~ (v1_relat_1 @ sk_D)
% 0.77/1.02        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.77/1.02      inference('eq_res', [status(thm)], ['41'])).
% 0.77/1.02  thf('43', plain, ((v1_funct_1 @ sk_D)),
% 0.77/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.02  thf('44', plain, ((v1_relat_1 @ sk_D)),
% 0.77/1.02      inference('sup-', [status(thm)], ['34', '35'])).
% 0.77/1.02  thf('45', plain,
% 0.77/1.02      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.77/1.02        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.77/1.02      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.77/1.02  thf('46', plain,
% 0.77/1.02      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.77/1.02          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.77/1.02      inference('demod', [status(thm)], ['0', '3'])).
% 0.77/1.02  thf('47', plain,
% 0.77/1.02      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.77/1.02        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.77/1.02      inference('sup-', [status(thm)], ['45', '46'])).
% 0.77/1.02  thf('48', plain,
% 0.77/1.02      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.77/1.02      inference('sup-', [status(thm)], ['28', '47'])).
% 0.77/1.02  thf('49', plain, ((v1_relat_1 @ sk_D)),
% 0.77/1.02      inference('sup-', [status(thm)], ['34', '35'])).
% 0.77/1.02  thf('50', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.77/1.02      inference('demod', [status(thm)], ['48', '49'])).
% 0.77/1.02  thf(t113_zfmisc_1, axiom,
% 0.77/1.02    (![A:$i,B:$i]:
% 0.77/1.02     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.77/1.02       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.77/1.02  thf('51', plain,
% 0.77/1.02      (![X37 : $i, X38 : $i]:
% 0.77/1.02         (((k2_zfmisc_1 @ X37 @ X38) = (k1_xboole_0))
% 0.77/1.02          | ((X37) != (k1_xboole_0)))),
% 0.77/1.02      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.77/1.02  thf('52', plain,
% 0.77/1.02      (![X38 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X38) = (k1_xboole_0))),
% 0.77/1.02      inference('simplify', [status(thm)], ['51'])).
% 0.77/1.02  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.77/1.02  thf('53', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.77/1.02      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.77/1.02  thf('54', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.77/1.02      inference('demod', [status(thm)], ['48', '49'])).
% 0.77/1.02  thf('55', plain,
% 0.77/1.02      (![X38 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X38) = (k1_xboole_0))),
% 0.77/1.02      inference('simplify', [status(thm)], ['51'])).
% 0.77/1.02  thf('56', plain, (((k1_xboole_0) = (sk_D))),
% 0.77/1.02      inference('demod', [status(thm)], ['14', '50', '52', '53', '54', '55'])).
% 0.77/1.02  thf('57', plain,
% 0.77/1.02      (![X51 : $i, X52 : $i]:
% 0.77/1.02         ((r1_tarski @ (k7_relat_1 @ X51 @ X52) @ X51) | ~ (v1_relat_1 @ X51))),
% 0.77/1.02      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.77/1.02  thf(t3_xboole_1, axiom,
% 0.77/1.02    (![A:$i]:
% 0.77/1.02     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.77/1.02  thf('58', plain,
% 0.77/1.02      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 0.77/1.02      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.77/1.02  thf('59', plain,
% 0.77/1.02      (![X0 : $i]:
% 0.77/1.02         (~ (v1_relat_1 @ k1_xboole_0)
% 0.77/1.02          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.77/1.02      inference('sup-', [status(thm)], ['57', '58'])).
% 0.77/1.02  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.77/1.02  thf('60', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/1.02      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.77/1.02  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.77/1.02  thf('61', plain, (![X46 : $i]: (v1_relat_1 @ (k6_relat_1 @ X46))),
% 0.77/1.02      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.77/1.02  thf('62', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.77/1.02      inference('sup+', [status(thm)], ['60', '61'])).
% 0.77/1.02  thf('63', plain,
% 0.77/1.02      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.77/1.02      inference('demod', [status(thm)], ['59', '62'])).
% 0.77/1.02  thf('64', plain,
% 0.77/1.02      (![X47 : $i, X48 : $i]:
% 0.77/1.02         (((k2_relat_1 @ (k7_relat_1 @ X47 @ X48)) = (k9_relat_1 @ X47 @ X48))
% 0.77/1.02          | ~ (v1_relat_1 @ X47))),
% 0.77/1.02      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.77/1.02  thf('65', plain,
% 0.77/1.02      (![X0 : $i]:
% 0.77/1.02         (((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))
% 0.77/1.02          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.77/1.02      inference('sup+', [status(thm)], ['63', '64'])).
% 0.77/1.02  thf(t60_relat_1, axiom,
% 0.77/1.02    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.77/1.02     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.77/1.02  thf('66', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/1.02      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.77/1.02  thf('67', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.77/1.02      inference('sup+', [status(thm)], ['60', '61'])).
% 0.77/1.02  thf('68', plain,
% 0.77/1.02      (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))),
% 0.77/1.02      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.77/1.02  thf('69', plain, (((k1_xboole_0) = (sk_D))),
% 0.77/1.02      inference('demod', [status(thm)], ['14', '50', '52', '53', '54', '55'])).
% 0.77/1.02  thf('70', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.77/1.02      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.77/1.02  thf('71', plain, ($false),
% 0.77/1.02      inference('demod', [status(thm)], ['4', '56', '68', '69', '70'])).
% 0.77/1.02  
% 0.77/1.02  % SZS output end Refutation
% 0.77/1.02  
% 0.86/1.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
