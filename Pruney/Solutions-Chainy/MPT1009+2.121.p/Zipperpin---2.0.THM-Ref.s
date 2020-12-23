%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jmLFAHRgLR

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:06 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 745 expanded)
%              Number of leaves         :   47 ( 246 expanded)
%              Depth                    :   19
%              Number of atoms          :  992 (7786 expanded)
%              Number of equality atoms :   72 ( 351 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

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
    ! [X69: $i,X70: $i,X71: $i,X72: $i] :
      ( ~ ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X70 @ X71 ) ) )
      | ( ( k7_relset_1 @ X70 @ X71 @ X69 @ X72 )
        = ( k9_relat_1 @ X69 @ X72 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ( v4_relat_1 @ X66 @ X67 )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X67 @ X68 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('7',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X57: $i,X58: $i] :
      ( ( X57
        = ( k7_relat_1 @ X57 @ X58 ) )
      | ~ ( v4_relat_1 @ X57 @ X58 )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X50 ) )
      | ( v1_relat_1 @ X49 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X53: $i,X54: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('14',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X55: $i,X56: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X55 @ X56 ) )
        = ( k9_relat_1 @ X55 @ X56 ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('17',plain,(
    ! [X59: $i] :
      ( ( r1_tarski @ X59 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X59 ) @ ( k2_relat_1 @ X59 ) ) )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('19',plain,(
    ! [X62: $i,X63: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X62 @ X63 ) @ X62 )
      | ~ ( v1_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X46: $i,X48: $i] :
      ( ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X48 ) )
      | ~ ( r1_tarski @ X46 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X50 ) )
      | ( v1_relat_1 @ X49 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['18','24'])).

thf('26',plain,
    ( ( r1_tarski @ sk_D @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ) @ ( k9_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['15','25'])).

thf('27',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('28',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('29',plain,(
    ! [X55: $i,X56: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X55 @ X56 ) )
        = ( k9_relat_1 @ X55 @ X56 ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('30',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k9_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('32',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k9_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('34',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['26','27','32','33'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) @ sk_D )
    | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X55: $i,X56: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X55 @ X56 ) )
        = ( k9_relat_1 @ X55 @ X56 ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('38',plain,(
    ! [X62: $i,X63: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X62 @ X63 ) @ X62 )
      | ~ ( v1_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('39',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( v1_relat_1 @ X60 )
      | ( r1_tarski @ ( k2_relat_1 @ X61 ) @ ( k2_relat_1 @ X60 ) )
      | ~ ( r1_tarski @ X61 @ X60 )
      | ~ ( v1_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('46',plain,(
    ! [X44: $i,X45: $i] :
      ( ( ( k4_xboole_0 @ X44 @ ( k1_tarski @ X45 ) )
        = X44 )
      | ( r2_hidden @ X45 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('47',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('48',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( v4_relat_1 @ X51 @ X52 )
      | ( r1_tarski @ ( k1_relat_1 @ X51 ) @ X52 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('51',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('52',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('53',plain,
    ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('54',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('55',plain,
    ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('56',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('57',plain,
    ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['46','57'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('59',plain,(
    ! [X37: $i,X39: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X37 ) @ X39 )
      | ~ ( r2_hidden @ X37 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('60',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('62',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('63',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_D ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('65',plain,(
    ! [X64: $i,X65: $i] :
      ( ( ( k1_relat_1 @ X65 )
       != ( k1_tarski @ X64 ) )
      | ( ( k2_relat_1 @ X65 )
        = ( k1_tarski @ ( k1_funct_1 @ X65 @ X64 ) ) )
      | ~ ( v1_funct_1 @ X65 )
      | ~ ( v1_relat_1 @ X65 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['66'])).

thf('68',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('70',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('72',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('75',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['73','74'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('76',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k2_zfmisc_1 @ X41 @ X42 )
        = k1_xboole_0 )
      | ( X41 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('77',plain,(
    ! [X42: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X42 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('78',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('79',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['73','74'])).

thf('80',plain,(
    ! [X42: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X42 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('81',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['36','75','77','78','79','80'])).

thf('82',plain,(
    ! [X62: $i,X63: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X62 @ X63 ) @ X62 )
      | ~ ( v1_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('83',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X42: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X42 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('88',plain,(
    ! [X53: $i,X54: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('89',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X55: $i,X56: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X55 @ X56 ) )
        = ( k9_relat_1 @ X55 @ X56 ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('93',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('94',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['87','88'])).

thf('95',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['36','75','77','78','79','80'])).

thf('97',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['4','81','95','96','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jmLFAHRgLR
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:58:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.68/0.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.68/0.87  % Solved by: fo/fo7.sh
% 0.68/0.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.87  % done 1045 iterations in 0.418s
% 0.68/0.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.68/0.87  % SZS output start Refutation
% 0.68/0.87  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.68/0.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.68/0.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.87  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.68/0.87  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.68/0.87  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.68/0.87  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.68/0.87  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.87  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.68/0.87  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.68/0.87  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.87  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.68/0.87  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.68/0.87  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.68/0.87  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.68/0.87  thf(sk_D_type, type, sk_D: $i).
% 0.68/0.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.87  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.68/0.87  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.68/0.87  thf(sk_C_type, type, sk_C: $i).
% 0.68/0.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.87  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.68/0.87  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.68/0.87  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.68/0.87  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.68/0.87  thf(t64_funct_2, conjecture,
% 0.68/0.87    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.87     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.68/0.87         ( m1_subset_1 @
% 0.68/0.87           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.68/0.87       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.68/0.87         ( r1_tarski @
% 0.68/0.87           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.68/0.87           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.68/0.87  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.87    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.87        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.68/0.87            ( m1_subset_1 @
% 0.68/0.87              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.68/0.87          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.68/0.87            ( r1_tarski @
% 0.68/0.87              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.68/0.87              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.68/0.87    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.68/0.87  thf('0', plain,
% 0.68/0.87      (~ (r1_tarski @ 
% 0.68/0.87          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.68/0.87          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('1', plain,
% 0.68/0.87      ((m1_subset_1 @ sk_D @ 
% 0.68/0.87        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf(redefinition_k7_relset_1, axiom,
% 0.68/0.87    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.87       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.68/0.87  thf('2', plain,
% 0.68/0.87      (![X69 : $i, X70 : $i, X71 : $i, X72 : $i]:
% 0.68/0.87         (~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X70 @ X71)))
% 0.68/0.87          | ((k7_relset_1 @ X70 @ X71 @ X69 @ X72) = (k9_relat_1 @ X69 @ X72)))),
% 0.68/0.87      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.68/0.87  thf('3', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.68/0.87           = (k9_relat_1 @ sk_D @ X0))),
% 0.68/0.87      inference('sup-', [status(thm)], ['1', '2'])).
% 0.68/0.87  thf('4', plain,
% 0.68/0.87      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.68/0.87          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.68/0.87      inference('demod', [status(thm)], ['0', '3'])).
% 0.68/0.87  thf('5', plain,
% 0.68/0.87      ((m1_subset_1 @ sk_D @ 
% 0.68/0.87        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf(cc2_relset_1, axiom,
% 0.68/0.87    (![A:$i,B:$i,C:$i]:
% 0.68/0.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.87       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.68/0.87  thf('6', plain,
% 0.68/0.87      (![X66 : $i, X67 : $i, X68 : $i]:
% 0.68/0.87         ((v4_relat_1 @ X66 @ X67)
% 0.68/0.87          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X67 @ X68))))),
% 0.68/0.87      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.68/0.87  thf('7', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.68/0.87      inference('sup-', [status(thm)], ['5', '6'])).
% 0.68/0.87  thf(t209_relat_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.68/0.87       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.68/0.87  thf('8', plain,
% 0.68/0.87      (![X57 : $i, X58 : $i]:
% 0.68/0.87         (((X57) = (k7_relat_1 @ X57 @ X58))
% 0.68/0.87          | ~ (v4_relat_1 @ X57 @ X58)
% 0.68/0.87          | ~ (v1_relat_1 @ X57))),
% 0.68/0.87      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.68/0.87  thf('9', plain,
% 0.68/0.87      ((~ (v1_relat_1 @ sk_D)
% 0.68/0.87        | ((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A))))),
% 0.68/0.87      inference('sup-', [status(thm)], ['7', '8'])).
% 0.68/0.87  thf('10', plain,
% 0.68/0.87      ((m1_subset_1 @ sk_D @ 
% 0.68/0.87        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf(cc2_relat_1, axiom,
% 0.68/0.87    (![A:$i]:
% 0.68/0.87     ( ( v1_relat_1 @ A ) =>
% 0.68/0.87       ( ![B:$i]:
% 0.68/0.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.68/0.87  thf('11', plain,
% 0.68/0.87      (![X49 : $i, X50 : $i]:
% 0.68/0.87         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X50))
% 0.68/0.87          | (v1_relat_1 @ X49)
% 0.68/0.87          | ~ (v1_relat_1 @ X50))),
% 0.68/0.87      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.68/0.87  thf('12', plain,
% 0.68/0.87      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.68/0.87        | (v1_relat_1 @ sk_D))),
% 0.68/0.87      inference('sup-', [status(thm)], ['10', '11'])).
% 0.68/0.87  thf(fc6_relat_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.68/0.87  thf('13', plain,
% 0.68/0.87      (![X53 : $i, X54 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X53 @ X54))),
% 0.68/0.87      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.68/0.87  thf('14', plain, ((v1_relat_1 @ sk_D)),
% 0.68/0.87      inference('demod', [status(thm)], ['12', '13'])).
% 0.68/0.87  thf('15', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.68/0.87      inference('demod', [status(thm)], ['9', '14'])).
% 0.68/0.87  thf(t148_relat_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( v1_relat_1 @ B ) =>
% 0.68/0.87       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.68/0.87  thf('16', plain,
% 0.68/0.87      (![X55 : $i, X56 : $i]:
% 0.68/0.87         (((k2_relat_1 @ (k7_relat_1 @ X55 @ X56)) = (k9_relat_1 @ X55 @ X56))
% 0.68/0.87          | ~ (v1_relat_1 @ X55))),
% 0.68/0.87      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.68/0.87  thf(t21_relat_1, axiom,
% 0.68/0.87    (![A:$i]:
% 0.68/0.87     ( ( v1_relat_1 @ A ) =>
% 0.68/0.87       ( r1_tarski @
% 0.68/0.87         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.68/0.87  thf('17', plain,
% 0.68/0.87      (![X59 : $i]:
% 0.68/0.87         ((r1_tarski @ X59 @ 
% 0.68/0.87           (k2_zfmisc_1 @ (k1_relat_1 @ X59) @ (k2_relat_1 @ X59)))
% 0.68/0.87          | ~ (v1_relat_1 @ X59))),
% 0.68/0.87      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.68/0.87  thf('18', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         ((r1_tarski @ (k7_relat_1 @ X1 @ X0) @ 
% 0.68/0.87           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.68/0.87            (k9_relat_1 @ X1 @ X0)))
% 0.68/0.87          | ~ (v1_relat_1 @ X1)
% 0.68/0.87          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.68/0.87      inference('sup+', [status(thm)], ['16', '17'])).
% 0.68/0.87  thf(t88_relat_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.68/0.87  thf('19', plain,
% 0.68/0.87      (![X62 : $i, X63 : $i]:
% 0.68/0.87         ((r1_tarski @ (k7_relat_1 @ X62 @ X63) @ X62) | ~ (v1_relat_1 @ X62))),
% 0.68/0.87      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.68/0.87  thf(t3_subset, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.68/0.87  thf('20', plain,
% 0.68/0.87      (![X46 : $i, X48 : $i]:
% 0.68/0.87         ((m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X48)) | ~ (r1_tarski @ X46 @ X48))),
% 0.68/0.87      inference('cnf', [status(esa)], [t3_subset])).
% 0.68/0.87  thf('21', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         (~ (v1_relat_1 @ X0)
% 0.68/0.87          | (m1_subset_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['19', '20'])).
% 0.68/0.87  thf('22', plain,
% 0.68/0.87      (![X49 : $i, X50 : $i]:
% 0.68/0.87         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X50))
% 0.68/0.87          | (v1_relat_1 @ X49)
% 0.68/0.87          | ~ (v1_relat_1 @ X50))),
% 0.68/0.87      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.68/0.87  thf('23', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         (~ (v1_relat_1 @ X0)
% 0.68/0.87          | ~ (v1_relat_1 @ X0)
% 0.68/0.87          | (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['21', '22'])).
% 0.68/0.87  thf('24', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         ((v1_relat_1 @ (k7_relat_1 @ X0 @ X1)) | ~ (v1_relat_1 @ X0))),
% 0.68/0.87      inference('simplify', [status(thm)], ['23'])).
% 0.68/0.87  thf('25', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         (~ (v1_relat_1 @ X1)
% 0.68/0.87          | (r1_tarski @ (k7_relat_1 @ X1 @ X0) @ 
% 0.68/0.87             (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.68/0.87              (k9_relat_1 @ X1 @ X0))))),
% 0.68/0.87      inference('clc', [status(thm)], ['18', '24'])).
% 0.68/0.87  thf('26', plain,
% 0.68/0.87      (((r1_tarski @ sk_D @ 
% 0.68/0.87         (k2_zfmisc_1 @ 
% 0.68/0.87          (k1_relat_1 @ (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A))) @ 
% 0.68/0.87          (k9_relat_1 @ sk_D @ (k1_tarski @ sk_A))))
% 0.68/0.87        | ~ (v1_relat_1 @ sk_D))),
% 0.68/0.87      inference('sup+', [status(thm)], ['15', '25'])).
% 0.68/0.87  thf('27', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.68/0.87      inference('demod', [status(thm)], ['9', '14'])).
% 0.68/0.87  thf('28', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.68/0.87      inference('demod', [status(thm)], ['9', '14'])).
% 0.68/0.87  thf('29', plain,
% 0.68/0.87      (![X55 : $i, X56 : $i]:
% 0.68/0.87         (((k2_relat_1 @ (k7_relat_1 @ X55 @ X56)) = (k9_relat_1 @ X55 @ X56))
% 0.68/0.87          | ~ (v1_relat_1 @ X55))),
% 0.68/0.87      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.68/0.87  thf('30', plain,
% 0.68/0.87      ((((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ (k1_tarski @ sk_A)))
% 0.68/0.87        | ~ (v1_relat_1 @ sk_D))),
% 0.68/0.87      inference('sup+', [status(thm)], ['28', '29'])).
% 0.68/0.87  thf('31', plain, ((v1_relat_1 @ sk_D)),
% 0.68/0.87      inference('demod', [status(thm)], ['12', '13'])).
% 0.68/0.87  thf('32', plain,
% 0.68/0.87      (((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.68/0.87      inference('demod', [status(thm)], ['30', '31'])).
% 0.68/0.87  thf('33', plain, ((v1_relat_1 @ sk_D)),
% 0.68/0.87      inference('demod', [status(thm)], ['12', '13'])).
% 0.68/0.87  thf('34', plain,
% 0.68/0.87      ((r1_tarski @ sk_D @ 
% 0.68/0.87        (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D)))),
% 0.68/0.87      inference('demod', [status(thm)], ['26', '27', '32', '33'])).
% 0.68/0.87  thf(d10_xboole_0, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.68/0.87  thf('35', plain,
% 0.68/0.87      (![X0 : $i, X2 : $i]:
% 0.68/0.87         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.68/0.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.68/0.87  thf('36', plain,
% 0.68/0.87      ((~ (r1_tarski @ 
% 0.68/0.87           (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D)) @ sk_D)
% 0.68/0.87        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D)) = (sk_D)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['34', '35'])).
% 0.68/0.87  thf('37', plain,
% 0.68/0.87      (![X55 : $i, X56 : $i]:
% 0.68/0.87         (((k2_relat_1 @ (k7_relat_1 @ X55 @ X56)) = (k9_relat_1 @ X55 @ X56))
% 0.68/0.87          | ~ (v1_relat_1 @ X55))),
% 0.68/0.87      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.68/0.87  thf('38', plain,
% 0.68/0.87      (![X62 : $i, X63 : $i]:
% 0.68/0.87         ((r1_tarski @ (k7_relat_1 @ X62 @ X63) @ X62) | ~ (v1_relat_1 @ X62))),
% 0.68/0.87      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.68/0.87  thf(t25_relat_1, axiom,
% 0.68/0.87    (![A:$i]:
% 0.68/0.87     ( ( v1_relat_1 @ A ) =>
% 0.68/0.87       ( ![B:$i]:
% 0.68/0.87         ( ( v1_relat_1 @ B ) =>
% 0.68/0.87           ( ( r1_tarski @ A @ B ) =>
% 0.68/0.87             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.68/0.87               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.68/0.87  thf('39', plain,
% 0.68/0.87      (![X60 : $i, X61 : $i]:
% 0.68/0.87         (~ (v1_relat_1 @ X60)
% 0.68/0.87          | (r1_tarski @ (k2_relat_1 @ X61) @ (k2_relat_1 @ X60))
% 0.68/0.87          | ~ (r1_tarski @ X61 @ X60)
% 0.68/0.87          | ~ (v1_relat_1 @ X61))),
% 0.68/0.87      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.68/0.87  thf('40', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         (~ (v1_relat_1 @ X0)
% 0.68/0.87          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.68/0.87          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 0.68/0.87             (k2_relat_1 @ X0))
% 0.68/0.87          | ~ (v1_relat_1 @ X0))),
% 0.68/0.87      inference('sup-', [status(thm)], ['38', '39'])).
% 0.68/0.87  thf('41', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 0.68/0.87           (k2_relat_1 @ X0))
% 0.68/0.87          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.68/0.87          | ~ (v1_relat_1 @ X0))),
% 0.68/0.87      inference('simplify', [status(thm)], ['40'])).
% 0.68/0.87  thf('42', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         ((v1_relat_1 @ (k7_relat_1 @ X0 @ X1)) | ~ (v1_relat_1 @ X0))),
% 0.68/0.87      inference('simplify', [status(thm)], ['23'])).
% 0.68/0.87  thf('43', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         (~ (v1_relat_1 @ X0)
% 0.68/0.87          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 0.68/0.87             (k2_relat_1 @ X0)))),
% 0.68/0.87      inference('clc', [status(thm)], ['41', '42'])).
% 0.68/0.87  thf('44', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1))
% 0.68/0.87          | ~ (v1_relat_1 @ X1)
% 0.68/0.87          | ~ (v1_relat_1 @ X1))),
% 0.68/0.87      inference('sup+', [status(thm)], ['37', '43'])).
% 0.68/0.87  thf('45', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         (~ (v1_relat_1 @ X1)
% 0.68/0.87          | (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1)))),
% 0.68/0.87      inference('simplify', [status(thm)], ['44'])).
% 0.68/0.87  thf(t65_zfmisc_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.68/0.87       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.68/0.87  thf('46', plain,
% 0.68/0.87      (![X44 : $i, X45 : $i]:
% 0.68/0.87         (((k4_xboole_0 @ X44 @ (k1_tarski @ X45)) = (X44))
% 0.68/0.87          | (r2_hidden @ X45 @ X44))),
% 0.68/0.87      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.68/0.87  thf('47', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.68/0.87      inference('sup-', [status(thm)], ['5', '6'])).
% 0.68/0.87  thf(d18_relat_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( v1_relat_1 @ B ) =>
% 0.68/0.87       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.68/0.87  thf('48', plain,
% 0.68/0.87      (![X51 : $i, X52 : $i]:
% 0.68/0.87         (~ (v4_relat_1 @ X51 @ X52)
% 0.68/0.87          | (r1_tarski @ (k1_relat_1 @ X51) @ X52)
% 0.68/0.87          | ~ (v1_relat_1 @ X51))),
% 0.68/0.87      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.68/0.87  thf('49', plain,
% 0.68/0.87      ((~ (v1_relat_1 @ sk_D)
% 0.68/0.87        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['47', '48'])).
% 0.68/0.87  thf('50', plain, ((v1_relat_1 @ sk_D)),
% 0.68/0.87      inference('demod', [status(thm)], ['12', '13'])).
% 0.68/0.87  thf('51', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.68/0.87      inference('demod', [status(thm)], ['49', '50'])).
% 0.68/0.87  thf(t28_xboole_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.68/0.87  thf('52', plain,
% 0.68/0.87      (![X5 : $i, X6 : $i]:
% 0.68/0.87         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.68/0.87      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.68/0.87  thf('53', plain,
% 0.68/0.87      (((k3_xboole_0 @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))
% 0.68/0.87         = (k1_relat_1 @ sk_D))),
% 0.68/0.87      inference('sup-', [status(thm)], ['51', '52'])).
% 0.68/0.87  thf(t100_xboole_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.68/0.87  thf('54', plain,
% 0.68/0.87      (![X3 : $i, X4 : $i]:
% 0.68/0.87         ((k4_xboole_0 @ X3 @ X4)
% 0.68/0.87           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.68/0.87      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.68/0.87  thf('55', plain,
% 0.68/0.87      (((k4_xboole_0 @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))
% 0.68/0.87         = (k5_xboole_0 @ (k1_relat_1 @ sk_D) @ (k1_relat_1 @ sk_D)))),
% 0.68/0.87      inference('sup+', [status(thm)], ['53', '54'])).
% 0.68/0.87  thf(t92_xboole_1, axiom,
% 0.68/0.87    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.68/0.87  thf('56', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.68/0.87      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.68/0.87  thf('57', plain,
% 0.68/0.87      (((k4_xboole_0 @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))
% 0.68/0.87         = (k1_xboole_0))),
% 0.68/0.87      inference('demod', [status(thm)], ['55', '56'])).
% 0.68/0.87  thf('58', plain,
% 0.68/0.87      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.68/0.87        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_D)))),
% 0.68/0.87      inference('sup+', [status(thm)], ['46', '57'])).
% 0.68/0.87  thf(l1_zfmisc_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.68/0.87  thf('59', plain,
% 0.68/0.87      (![X37 : $i, X39 : $i]:
% 0.68/0.87         ((r1_tarski @ (k1_tarski @ X37) @ X39) | ~ (r2_hidden @ X37 @ X39))),
% 0.68/0.87      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.68/0.87  thf('60', plain,
% 0.68/0.87      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.68/0.87        | (r1_tarski @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_D)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['58', '59'])).
% 0.68/0.87  thf('61', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.68/0.87      inference('demod', [status(thm)], ['49', '50'])).
% 0.68/0.87  thf('62', plain,
% 0.68/0.87      (![X0 : $i, X2 : $i]:
% 0.68/0.87         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.68/0.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.68/0.87  thf('63', plain,
% 0.68/0.87      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_D))
% 0.68/0.87        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['61', '62'])).
% 0.68/0.87  thf('64', plain,
% 0.68/0.87      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.68/0.87        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['60', '63'])).
% 0.68/0.87  thf(t14_funct_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.68/0.87       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.68/0.87         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.68/0.87  thf('65', plain,
% 0.68/0.87      (![X64 : $i, X65 : $i]:
% 0.68/0.87         (((k1_relat_1 @ X65) != (k1_tarski @ X64))
% 0.68/0.87          | ((k2_relat_1 @ X65) = (k1_tarski @ (k1_funct_1 @ X65 @ X64)))
% 0.68/0.87          | ~ (v1_funct_1 @ X65)
% 0.68/0.87          | ~ (v1_relat_1 @ X65))),
% 0.68/0.87      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.68/0.87  thf('66', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.68/0.87          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.68/0.87          | ~ (v1_relat_1 @ X0)
% 0.68/0.87          | ~ (v1_funct_1 @ X0)
% 0.68/0.87          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.68/0.87      inference('sup-', [status(thm)], ['64', '65'])).
% 0.68/0.87  thf('67', plain,
% 0.68/0.87      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.68/0.87        | ~ (v1_funct_1 @ sk_D)
% 0.68/0.87        | ~ (v1_relat_1 @ sk_D)
% 0.68/0.87        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.68/0.87      inference('eq_res', [status(thm)], ['66'])).
% 0.68/0.87  thf('68', plain, ((v1_funct_1 @ sk_D)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('69', plain, ((v1_relat_1 @ sk_D)),
% 0.68/0.87      inference('demod', [status(thm)], ['12', '13'])).
% 0.68/0.87  thf('70', plain,
% 0.68/0.87      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.68/0.87        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.68/0.87      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.68/0.87  thf('71', plain,
% 0.68/0.87      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.68/0.87          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.68/0.87      inference('demod', [status(thm)], ['0', '3'])).
% 0.68/0.87  thf('72', plain,
% 0.68/0.87      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.68/0.87        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['70', '71'])).
% 0.68/0.87  thf('73', plain,
% 0.68/0.87      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['45', '72'])).
% 0.68/0.87  thf('74', plain, ((v1_relat_1 @ sk_D)),
% 0.68/0.87      inference('demod', [status(thm)], ['12', '13'])).
% 0.68/0.87  thf('75', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.68/0.87      inference('demod', [status(thm)], ['73', '74'])).
% 0.68/0.87  thf(t113_zfmisc_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.68/0.87       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.68/0.87  thf('76', plain,
% 0.68/0.87      (![X41 : $i, X42 : $i]:
% 0.68/0.87         (((k2_zfmisc_1 @ X41 @ X42) = (k1_xboole_0))
% 0.68/0.87          | ((X41) != (k1_xboole_0)))),
% 0.68/0.87      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.68/0.87  thf('77', plain,
% 0.68/0.87      (![X42 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X42) = (k1_xboole_0))),
% 0.68/0.87      inference('simplify', [status(thm)], ['76'])).
% 0.68/0.87  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.68/0.87  thf('78', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.68/0.87      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.68/0.87  thf('79', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.68/0.87      inference('demod', [status(thm)], ['73', '74'])).
% 0.68/0.87  thf('80', plain,
% 0.68/0.87      (![X42 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X42) = (k1_xboole_0))),
% 0.68/0.87      inference('simplify', [status(thm)], ['76'])).
% 0.68/0.87  thf('81', plain, (((k1_xboole_0) = (sk_D))),
% 0.68/0.87      inference('demod', [status(thm)], ['36', '75', '77', '78', '79', '80'])).
% 0.68/0.87  thf('82', plain,
% 0.68/0.87      (![X62 : $i, X63 : $i]:
% 0.68/0.87         ((r1_tarski @ (k7_relat_1 @ X62 @ X63) @ X62) | ~ (v1_relat_1 @ X62))),
% 0.68/0.87      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.68/0.87  thf('83', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.68/0.87      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.68/0.87  thf('84', plain,
% 0.68/0.87      (![X0 : $i, X2 : $i]:
% 0.68/0.87         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.68/0.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.68/0.87  thf('85', plain,
% 0.68/0.87      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['83', '84'])).
% 0.68/0.87  thf('86', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         (~ (v1_relat_1 @ k1_xboole_0)
% 0.68/0.87          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['82', '85'])).
% 0.68/0.87  thf('87', plain,
% 0.68/0.87      (![X42 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X42) = (k1_xboole_0))),
% 0.68/0.87      inference('simplify', [status(thm)], ['76'])).
% 0.68/0.87  thf('88', plain,
% 0.68/0.87      (![X53 : $i, X54 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X53 @ X54))),
% 0.68/0.87      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.68/0.87  thf('89', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.68/0.87      inference('sup+', [status(thm)], ['87', '88'])).
% 0.68/0.87  thf('90', plain,
% 0.68/0.87      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.68/0.87      inference('demod', [status(thm)], ['86', '89'])).
% 0.68/0.87  thf('91', plain,
% 0.68/0.87      (![X55 : $i, X56 : $i]:
% 0.68/0.87         (((k2_relat_1 @ (k7_relat_1 @ X55 @ X56)) = (k9_relat_1 @ X55 @ X56))
% 0.68/0.87          | ~ (v1_relat_1 @ X55))),
% 0.68/0.87      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.68/0.87  thf('92', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         (((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))
% 0.68/0.87          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.68/0.87      inference('sup+', [status(thm)], ['90', '91'])).
% 0.68/0.87  thf(t60_relat_1, axiom,
% 0.68/0.87    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.68/0.87     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.68/0.87  thf('93', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.68/0.87      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.68/0.87  thf('94', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.68/0.87      inference('sup+', [status(thm)], ['87', '88'])).
% 0.68/0.87  thf('95', plain,
% 0.68/0.87      (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))),
% 0.68/0.87      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.68/0.87  thf('96', plain, (((k1_xboole_0) = (sk_D))),
% 0.68/0.87      inference('demod', [status(thm)], ['36', '75', '77', '78', '79', '80'])).
% 0.68/0.87  thf('97', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.68/0.87      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.68/0.87  thf('98', plain, ($false),
% 0.68/0.87      inference('demod', [status(thm)], ['4', '81', '95', '96', '97'])).
% 0.68/0.87  
% 0.68/0.87  % SZS output end Refutation
% 0.68/0.87  
% 0.73/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
