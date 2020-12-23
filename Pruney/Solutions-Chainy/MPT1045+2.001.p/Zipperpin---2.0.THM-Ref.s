%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zLHV3Anw2a

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:19 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 695 expanded)
%              Number of leaves         :   44 ( 211 expanded)
%              Depth                    :   14
%              Number of atoms          :  983 (8903 expanded)
%              Number of equality atoms :  115 ( 916 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_partfun1_type,type,(
    k3_partfun1: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('1',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X42 != X41 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X42 ) @ ( k1_tarski @ X41 ) )
       != ( k1_tarski @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('2',plain,(
    ! [X41: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X41 ) @ ( k1_tarski @ X41 ) )
     != ( k1_tarski @ X41 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('4',plain,(
    ! [X45: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X45 ) )
      = X45 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X46 @ X47 ) )
      = ( k3_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('11',plain,(
    ! [X41: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X41 ) ) ),
    inference(demod,[status(thm)],['2','9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
       != ( k1_tarski @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf('13',plain,(
    ! [X1: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('14',plain,(
    ! [X54: $i] :
      ( ( v1_funct_1 @ X54 )
      | ~ ( v1_xboole_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('15',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X64 ) @ X65 )
      | ( v1_funct_2 @ X64 @ ( k1_relat_1 @ X64 ) @ X65 )
      | ~ ( v1_funct_1 @ X64 )
      | ~ ( v1_relat_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('18',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('19',plain,(
    ! [X44: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('20',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ( v1_relat_1 @ X55 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('21',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18','21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','23'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X44: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('28',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X60 ) ) )
      | ( v1_partfun1 @ X58 @ X59 )
      | ~ ( v1_funct_2 @ X58 @ X59 @ X60 )
      | ~ ( v1_funct_1 @ X58 )
      | ( v1_xboole_0 @ X60 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ( v1_partfun1 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t161_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k5_partfun1 @ A @ B @ ( k3_partfun1 @ C @ A @ B ) )
          = ( k1_tarski @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( k5_partfun1 @ A @ B @ ( k3_partfun1 @ C @ A @ B ) )
            = ( k1_tarski @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t161_funct_2])).

thf('30',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('32',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k2_zfmisc_1 @ X39 @ X40 )
        = k1_xboole_0 )
      | ( X40 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('33',plain,(
    ! [X39: $i] :
      ( ( k2_zfmisc_1 @ X39 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('36',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r1_tarski @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('37',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('39',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,
    ( ( sk_C = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','43'])).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('46',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X60 ) ) )
      | ( v1_partfun1 @ X58 @ X59 )
      | ~ ( v1_funct_2 @ X58 @ X59 @ X60 )
      | ~ ( v1_funct_1 @ X58 )
      | ( v1_xboole_0 @ X60 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('49',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t174_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_partfun1 @ C @ A )
      <=> ( ( k5_partfun1 @ A @ B @ C )
          = ( k1_tarski @ C ) ) ) ) )).

thf('54',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ~ ( v1_partfun1 @ X61 @ X62 )
      | ( ( k5_partfun1 @ X62 @ X63 @ X61 )
        = ( k1_tarski @ X61 ) )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X63 ) ) )
      | ~ ( v1_funct_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t174_partfun1])).

thf('55',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_partfun1 @ sk_A @ sk_B @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ~ ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ( k5_partfun1 @ sk_A @ sk_B @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ~ ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( ( k5_partfun1 @ sk_A @ sk_B @ sk_C )
      = ( k1_tarski @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    ( k5_partfun1 @ sk_A @ sk_B @ ( k3_partfun1 @ sk_C @ sk_A @ sk_B ) )
 != ( k1_tarski @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t87_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k3_partfun1 @ C @ A @ B )
        = C ) ) )).

thf('61',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ( ( k3_partfun1 @ X66 @ X67 @ X68 )
        = X66 )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X67 @ X68 ) ) )
      | ~ ( v1_funct_1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[t87_partfun1])).

thf('62',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k3_partfun1 @ sk_C @ sk_A @ sk_B )
      = sk_C ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k3_partfun1 @ sk_C @ sk_A @ sk_B )
    = sk_C ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ( k5_partfun1 @ sk_A @ sk_B @ sk_C )
 != ( k1_tarski @ sk_C ) ),
    inference(demod,[status(thm)],['59','64'])).

thf('66',plain,
    ( ( ( k1_tarski @ sk_C )
     != ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['58','65'])).

thf('67',plain,(
    v1_xboole_0 @ sk_B ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['46','67'])).

thf('69',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['30','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ( v1_partfun1 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','70'])).

thf('72',plain,
    ( ( ( k5_partfun1 @ sk_A @ sk_B @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ~ ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('73',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['46','67'])).

thf('74',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['46','67'])).

thf('75',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['46','67'])).

thf('76',plain,
    ( ( ( k5_partfun1 @ sk_A @ sk_B @ k1_xboole_0 )
      = ( k1_tarski @ k1_xboole_0 ) )
    | ~ ( v1_partfun1 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('77',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['77'])).

thf('79',plain,(
    v1_xboole_0 @ sk_B ),
    inference(simplify,[status(thm)],['66'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['77'])).

thf('84',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ sk_B ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('87',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['85','86'])).

thf('88',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['79','87'])).

thf('89',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['77'])).

thf('90',plain,(
    sk_A = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['88','89'])).

thf('91',plain,(
    sk_A = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['78','90'])).

thf('92',plain,(
    v1_xboole_0 @ sk_B ),
    inference(simplify,[status(thm)],['66'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('94',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    sk_A = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['78','90'])).

thf('96',plain,
    ( ( ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k1_tarski @ k1_xboole_0 ) )
    | ~ ( v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','91','94','95'])).

thf('97',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['77'])).

thf('98',plain,(
    ( k5_partfun1 @ sk_A @ sk_B @ sk_C )
 != ( k1_tarski @ sk_C ) ),
    inference(demod,[status(thm)],['59','64'])).

thf('99',plain,
    ( ( ( k5_partfun1 @ k1_xboole_0 @ sk_B @ sk_C )
     != ( k1_tarski @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k2_zfmisc_1 @ X39 @ X40 )
        = k1_xboole_0 )
      | ( X39 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('101',plain,(
    ! [X40: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X40 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['77'])).

thf('103',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['101','104'])).

thf('106',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r1_tarski @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('107',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('109',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C )
      | ( k1_xboole_0 = sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('111',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('113',plain,
    ( ( ( k5_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 )
     != ( k1_tarski @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['99','111','112'])).

thf('114',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['92','93'])).

thf('115',plain,
    ( ( ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != ( k1_tarski @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    sk_A = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['88','89'])).

thf('117',plain,(
    ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['115','116'])).

thf('118',plain,(
    ~ ( v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['96','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ X0 ) ),
    inference(clc,[status(thm)],['71','118'])).

thf('120',plain,(
    $false ),
    inference(demod,[status(thm)],['13','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zLHV3Anw2a
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:44:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.05/1.22  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.05/1.22  % Solved by: fo/fo7.sh
% 1.05/1.22  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.22  % done 1848 iterations in 0.763s
% 1.05/1.22  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.05/1.22  % SZS output start Refutation
% 1.05/1.22  thf(sk_B_type, type, sk_B: $i).
% 1.05/1.22  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.05/1.22  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.05/1.22  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.05/1.22  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.05/1.22  thf(k3_partfun1_type, type, k3_partfun1: $i > $i > $i > $i).
% 1.05/1.22  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.05/1.22  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.05/1.22  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.05/1.22  thf(k5_partfun1_type, type, k5_partfun1: $i > $i > $i > $i).
% 1.05/1.22  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.05/1.22  thf(sk_C_type, type, sk_C: $i).
% 1.05/1.22  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.05/1.22  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.05/1.22  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.05/1.22  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.05/1.22  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.05/1.22  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.05/1.22  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.05/1.22  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.22  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.05/1.22  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.05/1.22  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.05/1.22  thf(l13_xboole_0, axiom,
% 1.05/1.22    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.05/1.22  thf('0', plain,
% 1.05/1.22      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.05/1.22      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.05/1.22  thf(t20_zfmisc_1, axiom,
% 1.05/1.22    (![A:$i,B:$i]:
% 1.05/1.22     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.05/1.22         ( k1_tarski @ A ) ) <=>
% 1.05/1.22       ( ( A ) != ( B ) ) ))).
% 1.05/1.22  thf('1', plain,
% 1.05/1.22      (![X41 : $i, X42 : $i]:
% 1.05/1.22         (((X42) != (X41))
% 1.05/1.22          | ((k4_xboole_0 @ (k1_tarski @ X42) @ (k1_tarski @ X41))
% 1.05/1.22              != (k1_tarski @ X42)))),
% 1.05/1.22      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 1.05/1.22  thf('2', plain,
% 1.05/1.22      (![X41 : $i]:
% 1.05/1.22         ((k4_xboole_0 @ (k1_tarski @ X41) @ (k1_tarski @ X41))
% 1.05/1.22           != (k1_tarski @ X41))),
% 1.05/1.22      inference('simplify', [status(thm)], ['1'])).
% 1.05/1.22  thf(t69_enumset1, axiom,
% 1.05/1.22    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.05/1.22  thf('3', plain, (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 1.05/1.22      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.05/1.22  thf(t11_setfam_1, axiom,
% 1.05/1.22    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 1.05/1.22  thf('4', plain, (![X45 : $i]: ((k1_setfam_1 @ (k1_tarski @ X45)) = (X45))),
% 1.05/1.22      inference('cnf', [status(esa)], [t11_setfam_1])).
% 1.05/1.22  thf('5', plain, (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 1.05/1.22      inference('sup+', [status(thm)], ['3', '4'])).
% 1.05/1.22  thf(t12_setfam_1, axiom,
% 1.05/1.22    (![A:$i,B:$i]:
% 1.05/1.22     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.05/1.22  thf('6', plain,
% 1.05/1.22      (![X46 : $i, X47 : $i]:
% 1.05/1.22         ((k1_setfam_1 @ (k2_tarski @ X46 @ X47)) = (k3_xboole_0 @ X46 @ X47))),
% 1.05/1.22      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.05/1.22  thf('7', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.05/1.22      inference('demod', [status(thm)], ['5', '6'])).
% 1.05/1.22  thf(t100_xboole_1, axiom,
% 1.05/1.22    (![A:$i,B:$i]:
% 1.05/1.22     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.05/1.22  thf('8', plain,
% 1.05/1.22      (![X4 : $i, X5 : $i]:
% 1.05/1.22         ((k4_xboole_0 @ X4 @ X5)
% 1.05/1.22           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.05/1.22      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.05/1.22  thf('9', plain,
% 1.05/1.22      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.05/1.22      inference('sup+', [status(thm)], ['7', '8'])).
% 1.05/1.22  thf(t92_xboole_1, axiom,
% 1.05/1.22    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.05/1.22  thf('10', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 1.05/1.22      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.05/1.22  thf('11', plain, (![X41 : $i]: ((k1_xboole_0) != (k1_tarski @ X41))),
% 1.05/1.22      inference('demod', [status(thm)], ['2', '9', '10'])).
% 1.05/1.22  thf('12', plain,
% 1.05/1.22      (![X0 : $i, X1 : $i]: (((X0) != (k1_tarski @ X1)) | ~ (v1_xboole_0 @ X0))),
% 1.05/1.22      inference('sup-', [status(thm)], ['0', '11'])).
% 1.05/1.22  thf('13', plain, (![X1 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X1))),
% 1.05/1.22      inference('simplify', [status(thm)], ['12'])).
% 1.05/1.22  thf(cc1_funct_1, axiom,
% 1.05/1.22    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 1.05/1.22  thf('14', plain, (![X54 : $i]: ((v1_funct_1 @ X54) | ~ (v1_xboole_0 @ X54))),
% 1.05/1.22      inference('cnf', [status(esa)], [cc1_funct_1])).
% 1.05/1.22  thf(t60_relat_1, axiom,
% 1.05/1.22    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.05/1.22     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.05/1.22  thf('15', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.05/1.22      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.05/1.22  thf(t4_funct_2, axiom,
% 1.05/1.22    (![A:$i,B:$i]:
% 1.05/1.22     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.05/1.22       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.05/1.22         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 1.05/1.22           ( m1_subset_1 @
% 1.05/1.22             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 1.05/1.22  thf('16', plain,
% 1.05/1.22      (![X64 : $i, X65 : $i]:
% 1.05/1.22         (~ (r1_tarski @ (k2_relat_1 @ X64) @ X65)
% 1.05/1.22          | (v1_funct_2 @ X64 @ (k1_relat_1 @ X64) @ X65)
% 1.05/1.22          | ~ (v1_funct_1 @ X64)
% 1.05/1.22          | ~ (v1_relat_1 @ X64))),
% 1.05/1.22      inference('cnf', [status(esa)], [t4_funct_2])).
% 1.05/1.22  thf('17', plain,
% 1.05/1.22      (![X0 : $i]:
% 1.05/1.22         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 1.05/1.22          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.05/1.22          | ~ (v1_funct_1 @ k1_xboole_0)
% 1.05/1.22          | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 1.05/1.22      inference('sup-', [status(thm)], ['15', '16'])).
% 1.05/1.22  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.05/1.22  thf('18', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 1.05/1.22      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.05/1.22  thf(t4_subset_1, axiom,
% 1.05/1.22    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.05/1.22  thf('19', plain,
% 1.05/1.22      (![X44 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X44))),
% 1.05/1.22      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.05/1.22  thf(cc1_relset_1, axiom,
% 1.05/1.22    (![A:$i,B:$i,C:$i]:
% 1.05/1.22     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.22       ( v1_relat_1 @ C ) ))).
% 1.05/1.22  thf('20', plain,
% 1.05/1.22      (![X55 : $i, X56 : $i, X57 : $i]:
% 1.05/1.22         ((v1_relat_1 @ X55)
% 1.05/1.22          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57))))),
% 1.05/1.22      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.05/1.22  thf('21', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.05/1.22      inference('sup-', [status(thm)], ['19', '20'])).
% 1.05/1.22  thf('22', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.05/1.22      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.05/1.22  thf('23', plain,
% 1.05/1.22      (![X0 : $i]:
% 1.05/1.22         (~ (v1_funct_1 @ k1_xboole_0)
% 1.05/1.22          | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0))),
% 1.05/1.22      inference('demod', [status(thm)], ['17', '18', '21', '22'])).
% 1.05/1.22  thf('24', plain,
% 1.05/1.22      (![X0 : $i]:
% 1.05/1.22         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.05/1.22          | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0))),
% 1.05/1.22      inference('sup-', [status(thm)], ['14', '23'])).
% 1.05/1.22  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.05/1.22  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.05/1.22      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.05/1.22  thf('26', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.05/1.22      inference('demod', [status(thm)], ['24', '25'])).
% 1.05/1.22  thf('27', plain,
% 1.05/1.22      (![X44 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X44))),
% 1.05/1.22      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.05/1.22  thf(cc5_funct_2, axiom,
% 1.05/1.22    (![A:$i,B:$i]:
% 1.05/1.22     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.05/1.22       ( ![C:$i]:
% 1.05/1.22         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.22           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 1.05/1.22             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 1.05/1.22  thf('28', plain,
% 1.05/1.22      (![X58 : $i, X59 : $i, X60 : $i]:
% 1.05/1.22         (~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X60)))
% 1.05/1.22          | (v1_partfun1 @ X58 @ X59)
% 1.05/1.22          | ~ (v1_funct_2 @ X58 @ X59 @ X60)
% 1.05/1.22          | ~ (v1_funct_1 @ X58)
% 1.05/1.22          | (v1_xboole_0 @ X60))),
% 1.05/1.22      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.05/1.22  thf('29', plain,
% 1.05/1.22      (![X0 : $i, X1 : $i]:
% 1.05/1.22         ((v1_xboole_0 @ X0)
% 1.05/1.22          | ~ (v1_funct_1 @ k1_xboole_0)
% 1.05/1.22          | ~ (v1_funct_2 @ k1_xboole_0 @ X1 @ X0)
% 1.05/1.22          | (v1_partfun1 @ k1_xboole_0 @ X1))),
% 1.05/1.22      inference('sup-', [status(thm)], ['27', '28'])).
% 1.05/1.22  thf(t161_funct_2, conjecture,
% 1.05/1.22    (![A:$i,B:$i,C:$i]:
% 1.05/1.22     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.05/1.22         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.05/1.22       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.05/1.22         ( ( k5_partfun1 @ A @ B @ ( k3_partfun1 @ C @ A @ B ) ) =
% 1.05/1.22           ( k1_tarski @ C ) ) ) ))).
% 1.05/1.22  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.22    (~( ![A:$i,B:$i,C:$i]:
% 1.05/1.22        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.05/1.22            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.05/1.22          ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.05/1.22            ( ( k5_partfun1 @ A @ B @ ( k3_partfun1 @ C @ A @ B ) ) =
% 1.05/1.22              ( k1_tarski @ C ) ) ) ) )),
% 1.05/1.22    inference('cnf.neg', [status(esa)], [t161_funct_2])).
% 1.05/1.22  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.22  thf('31', plain,
% 1.05/1.22      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.05/1.22      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.05/1.22  thf(t113_zfmisc_1, axiom,
% 1.05/1.22    (![A:$i,B:$i]:
% 1.05/1.22     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.05/1.22       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.05/1.22  thf('32', plain,
% 1.05/1.22      (![X39 : $i, X40 : $i]:
% 1.05/1.22         (((k2_zfmisc_1 @ X39 @ X40) = (k1_xboole_0))
% 1.05/1.22          | ((X40) != (k1_xboole_0)))),
% 1.05/1.22      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.05/1.22  thf('33', plain,
% 1.05/1.22      (![X39 : $i]: ((k2_zfmisc_1 @ X39 @ k1_xboole_0) = (k1_xboole_0))),
% 1.05/1.22      inference('simplify', [status(thm)], ['32'])).
% 1.05/1.22  thf('34', plain,
% 1.05/1.22      (![X0 : $i, X1 : $i]:
% 1.05/1.22         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.05/1.22      inference('sup+', [status(thm)], ['31', '33'])).
% 1.05/1.22  thf('35', plain,
% 1.05/1.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.22  thf(t3_subset, axiom,
% 1.05/1.22    (![A:$i,B:$i]:
% 1.05/1.22     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.05/1.22  thf('36', plain,
% 1.05/1.22      (![X48 : $i, X49 : $i]:
% 1.05/1.22         ((r1_tarski @ X48 @ X49) | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X49)))),
% 1.05/1.22      inference('cnf', [status(esa)], [t3_subset])).
% 1.05/1.22  thf('37', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 1.05/1.22      inference('sup-', [status(thm)], ['35', '36'])).
% 1.05/1.22  thf('38', plain,
% 1.05/1.22      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.05/1.22      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.05/1.22  thf('39', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 1.05/1.22      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.05/1.22  thf(d10_xboole_0, axiom,
% 1.05/1.22    (![A:$i,B:$i]:
% 1.05/1.22     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.05/1.22  thf('40', plain,
% 1.05/1.22      (![X1 : $i, X3 : $i]:
% 1.05/1.22         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 1.05/1.22      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.05/1.22  thf('41', plain,
% 1.05/1.22      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.05/1.22      inference('sup-', [status(thm)], ['39', '40'])).
% 1.05/1.22  thf('42', plain,
% 1.05/1.22      (![X0 : $i, X1 : $i]:
% 1.05/1.22         (~ (r1_tarski @ X1 @ X0)
% 1.05/1.22          | ~ (v1_xboole_0 @ X0)
% 1.05/1.22          | ((X1) = (k1_xboole_0)))),
% 1.05/1.22      inference('sup-', [status(thm)], ['38', '41'])).
% 1.05/1.22  thf('43', plain,
% 1.05/1.22      ((((sk_C) = (k1_xboole_0))
% 1.05/1.22        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.22      inference('sup-', [status(thm)], ['37', '42'])).
% 1.05/1.22  thf('44', plain,
% 1.05/1.22      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.05/1.22        | ~ (v1_xboole_0 @ sk_B)
% 1.05/1.22        | ((sk_C) = (k1_xboole_0)))),
% 1.05/1.22      inference('sup-', [status(thm)], ['34', '43'])).
% 1.05/1.22  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.05/1.22      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.05/1.22  thf('46', plain, ((~ (v1_xboole_0 @ sk_B) | ((sk_C) = (k1_xboole_0)))),
% 1.05/1.22      inference('demod', [status(thm)], ['44', '45'])).
% 1.05/1.22  thf('47', plain,
% 1.05/1.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.22  thf('48', plain,
% 1.05/1.22      (![X58 : $i, X59 : $i, X60 : $i]:
% 1.05/1.22         (~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X60)))
% 1.05/1.22          | (v1_partfun1 @ X58 @ X59)
% 1.05/1.22          | ~ (v1_funct_2 @ X58 @ X59 @ X60)
% 1.05/1.22          | ~ (v1_funct_1 @ X58)
% 1.05/1.22          | (v1_xboole_0 @ X60))),
% 1.05/1.22      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.05/1.22  thf('49', plain,
% 1.05/1.22      (((v1_xboole_0 @ sk_B)
% 1.05/1.22        | ~ (v1_funct_1 @ sk_C)
% 1.05/1.22        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.05/1.22        | (v1_partfun1 @ sk_C @ sk_A))),
% 1.05/1.22      inference('sup-', [status(thm)], ['47', '48'])).
% 1.05/1.22  thf('50', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.22  thf('51', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.05/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.22  thf('52', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_C @ sk_A))),
% 1.05/1.22      inference('demod', [status(thm)], ['49', '50', '51'])).
% 1.05/1.22  thf('53', plain,
% 1.05/1.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.22  thf(t174_partfun1, axiom,
% 1.05/1.22    (![A:$i,B:$i,C:$i]:
% 1.05/1.22     ( ( ( v1_funct_1 @ C ) & 
% 1.05/1.22         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.05/1.22       ( ( v1_partfun1 @ C @ A ) <=>
% 1.05/1.22         ( ( k5_partfun1 @ A @ B @ C ) = ( k1_tarski @ C ) ) ) ))).
% 1.05/1.22  thf('54', plain,
% 1.05/1.22      (![X61 : $i, X62 : $i, X63 : $i]:
% 1.05/1.22         (~ (v1_partfun1 @ X61 @ X62)
% 1.05/1.22          | ((k5_partfun1 @ X62 @ X63 @ X61) = (k1_tarski @ X61))
% 1.05/1.22          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X63)))
% 1.05/1.22          | ~ (v1_funct_1 @ X61))),
% 1.05/1.22      inference('cnf', [status(esa)], [t174_partfun1])).
% 1.05/1.22  thf('55', plain,
% 1.05/1.22      ((~ (v1_funct_1 @ sk_C)
% 1.05/1.22        | ((k5_partfun1 @ sk_A @ sk_B @ sk_C) = (k1_tarski @ sk_C))
% 1.05/1.22        | ~ (v1_partfun1 @ sk_C @ sk_A))),
% 1.05/1.22      inference('sup-', [status(thm)], ['53', '54'])).
% 1.05/1.22  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.22  thf('57', plain,
% 1.05/1.22      ((((k5_partfun1 @ sk_A @ sk_B @ sk_C) = (k1_tarski @ sk_C))
% 1.05/1.22        | ~ (v1_partfun1 @ sk_C @ sk_A))),
% 1.05/1.22      inference('demod', [status(thm)], ['55', '56'])).
% 1.05/1.22  thf('58', plain,
% 1.05/1.22      (((v1_xboole_0 @ sk_B)
% 1.05/1.22        | ((k5_partfun1 @ sk_A @ sk_B @ sk_C) = (k1_tarski @ sk_C)))),
% 1.05/1.22      inference('sup-', [status(thm)], ['52', '57'])).
% 1.05/1.22  thf('59', plain,
% 1.05/1.22      (((k5_partfun1 @ sk_A @ sk_B @ (k3_partfun1 @ sk_C @ sk_A @ sk_B))
% 1.05/1.22         != (k1_tarski @ sk_C))),
% 1.05/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.22  thf('60', plain,
% 1.05/1.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.22  thf(t87_partfun1, axiom,
% 1.05/1.22    (![A:$i,B:$i,C:$i]:
% 1.05/1.22     ( ( ( v1_funct_1 @ C ) & 
% 1.05/1.22         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.05/1.22       ( ( k3_partfun1 @ C @ A @ B ) = ( C ) ) ))).
% 1.05/1.22  thf('61', plain,
% 1.05/1.22      (![X66 : $i, X67 : $i, X68 : $i]:
% 1.05/1.22         (((k3_partfun1 @ X66 @ X67 @ X68) = (X66))
% 1.05/1.22          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X67 @ X68)))
% 1.05/1.22          | ~ (v1_funct_1 @ X66))),
% 1.05/1.22      inference('cnf', [status(esa)], [t87_partfun1])).
% 1.05/1.22  thf('62', plain,
% 1.05/1.22      ((~ (v1_funct_1 @ sk_C) | ((k3_partfun1 @ sk_C @ sk_A @ sk_B) = (sk_C)))),
% 1.05/1.22      inference('sup-', [status(thm)], ['60', '61'])).
% 1.05/1.22  thf('63', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.22  thf('64', plain, (((k3_partfun1 @ sk_C @ sk_A @ sk_B) = (sk_C))),
% 1.05/1.22      inference('demod', [status(thm)], ['62', '63'])).
% 1.05/1.22  thf('65', plain,
% 1.05/1.22      (((k5_partfun1 @ sk_A @ sk_B @ sk_C) != (k1_tarski @ sk_C))),
% 1.05/1.22      inference('demod', [status(thm)], ['59', '64'])).
% 1.05/1.22  thf('66', plain,
% 1.05/1.22      ((((k1_tarski @ sk_C) != (k1_tarski @ sk_C)) | (v1_xboole_0 @ sk_B))),
% 1.05/1.22      inference('sup-', [status(thm)], ['58', '65'])).
% 1.05/1.22  thf('67', plain, ((v1_xboole_0 @ sk_B)),
% 1.05/1.22      inference('simplify', [status(thm)], ['66'])).
% 1.05/1.22  thf('68', plain, (((sk_C) = (k1_xboole_0))),
% 1.05/1.22      inference('demod', [status(thm)], ['46', '67'])).
% 1.05/1.22  thf('69', plain, ((v1_funct_1 @ k1_xboole_0)),
% 1.05/1.22      inference('demod', [status(thm)], ['30', '68'])).
% 1.05/1.22  thf('70', plain,
% 1.05/1.22      (![X0 : $i, X1 : $i]:
% 1.05/1.22         ((v1_xboole_0 @ X0)
% 1.05/1.22          | ~ (v1_funct_2 @ k1_xboole_0 @ X1 @ X0)
% 1.05/1.22          | (v1_partfun1 @ k1_xboole_0 @ X1))),
% 1.05/1.22      inference('demod', [status(thm)], ['29', '69'])).
% 1.05/1.22  thf('71', plain,
% 1.05/1.22      (![X0 : $i]:
% 1.05/1.22         ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ X0))),
% 1.05/1.22      inference('sup-', [status(thm)], ['26', '70'])).
% 1.05/1.22  thf('72', plain,
% 1.05/1.22      ((((k5_partfun1 @ sk_A @ sk_B @ sk_C) = (k1_tarski @ sk_C))
% 1.05/1.22        | ~ (v1_partfun1 @ sk_C @ sk_A))),
% 1.05/1.22      inference('demod', [status(thm)], ['55', '56'])).
% 1.05/1.22  thf('73', plain, (((sk_C) = (k1_xboole_0))),
% 1.05/1.22      inference('demod', [status(thm)], ['46', '67'])).
% 1.05/1.22  thf('74', plain, (((sk_C) = (k1_xboole_0))),
% 1.05/1.22      inference('demod', [status(thm)], ['46', '67'])).
% 1.05/1.22  thf('75', plain, (((sk_C) = (k1_xboole_0))),
% 1.05/1.22      inference('demod', [status(thm)], ['46', '67'])).
% 1.05/1.22  thf('76', plain,
% 1.05/1.22      ((((k5_partfun1 @ sk_A @ sk_B @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))
% 1.05/1.22        | ~ (v1_partfun1 @ k1_xboole_0 @ sk_A))),
% 1.05/1.22      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 1.05/1.22  thf('77', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) != (k1_xboole_0)))),
% 1.05/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.22  thf('78', plain,
% 1.05/1.22      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.22      inference('split', [status(esa)], ['77'])).
% 1.05/1.22  thf('79', plain, ((v1_xboole_0 @ sk_B)),
% 1.05/1.22      inference('simplify', [status(thm)], ['66'])).
% 1.05/1.22  thf('80', plain,
% 1.05/1.22      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.05/1.22      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.05/1.22  thf('81', plain,
% 1.05/1.22      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.05/1.22      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.05/1.22  thf('82', plain,
% 1.05/1.22      (![X0 : $i, X1 : $i]:
% 1.05/1.22         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 1.05/1.22      inference('sup+', [status(thm)], ['80', '81'])).
% 1.05/1.22  thf('83', plain,
% 1.05/1.22      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.05/1.22      inference('split', [status(esa)], ['77'])).
% 1.05/1.22  thf('84', plain,
% 1.05/1.22      ((![X0 : $i]:
% 1.05/1.22          (((X0) != (k1_xboole_0))
% 1.05/1.22           | ~ (v1_xboole_0 @ X0)
% 1.05/1.22           | ~ (v1_xboole_0 @ sk_B)))
% 1.05/1.22         <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.05/1.22      inference('sup-', [status(thm)], ['82', '83'])).
% 1.05/1.22  thf('85', plain,
% 1.05/1.22      (((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 1.05/1.22         <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.05/1.22      inference('simplify', [status(thm)], ['84'])).
% 1.05/1.22  thf('86', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.05/1.22      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.05/1.22  thf('87', plain,
% 1.05/1.22      ((~ (v1_xboole_0 @ sk_B)) <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.05/1.22      inference('simplify_reflect+', [status(thm)], ['85', '86'])).
% 1.05/1.22  thf('88', plain, ((((sk_B) = (k1_xboole_0)))),
% 1.05/1.22      inference('sup-', [status(thm)], ['79', '87'])).
% 1.05/1.22  thf('89', plain, ((((sk_A) = (k1_xboole_0))) | ~ (((sk_B) = (k1_xboole_0)))),
% 1.05/1.22      inference('split', [status(esa)], ['77'])).
% 1.05/1.22  thf('90', plain, ((((sk_A) = (k1_xboole_0)))),
% 1.05/1.22      inference('sat_resolution*', [status(thm)], ['88', '89'])).
% 1.05/1.22  thf('91', plain, (((sk_A) = (k1_xboole_0))),
% 1.05/1.22      inference('simpl_trail', [status(thm)], ['78', '90'])).
% 1.05/1.22  thf('92', plain, ((v1_xboole_0 @ sk_B)),
% 1.05/1.22      inference('simplify', [status(thm)], ['66'])).
% 1.05/1.22  thf('93', plain,
% 1.05/1.22      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.05/1.22      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.05/1.22  thf('94', plain, (((sk_B) = (k1_xboole_0))),
% 1.05/1.22      inference('sup-', [status(thm)], ['92', '93'])).
% 1.05/1.22  thf('95', plain, (((sk_A) = (k1_xboole_0))),
% 1.05/1.22      inference('simpl_trail', [status(thm)], ['78', '90'])).
% 1.05/1.22  thf('96', plain,
% 1.05/1.22      ((((k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 1.05/1.22          = (k1_tarski @ k1_xboole_0))
% 1.05/1.22        | ~ (v1_partfun1 @ k1_xboole_0 @ k1_xboole_0))),
% 1.05/1.22      inference('demod', [status(thm)], ['76', '91', '94', '95'])).
% 1.05/1.22  thf('97', plain,
% 1.05/1.22      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.22      inference('split', [status(esa)], ['77'])).
% 1.05/1.22  thf('98', plain,
% 1.05/1.22      (((k5_partfun1 @ sk_A @ sk_B @ sk_C) != (k1_tarski @ sk_C))),
% 1.05/1.22      inference('demod', [status(thm)], ['59', '64'])).
% 1.05/1.22  thf('99', plain,
% 1.05/1.22      ((((k5_partfun1 @ k1_xboole_0 @ sk_B @ sk_C) != (k1_tarski @ sk_C)))
% 1.05/1.22         <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.22      inference('sup-', [status(thm)], ['97', '98'])).
% 1.05/1.22  thf('100', plain,
% 1.05/1.22      (![X39 : $i, X40 : $i]:
% 1.05/1.22         (((k2_zfmisc_1 @ X39 @ X40) = (k1_xboole_0))
% 1.05/1.22          | ((X39) != (k1_xboole_0)))),
% 1.05/1.22      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.05/1.22  thf('101', plain,
% 1.05/1.22      (![X40 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X40) = (k1_xboole_0))),
% 1.05/1.22      inference('simplify', [status(thm)], ['100'])).
% 1.05/1.22  thf('102', plain,
% 1.05/1.22      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.22      inference('split', [status(esa)], ['77'])).
% 1.05/1.22  thf('103', plain,
% 1.05/1.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.22  thf('104', plain,
% 1.05/1.22      (((m1_subset_1 @ sk_C @ 
% 1.05/1.22         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 1.05/1.22         <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.22      inference('sup+', [status(thm)], ['102', '103'])).
% 1.05/1.22  thf('105', plain,
% 1.05/1.22      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))
% 1.05/1.22         <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.22      inference('sup+', [status(thm)], ['101', '104'])).
% 1.05/1.22  thf('106', plain,
% 1.05/1.22      (![X48 : $i, X49 : $i]:
% 1.05/1.22         ((r1_tarski @ X48 @ X49) | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X49)))),
% 1.05/1.22      inference('cnf', [status(esa)], [t3_subset])).
% 1.05/1.22  thf('107', plain,
% 1.05/1.22      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.22      inference('sup-', [status(thm)], ['105', '106'])).
% 1.05/1.22  thf('108', plain,
% 1.05/1.22      (![X1 : $i, X3 : $i]:
% 1.05/1.22         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 1.05/1.22      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.05/1.22  thf('109', plain,
% 1.05/1.22      (((~ (r1_tarski @ k1_xboole_0 @ sk_C) | ((k1_xboole_0) = (sk_C))))
% 1.05/1.22         <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.22      inference('sup-', [status(thm)], ['107', '108'])).
% 1.05/1.22  thf('110', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 1.05/1.22      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.05/1.22  thf('111', plain,
% 1.05/1.22      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.22      inference('demod', [status(thm)], ['109', '110'])).
% 1.05/1.22  thf('112', plain,
% 1.05/1.22      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.22      inference('demod', [status(thm)], ['109', '110'])).
% 1.05/1.22  thf('113', plain,
% 1.05/1.22      ((((k5_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0)
% 1.05/1.22          != (k1_tarski @ k1_xboole_0)))
% 1.05/1.22         <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.22      inference('demod', [status(thm)], ['99', '111', '112'])).
% 1.05/1.22  thf('114', plain, (((sk_B) = (k1_xboole_0))),
% 1.05/1.22      inference('sup-', [status(thm)], ['92', '93'])).
% 1.05/1.22  thf('115', plain,
% 1.05/1.22      ((((k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 1.05/1.22          != (k1_tarski @ k1_xboole_0)))
% 1.05/1.22         <= ((((sk_A) = (k1_xboole_0))))),
% 1.05/1.22      inference('demod', [status(thm)], ['113', '114'])).
% 1.05/1.22  thf('116', plain, ((((sk_A) = (k1_xboole_0)))),
% 1.05/1.22      inference('sat_resolution*', [status(thm)], ['88', '89'])).
% 1.05/1.22  thf('117', plain,
% 1.05/1.22      (((k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 1.05/1.22         != (k1_tarski @ k1_xboole_0))),
% 1.05/1.22      inference('simpl_trail', [status(thm)], ['115', '116'])).
% 1.05/1.22  thf('118', plain, (~ (v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 1.05/1.22      inference('simplify_reflect-', [status(thm)], ['96', '117'])).
% 1.05/1.22  thf('119', plain, (![X0 : $i]: (v1_xboole_0 @ X0)),
% 1.05/1.22      inference('clc', [status(thm)], ['71', '118'])).
% 1.05/1.22  thf('120', plain, ($false), inference('demod', [status(thm)], ['13', '119'])).
% 1.05/1.22  
% 1.05/1.22  % SZS output end Refutation
% 1.05/1.22  
% 1.06/1.23  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
