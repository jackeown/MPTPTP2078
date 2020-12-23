%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v3nsVEff1V

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:20 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 155 expanded)
%              Number of leaves         :   50 (  67 expanded)
%              Depth                    :   21
%              Number of atoms          :  862 (1513 expanded)
%              Number of equality atoms :   49 (  76 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('0',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ ( sk_B @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r2_hidden @ X22 @ X23 )
      | ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t61_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_funct_2])).

thf('3',plain,(
    v1_funct_2 @ sk_C_2 @ ( k1_tarski @ sk_A ) @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('4',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( v1_funct_2 @ X50 @ X48 @ X49 )
      | ( X48
        = ( k1_relset_1 @ X48 @ X49 @ X50 ) )
      | ~ ( zip_tseitin_1 @ X50 @ X49 @ X48 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X46: $i,X47: $i] :
      ( ( zip_tseitin_0 @ X46 @ X47 )
      | ( X46 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( zip_tseitin_0 @ X51 @ X52 )
      | ( zip_tseitin_1 @ X53 @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X51 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['5','12'])).

thf(t56_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf('14',plain,(
    ! [X32: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X32 ) @ ( sk_C_1 @ X32 ) ) @ X32 )
      | ( X32 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf('15',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('16',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ( r2_hidden @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ sk_C_2 ) @ ( sk_C_1 @ sk_C_2 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('20',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v1_relat_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('21',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ sk_C_2 ) @ ( sk_C_1 @ sk_C_2 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf(t128_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
    <=> ( ( A = C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('23',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X13 = X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X12 ) @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('24',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( ( sk_B_1 @ sk_C_2 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X32: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X32 ) @ ( sk_C_1 @ X32 ) ) @ X32 )
      | ( X32 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf('26',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C_1 @ sk_C_2 ) ) @ sk_C_2 )
    | ( sk_C_2 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('28',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C_1 @ sk_C_2 ) ) @ sk_C_2 )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C_1 @ sk_C_2 ) ) @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('30',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X29 @ X30 ) @ X31 )
      | ( r2_hidden @ X29 @ ( k1_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('31',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('33',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('35',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( v4_relat_1 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('36',plain,(
    v4_relat_1 @ sk_C_2 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('37',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v4_relat_1 @ X27 @ X28 )
      | ( r1_tarski @ ( k1_relat_1 @ X27 ) @ X28 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('40',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('45',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ~ ( r2_hidden @ X54 @ X55 )
      | ( X56 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X57 )
      | ~ ( v1_funct_2 @ X57 @ X55 @ X56 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X56 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X57 @ X54 ) @ X56 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ sk_B_2 )
      | ~ ( v1_funct_2 @ sk_C_2 @ ( k1_tarski @ sk_A ) @ sk_B_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( sk_B_2 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_2 @ sk_C_2 @ ( k1_tarski @ sk_A ) @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ sk_B_2 )
      | ( sk_B_2 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['43','51'])).

thf('53',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ sk_A ) @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','54'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('56',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t22_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) )
      <=> ( ( k1_relset_1 @ B @ A @ C )
          = B ) ) ) )).

thf('57',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( ( k1_relset_1 @ X41 @ X42 @ X43 )
       != X41 )
      | ~ ( r2_hidden @ X44 @ X41 )
      | ( r2_hidden @ ( k4_tarski @ X44 @ ( sk_E @ X44 @ X43 ) ) @ X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_relset_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_E @ X2 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
       != X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ k1_xboole_0 ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','60'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('62',plain,(
    ! [X11: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('63',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ k1_xboole_0 ) ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['61','62'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('64',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X33 @ X34 )
      | ~ ( r1_tarski @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('65',plain,(
    ~ ( r1_tarski @ k1_xboole_0 @ ( k4_tarski @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('66',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['65','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v3nsVEff1V
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:01:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 0.84/1.05  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.84/1.05  % Solved by: fo/fo7.sh
% 0.84/1.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.05  % done 707 iterations in 0.608s
% 0.84/1.05  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.84/1.05  % SZS output start Refutation
% 0.84/1.05  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.84/1.05  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.84/1.05  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.84/1.05  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.84/1.05  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.84/1.05  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.05  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.84/1.05  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.84/1.05  thf(sk_E_type, type, sk_E: $i > $i > $i).
% 0.84/1.05  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.84/1.05  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.84/1.05  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.84/1.05  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.84/1.05  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.84/1.05  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.84/1.05  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.84/1.05  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.84/1.05  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.84/1.05  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.84/1.05  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.84/1.05  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.84/1.05  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.84/1.05  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.84/1.05  thf(sk_B_type, type, sk_B: $i > $i).
% 0.84/1.05  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.84/1.05  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.84/1.05  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.84/1.05  thf(existence_m1_subset_1, axiom,
% 0.84/1.05    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.84/1.05  thf('0', plain, (![X17 : $i]: (m1_subset_1 @ (sk_B @ X17) @ X17)),
% 0.84/1.05      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.84/1.05  thf(t2_subset, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( m1_subset_1 @ A @ B ) =>
% 0.84/1.05       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.84/1.05  thf('1', plain,
% 0.84/1.05      (![X22 : $i, X23 : $i]:
% 0.84/1.05         ((r2_hidden @ X22 @ X23)
% 0.84/1.05          | (v1_xboole_0 @ X23)
% 0.84/1.05          | ~ (m1_subset_1 @ X22 @ X23))),
% 0.84/1.05      inference('cnf', [status(esa)], [t2_subset])).
% 0.84/1.05  thf('2', plain,
% 0.84/1.05      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.84/1.05      inference('sup-', [status(thm)], ['0', '1'])).
% 0.84/1.05  thf(t61_funct_2, conjecture,
% 0.84/1.05    (![A:$i,B:$i,C:$i]:
% 0.84/1.05     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.84/1.05         ( m1_subset_1 @
% 0.84/1.05           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.84/1.05       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.84/1.05         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.84/1.05  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.05    (~( ![A:$i,B:$i,C:$i]:
% 0.84/1.05        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.84/1.05            ( m1_subset_1 @
% 0.84/1.05              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.84/1.05          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.84/1.05            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.84/1.05    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.84/1.05  thf('3', plain, ((v1_funct_2 @ sk_C_2 @ (k1_tarski @ sk_A) @ sk_B_2)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf(d1_funct_2, axiom,
% 0.84/1.05    (![A:$i,B:$i,C:$i]:
% 0.84/1.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.84/1.05       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.84/1.05           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.84/1.05             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.84/1.05         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.84/1.05           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.84/1.05             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.84/1.05  thf(zf_stmt_1, axiom,
% 0.84/1.05    (![C:$i,B:$i,A:$i]:
% 0.84/1.05     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.84/1.05       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.84/1.05  thf('4', plain,
% 0.84/1.05      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.84/1.05         (~ (v1_funct_2 @ X50 @ X48 @ X49)
% 0.84/1.05          | ((X48) = (k1_relset_1 @ X48 @ X49 @ X50))
% 0.84/1.05          | ~ (zip_tseitin_1 @ X50 @ X49 @ X48))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.84/1.05  thf('5', plain,
% 0.84/1.05      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ (k1_tarski @ sk_A))
% 0.84/1.05        | ((k1_tarski @ sk_A)
% 0.84/1.05            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ sk_C_2)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['3', '4'])).
% 0.84/1.05  thf(zf_stmt_2, axiom,
% 0.84/1.05    (![B:$i,A:$i]:
% 0.84/1.05     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.84/1.05       ( zip_tseitin_0 @ B @ A ) ))).
% 0.84/1.05  thf('6', plain,
% 0.84/1.05      (![X46 : $i, X47 : $i]:
% 0.84/1.05         ((zip_tseitin_0 @ X46 @ X47) | ((X46) = (k1_xboole_0)))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.84/1.05  thf('7', plain,
% 0.84/1.05      ((m1_subset_1 @ sk_C_2 @ 
% 0.84/1.05        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.84/1.05  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.84/1.05  thf(zf_stmt_5, axiom,
% 0.84/1.05    (![A:$i,B:$i,C:$i]:
% 0.84/1.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.84/1.05       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.84/1.05         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.84/1.05           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.84/1.05             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.84/1.05  thf('8', plain,
% 0.84/1.05      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.84/1.05         (~ (zip_tseitin_0 @ X51 @ X52)
% 0.84/1.05          | (zip_tseitin_1 @ X53 @ X51 @ X52)
% 0.84/1.05          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X51))))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.84/1.05  thf('9', plain,
% 0.84/1.05      (((zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ (k1_tarski @ sk_A))
% 0.84/1.05        | ~ (zip_tseitin_0 @ sk_B_2 @ (k1_tarski @ sk_A)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['7', '8'])).
% 0.84/1.05  thf('10', plain,
% 0.84/1.05      ((((sk_B_2) = (k1_xboole_0))
% 0.84/1.05        | (zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ (k1_tarski @ sk_A)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['6', '9'])).
% 0.84/1.05  thf('11', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('12', plain, ((zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ (k1_tarski @ sk_A))),
% 0.84/1.05      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.84/1.05  thf('13', plain,
% 0.84/1.05      (((k1_tarski @ sk_A)
% 0.84/1.05         = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ sk_C_2))),
% 0.84/1.05      inference('demod', [status(thm)], ['5', '12'])).
% 0.84/1.05  thf(t56_relat_1, axiom,
% 0.84/1.05    (![A:$i]:
% 0.84/1.05     ( ( v1_relat_1 @ A ) =>
% 0.84/1.05       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.84/1.05         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.84/1.05  thf('14', plain,
% 0.84/1.05      (![X32 : $i]:
% 0.84/1.05         ((r2_hidden @ (k4_tarski @ (sk_B_1 @ X32) @ (sk_C_1 @ X32)) @ X32)
% 0.84/1.05          | ((X32) = (k1_xboole_0))
% 0.84/1.05          | ~ (v1_relat_1 @ X32))),
% 0.84/1.05      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.84/1.05  thf('15', plain,
% 0.84/1.05      ((m1_subset_1 @ sk_C_2 @ 
% 0.84/1.05        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf(l3_subset_1, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.84/1.05       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.84/1.05  thf('16', plain,
% 0.84/1.05      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X18 @ X19)
% 0.84/1.05          | (r2_hidden @ X18 @ X20)
% 0.84/1.05          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.84/1.05      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.84/1.05  thf('17', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2))
% 0.84/1.05          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.84/1.05      inference('sup-', [status(thm)], ['15', '16'])).
% 0.84/1.05  thf('18', plain,
% 0.84/1.05      ((~ (v1_relat_1 @ sk_C_2)
% 0.84/1.05        | ((sk_C_2) = (k1_xboole_0))
% 0.84/1.05        | (r2_hidden @ (k4_tarski @ (sk_B_1 @ sk_C_2) @ (sk_C_1 @ sk_C_2)) @ 
% 0.84/1.05           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['14', '17'])).
% 0.84/1.05  thf('19', plain,
% 0.84/1.05      ((m1_subset_1 @ sk_C_2 @ 
% 0.84/1.05        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf(cc1_relset_1, axiom,
% 0.84/1.05    (![A:$i,B:$i,C:$i]:
% 0.84/1.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.84/1.05       ( v1_relat_1 @ C ) ))).
% 0.84/1.05  thf('20', plain,
% 0.84/1.05      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.84/1.05         ((v1_relat_1 @ X35)
% 0.84/1.05          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.84/1.05      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.84/1.05  thf('21', plain, ((v1_relat_1 @ sk_C_2)),
% 0.84/1.05      inference('sup-', [status(thm)], ['19', '20'])).
% 0.84/1.05  thf('22', plain,
% 0.84/1.05      ((((sk_C_2) = (k1_xboole_0))
% 0.84/1.05        | (r2_hidden @ (k4_tarski @ (sk_B_1 @ sk_C_2) @ (sk_C_1 @ sk_C_2)) @ 
% 0.84/1.05           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.84/1.05      inference('demod', [status(thm)], ['18', '21'])).
% 0.84/1.05  thf(t128_zfmisc_1, axiom,
% 0.84/1.05    (![A:$i,B:$i,C:$i,D:$i]:
% 0.84/1.05     ( ( r2_hidden @
% 0.84/1.05         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.84/1.05       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.84/1.05  thf('23', plain,
% 0.84/1.05      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.84/1.05         (((X13) = (X12))
% 0.84/1.05          | ~ (r2_hidden @ (k4_tarski @ X13 @ X14) @ 
% 0.84/1.05               (k2_zfmisc_1 @ (k1_tarski @ X12) @ X15)))),
% 0.84/1.05      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 0.84/1.05  thf('24', plain,
% 0.84/1.05      ((((sk_C_2) = (k1_xboole_0)) | ((sk_B_1 @ sk_C_2) = (sk_A)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['22', '23'])).
% 0.84/1.05  thf('25', plain,
% 0.84/1.05      (![X32 : $i]:
% 0.84/1.05         ((r2_hidden @ (k4_tarski @ (sk_B_1 @ X32) @ (sk_C_1 @ X32)) @ X32)
% 0.84/1.05          | ((X32) = (k1_xboole_0))
% 0.84/1.05          | ~ (v1_relat_1 @ X32))),
% 0.84/1.05      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.84/1.05  thf('26', plain,
% 0.84/1.05      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_C_1 @ sk_C_2)) @ sk_C_2)
% 0.84/1.05        | ((sk_C_2) = (k1_xboole_0))
% 0.84/1.05        | ~ (v1_relat_1 @ sk_C_2)
% 0.84/1.05        | ((sk_C_2) = (k1_xboole_0)))),
% 0.84/1.05      inference('sup+', [status(thm)], ['24', '25'])).
% 0.84/1.05  thf('27', plain, ((v1_relat_1 @ sk_C_2)),
% 0.84/1.05      inference('sup-', [status(thm)], ['19', '20'])).
% 0.84/1.05  thf('28', plain,
% 0.84/1.05      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_C_1 @ sk_C_2)) @ sk_C_2)
% 0.84/1.05        | ((sk_C_2) = (k1_xboole_0))
% 0.84/1.05        | ((sk_C_2) = (k1_xboole_0)))),
% 0.84/1.05      inference('demod', [status(thm)], ['26', '27'])).
% 0.84/1.05  thf('29', plain,
% 0.84/1.05      ((((sk_C_2) = (k1_xboole_0))
% 0.84/1.05        | (r2_hidden @ (k4_tarski @ sk_A @ (sk_C_1 @ sk_C_2)) @ sk_C_2))),
% 0.84/1.05      inference('simplify', [status(thm)], ['28'])).
% 0.84/1.05  thf(t20_relat_1, axiom,
% 0.84/1.05    (![A:$i,B:$i,C:$i]:
% 0.84/1.05     ( ( v1_relat_1 @ C ) =>
% 0.84/1.05       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.84/1.05         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.84/1.05           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.84/1.05  thf('30', plain,
% 0.84/1.05      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.84/1.05         (~ (r2_hidden @ (k4_tarski @ X29 @ X30) @ X31)
% 0.84/1.05          | (r2_hidden @ X29 @ (k1_relat_1 @ X31))
% 0.84/1.05          | ~ (v1_relat_1 @ X31))),
% 0.84/1.05      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.84/1.05  thf('31', plain,
% 0.84/1.05      ((((sk_C_2) = (k1_xboole_0))
% 0.84/1.05        | ~ (v1_relat_1 @ sk_C_2)
% 0.84/1.05        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_2)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['29', '30'])).
% 0.84/1.05  thf('32', plain, ((v1_relat_1 @ sk_C_2)),
% 0.84/1.05      inference('sup-', [status(thm)], ['19', '20'])).
% 0.84/1.05  thf('33', plain,
% 0.84/1.05      ((((sk_C_2) = (k1_xboole_0)) | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_2)))),
% 0.84/1.05      inference('demod', [status(thm)], ['31', '32'])).
% 0.84/1.05  thf('34', plain,
% 0.84/1.05      ((m1_subset_1 @ sk_C_2 @ 
% 0.84/1.05        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf(cc2_relset_1, axiom,
% 0.84/1.05    (![A:$i,B:$i,C:$i]:
% 0.84/1.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.84/1.05       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.84/1.05  thf('35', plain,
% 0.84/1.05      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.84/1.05         ((v4_relat_1 @ X38 @ X39)
% 0.84/1.05          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 0.84/1.05      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.84/1.05  thf('36', plain, ((v4_relat_1 @ sk_C_2 @ (k1_tarski @ sk_A))),
% 0.84/1.05      inference('sup-', [status(thm)], ['34', '35'])).
% 0.84/1.05  thf(d18_relat_1, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( v1_relat_1 @ B ) =>
% 0.84/1.05       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.84/1.05  thf('37', plain,
% 0.84/1.05      (![X27 : $i, X28 : $i]:
% 0.84/1.05         (~ (v4_relat_1 @ X27 @ X28)
% 0.84/1.05          | (r1_tarski @ (k1_relat_1 @ X27) @ X28)
% 0.84/1.05          | ~ (v1_relat_1 @ X27))),
% 0.84/1.05      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.84/1.05  thf('38', plain,
% 0.84/1.05      ((~ (v1_relat_1 @ sk_C_2)
% 0.84/1.05        | (r1_tarski @ (k1_relat_1 @ sk_C_2) @ (k1_tarski @ sk_A)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['36', '37'])).
% 0.84/1.05  thf('39', plain, ((v1_relat_1 @ sk_C_2)),
% 0.84/1.05      inference('sup-', [status(thm)], ['19', '20'])).
% 0.84/1.05  thf('40', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_2) @ (k1_tarski @ sk_A))),
% 0.84/1.05      inference('demod', [status(thm)], ['38', '39'])).
% 0.84/1.05  thf(d3_tarski, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( r1_tarski @ A @ B ) <=>
% 0.84/1.05       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.84/1.05  thf('41', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X0 @ X1)
% 0.84/1.05          | (r2_hidden @ X0 @ X2)
% 0.84/1.05          | ~ (r1_tarski @ X1 @ X2))),
% 0.84/1.05      inference('cnf', [status(esa)], [d3_tarski])).
% 0.84/1.05  thf('42', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         ((r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.84/1.05          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['40', '41'])).
% 0.84/1.05  thf('43', plain,
% 0.84/1.05      ((((sk_C_2) = (k1_xboole_0)) | (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['33', '42'])).
% 0.84/1.05  thf('44', plain,
% 0.84/1.05      ((m1_subset_1 @ sk_C_2 @ 
% 0.84/1.05        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf(t7_funct_2, axiom,
% 0.84/1.05    (![A:$i,B:$i,C:$i,D:$i]:
% 0.84/1.05     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.84/1.05         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.84/1.05       ( ( r2_hidden @ C @ A ) =>
% 0.84/1.05         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.84/1.05           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.84/1.05  thf('45', plain,
% 0.84/1.05      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X54 @ X55)
% 0.84/1.05          | ((X56) = (k1_xboole_0))
% 0.84/1.05          | ~ (v1_funct_1 @ X57)
% 0.84/1.05          | ~ (v1_funct_2 @ X57 @ X55 @ X56)
% 0.84/1.05          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X56)))
% 0.84/1.05          | (r2_hidden @ (k1_funct_1 @ X57 @ X54) @ X56))),
% 0.84/1.05      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.84/1.05  thf('46', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         ((r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ sk_B_2)
% 0.84/1.05          | ~ (v1_funct_2 @ sk_C_2 @ (k1_tarski @ sk_A) @ sk_B_2)
% 0.84/1.05          | ~ (v1_funct_1 @ sk_C_2)
% 0.84/1.05          | ((sk_B_2) = (k1_xboole_0))
% 0.84/1.05          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['44', '45'])).
% 0.84/1.05  thf('47', plain, ((v1_funct_2 @ sk_C_2 @ (k1_tarski @ sk_A) @ sk_B_2)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('48', plain, ((v1_funct_1 @ sk_C_2)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('49', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         ((r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ sk_B_2)
% 0.84/1.05          | ((sk_B_2) = (k1_xboole_0))
% 0.84/1.05          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.84/1.05      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.84/1.05  thf('50', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('51', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         ((r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ sk_B_2)
% 0.84/1.05          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.84/1.05      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 0.84/1.05  thf('52', plain,
% 0.84/1.05      ((((sk_C_2) = (k1_xboole_0))
% 0.84/1.05        | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ sk_A) @ sk_B_2))),
% 0.84/1.05      inference('sup-', [status(thm)], ['43', '51'])).
% 0.84/1.05  thf('53', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C_2 @ sk_A) @ sk_B_2)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('54', plain, (((sk_C_2) = (k1_xboole_0))),
% 0.84/1.05      inference('clc', [status(thm)], ['52', '53'])).
% 0.84/1.05  thf('55', plain,
% 0.84/1.05      (((k1_tarski @ sk_A)
% 0.84/1.05         = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ k1_xboole_0))),
% 0.84/1.05      inference('demod', [status(thm)], ['13', '54'])).
% 0.84/1.05  thf(t4_subset_1, axiom,
% 0.84/1.05    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.84/1.05  thf('56', plain,
% 0.84/1.05      (![X21 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X21))),
% 0.84/1.05      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.84/1.05  thf(t22_relset_1, axiom,
% 0.84/1.05    (![A:$i,B:$i,C:$i]:
% 0.84/1.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.84/1.05       ( ( ![D:$i]:
% 0.84/1.05           ( ~( ( r2_hidden @ D @ B ) & 
% 0.84/1.05                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.84/1.05         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 0.84/1.05  thf('57', plain,
% 0.84/1.05      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.84/1.05         (((k1_relset_1 @ X41 @ X42 @ X43) != (X41))
% 0.84/1.05          | ~ (r2_hidden @ X44 @ X41)
% 0.84/1.05          | (r2_hidden @ (k4_tarski @ X44 @ (sk_E @ X44 @ X43)) @ X43)
% 0.84/1.05          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 0.84/1.05      inference('cnf', [status(esa)], [t22_relset_1])).
% 0.84/1.05  thf('58', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.05         ((r2_hidden @ (k4_tarski @ X2 @ (sk_E @ X2 @ k1_xboole_0)) @ 
% 0.84/1.05           k1_xboole_0)
% 0.84/1.05          | ~ (r2_hidden @ X2 @ X1)
% 0.84/1.05          | ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) != (X1)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['56', '57'])).
% 0.84/1.05  thf('59', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.84/1.05          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.84/1.05          | (r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ k1_xboole_0)) @ 
% 0.84/1.05             k1_xboole_0))),
% 0.84/1.05      inference('sup-', [status(thm)], ['55', '58'])).
% 0.84/1.05  thf('60', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ k1_xboole_0)) @ 
% 0.84/1.05           k1_xboole_0)
% 0.84/1.05          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.84/1.05      inference('simplify', [status(thm)], ['59'])).
% 0.84/1.05  thf('61', plain,
% 0.84/1.05      (((v1_xboole_0 @ (k1_tarski @ sk_A))
% 0.84/1.05        | (r2_hidden @ 
% 0.84/1.05           (k4_tarski @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 0.84/1.05            (sk_E @ (sk_B @ (k1_tarski @ sk_A)) @ k1_xboole_0)) @ 
% 0.84/1.05           k1_xboole_0))),
% 0.84/1.05      inference('sup-', [status(thm)], ['2', '60'])).
% 0.84/1.05  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.84/1.05  thf('62', plain, (![X11 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X11))),
% 0.84/1.05      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.84/1.05  thf('63', plain,
% 0.84/1.05      ((r2_hidden @ 
% 0.84/1.05        (k4_tarski @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 0.84/1.05         (sk_E @ (sk_B @ (k1_tarski @ sk_A)) @ k1_xboole_0)) @ 
% 0.84/1.05        k1_xboole_0)),
% 0.84/1.05      inference('clc', [status(thm)], ['61', '62'])).
% 0.84/1.05  thf(t7_ordinal1, axiom,
% 0.84/1.05    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.84/1.05  thf('64', plain,
% 0.84/1.05      (![X33 : $i, X34 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X33 @ X34) | ~ (r1_tarski @ X34 @ X33))),
% 0.84/1.05      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.84/1.05  thf('65', plain,
% 0.84/1.05      (~ (r1_tarski @ k1_xboole_0 @ 
% 0.84/1.05          (k4_tarski @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 0.84/1.05           (sk_E @ (sk_B @ (k1_tarski @ sk_A)) @ k1_xboole_0)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['63', '64'])).
% 0.84/1.05  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.84/1.05  thf('66', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.84/1.05      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.84/1.05  thf('67', plain, ($false), inference('demod', [status(thm)], ['65', '66'])).
% 0.84/1.05  
% 0.84/1.05  % SZS output end Refutation
% 0.84/1.05  
% 0.84/1.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
