%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Jma13BISAW

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:32 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 255 expanded)
%              Number of leaves         :   54 (  99 expanded)
%              Depth                    :   17
%              Number of atoms          : 1003 (2775 expanded)
%              Number of equality atoms :   92 ( 199 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X4 != X3 )
      | ( r2_hidden @ X4 @ X5 )
      | ( X5
       != ( k2_tarski @ X6 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X3: $i,X6: $i] :
      ( r2_hidden @ X3 @ ( k2_tarski @ X6 @ X3 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

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

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t22_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) )
      <=> ( ( k1_relset_1 @ B @ A @ C )
          = B ) ) ) )).

thf('5',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( ( k1_relset_1 @ X42 @ X43 @ X44 )
       != X42 )
      | ~ ( r2_hidden @ X45 @ X42 )
      | ( r2_hidden @ ( k4_tarski @ X45 @ ( sk_E @ X45 @ X44 ) ) @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_C ) ) @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ),
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

thf('8',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( v1_funct_2 @ X51 @ X49 @ X50 )
      | ( X49
        = ( k1_relset_1 @ X49 @ X50 @ X51 ) )
      | ~ ( zip_tseitin_1 @ X51 @ X50 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('9',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X47: $i,X48: $i] :
      ( ( zip_tseitin_0 @ X47 @ X48 )
      | ( X47 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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

thf('12',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( zip_tseitin_0 @ X52 @ X53 )
      | ( zip_tseitin_1 @ X54 @ X52 @ X53 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('13',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['9','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_C ) ) @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['6','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_C ) ) @ sk_C ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( sk_E @ sk_A @ sk_C ) ) @ sk_C ),
    inference('sup-',[status(thm)],['3','19'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('29',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( v4_relat_1 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('30',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X28: $i,X29: $i] :
      ( ( X28
        = ( k7_relat_1 @ X28 @ X29 ) )
      | ~ ( v4_relat_1 @ X28 @ X29 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('34',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v1_relat_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','35'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X24 @ X25 ) )
        = ( k9_relat_1 @ X24 @ X25 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('38',plain,(
    ! [X30: $i] :
      ( ( ( k2_relat_1 @ X30 )
       != k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('42',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('43',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('44',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('45',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X24 @ X25 ) )
        = ( k9_relat_1 @ X24 @ X25 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('46',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41','42','43','48'])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('50',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k11_relat_1 @ X26 @ X27 )
        = k1_xboole_0 )
      | ( r2_hidden @ X27 @ ( k1_relat_1 @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('51',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X12 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( m1_subset_1 @ ( k1_tarski @ X1 ) @ ( k1_zfmisc_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('56',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v4_relat_1 @ X22 @ X23 )
      | ( r1_tarski @ ( k1_relat_1 @ X22 ) @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('57',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('59',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('61',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k11_relat_1 @ sk_C @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['54','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('64',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k11_relat_1 @ X20 @ X21 )
        = ( k9_relat_1 @ X20 @ ( k1_tarski @ X21 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('66',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k11_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('68',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k11_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['62','63','68'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('70',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k1_relat_1 @ X32 )
       != ( k1_tarski @ X31 ) )
      | ( ( k2_relat_1 @ X32 )
        = ( k1_tarski @ ( k1_funct_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ( ( k2_relat_1 @ sk_C )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['71'])).

thf('73',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('75',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('78',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k2_relset_1 @ X40 @ X41 @ X39 )
        = ( k2_relat_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('79',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','79'])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['75','80'])).

thf('82',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','81'])).

thf('83',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['82'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('84',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('85',plain,(
    $false ),
    inference(demod,[status(thm)],['27','83','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Jma13BISAW
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:45:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.48/1.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.48/1.71  % Solved by: fo/fo7.sh
% 1.48/1.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.48/1.71  % done 918 iterations in 1.254s
% 1.48/1.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.48/1.71  % SZS output start Refutation
% 1.48/1.71  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 1.48/1.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.48/1.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.48/1.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.48/1.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.48/1.71  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.48/1.71  thf(sk_C_type, type, sk_C: $i).
% 1.48/1.71  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.48/1.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.48/1.71  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.48/1.71  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.48/1.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.48/1.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.48/1.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.48/1.71  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.48/1.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.48/1.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.48/1.71  thf(sk_A_type, type, sk_A: $i).
% 1.48/1.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.48/1.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.48/1.71  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.48/1.71  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.48/1.71  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.48/1.71  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.48/1.71  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.48/1.71  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.48/1.71  thf(sk_B_type, type, sk_B: $i).
% 1.48/1.71  thf(sk_E_type, type, sk_E: $i > $i > $i).
% 1.48/1.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.48/1.71  thf(t69_enumset1, axiom,
% 1.48/1.71    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.48/1.71  thf('0', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 1.48/1.71      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.48/1.71  thf(d2_tarski, axiom,
% 1.48/1.71    (![A:$i,B:$i,C:$i]:
% 1.48/1.71     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 1.48/1.71       ( ![D:$i]:
% 1.48/1.71         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 1.48/1.71  thf('1', plain,
% 1.48/1.71      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.48/1.71         (((X4) != (X3))
% 1.48/1.71          | (r2_hidden @ X4 @ X5)
% 1.48/1.71          | ((X5) != (k2_tarski @ X6 @ X3)))),
% 1.48/1.71      inference('cnf', [status(esa)], [d2_tarski])).
% 1.48/1.71  thf('2', plain,
% 1.48/1.71      (![X3 : $i, X6 : $i]: (r2_hidden @ X3 @ (k2_tarski @ X6 @ X3))),
% 1.48/1.71      inference('simplify', [status(thm)], ['1'])).
% 1.48/1.71  thf('3', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.48/1.71      inference('sup+', [status(thm)], ['0', '2'])).
% 1.48/1.71  thf(t62_funct_2, conjecture,
% 1.48/1.71    (![A:$i,B:$i,C:$i]:
% 1.48/1.71     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 1.48/1.71         ( m1_subset_1 @
% 1.48/1.71           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 1.48/1.71       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.48/1.71         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 1.48/1.71           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 1.48/1.71  thf(zf_stmt_0, negated_conjecture,
% 1.48/1.71    (~( ![A:$i,B:$i,C:$i]:
% 1.48/1.71        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 1.48/1.71            ( m1_subset_1 @
% 1.48/1.71              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 1.48/1.71          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.48/1.71            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 1.48/1.71              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 1.48/1.71    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 1.48/1.71  thf('4', plain,
% 1.48/1.71      ((m1_subset_1 @ sk_C @ 
% 1.48/1.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.48/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.48/1.71  thf(t22_relset_1, axiom,
% 1.48/1.71    (![A:$i,B:$i,C:$i]:
% 1.48/1.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.48/1.71       ( ( ![D:$i]:
% 1.48/1.71           ( ~( ( r2_hidden @ D @ B ) & 
% 1.48/1.71                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 1.48/1.71         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 1.48/1.71  thf('5', plain,
% 1.48/1.71      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 1.48/1.71         (((k1_relset_1 @ X42 @ X43 @ X44) != (X42))
% 1.48/1.71          | ~ (r2_hidden @ X45 @ X42)
% 1.48/1.71          | (r2_hidden @ (k4_tarski @ X45 @ (sk_E @ X45 @ X44)) @ X44)
% 1.48/1.71          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43))))),
% 1.48/1.71      inference('cnf', [status(esa)], [t22_relset_1])).
% 1.48/1.71  thf('6', plain,
% 1.48/1.71      (![X0 : $i]:
% 1.48/1.71         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C)) @ sk_C)
% 1.48/1.71          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 1.48/1.71          | ((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)
% 1.48/1.71              != (k1_tarski @ sk_A)))),
% 1.48/1.71      inference('sup-', [status(thm)], ['4', '5'])).
% 1.48/1.71  thf('7', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)),
% 1.48/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.48/1.71  thf(d1_funct_2, axiom,
% 1.48/1.71    (![A:$i,B:$i,C:$i]:
% 1.48/1.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.48/1.71       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.48/1.71           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.48/1.71             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.48/1.71         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.48/1.71           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.48/1.71             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.48/1.71  thf(zf_stmt_1, axiom,
% 1.48/1.71    (![C:$i,B:$i,A:$i]:
% 1.48/1.71     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.48/1.71       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.48/1.71  thf('8', plain,
% 1.48/1.71      (![X49 : $i, X50 : $i, X51 : $i]:
% 1.48/1.71         (~ (v1_funct_2 @ X51 @ X49 @ X50)
% 1.48/1.71          | ((X49) = (k1_relset_1 @ X49 @ X50 @ X51))
% 1.48/1.71          | ~ (zip_tseitin_1 @ X51 @ X50 @ X49))),
% 1.48/1.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.48/1.71  thf('9', plain,
% 1.48/1.71      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 1.48/1.71        | ((k1_tarski @ sk_A)
% 1.48/1.71            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)))),
% 1.48/1.71      inference('sup-', [status(thm)], ['7', '8'])).
% 1.48/1.71  thf(zf_stmt_2, axiom,
% 1.48/1.71    (![B:$i,A:$i]:
% 1.48/1.71     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.48/1.71       ( zip_tseitin_0 @ B @ A ) ))).
% 1.48/1.71  thf('10', plain,
% 1.48/1.71      (![X47 : $i, X48 : $i]:
% 1.48/1.71         ((zip_tseitin_0 @ X47 @ X48) | ((X47) = (k1_xboole_0)))),
% 1.48/1.71      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.48/1.71  thf('11', plain,
% 1.48/1.71      ((m1_subset_1 @ sk_C @ 
% 1.48/1.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.48/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.48/1.71  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.48/1.71  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.48/1.71  thf(zf_stmt_5, axiom,
% 1.48/1.71    (![A:$i,B:$i,C:$i]:
% 1.48/1.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.48/1.71       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.48/1.71         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.48/1.71           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.48/1.71             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.48/1.71  thf('12', plain,
% 1.48/1.71      (![X52 : $i, X53 : $i, X54 : $i]:
% 1.48/1.71         (~ (zip_tseitin_0 @ X52 @ X53)
% 1.48/1.71          | (zip_tseitin_1 @ X54 @ X52 @ X53)
% 1.48/1.71          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X52))))),
% 1.48/1.71      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.48/1.71  thf('13', plain,
% 1.48/1.71      (((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 1.48/1.71        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 1.48/1.71      inference('sup-', [status(thm)], ['11', '12'])).
% 1.48/1.71  thf('14', plain,
% 1.48/1.71      ((((sk_B) = (k1_xboole_0))
% 1.48/1.71        | (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A)))),
% 1.48/1.71      inference('sup-', [status(thm)], ['10', '13'])).
% 1.48/1.71  thf('15', plain, (((sk_B) != (k1_xboole_0))),
% 1.48/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.48/1.71  thf('16', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))),
% 1.48/1.71      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 1.48/1.71  thf('17', plain,
% 1.48/1.71      (((k1_tarski @ sk_A) = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C))),
% 1.48/1.71      inference('demod', [status(thm)], ['9', '16'])).
% 1.48/1.71  thf('18', plain,
% 1.48/1.71      (![X0 : $i]:
% 1.48/1.71         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C)) @ sk_C)
% 1.48/1.71          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 1.48/1.71          | ((k1_tarski @ sk_A) != (k1_tarski @ sk_A)))),
% 1.48/1.71      inference('demod', [status(thm)], ['6', '17'])).
% 1.48/1.71  thf('19', plain,
% 1.48/1.71      (![X0 : $i]:
% 1.48/1.71         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 1.48/1.71          | (r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C)) @ sk_C))),
% 1.48/1.71      inference('simplify', [status(thm)], ['18'])).
% 1.48/1.71  thf('20', plain,
% 1.48/1.71      ((r2_hidden @ (k4_tarski @ sk_A @ (sk_E @ sk_A @ sk_C)) @ sk_C)),
% 1.48/1.71      inference('sup-', [status(thm)], ['3', '19'])).
% 1.48/1.71  thf(d10_xboole_0, axiom,
% 1.48/1.71    (![A:$i,B:$i]:
% 1.48/1.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.48/1.71  thf('21', plain,
% 1.48/1.71      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.48/1.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.48/1.71  thf('22', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.48/1.71      inference('simplify', [status(thm)], ['21'])).
% 1.48/1.71  thf(t3_subset, axiom,
% 1.48/1.71    (![A:$i,B:$i]:
% 1.48/1.71     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.48/1.71  thf('23', plain,
% 1.48/1.71      (![X14 : $i, X16 : $i]:
% 1.48/1.71         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 1.48/1.71      inference('cnf', [status(esa)], [t3_subset])).
% 1.48/1.71  thf('24', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.48/1.71      inference('sup-', [status(thm)], ['22', '23'])).
% 1.48/1.71  thf(t5_subset, axiom,
% 1.48/1.71    (![A:$i,B:$i,C:$i]:
% 1.48/1.71     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.48/1.71          ( v1_xboole_0 @ C ) ) ))).
% 1.48/1.71  thf('25', plain,
% 1.48/1.71      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.48/1.71         (~ (r2_hidden @ X17 @ X18)
% 1.48/1.71          | ~ (v1_xboole_0 @ X19)
% 1.48/1.71          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 1.48/1.71      inference('cnf', [status(esa)], [t5_subset])).
% 1.48/1.71  thf('26', plain,
% 1.48/1.71      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 1.48/1.71      inference('sup-', [status(thm)], ['24', '25'])).
% 1.48/1.71  thf('27', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.48/1.71      inference('sup-', [status(thm)], ['20', '26'])).
% 1.48/1.71  thf('28', plain,
% 1.48/1.71      ((m1_subset_1 @ sk_C @ 
% 1.48/1.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.48/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.48/1.71  thf(cc2_relset_1, axiom,
% 1.48/1.71    (![A:$i,B:$i,C:$i]:
% 1.48/1.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.48/1.71       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.48/1.71  thf('29', plain,
% 1.48/1.71      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.48/1.71         ((v4_relat_1 @ X36 @ X37)
% 1.48/1.71          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 1.48/1.71      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.48/1.71  thf('30', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 1.48/1.71      inference('sup-', [status(thm)], ['28', '29'])).
% 1.48/1.71  thf(t209_relat_1, axiom,
% 1.48/1.71    (![A:$i,B:$i]:
% 1.48/1.71     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.48/1.71       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 1.48/1.71  thf('31', plain,
% 1.48/1.71      (![X28 : $i, X29 : $i]:
% 1.48/1.71         (((X28) = (k7_relat_1 @ X28 @ X29))
% 1.48/1.71          | ~ (v4_relat_1 @ X28 @ X29)
% 1.48/1.71          | ~ (v1_relat_1 @ X28))),
% 1.48/1.71      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.48/1.71  thf('32', plain,
% 1.48/1.71      ((~ (v1_relat_1 @ sk_C)
% 1.48/1.71        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A))))),
% 1.48/1.71      inference('sup-', [status(thm)], ['30', '31'])).
% 1.48/1.71  thf('33', plain,
% 1.48/1.71      ((m1_subset_1 @ sk_C @ 
% 1.48/1.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.48/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.48/1.71  thf(cc1_relset_1, axiom,
% 1.48/1.71    (![A:$i,B:$i,C:$i]:
% 1.48/1.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.48/1.71       ( v1_relat_1 @ C ) ))).
% 1.48/1.71  thf('34', plain,
% 1.48/1.71      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.48/1.71         ((v1_relat_1 @ X33)
% 1.48/1.71          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 1.48/1.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.48/1.71  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 1.48/1.71      inference('sup-', [status(thm)], ['33', '34'])).
% 1.48/1.71  thf('36', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 1.48/1.71      inference('demod', [status(thm)], ['32', '35'])).
% 1.48/1.71  thf(t148_relat_1, axiom,
% 1.48/1.71    (![A:$i,B:$i]:
% 1.48/1.71     ( ( v1_relat_1 @ B ) =>
% 1.48/1.71       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 1.48/1.71  thf('37', plain,
% 1.48/1.71      (![X24 : $i, X25 : $i]:
% 1.48/1.71         (((k2_relat_1 @ (k7_relat_1 @ X24 @ X25)) = (k9_relat_1 @ X24 @ X25))
% 1.48/1.71          | ~ (v1_relat_1 @ X24))),
% 1.48/1.71      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.48/1.71  thf(t64_relat_1, axiom,
% 1.48/1.71    (![A:$i]:
% 1.48/1.71     ( ( v1_relat_1 @ A ) =>
% 1.48/1.71       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 1.48/1.71           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 1.48/1.71         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 1.48/1.71  thf('38', plain,
% 1.48/1.71      (![X30 : $i]:
% 1.48/1.71         (((k2_relat_1 @ X30) != (k1_xboole_0))
% 1.48/1.71          | ((X30) = (k1_xboole_0))
% 1.48/1.71          | ~ (v1_relat_1 @ X30))),
% 1.48/1.71      inference('cnf', [status(esa)], [t64_relat_1])).
% 1.48/1.71  thf('39', plain,
% 1.48/1.71      (![X0 : $i, X1 : $i]:
% 1.48/1.71         (((k9_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 1.48/1.71          | ~ (v1_relat_1 @ X1)
% 1.48/1.71          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.48/1.71          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 1.48/1.71      inference('sup-', [status(thm)], ['37', '38'])).
% 1.48/1.71  thf('40', plain,
% 1.48/1.71      ((~ (v1_relat_1 @ sk_C)
% 1.48/1.71        | ((k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 1.48/1.71        | ~ (v1_relat_1 @ sk_C)
% 1.48/1.71        | ((k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)) != (k1_xboole_0)))),
% 1.48/1.71      inference('sup-', [status(thm)], ['36', '39'])).
% 1.48/1.71  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 1.48/1.71      inference('sup-', [status(thm)], ['33', '34'])).
% 1.48/1.71  thf('42', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 1.48/1.71      inference('demod', [status(thm)], ['32', '35'])).
% 1.48/1.71  thf('43', plain, ((v1_relat_1 @ sk_C)),
% 1.48/1.71      inference('sup-', [status(thm)], ['33', '34'])).
% 1.48/1.71  thf('44', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 1.48/1.71      inference('demod', [status(thm)], ['32', '35'])).
% 1.48/1.71  thf('45', plain,
% 1.48/1.71      (![X24 : $i, X25 : $i]:
% 1.48/1.71         (((k2_relat_1 @ (k7_relat_1 @ X24 @ X25)) = (k9_relat_1 @ X24 @ X25))
% 1.48/1.71          | ~ (v1_relat_1 @ X24))),
% 1.48/1.71      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.48/1.71  thf('46', plain,
% 1.48/1.71      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)))
% 1.48/1.71        | ~ (v1_relat_1 @ sk_C))),
% 1.48/1.71      inference('sup+', [status(thm)], ['44', '45'])).
% 1.48/1.71  thf('47', plain, ((v1_relat_1 @ sk_C)),
% 1.48/1.71      inference('sup-', [status(thm)], ['33', '34'])).
% 1.48/1.71  thf('48', plain,
% 1.48/1.71      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 1.48/1.71      inference('demod', [status(thm)], ['46', '47'])).
% 1.48/1.71  thf('49', plain,
% 1.48/1.71      ((((sk_C) = (k1_xboole_0)) | ((k2_relat_1 @ sk_C) != (k1_xboole_0)))),
% 1.48/1.71      inference('demod', [status(thm)], ['40', '41', '42', '43', '48'])).
% 1.48/1.71  thf(t205_relat_1, axiom,
% 1.48/1.71    (![A:$i,B:$i]:
% 1.48/1.71     ( ( v1_relat_1 @ B ) =>
% 1.48/1.71       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 1.48/1.71         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 1.48/1.71  thf('50', plain,
% 1.48/1.71      (![X26 : $i, X27 : $i]:
% 1.48/1.71         (((k11_relat_1 @ X26 @ X27) = (k1_xboole_0))
% 1.48/1.71          | (r2_hidden @ X27 @ (k1_relat_1 @ X26))
% 1.48/1.71          | ~ (v1_relat_1 @ X26))),
% 1.48/1.71      inference('cnf', [status(esa)], [t205_relat_1])).
% 1.48/1.71  thf(t63_subset_1, axiom,
% 1.48/1.71    (![A:$i,B:$i]:
% 1.48/1.71     ( ( r2_hidden @ A @ B ) =>
% 1.48/1.71       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.48/1.71  thf('51', plain,
% 1.48/1.71      (![X12 : $i, X13 : $i]:
% 1.48/1.71         ((m1_subset_1 @ (k1_tarski @ X12) @ (k1_zfmisc_1 @ X13))
% 1.48/1.71          | ~ (r2_hidden @ X12 @ X13))),
% 1.48/1.71      inference('cnf', [status(esa)], [t63_subset_1])).
% 1.48/1.71  thf('52', plain,
% 1.48/1.71      (![X0 : $i, X1 : $i]:
% 1.48/1.71         (~ (v1_relat_1 @ X0)
% 1.48/1.71          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 1.48/1.71          | (m1_subset_1 @ (k1_tarski @ X1) @ (k1_zfmisc_1 @ (k1_relat_1 @ X0))))),
% 1.48/1.71      inference('sup-', [status(thm)], ['50', '51'])).
% 1.48/1.71  thf('53', plain,
% 1.48/1.71      (![X14 : $i, X15 : $i]:
% 1.48/1.71         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 1.48/1.71      inference('cnf', [status(esa)], [t3_subset])).
% 1.48/1.71  thf('54', plain,
% 1.48/1.71      (![X0 : $i, X1 : $i]:
% 1.48/1.71         (((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 1.48/1.71          | ~ (v1_relat_1 @ X0)
% 1.48/1.71          | (r1_tarski @ (k1_tarski @ X1) @ (k1_relat_1 @ X0)))),
% 1.48/1.71      inference('sup-', [status(thm)], ['52', '53'])).
% 1.48/1.71  thf('55', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 1.48/1.71      inference('sup-', [status(thm)], ['28', '29'])).
% 1.48/1.71  thf(d18_relat_1, axiom,
% 1.48/1.71    (![A:$i,B:$i]:
% 1.48/1.71     ( ( v1_relat_1 @ B ) =>
% 1.48/1.71       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.48/1.71  thf('56', plain,
% 1.48/1.71      (![X22 : $i, X23 : $i]:
% 1.48/1.71         (~ (v4_relat_1 @ X22 @ X23)
% 1.48/1.71          | (r1_tarski @ (k1_relat_1 @ X22) @ X23)
% 1.48/1.71          | ~ (v1_relat_1 @ X22))),
% 1.48/1.71      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.48/1.71  thf('57', plain,
% 1.48/1.71      ((~ (v1_relat_1 @ sk_C)
% 1.48/1.71        | (r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A)))),
% 1.48/1.71      inference('sup-', [status(thm)], ['55', '56'])).
% 1.48/1.71  thf('58', plain, ((v1_relat_1 @ sk_C)),
% 1.48/1.71      inference('sup-', [status(thm)], ['33', '34'])).
% 1.48/1.71  thf('59', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A))),
% 1.48/1.71      inference('demod', [status(thm)], ['57', '58'])).
% 1.48/1.71  thf('60', plain,
% 1.48/1.71      (![X0 : $i, X2 : $i]:
% 1.48/1.71         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.48/1.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.48/1.71  thf('61', plain,
% 1.48/1.71      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_C))
% 1.48/1.71        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.48/1.71      inference('sup-', [status(thm)], ['59', '60'])).
% 1.48/1.71  thf('62', plain,
% 1.48/1.71      ((~ (v1_relat_1 @ sk_C)
% 1.48/1.71        | ((k11_relat_1 @ sk_C @ sk_A) = (k1_xboole_0))
% 1.48/1.71        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.48/1.71      inference('sup-', [status(thm)], ['54', '61'])).
% 1.48/1.71  thf('63', plain, ((v1_relat_1 @ sk_C)),
% 1.48/1.71      inference('sup-', [status(thm)], ['33', '34'])).
% 1.48/1.71  thf(d16_relat_1, axiom,
% 1.48/1.71    (![A:$i]:
% 1.48/1.71     ( ( v1_relat_1 @ A ) =>
% 1.48/1.71       ( ![B:$i]:
% 1.48/1.71         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 1.48/1.71  thf('64', plain,
% 1.48/1.71      (![X20 : $i, X21 : $i]:
% 1.48/1.71         (((k11_relat_1 @ X20 @ X21) = (k9_relat_1 @ X20 @ (k1_tarski @ X21)))
% 1.48/1.71          | ~ (v1_relat_1 @ X20))),
% 1.48/1.71      inference('cnf', [status(esa)], [d16_relat_1])).
% 1.48/1.71  thf('65', plain,
% 1.48/1.71      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 1.48/1.71      inference('demod', [status(thm)], ['46', '47'])).
% 1.48/1.71  thf('66', plain,
% 1.48/1.71      ((((k2_relat_1 @ sk_C) = (k11_relat_1 @ sk_C @ sk_A))
% 1.48/1.71        | ~ (v1_relat_1 @ sk_C))),
% 1.48/1.71      inference('sup+', [status(thm)], ['64', '65'])).
% 1.48/1.71  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 1.48/1.71      inference('sup-', [status(thm)], ['33', '34'])).
% 1.48/1.71  thf('68', plain, (((k2_relat_1 @ sk_C) = (k11_relat_1 @ sk_C @ sk_A))),
% 1.48/1.71      inference('demod', [status(thm)], ['66', '67'])).
% 1.48/1.71  thf('69', plain,
% 1.48/1.71      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 1.48/1.71        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.48/1.71      inference('demod', [status(thm)], ['62', '63', '68'])).
% 1.48/1.71  thf(t14_funct_1, axiom,
% 1.48/1.71    (![A:$i,B:$i]:
% 1.48/1.71     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.48/1.71       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 1.48/1.71         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 1.48/1.71  thf('70', plain,
% 1.48/1.71      (![X31 : $i, X32 : $i]:
% 1.48/1.71         (((k1_relat_1 @ X32) != (k1_tarski @ X31))
% 1.48/1.71          | ((k2_relat_1 @ X32) = (k1_tarski @ (k1_funct_1 @ X32 @ X31)))
% 1.48/1.71          | ~ (v1_funct_1 @ X32)
% 1.48/1.71          | ~ (v1_relat_1 @ X32))),
% 1.48/1.71      inference('cnf', [status(esa)], [t14_funct_1])).
% 1.48/1.71  thf('71', plain,
% 1.48/1.71      (![X0 : $i]:
% 1.48/1.71         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 1.48/1.71          | ((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 1.48/1.71          | ~ (v1_relat_1 @ X0)
% 1.48/1.71          | ~ (v1_funct_1 @ X0)
% 1.48/1.71          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 1.48/1.71      inference('sup-', [status(thm)], ['69', '70'])).
% 1.48/1.71  thf('72', plain,
% 1.48/1.71      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 1.48/1.71        | ~ (v1_funct_1 @ sk_C)
% 1.48/1.71        | ~ (v1_relat_1 @ sk_C)
% 1.48/1.71        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.48/1.71      inference('eq_res', [status(thm)], ['71'])).
% 1.48/1.71  thf('73', plain, ((v1_funct_1 @ sk_C)),
% 1.48/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.48/1.71  thf('74', plain, ((v1_relat_1 @ sk_C)),
% 1.48/1.71      inference('sup-', [status(thm)], ['33', '34'])).
% 1.48/1.71  thf('75', plain,
% 1.48/1.71      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 1.48/1.71        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.48/1.71      inference('demod', [status(thm)], ['72', '73', '74'])).
% 1.48/1.71  thf('76', plain,
% 1.48/1.71      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)
% 1.48/1.71         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 1.48/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.48/1.71  thf('77', plain,
% 1.48/1.71      ((m1_subset_1 @ sk_C @ 
% 1.48/1.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.48/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.48/1.71  thf(redefinition_k2_relset_1, axiom,
% 1.48/1.71    (![A:$i,B:$i,C:$i]:
% 1.48/1.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.48/1.71       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.48/1.71  thf('78', plain,
% 1.48/1.71      (![X39 : $i, X40 : $i, X41 : $i]:
% 1.48/1.71         (((k2_relset_1 @ X40 @ X41 @ X39) = (k2_relat_1 @ X39))
% 1.48/1.71          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 1.48/1.71      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.48/1.71  thf('79', plain,
% 1.48/1.71      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.48/1.71      inference('sup-', [status(thm)], ['77', '78'])).
% 1.48/1.71  thf('80', plain,
% 1.48/1.71      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 1.48/1.71      inference('demod', [status(thm)], ['76', '79'])).
% 1.48/1.71  thf('81', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 1.48/1.71      inference('simplify_reflect-', [status(thm)], ['75', '80'])).
% 1.48/1.71  thf('82', plain,
% 1.48/1.71      ((((sk_C) = (k1_xboole_0)) | ((k1_xboole_0) != (k1_xboole_0)))),
% 1.48/1.71      inference('demod', [status(thm)], ['49', '81'])).
% 1.48/1.71  thf('83', plain, (((sk_C) = (k1_xboole_0))),
% 1.48/1.71      inference('simplify', [status(thm)], ['82'])).
% 1.48/1.71  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.48/1.71  thf('84', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.48/1.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.48/1.71  thf('85', plain, ($false),
% 1.48/1.71      inference('demod', [status(thm)], ['27', '83', '84'])).
% 1.48/1.71  
% 1.48/1.71  % SZS output end Refutation
% 1.48/1.71  
% 1.48/1.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
