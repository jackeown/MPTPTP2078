%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fQKkUWCTb0

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:18 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 161 expanded)
%              Number of leaves         :   45 (  68 expanded)
%              Depth                    :   14
%              Number of atoms          :  672 (1602 expanded)
%              Number of equality atoms :   41 (  94 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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

thf('0',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ),
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
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( v1_funct_2 @ X51 @ X49 @ X50 )
      | ( X49
        = ( k1_relset_1 @ X49 @ X50 @ X51 ) )
      | ~ ( zip_tseitin_2 @ X51 @ X50 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('3',plain,(
    ! [X47: $i,X48: $i] :
      ( ( zip_tseitin_1 @ X47 @ X48 )
      | ( X47 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_1 @ B @ A )
         => ( zip_tseitin_2 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( zip_tseitin_1 @ X52 @ X53 )
      | ( zip_tseitin_2 @ X54 @ X52 @ X53 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_1 @ sk_B_2 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( ( k1_relset_1 @ X45 @ X46 @ X44 )
        = ( k1_relat_1 @ X44 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_enumset1 @ X16 @ X16 @ X17 )
      = ( k2_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 )
      | ( r2_hidden @ X8 @ X12 )
      | ( X12
       != ( k1_enumset1 @ X11 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('17',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X8 @ ( k1_enumset1 @ X11 @ X10 @ X9 ) )
      | ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X4 != X3 )
      | ~ ( zip_tseitin_0 @ X4 @ X5 @ X6 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('20',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ~ ( zip_tseitin_0 @ X3 @ X5 @ X6 @ X3 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','21'])).

thf('23',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['13','22'])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('24',plain,(
    ! [X28: $i,X29: $i,X31: $i] :
      ( ~ ( r2_hidden @ X28 @ ( k1_relat_1 @ X29 ) )
      | ( r2_hidden @ ( k4_tarski @ X28 @ X31 ) @ X29 )
      | ( X31
       != ( k1_funct_1 @ X29 @ X28 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('25',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ~ ( v1_funct_1 @ X29 )
      | ( r2_hidden @ ( k4_tarski @ X28 @ ( k1_funct_1 @ X29 @ X28 ) ) @ X29 )
      | ~ ( r2_hidden @ X28 @ ( k1_relat_1 @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('29',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v1_relat_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('30',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) @ sk_C_1 ),
    inference(demod,[status(thm)],['26','27','30'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('33',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('35',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_xboole_0 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X41 ) ) )
      | ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('36',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('38',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( v5_relat_1 @ X38 @ X40 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('39',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B_2 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['13','22'])).

thf(t176_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v5_relat_1 @ C @ A )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) )
       => ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ) )).

thf('41',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X32 @ ( k1_relat_1 @ X33 ) )
      | ( m1_subset_1 @ ( k1_funct_1 @ X33 @ X32 ) @ X34 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v5_relat_1 @ X33 @ X34 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t176_funct_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v5_relat_1 @ sk_C_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('44',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_C_1 @ X0 )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['39','45'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('47',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r2_hidden @ X21 @ X22 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference(demod,[status(thm)],['36','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['33','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fQKkUWCTb0
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:49:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.43/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.61  % Solved by: fo/fo7.sh
% 0.43/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.61  % done 164 iterations in 0.165s
% 0.43/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.61  % SZS output start Refutation
% 0.43/0.61  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.43/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.43/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.43/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.43/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.43/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.43/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.43/0.61  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.43/0.61  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.43/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.43/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.43/0.61  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.43/0.61  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.43/0.61  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.43/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.43/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.43/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.61  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.43/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.43/0.61  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.43/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.43/0.61  thf(t61_funct_2, conjecture,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.43/0.61         ( m1_subset_1 @
% 0.43/0.61           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.43/0.61       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.43/0.61         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.43/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.43/0.61        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.43/0.61            ( m1_subset_1 @
% 0.43/0.61              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.43/0.61          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.43/0.61            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.43/0.61    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.43/0.61  thf('0', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B_2)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(d1_funct_2, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.61       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.43/0.61           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.43/0.61             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.43/0.61         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.43/0.61           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.43/0.61             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.43/0.61  thf(zf_stmt_1, axiom,
% 0.43/0.61    (![C:$i,B:$i,A:$i]:
% 0.43/0.61     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.43/0.61       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.43/0.61  thf('1', plain,
% 0.43/0.61      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.43/0.61         (~ (v1_funct_2 @ X51 @ X49 @ X50)
% 0.43/0.61          | ((X49) = (k1_relset_1 @ X49 @ X50 @ X51))
% 0.43/0.61          | ~ (zip_tseitin_2 @ X51 @ X50 @ X49))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.43/0.61  thf('2', plain,
% 0.43/0.61      ((~ (zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ (k1_tarski @ sk_A))
% 0.43/0.61        | ((k1_tarski @ sk_A)
% 0.43/0.61            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ sk_C_1)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['0', '1'])).
% 0.43/0.61  thf(zf_stmt_2, axiom,
% 0.43/0.61    (![B:$i,A:$i]:
% 0.43/0.61     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.43/0.61       ( zip_tseitin_1 @ B @ A ) ))).
% 0.43/0.61  thf('3', plain,
% 0.43/0.61      (![X47 : $i, X48 : $i]:
% 0.43/0.61         ((zip_tseitin_1 @ X47 @ X48) | ((X47) = (k1_xboole_0)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.43/0.61  thf('4', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_C_1 @ 
% 0.43/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.43/0.61  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $o).
% 0.43/0.61  thf(zf_stmt_5, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.61       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.43/0.61         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.43/0.61           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.43/0.61             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.43/0.61  thf('5', plain,
% 0.43/0.61      (![X52 : $i, X53 : $i, X54 : $i]:
% 0.43/0.61         (~ (zip_tseitin_1 @ X52 @ X53)
% 0.43/0.61          | (zip_tseitin_2 @ X54 @ X52 @ X53)
% 0.43/0.61          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X52))))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.43/0.61  thf('6', plain,
% 0.43/0.61      (((zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ (k1_tarski @ sk_A))
% 0.43/0.61        | ~ (zip_tseitin_1 @ sk_B_2 @ (k1_tarski @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.43/0.61  thf('7', plain,
% 0.43/0.61      ((((sk_B_2) = (k1_xboole_0))
% 0.43/0.61        | (zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ (k1_tarski @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['3', '6'])).
% 0.43/0.61  thf('8', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('9', plain, ((zip_tseitin_2 @ sk_C_1 @ sk_B_2 @ (k1_tarski @ sk_A))),
% 0.43/0.61      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.43/0.61  thf('10', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_C_1 @ 
% 0.43/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(redefinition_k1_relset_1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.43/0.61  thf('11', plain,
% 0.43/0.61      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.43/0.61         (((k1_relset_1 @ X45 @ X46 @ X44) = (k1_relat_1 @ X44))
% 0.43/0.61          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46))))),
% 0.43/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.43/0.61  thf('12', plain,
% 0.43/0.61      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ sk_C_1)
% 0.43/0.61         = (k1_relat_1 @ sk_C_1))),
% 0.43/0.61      inference('sup-', [status(thm)], ['10', '11'])).
% 0.43/0.61  thf('13', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.43/0.61      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.43/0.61  thf(t69_enumset1, axiom,
% 0.43/0.61    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.43/0.61  thf('14', plain,
% 0.43/0.61      (![X15 : $i]: ((k2_tarski @ X15 @ X15) = (k1_tarski @ X15))),
% 0.43/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.43/0.61  thf(t70_enumset1, axiom,
% 0.43/0.61    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.43/0.61  thf('15', plain,
% 0.43/0.61      (![X16 : $i, X17 : $i]:
% 0.43/0.61         ((k1_enumset1 @ X16 @ X16 @ X17) = (k2_tarski @ X16 @ X17))),
% 0.43/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.43/0.61  thf(d1_enumset1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.61     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.43/0.61       ( ![E:$i]:
% 0.43/0.61         ( ( r2_hidden @ E @ D ) <=>
% 0.43/0.61           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.43/0.61  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.43/0.61  thf(zf_stmt_7, axiom,
% 0.43/0.61    (![E:$i,C:$i,B:$i,A:$i]:
% 0.43/0.61     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.43/0.61       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.43/0.61  thf(zf_stmt_8, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.61     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.43/0.61       ( ![E:$i]:
% 0.43/0.61         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.43/0.61  thf('16', plain,
% 0.43/0.61      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.43/0.61         ((zip_tseitin_0 @ X8 @ X9 @ X10 @ X11)
% 0.43/0.61          | (r2_hidden @ X8 @ X12)
% 0.43/0.61          | ((X12) != (k1_enumset1 @ X11 @ X10 @ X9)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.43/0.61  thf('17', plain,
% 0.43/0.61      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.43/0.61         ((r2_hidden @ X8 @ (k1_enumset1 @ X11 @ X10 @ X9))
% 0.43/0.61          | (zip_tseitin_0 @ X8 @ X9 @ X10 @ X11))),
% 0.43/0.61      inference('simplify', [status(thm)], ['16'])).
% 0.43/0.61  thf('18', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.61         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.43/0.61          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.43/0.61      inference('sup+', [status(thm)], ['15', '17'])).
% 0.43/0.61  thf('19', plain,
% 0.43/0.61      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.43/0.61         (((X4) != (X3)) | ~ (zip_tseitin_0 @ X4 @ X5 @ X6 @ X3))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.43/0.61  thf('20', plain,
% 0.43/0.61      (![X3 : $i, X5 : $i, X6 : $i]: ~ (zip_tseitin_0 @ X3 @ X5 @ X6 @ X3)),
% 0.43/0.61      inference('simplify', [status(thm)], ['19'])).
% 0.43/0.61  thf('21', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.43/0.61      inference('sup-', [status(thm)], ['18', '20'])).
% 0.43/0.61  thf('22', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.43/0.61      inference('sup+', [status(thm)], ['14', '21'])).
% 0.43/0.61  thf('23', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))),
% 0.43/0.61      inference('sup+', [status(thm)], ['13', '22'])).
% 0.43/0.61  thf(d4_funct_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.43/0.61       ( ![B:$i,C:$i]:
% 0.43/0.61         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.43/0.61             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.43/0.61               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.43/0.61           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.43/0.61             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.43/0.61               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.43/0.61  thf('24', plain,
% 0.43/0.61      (![X28 : $i, X29 : $i, X31 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X28 @ (k1_relat_1 @ X29))
% 0.43/0.61          | (r2_hidden @ (k4_tarski @ X28 @ X31) @ X29)
% 0.43/0.61          | ((X31) != (k1_funct_1 @ X29 @ X28))
% 0.43/0.61          | ~ (v1_funct_1 @ X29)
% 0.43/0.61          | ~ (v1_relat_1 @ X29))),
% 0.43/0.61      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.43/0.61  thf('25', plain,
% 0.43/0.61      (![X28 : $i, X29 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ X29)
% 0.43/0.61          | ~ (v1_funct_1 @ X29)
% 0.43/0.61          | (r2_hidden @ (k4_tarski @ X28 @ (k1_funct_1 @ X29 @ X28)) @ X29)
% 0.43/0.61          | ~ (r2_hidden @ X28 @ (k1_relat_1 @ X29)))),
% 0.43/0.61      inference('simplify', [status(thm)], ['24'])).
% 0.43/0.61  thf('26', plain,
% 0.43/0.61      (((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C_1 @ sk_A)) @ sk_C_1)
% 0.43/0.61        | ~ (v1_funct_1 @ sk_C_1)
% 0.43/0.61        | ~ (v1_relat_1 @ sk_C_1))),
% 0.43/0.61      inference('sup-', [status(thm)], ['23', '25'])).
% 0.43/0.61  thf('27', plain, ((v1_funct_1 @ sk_C_1)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('28', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_C_1 @ 
% 0.43/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(cc1_relset_1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.61       ( v1_relat_1 @ C ) ))).
% 0.43/0.61  thf('29', plain,
% 0.43/0.61      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.43/0.61         ((v1_relat_1 @ X35)
% 0.43/0.61          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.43/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.43/0.61  thf('30', plain, ((v1_relat_1 @ sk_C_1)),
% 0.43/0.61      inference('sup-', [status(thm)], ['28', '29'])).
% 0.43/0.61  thf('31', plain,
% 0.43/0.61      ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C_1 @ sk_A)) @ sk_C_1)),
% 0.43/0.61      inference('demod', [status(thm)], ['26', '27', '30'])).
% 0.43/0.61  thf(d1_xboole_0, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.43/0.61  thf('32', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.43/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.43/0.61  thf('33', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.43/0.61      inference('sup-', [status(thm)], ['31', '32'])).
% 0.43/0.61  thf('34', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_C_1 @ 
% 0.43/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(cc4_relset_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( v1_xboole_0 @ A ) =>
% 0.43/0.61       ( ![C:$i]:
% 0.43/0.61         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.43/0.61           ( v1_xboole_0 @ C ) ) ) ))).
% 0.43/0.61  thf('35', plain,
% 0.43/0.61      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.43/0.61         (~ (v1_xboole_0 @ X41)
% 0.43/0.61          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X41)))
% 0.43/0.61          | (v1_xboole_0 @ X42))),
% 0.43/0.61      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.43/0.61  thf('36', plain, (((v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ sk_B_2))),
% 0.43/0.61      inference('sup-', [status(thm)], ['34', '35'])).
% 0.43/0.61  thf('37', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_C_1 @ 
% 0.43/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(cc2_relset_1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.61       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.43/0.61  thf('38', plain,
% 0.43/0.61      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.43/0.61         ((v5_relat_1 @ X38 @ X40)
% 0.43/0.61          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 0.43/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.43/0.61  thf('39', plain, ((v5_relat_1 @ sk_C_1 @ sk_B_2)),
% 0.43/0.61      inference('sup-', [status(thm)], ['37', '38'])).
% 0.43/0.61  thf('40', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))),
% 0.43/0.61      inference('sup+', [status(thm)], ['13', '22'])).
% 0.43/0.61  thf(t176_funct_1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & ( v1_funct_1 @ C ) ) =>
% 0.43/0.61       ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) =>
% 0.43/0.61         ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ))).
% 0.43/0.61  thf('41', plain,
% 0.43/0.61      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X32 @ (k1_relat_1 @ X33))
% 0.43/0.61          | (m1_subset_1 @ (k1_funct_1 @ X33 @ X32) @ X34)
% 0.43/0.61          | ~ (v1_funct_1 @ X33)
% 0.43/0.61          | ~ (v5_relat_1 @ X33 @ X34)
% 0.43/0.61          | ~ (v1_relat_1 @ X33))),
% 0.43/0.61      inference('cnf', [status(esa)], [t176_funct_1])).
% 0.43/0.61  thf('42', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ sk_C_1)
% 0.43/0.61          | ~ (v5_relat_1 @ sk_C_1 @ X0)
% 0.43/0.61          | ~ (v1_funct_1 @ sk_C_1)
% 0.43/0.61          | (m1_subset_1 @ (k1_funct_1 @ sk_C_1 @ sk_A) @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['40', '41'])).
% 0.43/0.61  thf('43', plain, ((v1_relat_1 @ sk_C_1)),
% 0.43/0.61      inference('sup-', [status(thm)], ['28', '29'])).
% 0.43/0.61  thf('44', plain, ((v1_funct_1 @ sk_C_1)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('45', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (v5_relat_1 @ sk_C_1 @ X0)
% 0.43/0.61          | (m1_subset_1 @ (k1_funct_1 @ sk_C_1 @ sk_A) @ X0))),
% 0.43/0.61      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.43/0.61  thf('46', plain, ((m1_subset_1 @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B_2)),
% 0.43/0.61      inference('sup-', [status(thm)], ['39', '45'])).
% 0.43/0.61  thf(t2_subset, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( m1_subset_1 @ A @ B ) =>
% 0.43/0.61       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.43/0.61  thf('47', plain,
% 0.43/0.61      (![X21 : $i, X22 : $i]:
% 0.43/0.61         ((r2_hidden @ X21 @ X22)
% 0.43/0.61          | (v1_xboole_0 @ X22)
% 0.43/0.61          | ~ (m1_subset_1 @ X21 @ X22))),
% 0.43/0.61      inference('cnf', [status(esa)], [t2_subset])).
% 0.43/0.61  thf('48', plain,
% 0.43/0.61      (((v1_xboole_0 @ sk_B_2)
% 0.43/0.61        | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B_2))),
% 0.43/0.61      inference('sup-', [status(thm)], ['46', '47'])).
% 0.43/0.61  thf('49', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B_2)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('50', plain, ((v1_xboole_0 @ sk_B_2)),
% 0.43/0.61      inference('clc', [status(thm)], ['48', '49'])).
% 0.43/0.61  thf('51', plain, ((v1_xboole_0 @ sk_C_1)),
% 0.43/0.61      inference('demod', [status(thm)], ['36', '50'])).
% 0.43/0.61  thf('52', plain, ($false), inference('demod', [status(thm)], ['33', '51'])).
% 0.43/0.61  
% 0.43/0.61  % SZS output end Refutation
% 0.43/0.61  
% 0.43/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
