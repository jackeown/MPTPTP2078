%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.s119zXsAwW

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:14 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 153 expanded)
%              Number of leaves         :   50 (  67 expanded)
%              Depth                    :   18
%              Number of atoms          :  884 (1365 expanded)
%              Number of equality atoms :   55 (  85 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( X5 = X6 )
      | ( X5 = X7 )
      | ( X5 = X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( k1_funct_1 @ D @ C )
          = B ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ D @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_funct_2])).

thf('1',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

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

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('2',plain,(
    ! [X50: $i,X51: $i] :
      ( ( zip_tseitin_1 @ X50 @ X51 )
      | ( X50 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('3',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(zf_stmt_3,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_1 @ B @ A )
         => ( zip_tseitin_2 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ~ ( zip_tseitin_1 @ X55 @ X56 )
      | ( zip_tseitin_2 @ X57 @ X55 @ X56 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X55 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('7',plain,
    ( ( zip_tseitin_2 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ X0 )
      | ( zip_tseitin_2 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( v1_funct_2 @ X54 @ X52 @ X53 )
      | ( X52
        = ( k1_relset_1 @ X52 @ X53 @ X54 ) )
      | ~ ( zip_tseitin_2 @ X54 @ X53 @ X52 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('11',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( ( k1_relset_1 @ X48 @ X49 @ X47 )
        = ( k1_relat_1 @ X47 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('14',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('17',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_7,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( r2_hidden @ X9 @ X13 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('20',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('21',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X39 @ X40 )
      | ~ ( r1_tarski @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D_2 ) )
      | ( zip_tseitin_0 @ X0 @ sk_B_1 @ sk_B_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf('26',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ~ ( zip_tseitin_0 @ X4 @ X6 @ X7 @ X4 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X33: $i,X35: $i,X37: $i,X38: $i] :
      ( ( X35
       != ( k2_relat_1 @ X33 ) )
      | ( r2_hidden @ X37 @ X35 )
      | ~ ( r2_hidden @ X38 @ ( k1_relat_1 @ X33 ) )
      | ( X37
       != ( k1_funct_1 @ X33 @ X38 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('30',plain,(
    ! [X33: $i,X38: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( r2_hidden @ X38 @ ( k1_relat_1 @ X33 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X33 @ X38 ) @ ( k2_relat_1 @ X33 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ~ ( v1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('33',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('34',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( v1_relat_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('35',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['31','32','35'])).

thf('37',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) @ ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['1','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('39',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( v5_relat_1 @ X44 @ X46 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('40',plain,(
    v5_relat_1 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('41',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v5_relat_1 @ X30 @ X31 )
      | ( r1_tarski @ ( k2_relat_1 @ X30 ) @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('44',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('45',plain,(
    ! [X24: $i,X26: $i] :
      ( ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( r1_tarski @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('47',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( m1_subset_1 @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['37','48'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('50',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r2_hidden @ X22 @ X23 )
      | ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('53',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('54',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( zip_tseitin_0 @ X14 @ X10 @ X11 @ X12 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('55',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ~ ( zip_tseitin_0 @ X14 @ X10 @ X11 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','56'])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ~ ( zip_tseitin_0 @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) @ sk_B_1 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf('59',plain,
    ( ( ( k1_funct_1 @ sk_D_2 @ sk_C_1 )
      = sk_B_1 )
    | ( ( k1_funct_1 @ sk_D_2 @ sk_C_1 )
      = sk_B_1 )
    | ( ( k1_funct_1 @ sk_D_2 @ sk_C_1 )
      = sk_B_1 )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','58'])).

thf('60',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( ( k1_funct_1 @ sk_D_2 @ sk_C_1 )
      = sk_B_1 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ( k1_funct_1 @ sk_D_2 @ sk_C_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('62',plain,(
    v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('64',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('65',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 )
      | ~ ( v1_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ sk_B_1 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['62','69'])).

thf('71',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ~ ( zip_tseitin_0 @ X4 @ X6 @ X7 @ X4 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('72',plain,(
    $false ),
    inference('sup-',[status(thm)],['70','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.s119zXsAwW
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:34:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.75/0.93  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/0.93  % Solved by: fo/fo7.sh
% 0.75/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.93  % done 475 iterations in 0.500s
% 0.75/0.93  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/0.93  % SZS output start Refutation
% 0.75/0.93  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.75/0.93  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.75/0.93  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.75/0.93  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.75/0.93  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.75/0.93  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.75/0.93  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.75/0.93  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.75/0.93  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.93  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.75/0.93  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.75/0.93  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.75/0.93  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.75/0.93  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/0.93  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.75/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.93  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.75/0.93  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.75/0.93  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.75/0.93  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.75/0.93  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.75/0.93  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.75/0.93  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.75/0.93  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.75/0.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.93  thf(d1_enumset1, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.93     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.75/0.93       ( ![E:$i]:
% 0.75/0.93         ( ( r2_hidden @ E @ D ) <=>
% 0.75/0.93           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.75/0.93  thf(zf_stmt_0, axiom,
% 0.75/0.93    (![E:$i,C:$i,B:$i,A:$i]:
% 0.75/0.93     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.75/0.93       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.75/0.93  thf('0', plain,
% 0.75/0.93      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.75/0.93         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 0.75/0.93          | ((X5) = (X6))
% 0.75/0.93          | ((X5) = (X7))
% 0.75/0.93          | ((X5) = (X8)))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf(t65_funct_2, conjecture,
% 0.75/0.93    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.93     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.75/0.93         ( m1_subset_1 @
% 0.75/0.93           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.75/0.93       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.75/0.93  thf(zf_stmt_1, negated_conjecture,
% 0.75/0.93    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.93        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.75/0.93            ( m1_subset_1 @
% 0.75/0.93              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.75/0.93          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.75/0.93    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.75/0.93  thf('1', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.93  thf(d1_funct_2, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.93       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.75/0.93           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.75/0.93             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.75/0.93         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.75/0.93           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.75/0.93             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.75/0.93  thf(zf_stmt_2, axiom,
% 0.75/0.93    (![B:$i,A:$i]:
% 0.75/0.93     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.75/0.93       ( zip_tseitin_1 @ B @ A ) ))).
% 0.75/0.93  thf('2', plain,
% 0.75/0.93      (![X50 : $i, X51 : $i]:
% 0.75/0.93         ((zip_tseitin_1 @ X50 @ X51) | ((X50) = (k1_xboole_0)))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.75/0.93  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.75/0.93  thf('3', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.75/0.93      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.75/0.93  thf('4', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.93         ((r1_tarski @ X0 @ X1) | (zip_tseitin_1 @ X0 @ X2))),
% 0.75/0.93      inference('sup+', [status(thm)], ['2', '3'])).
% 0.75/0.93  thf('5', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_D_2 @ 
% 0.75/0.93        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.93  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.75/0.93  thf(zf_stmt_4, axiom,
% 0.75/0.93    (![C:$i,B:$i,A:$i]:
% 0.75/0.93     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.75/0.93       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.75/0.93  thf(zf_stmt_5, type, zip_tseitin_1 : $i > $i > $o).
% 0.75/0.93  thf(zf_stmt_6, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.93       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.75/0.93         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.75/0.93           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.75/0.93             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.75/0.93  thf('6', plain,
% 0.75/0.93      (![X55 : $i, X56 : $i, X57 : $i]:
% 0.75/0.93         (~ (zip_tseitin_1 @ X55 @ X56)
% 0.75/0.93          | (zip_tseitin_2 @ X57 @ X55 @ X56)
% 0.75/0.93          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X55))))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.75/0.93  thf('7', plain,
% 0.75/0.93      (((zip_tseitin_2 @ sk_D_2 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.75/0.93        | ~ (zip_tseitin_1 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.75/0.93      inference('sup-', [status(thm)], ['5', '6'])).
% 0.75/0.93  thf('8', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         ((r1_tarski @ (k1_tarski @ sk_B_1) @ X0)
% 0.75/0.93          | (zip_tseitin_2 @ sk_D_2 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.75/0.93      inference('sup-', [status(thm)], ['4', '7'])).
% 0.75/0.93  thf('9', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.93  thf('10', plain,
% 0.75/0.93      (![X52 : $i, X53 : $i, X54 : $i]:
% 0.75/0.93         (~ (v1_funct_2 @ X54 @ X52 @ X53)
% 0.75/0.93          | ((X52) = (k1_relset_1 @ X52 @ X53 @ X54))
% 0.75/0.93          | ~ (zip_tseitin_2 @ X54 @ X53 @ X52))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.75/0.93  thf('11', plain,
% 0.75/0.93      ((~ (zip_tseitin_2 @ sk_D_2 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.75/0.93        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_2)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['9', '10'])).
% 0.75/0.93  thf('12', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_D_2 @ 
% 0.75/0.93        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.93  thf(redefinition_k1_relset_1, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.93       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.75/0.93  thf('13', plain,
% 0.75/0.93      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.75/0.93         (((k1_relset_1 @ X48 @ X49 @ X47) = (k1_relat_1 @ X47))
% 0.75/0.93          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49))))),
% 0.75/0.93      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.75/0.93  thf('14', plain,
% 0.75/0.93      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_2)
% 0.75/0.93         = (k1_relat_1 @ sk_D_2))),
% 0.75/0.93      inference('sup-', [status(thm)], ['12', '13'])).
% 0.75/0.93  thf('15', plain,
% 0.75/0.93      ((~ (zip_tseitin_2 @ sk_D_2 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.75/0.93        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.75/0.93      inference('demod', [status(thm)], ['11', '14'])).
% 0.75/0.93  thf('16', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         ((r1_tarski @ (k1_tarski @ sk_B_1) @ X0)
% 0.75/0.93          | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['8', '15'])).
% 0.75/0.93  thf(t69_enumset1, axiom,
% 0.75/0.93    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.75/0.93  thf('17', plain,
% 0.75/0.93      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.75/0.93      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.75/0.93  thf(t70_enumset1, axiom,
% 0.75/0.93    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.75/0.93  thf('18', plain,
% 0.75/0.93      (![X17 : $i, X18 : $i]:
% 0.75/0.93         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.75/0.93      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.75/0.93  thf(zf_stmt_7, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.75/0.93  thf(zf_stmt_8, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.93     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.75/0.93       ( ![E:$i]:
% 0.75/0.93         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.75/0.93  thf('19', plain,
% 0.75/0.93      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.75/0.93         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.75/0.93          | (r2_hidden @ X9 @ X13)
% 0.75/0.93          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.75/0.93  thf('20', plain,
% 0.75/0.93      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.75/0.93         ((r2_hidden @ X9 @ (k1_enumset1 @ X12 @ X11 @ X10))
% 0.75/0.93          | (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12))),
% 0.75/0.93      inference('simplify', [status(thm)], ['19'])).
% 0.75/0.93  thf(t7_ordinal1, axiom,
% 0.75/0.93    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.75/0.93  thf('21', plain,
% 0.75/0.93      (![X39 : $i, X40 : $i]:
% 0.75/0.93         (~ (r2_hidden @ X39 @ X40) | ~ (r1_tarski @ X40 @ X39))),
% 0.75/0.93      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.75/0.93  thf('22', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.75/0.93         ((zip_tseitin_0 @ X3 @ X0 @ X1 @ X2)
% 0.75/0.93          | ~ (r1_tarski @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3))),
% 0.75/0.93      inference('sup-', [status(thm)], ['20', '21'])).
% 0.75/0.93  thf('23', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.93         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2)
% 0.75/0.93          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.75/0.93      inference('sup-', [status(thm)], ['18', '22'])).
% 0.75/0.93  thf('24', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         (~ (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.75/0.93          | (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['17', '23'])).
% 0.75/0.93  thf('25', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (((sk_A) = (k1_relat_1 @ sk_D_2))
% 0.75/0.93          | (zip_tseitin_0 @ X0 @ sk_B_1 @ sk_B_1 @ sk_B_1))),
% 0.75/0.93      inference('sup-', [status(thm)], ['16', '24'])).
% 0.75/0.93  thf('26', plain,
% 0.75/0.93      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.75/0.93         (((X5) != (X4)) | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X4))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('27', plain,
% 0.75/0.93      (![X4 : $i, X6 : $i, X7 : $i]: ~ (zip_tseitin_0 @ X4 @ X6 @ X7 @ X4)),
% 0.75/0.93      inference('simplify', [status(thm)], ['26'])).
% 0.75/0.93  thf('28', plain, (((sk_A) = (k1_relat_1 @ sk_D_2))),
% 0.75/0.93      inference('sup-', [status(thm)], ['25', '27'])).
% 0.75/0.93  thf(d5_funct_1, axiom,
% 0.75/0.93    (![A:$i]:
% 0.75/0.93     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.75/0.93       ( ![B:$i]:
% 0.75/0.93         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.75/0.93           ( ![C:$i]:
% 0.75/0.93             ( ( r2_hidden @ C @ B ) <=>
% 0.75/0.93               ( ?[D:$i]:
% 0.75/0.93                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.75/0.93                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.75/0.93  thf('29', plain,
% 0.75/0.93      (![X33 : $i, X35 : $i, X37 : $i, X38 : $i]:
% 0.75/0.93         (((X35) != (k2_relat_1 @ X33))
% 0.75/0.93          | (r2_hidden @ X37 @ X35)
% 0.75/0.93          | ~ (r2_hidden @ X38 @ (k1_relat_1 @ X33))
% 0.75/0.93          | ((X37) != (k1_funct_1 @ X33 @ X38))
% 0.75/0.93          | ~ (v1_funct_1 @ X33)
% 0.75/0.93          | ~ (v1_relat_1 @ X33))),
% 0.75/0.93      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.75/0.93  thf('30', plain,
% 0.75/0.93      (![X33 : $i, X38 : $i]:
% 0.75/0.93         (~ (v1_relat_1 @ X33)
% 0.75/0.93          | ~ (v1_funct_1 @ X33)
% 0.75/0.93          | ~ (r2_hidden @ X38 @ (k1_relat_1 @ X33))
% 0.75/0.93          | (r2_hidden @ (k1_funct_1 @ X33 @ X38) @ (k2_relat_1 @ X33)))),
% 0.75/0.93      inference('simplify', [status(thm)], ['29'])).
% 0.75/0.93  thf('31', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (~ (r2_hidden @ X0 @ sk_A)
% 0.75/0.93          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2))
% 0.75/0.93          | ~ (v1_funct_1 @ sk_D_2)
% 0.75/0.93          | ~ (v1_relat_1 @ sk_D_2))),
% 0.75/0.93      inference('sup-', [status(thm)], ['28', '30'])).
% 0.75/0.93  thf('32', plain, ((v1_funct_1 @ sk_D_2)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.93  thf('33', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_D_2 @ 
% 0.75/0.93        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.93  thf(cc1_relset_1, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.93       ( v1_relat_1 @ C ) ))).
% 0.75/0.93  thf('34', plain,
% 0.75/0.93      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.75/0.93         ((v1_relat_1 @ X41)
% 0.75/0.93          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43))))),
% 0.75/0.93      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.75/0.93  thf('35', plain, ((v1_relat_1 @ sk_D_2)),
% 0.75/0.93      inference('sup-', [status(thm)], ['33', '34'])).
% 0.75/0.93  thf('36', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (~ (r2_hidden @ X0 @ sk_A)
% 0.75/0.93          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2)))),
% 0.75/0.93      inference('demod', [status(thm)], ['31', '32', '35'])).
% 0.75/0.93  thf('37', plain,
% 0.75/0.93      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_1) @ (k2_relat_1 @ sk_D_2))),
% 0.75/0.93      inference('sup-', [status(thm)], ['1', '36'])).
% 0.75/0.93  thf('38', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_D_2 @ 
% 0.75/0.93        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.93  thf(cc2_relset_1, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.93       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.75/0.93  thf('39', plain,
% 0.75/0.93      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.75/0.93         ((v5_relat_1 @ X44 @ X46)
% 0.75/0.93          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46))))),
% 0.75/0.93      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.75/0.93  thf('40', plain, ((v5_relat_1 @ sk_D_2 @ (k1_tarski @ sk_B_1))),
% 0.75/0.93      inference('sup-', [status(thm)], ['38', '39'])).
% 0.75/0.93  thf(d19_relat_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( v1_relat_1 @ B ) =>
% 0.75/0.93       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.75/0.93  thf('41', plain,
% 0.75/0.93      (![X30 : $i, X31 : $i]:
% 0.75/0.93         (~ (v5_relat_1 @ X30 @ X31)
% 0.75/0.93          | (r1_tarski @ (k2_relat_1 @ X30) @ X31)
% 0.75/0.93          | ~ (v1_relat_1 @ X30))),
% 0.75/0.93      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.75/0.93  thf('42', plain,
% 0.75/0.93      ((~ (v1_relat_1 @ sk_D_2)
% 0.75/0.93        | (r1_tarski @ (k2_relat_1 @ sk_D_2) @ (k1_tarski @ sk_B_1)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['40', '41'])).
% 0.75/0.93  thf('43', plain, ((v1_relat_1 @ sk_D_2)),
% 0.75/0.93      inference('sup-', [status(thm)], ['33', '34'])).
% 0.75/0.93  thf('44', plain,
% 0.75/0.93      ((r1_tarski @ (k2_relat_1 @ sk_D_2) @ (k1_tarski @ sk_B_1))),
% 0.75/0.93      inference('demod', [status(thm)], ['42', '43'])).
% 0.75/0.93  thf(t3_subset, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.75/0.93  thf('45', plain,
% 0.75/0.93      (![X24 : $i, X26 : $i]:
% 0.75/0.93         ((m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X26)) | ~ (r1_tarski @ X24 @ X26))),
% 0.75/0.93      inference('cnf', [status(esa)], [t3_subset])).
% 0.75/0.93  thf('46', plain,
% 0.75/0.93      ((m1_subset_1 @ (k2_relat_1 @ sk_D_2) @ 
% 0.75/0.93        (k1_zfmisc_1 @ (k1_tarski @ sk_B_1)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['44', '45'])).
% 0.75/0.93  thf(t4_subset, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.75/0.93       ( m1_subset_1 @ A @ C ) ))).
% 0.75/0.93  thf('47', plain,
% 0.75/0.93      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.75/0.93         (~ (r2_hidden @ X27 @ X28)
% 0.75/0.93          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 0.75/0.93          | (m1_subset_1 @ X27 @ X29))),
% 0.75/0.93      inference('cnf', [status(esa)], [t4_subset])).
% 0.75/0.93  thf('48', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         ((m1_subset_1 @ X0 @ (k1_tarski @ sk_B_1))
% 0.75/0.93          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['46', '47'])).
% 0.75/0.93  thf('49', plain,
% 0.75/0.93      ((m1_subset_1 @ (k1_funct_1 @ sk_D_2 @ sk_C_1) @ (k1_tarski @ sk_B_1))),
% 0.75/0.93      inference('sup-', [status(thm)], ['37', '48'])).
% 0.75/0.93  thf(t2_subset, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( m1_subset_1 @ A @ B ) =>
% 0.75/0.93       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.75/0.93  thf('50', plain,
% 0.75/0.93      (![X22 : $i, X23 : $i]:
% 0.75/0.93         ((r2_hidden @ X22 @ X23)
% 0.75/0.93          | (v1_xboole_0 @ X23)
% 0.75/0.93          | ~ (m1_subset_1 @ X22 @ X23))),
% 0.75/0.93      inference('cnf', [status(esa)], [t2_subset])).
% 0.75/0.93  thf('51', plain,
% 0.75/0.93      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.75/0.93        | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_1) @ (k1_tarski @ sk_B_1)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['49', '50'])).
% 0.75/0.93  thf('52', plain,
% 0.75/0.93      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.75/0.93      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.75/0.93  thf('53', plain,
% 0.75/0.93      (![X17 : $i, X18 : $i]:
% 0.75/0.93         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.75/0.93      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.75/0.93  thf('54', plain,
% 0.75/0.93      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.75/0.93         (~ (r2_hidden @ X14 @ X13)
% 0.75/0.93          | ~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 0.75/0.93          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.75/0.93  thf('55', plain,
% 0.75/0.93      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 0.75/0.93         (~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 0.75/0.93          | ~ (r2_hidden @ X14 @ (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.75/0.93      inference('simplify', [status(thm)], ['54'])).
% 0.75/0.93  thf('56', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.93         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.75/0.93          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.75/0.93      inference('sup-', [status(thm)], ['53', '55'])).
% 0.75/0.93  thf('57', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.75/0.93          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['52', '56'])).
% 0.75/0.93  thf('58', plain,
% 0.75/0.93      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.75/0.93        | ~ (zip_tseitin_0 @ (k1_funct_1 @ sk_D_2 @ sk_C_1) @ sk_B_1 @ 
% 0.75/0.93             sk_B_1 @ sk_B_1))),
% 0.75/0.93      inference('sup-', [status(thm)], ['51', '57'])).
% 0.75/0.93  thf('59', plain,
% 0.75/0.93      ((((k1_funct_1 @ sk_D_2 @ sk_C_1) = (sk_B_1))
% 0.75/0.93        | ((k1_funct_1 @ sk_D_2 @ sk_C_1) = (sk_B_1))
% 0.75/0.93        | ((k1_funct_1 @ sk_D_2 @ sk_C_1) = (sk_B_1))
% 0.75/0.93        | (v1_xboole_0 @ (k1_tarski @ sk_B_1)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['0', '58'])).
% 0.75/0.93  thf('60', plain,
% 0.75/0.93      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.75/0.93        | ((k1_funct_1 @ sk_D_2 @ sk_C_1) = (sk_B_1)))),
% 0.75/0.93      inference('simplify', [status(thm)], ['59'])).
% 0.75/0.93  thf('61', plain, (((k1_funct_1 @ sk_D_2 @ sk_C_1) != (sk_B_1))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.93  thf('62', plain, ((v1_xboole_0 @ (k1_tarski @ sk_B_1))),
% 0.75/0.93      inference('simplify_reflect-', [status(thm)], ['60', '61'])).
% 0.75/0.93  thf('63', plain,
% 0.75/0.93      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.75/0.93      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.75/0.93  thf('64', plain,
% 0.75/0.93      (![X17 : $i, X18 : $i]:
% 0.75/0.93         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.75/0.93      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.75/0.93  thf('65', plain,
% 0.75/0.93      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.75/0.93         ((r2_hidden @ X9 @ (k1_enumset1 @ X12 @ X11 @ X10))
% 0.75/0.93          | (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12))),
% 0.75/0.93      inference('simplify', [status(thm)], ['19'])).
% 0.75/0.93  thf(d1_xboole_0, axiom,
% 0.75/0.93    (![A:$i]:
% 0.75/0.93     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.75/0.93  thf('66', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.75/0.93      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.75/0.93  thf('67', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.75/0.93         ((zip_tseitin_0 @ X3 @ X0 @ X1 @ X2)
% 0.75/0.93          | ~ (v1_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['65', '66'])).
% 0.75/0.93  thf('68', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.93         (~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))
% 0.75/0.93          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.75/0.93      inference('sup-', [status(thm)], ['64', '67'])).
% 0.75/0.93  thf('69', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         (~ (v1_xboole_0 @ (k1_tarski @ X0))
% 0.75/0.93          | (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['63', '68'])).
% 0.75/0.93  thf('70', plain,
% 0.75/0.93      (![X0 : $i]: (zip_tseitin_0 @ X0 @ sk_B_1 @ sk_B_1 @ sk_B_1)),
% 0.75/0.93      inference('sup-', [status(thm)], ['62', '69'])).
% 0.75/0.93  thf('71', plain,
% 0.75/0.93      (![X4 : $i, X6 : $i, X7 : $i]: ~ (zip_tseitin_0 @ X4 @ X6 @ X7 @ X4)),
% 0.75/0.93      inference('simplify', [status(thm)], ['26'])).
% 0.75/0.93  thf('72', plain, ($false), inference('sup-', [status(thm)], ['70', '71'])).
% 0.75/0.93  
% 0.75/0.93  % SZS output end Refutation
% 0.75/0.93  
% 0.75/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
