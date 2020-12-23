%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z9Qgo344jb

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:19 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 121 expanded)
%              Number of leaves         :   45 (  57 expanded)
%              Depth                    :   18
%              Number of atoms          :  763 (1129 expanded)
%              Number of equality atoms :   54 (  76 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(d2_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( ( F != D )
              & ( F != C )
              & ( F != B )
              & ( F != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [F: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ D @ C @ B @ A )
    <=> ( ( F != A )
        & ( F != B )
        & ( F != C )
        & ( F != D ) ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 @ X12 )
      | ( X8 = X9 )
      | ( X8 = X10 )
      | ( X8 = X11 )
      | ( X8 = X12 ) ) ),
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
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v5_relat_1 @ X33 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('4',plain,(
    v5_relat_1 @ sk_D @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
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
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('6',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ( X41
        = ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ~ ( zip_tseitin_2 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,
    ( ~ ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k1_relset_1 @ X37 @ X38 @ X36 )
        = ( k1_relat_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('10',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(zf_stmt_3,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf(zf_stmt_6,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_1 @ B @ A )
         => ( zip_tseitin_2 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_1 @ X44 @ X45 )
      | ( zip_tseitin_2 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('14',plain,
    ( ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_1 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('18',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('20',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X4 @ X4 @ X5 @ X6 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(zf_stmt_7,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 @ X17 )
      | ( r2_hidden @ X13 @ X18 )
      | ( X18
       != ( k2_enumset1 @ X17 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('22',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X13 @ ( k2_enumset1 @ X17 @ X16 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('23',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ~ ( r1_tarski @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 )
      | ~ ( r1_tarski @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      | ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ ( k1_tarski @ X1 ) @ X2 )
      | ( zip_tseitin_0 @ X0 @ X1 @ X1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','27'])).

thf('29',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X8 != X7 )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X7: $i,X9: $i,X10: $i,X11: $i] :
      ~ ( zip_tseitin_0 @ X7 @ X9 @ X10 @ X11 @ X7 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_1 @ ( k1_tarski @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['14','31'])).

thf('33',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['11','32'])).

thf(t172_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) )).

thf('34',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X26 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X26 @ X25 ) @ X27 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v5_relat_1 @ X26 @ X27 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('37',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_relat_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('38',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['35','38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','40'])).

thf('42',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['1','41'])).

thf('43',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('44',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('45',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X4 @ X4 @ X5 @ X6 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('46',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ~ ( zip_tseitin_0 @ X19 @ X14 @ X15 @ X16 @ X17 )
      | ( X18
       != ( k2_enumset1 @ X17 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('47',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X19 @ X14 @ X15 @ X16 @ X17 )
      | ~ ( r2_hidden @ X19 @ ( k2_enumset1 @ X17 @ X16 @ X15 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','49'])).

thf('51',plain,(
    ~ ( zip_tseitin_0 @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['42','50'])).

thf('52',plain,
    ( ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B ) ),
    inference('sup-',[status(thm)],['0','51'])).

thf('53',plain,
    ( ( k1_funct_1 @ sk_D @ sk_C )
    = sk_B ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ( k1_funct_1 @ sk_D @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('55',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z9Qgo344jb
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:31:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.41/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.61  % Solved by: fo/fo7.sh
% 0.41/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.61  % done 100 iterations in 0.160s
% 0.41/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.61  % SZS output start Refutation
% 0.41/0.61  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.41/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.41/0.61  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.41/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.41/0.61  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.41/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.41/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.61  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.41/0.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.41/0.61  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.41/0.61  thf(sk_D_type, type, sk_D: $i).
% 0.41/0.61  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.41/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.61  thf(d2_enumset1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.41/0.61     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.41/0.61       ( ![F:$i]:
% 0.41/0.61         ( ( r2_hidden @ F @ E ) <=>
% 0.41/0.61           ( ~( ( ( F ) != ( D ) ) & ( ( F ) != ( C ) ) & ( ( F ) != ( B ) ) & 
% 0.41/0.61                ( ( F ) != ( A ) ) ) ) ) ) ))).
% 0.41/0.61  thf(zf_stmt_0, axiom,
% 0.41/0.61    (![F:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.41/0.61     ( ( zip_tseitin_0 @ F @ D @ C @ B @ A ) <=>
% 0.41/0.61       ( ( ( F ) != ( A ) ) & ( ( F ) != ( B ) ) & ( ( F ) != ( C ) ) & 
% 0.41/0.61         ( ( F ) != ( D ) ) ) ))).
% 0.41/0.61  thf('0', plain,
% 0.41/0.61      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.41/0.61         ((zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 @ X12)
% 0.41/0.61          | ((X8) = (X9))
% 0.41/0.61          | ((X8) = (X10))
% 0.41/0.61          | ((X8) = (X11))
% 0.41/0.61          | ((X8) = (X12)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(t65_funct_2, conjecture,
% 0.41/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.61     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.41/0.61         ( m1_subset_1 @
% 0.41/0.61           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.41/0.61       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.41/0.61  thf(zf_stmt_1, negated_conjecture,
% 0.41/0.61    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.61        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.41/0.61            ( m1_subset_1 @
% 0.41/0.61              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.41/0.61          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.41/0.61    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.41/0.61  thf('1', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.61  thf('2', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_D @ 
% 0.41/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.61  thf(cc2_relset_1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.61       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.41/0.61  thf('3', plain,
% 0.41/0.61      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.41/0.61         ((v5_relat_1 @ X33 @ X35)
% 0.41/0.61          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.41/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.41/0.61  thf('4', plain, ((v5_relat_1 @ sk_D @ (k1_tarski @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.41/0.61  thf('5', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.61  thf(d1_funct_2, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.61       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.41/0.61           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.41/0.61             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.41/0.61         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.61           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.41/0.61             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.41/0.61  thf(zf_stmt_2, axiom,
% 0.41/0.61    (![C:$i,B:$i,A:$i]:
% 0.41/0.61     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.41/0.61       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.41/0.61  thf('6', plain,
% 0.41/0.61      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.41/0.61         (~ (v1_funct_2 @ X43 @ X41 @ X42)
% 0.41/0.61          | ((X41) = (k1_relset_1 @ X41 @ X42 @ X43))
% 0.41/0.61          | ~ (zip_tseitin_2 @ X43 @ X42 @ X41))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.41/0.61  thf('7', plain,
% 0.41/0.61      ((~ (zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.41/0.61        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.41/0.61  thf('8', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_D @ 
% 0.41/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.61  thf(redefinition_k1_relset_1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.41/0.61  thf('9', plain,
% 0.41/0.61      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.41/0.61         (((k1_relset_1 @ X37 @ X38 @ X36) = (k1_relat_1 @ X36))
% 0.41/0.61          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.41/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.41/0.61  thf('10', plain,
% 0.41/0.61      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.41/0.61      inference('sup-', [status(thm)], ['8', '9'])).
% 0.41/0.61  thf('11', plain,
% 0.41/0.61      ((~ (zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.41/0.61        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.41/0.61      inference('demod', [status(thm)], ['7', '10'])).
% 0.41/0.61  thf('12', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_D @ 
% 0.41/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.61  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.41/0.61  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $o).
% 0.41/0.61  thf(zf_stmt_5, axiom,
% 0.41/0.61    (![B:$i,A:$i]:
% 0.41/0.61     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.61       ( zip_tseitin_1 @ B @ A ) ))).
% 0.41/0.61  thf(zf_stmt_6, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.61       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.41/0.61         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.41/0.61           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.41/0.61             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.41/0.61  thf('13', plain,
% 0.41/0.61      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.41/0.61         (~ (zip_tseitin_1 @ X44 @ X45)
% 0.41/0.61          | (zip_tseitin_2 @ X46 @ X44 @ X45)
% 0.41/0.61          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.41/0.61  thf('14', plain,
% 0.41/0.61      (((zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.41/0.61        | ~ (zip_tseitin_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.61  thf('15', plain,
% 0.41/0.61      (![X39 : $i, X40 : $i]:
% 0.41/0.61         ((zip_tseitin_1 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.41/0.61  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.41/0.61  thf('16', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.41/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.41/0.61  thf('17', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         ((r1_tarski @ X0 @ X1) | (zip_tseitin_1 @ X0 @ X2))),
% 0.41/0.61      inference('sup+', [status(thm)], ['15', '16'])).
% 0.41/0.61  thf(t69_enumset1, axiom,
% 0.41/0.61    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.41/0.61  thf('18', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.41/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.41/0.61  thf(t70_enumset1, axiom,
% 0.41/0.61    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.41/0.61  thf('19', plain,
% 0.41/0.61      (![X2 : $i, X3 : $i]:
% 0.41/0.61         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 0.41/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.41/0.61  thf(t71_enumset1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.41/0.61  thf('20', plain,
% 0.41/0.61      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.41/0.61         ((k2_enumset1 @ X4 @ X4 @ X5 @ X6) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 0.41/0.61      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.41/0.61  thf(zf_stmt_7, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.41/0.61  thf(zf_stmt_8, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.41/0.61     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.41/0.61       ( ![F:$i]:
% 0.41/0.61         ( ( r2_hidden @ F @ E ) <=> ( ~( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) ) ))).
% 0.41/0.61  thf('21', plain,
% 0.41/0.61      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.41/0.61         ((zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 @ X17)
% 0.41/0.61          | (r2_hidden @ X13 @ X18)
% 0.41/0.61          | ((X18) != (k2_enumset1 @ X17 @ X16 @ X15 @ X14)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.41/0.61  thf('22', plain,
% 0.41/0.61      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.41/0.61         ((r2_hidden @ X13 @ (k2_enumset1 @ X17 @ X16 @ X15 @ X14))
% 0.41/0.61          | (zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 @ X17))),
% 0.41/0.62      inference('simplify', [status(thm)], ['21'])).
% 0.41/0.62  thf(t7_ordinal1, axiom,
% 0.41/0.62    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.62  thf('23', plain,
% 0.41/0.62      (![X28 : $i, X29 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X28 @ X29) | ~ (r1_tarski @ X29 @ X28))),
% 0.41/0.62      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.41/0.62  thf('24', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.41/0.62         ((zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3)
% 0.41/0.62          | ~ (r1_tarski @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4))),
% 0.41/0.62      inference('sup-', [status(thm)], ['22', '23'])).
% 0.41/0.62  thf('25', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.62         (~ (r1_tarski @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.41/0.62          | (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2))),
% 0.41/0.62      inference('sup-', [status(thm)], ['20', '24'])).
% 0.41/0.62  thf('26', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.62         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2)
% 0.41/0.62          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['19', '25'])).
% 0.41/0.62  thf('27', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (~ (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.41/0.62          | (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['18', '26'])).
% 0.41/0.62  thf('28', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.62         ((zip_tseitin_1 @ (k1_tarski @ X1) @ X2)
% 0.41/0.62          | (zip_tseitin_0 @ X0 @ X1 @ X1 @ X1 @ X1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['17', '27'])).
% 0.41/0.62  thf('29', plain,
% 0.41/0.62      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.41/0.62         (((X8) != (X7)) | ~ (zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 @ X7))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('30', plain,
% 0.41/0.62      (![X7 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.41/0.62         ~ (zip_tseitin_0 @ X7 @ X9 @ X10 @ X11 @ X7)),
% 0.41/0.62      inference('simplify', [status(thm)], ['29'])).
% 0.41/0.62  thf('31', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]: (zip_tseitin_1 @ (k1_tarski @ X0) @ X1)),
% 0.41/0.62      inference('sup-', [status(thm)], ['28', '30'])).
% 0.41/0.62  thf('32', plain, ((zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)),
% 0.41/0.62      inference('demod', [status(thm)], ['14', '31'])).
% 0.41/0.62  thf('33', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.41/0.62      inference('demod', [status(thm)], ['11', '32'])).
% 0.41/0.62  thf(t172_funct_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.41/0.62       ( ![C:$i]:
% 0.41/0.62         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.41/0.62           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 0.41/0.62  thf('34', plain,
% 0.41/0.62      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X25 @ (k1_relat_1 @ X26))
% 0.41/0.62          | (r2_hidden @ (k1_funct_1 @ X26 @ X25) @ X27)
% 0.41/0.62          | ~ (v1_funct_1 @ X26)
% 0.41/0.62          | ~ (v5_relat_1 @ X26 @ X27)
% 0.41/0.62          | ~ (v1_relat_1 @ X26))),
% 0.41/0.62      inference('cnf', [status(esa)], [t172_funct_1])).
% 0.41/0.62  thf('35', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X0 @ sk_A)
% 0.41/0.62          | ~ (v1_relat_1 @ sk_D)
% 0.41/0.62          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.41/0.62          | ~ (v1_funct_1 @ sk_D)
% 0.41/0.62          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['33', '34'])).
% 0.41/0.62  thf('36', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_D @ 
% 0.41/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.62  thf(cc1_relset_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.62       ( v1_relat_1 @ C ) ))).
% 0.41/0.62  thf('37', plain,
% 0.41/0.62      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.41/0.62         ((v1_relat_1 @ X30)
% 0.41/0.62          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.41/0.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.41/0.62  thf('38', plain, ((v1_relat_1 @ sk_D)),
% 0.41/0.62      inference('sup-', [status(thm)], ['36', '37'])).
% 0.41/0.62  thf('39', plain, ((v1_funct_1 @ sk_D)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.62  thf('40', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X0 @ sk_A)
% 0.41/0.62          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.41/0.62          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.41/0.62      inference('demod', [status(thm)], ['35', '38', '39'])).
% 0.41/0.62  thf('41', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.41/0.62          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.41/0.62      inference('sup-', [status(thm)], ['4', '40'])).
% 0.41/0.62  thf('42', plain,
% 0.41/0.62      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ (k1_tarski @ sk_B))),
% 0.41/0.62      inference('sup-', [status(thm)], ['1', '41'])).
% 0.41/0.62  thf('43', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.41/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.41/0.62  thf('44', plain,
% 0.41/0.62      (![X2 : $i, X3 : $i]:
% 0.41/0.62         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 0.41/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.41/0.62  thf('45', plain,
% 0.41/0.62      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.41/0.62         ((k2_enumset1 @ X4 @ X4 @ X5 @ X6) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 0.41/0.62      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.41/0.62  thf('46', plain,
% 0.41/0.62      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X19 @ X18)
% 0.41/0.62          | ~ (zip_tseitin_0 @ X19 @ X14 @ X15 @ X16 @ X17)
% 0.41/0.62          | ((X18) != (k2_enumset1 @ X17 @ X16 @ X15 @ X14)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.41/0.62  thf('47', plain,
% 0.41/0.62      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X19 : $i]:
% 0.41/0.62         (~ (zip_tseitin_0 @ X19 @ X14 @ X15 @ X16 @ X17)
% 0.41/0.62          | ~ (r2_hidden @ X19 @ (k2_enumset1 @ X17 @ X16 @ X15 @ X14)))),
% 0.41/0.62      inference('simplify', [status(thm)], ['46'])).
% 0.41/0.62  thf('48', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.41/0.62          | ~ (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2))),
% 0.41/0.62      inference('sup-', [status(thm)], ['45', '47'])).
% 0.41/0.62  thf('49', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.41/0.62          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['44', '48'])).
% 0.41/0.62  thf('50', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.41/0.62          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['43', '49'])).
% 0.41/0.62  thf('51', plain,
% 0.41/0.62      (~ (zip_tseitin_0 @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B @ sk_B @ sk_B @ 
% 0.41/0.62          sk_B)),
% 0.41/0.62      inference('sup-', [status(thm)], ['42', '50'])).
% 0.41/0.62  thf('52', plain,
% 0.41/0.62      ((((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.41/0.62        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.41/0.62        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.41/0.62        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['0', '51'])).
% 0.41/0.62  thf('53', plain, (((k1_funct_1 @ sk_D @ sk_C) = (sk_B))),
% 0.41/0.62      inference('simplify', [status(thm)], ['52'])).
% 0.41/0.62  thf('54', plain, (((k1_funct_1 @ sk_D @ sk_C) != (sk_B))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.62  thf('55', plain, ($false),
% 0.41/0.62      inference('simplify_reflect-', [status(thm)], ['53', '54'])).
% 0.41/0.62  
% 0.41/0.62  % SZS output end Refutation
% 0.41/0.62  
% 0.41/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
