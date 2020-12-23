%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ut0N1NGqJl

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 144 expanded)
%              Number of leaves         :   48 (  64 expanded)
%              Depth                    :   19
%              Number of atoms          :  852 (1310 expanded)
%              Number of equality atoms :   51 (  81 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
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

thf('3',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_2 @ X47 @ X45 @ X46 )
      | ( X45
        = ( k1_relset_1 @ X45 @ X46 @ X47 ) )
      | ~ ( zip_tseitin_2 @ X47 @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,
    ( ~ ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(zf_stmt_3,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('5',plain,(
    ! [X43: $i,X44: $i] :
      ( ( zip_tseitin_1 @ X43 @ X44 )
      | ( X43 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('6',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(zf_stmt_4,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

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

thf('9',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( zip_tseitin_1 @ X48 @ X49 )
      | ( zip_tseitin_2 @ X50 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('10',plain,
    ( ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ X0 )
      | ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('12',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('13',plain,(
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

thf('14',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( r2_hidden @ X9 @ X13 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('15',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('16',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ~ ( r1_tarski @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      | ( zip_tseitin_0 @ X0 @ sk_B_1 @ sk_B_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','19'])).

thf('21',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ~ ( zip_tseitin_0 @ X4 @ X6 @ X7 @ X4 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k1_relset_1 @ X38 @ X39 @ X37 )
        = ( k1_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('26',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['4','23','26'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('28',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k1_relat_1 @ X28 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X28 @ X27 ) @ ( k2_relat_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('31',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v1_relat_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['29','32','33'])).

thf('35',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('37',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X34 @ X35 @ X36 ) @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('38',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('40',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k2_relset_1 @ X41 @ X42 @ X40 )
        = ( k2_relat_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('41',plain,
    ( ( k2_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['38','41'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('43',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( m1_subset_1 @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_C ) @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['35','44'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('46',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r2_hidden @ X22 @ X23 )
      | ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('49',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('50',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( zip_tseitin_0 @ X14 @ X10 @ X11 @ X12 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('51',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ~ ( zip_tseitin_0 @ X14 @ X10 @ X11 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ~ ( zip_tseitin_0 @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B_1 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['47','53'])).

thf('55',plain,
    ( ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B_1 )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B_1 )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B_1 )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','54'])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B_1 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ( k1_funct_1 @ sk_D @ sk_C )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('58',plain,(
    v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('60',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('61',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 )
      | ~ ( v1_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ sk_B_1 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['58','65'])).

thf('67',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ~ ( zip_tseitin_0 @ X4 @ X6 @ X7 @ X4 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('68',plain,(
    $false ),
    inference('sup-',[status(thm)],['66','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ut0N1NGqJl
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:18:23 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.58  % Solved by: fo/fo7.sh
% 0.22/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.58  % done 140 iterations in 0.144s
% 0.22/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.58  % SZS output start Refutation
% 0.22/0.58  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.22/0.58  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.22/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.58  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.22/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.58  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.22/0.58  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.58  thf(d1_enumset1, axiom,
% 0.22/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.58     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.58       ( ![E:$i]:
% 0.22/0.58         ( ( r2_hidden @ E @ D ) <=>
% 0.22/0.58           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.22/0.58  thf(zf_stmt_0, axiom,
% 0.22/0.58    (![E:$i,C:$i,B:$i,A:$i]:
% 0.22/0.58     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.22/0.58       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.22/0.58  thf('0', plain,
% 0.22/0.58      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.58         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 0.22/0.58          | ((X5) = (X6))
% 0.22/0.58          | ((X5) = (X7))
% 0.22/0.58          | ((X5) = (X8)))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf(t65_funct_2, conjecture,
% 0.22/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.58     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.22/0.58         ( m1_subset_1 @
% 0.22/0.58           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.22/0.58       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.22/0.58  thf(zf_stmt_1, negated_conjecture,
% 0.22/0.58    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.58        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.22/0.58            ( m1_subset_1 @
% 0.22/0.58              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.22/0.58          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.22/0.58    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.22/0.58  thf('1', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.58  thf('2', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.58  thf(d1_funct_2, axiom,
% 0.22/0.58    (![A:$i,B:$i,C:$i]:
% 0.22/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.58       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.22/0.58           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.22/0.58             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.58         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.58           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.22/0.58             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.22/0.58  thf(zf_stmt_2, axiom,
% 0.22/0.58    (![C:$i,B:$i,A:$i]:
% 0.22/0.58     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.22/0.58       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.22/0.58  thf('3', plain,
% 0.22/0.58      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.22/0.58         (~ (v1_funct_2 @ X47 @ X45 @ X46)
% 0.22/0.58          | ((X45) = (k1_relset_1 @ X45 @ X46 @ X47))
% 0.22/0.58          | ~ (zip_tseitin_2 @ X47 @ X46 @ X45))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.58  thf('4', plain,
% 0.22/0.58      ((~ (zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.22/0.58        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.58  thf(zf_stmt_3, axiom,
% 0.22/0.58    (![B:$i,A:$i]:
% 0.22/0.58     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.58       ( zip_tseitin_1 @ B @ A ) ))).
% 0.22/0.58  thf('5', plain,
% 0.22/0.58      (![X43 : $i, X44 : $i]:
% 0.22/0.58         ((zip_tseitin_1 @ X43 @ X44) | ((X43) = (k1_xboole_0)))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.58  thf('6', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.22/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.58  thf('7', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.58         ((r1_tarski @ X0 @ X1) | (zip_tseitin_1 @ X0 @ X2))),
% 0.22/0.58      inference('sup+', [status(thm)], ['5', '6'])).
% 0.22/0.58  thf('8', plain,
% 0.22/0.58      ((m1_subset_1 @ sk_D @ 
% 0.22/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.58  thf(zf_stmt_4, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.22/0.58  thf(zf_stmt_5, type, zip_tseitin_1 : $i > $i > $o).
% 0.22/0.58  thf(zf_stmt_6, axiom,
% 0.22/0.58    (![A:$i,B:$i,C:$i]:
% 0.22/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.58       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.22/0.58         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.22/0.58           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.22/0.58             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.22/0.58  thf('9', plain,
% 0.22/0.58      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.22/0.58         (~ (zip_tseitin_1 @ X48 @ X49)
% 0.22/0.58          | (zip_tseitin_2 @ X50 @ X48 @ X49)
% 0.22/0.58          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48))))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.22/0.58  thf('10', plain,
% 0.22/0.58      (((zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.22/0.58        | ~ (zip_tseitin_1 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.22/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.58  thf('11', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         ((r1_tarski @ (k1_tarski @ sk_B_1) @ X0)
% 0.22/0.58          | (zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.22/0.58      inference('sup-', [status(thm)], ['7', '10'])).
% 0.22/0.58  thf(t69_enumset1, axiom,
% 0.22/0.58    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.58  thf('12', plain,
% 0.22/0.58      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.22/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.58  thf(t70_enumset1, axiom,
% 0.22/0.58    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.22/0.58  thf('13', plain,
% 0.22/0.58      (![X17 : $i, X18 : $i]:
% 0.22/0.58         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.22/0.58      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.58  thf(zf_stmt_7, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.22/0.58  thf(zf_stmt_8, axiom,
% 0.22/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.58     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.58       ( ![E:$i]:
% 0.22/0.58         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.22/0.58  thf('14', plain,
% 0.22/0.58      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.58         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.22/0.58          | (r2_hidden @ X9 @ X13)
% 0.22/0.58          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.22/0.58  thf('15', plain,
% 0.22/0.58      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.58         ((r2_hidden @ X9 @ (k1_enumset1 @ X12 @ X11 @ X10))
% 0.22/0.58          | (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12))),
% 0.22/0.58      inference('simplify', [status(thm)], ['14'])).
% 0.22/0.58  thf(t7_ordinal1, axiom,
% 0.22/0.58    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.58  thf('16', plain,
% 0.22/0.58      (![X29 : $i, X30 : $i]:
% 0.22/0.58         (~ (r2_hidden @ X29 @ X30) | ~ (r1_tarski @ X30 @ X29))),
% 0.22/0.58      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.22/0.58  thf('17', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.58         ((zip_tseitin_0 @ X3 @ X0 @ X1 @ X2)
% 0.22/0.58          | ~ (r1_tarski @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3))),
% 0.22/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.58  thf('18', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.58         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2)
% 0.22/0.58          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.22/0.58      inference('sup-', [status(thm)], ['13', '17'])).
% 0.22/0.58  thf('19', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (~ (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.22/0.58          | (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['12', '18'])).
% 0.22/0.58  thf('20', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         ((zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.22/0.58          | (zip_tseitin_0 @ X0 @ sk_B_1 @ sk_B_1 @ sk_B_1))),
% 0.22/0.58      inference('sup-', [status(thm)], ['11', '19'])).
% 0.22/0.58  thf('21', plain,
% 0.22/0.58      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.58         (((X5) != (X4)) | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X4))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('22', plain,
% 0.22/0.58      (![X4 : $i, X6 : $i, X7 : $i]: ~ (zip_tseitin_0 @ X4 @ X6 @ X7 @ X4)),
% 0.22/0.58      inference('simplify', [status(thm)], ['21'])).
% 0.22/0.58  thf('23', plain, ((zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.22/0.58      inference('sup-', [status(thm)], ['20', '22'])).
% 0.22/0.58  thf('24', plain,
% 0.22/0.58      ((m1_subset_1 @ sk_D @ 
% 0.22/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.58  thf(redefinition_k1_relset_1, axiom,
% 0.22/0.58    (![A:$i,B:$i,C:$i]:
% 0.22/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.58       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.22/0.58  thf('25', plain,
% 0.22/0.58      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.22/0.58         (((k1_relset_1 @ X38 @ X39 @ X37) = (k1_relat_1 @ X37))
% 0.22/0.58          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.22/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.22/0.58  thf('26', plain,
% 0.22/0.58      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D)
% 0.22/0.58         = (k1_relat_1 @ sk_D))),
% 0.22/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.58  thf('27', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.22/0.58      inference('demod', [status(thm)], ['4', '23', '26'])).
% 0.22/0.58  thf(t12_funct_1, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.58       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.22/0.58         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.22/0.58  thf('28', plain,
% 0.22/0.58      (![X27 : $i, X28 : $i]:
% 0.22/0.58         (~ (r2_hidden @ X27 @ (k1_relat_1 @ X28))
% 0.22/0.58          | (r2_hidden @ (k1_funct_1 @ X28 @ X27) @ (k2_relat_1 @ X28))
% 0.22/0.58          | ~ (v1_funct_1 @ X28)
% 0.22/0.58          | ~ (v1_relat_1 @ X28))),
% 0.22/0.58      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.22/0.58  thf('29', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         (~ (r2_hidden @ X0 @ sk_A)
% 0.22/0.58          | ~ (v1_relat_1 @ sk_D)
% 0.22/0.58          | ~ (v1_funct_1 @ sk_D)
% 0.22/0.58          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.58  thf('30', plain,
% 0.22/0.58      ((m1_subset_1 @ sk_D @ 
% 0.22/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.58  thf(cc1_relset_1, axiom,
% 0.22/0.58    (![A:$i,B:$i,C:$i]:
% 0.22/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.58       ( v1_relat_1 @ C ) ))).
% 0.22/0.58  thf('31', plain,
% 0.22/0.58      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.22/0.58         ((v1_relat_1 @ X31)
% 0.22/0.58          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.22/0.58      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.58  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.58      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.58  thf('33', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.58  thf('34', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         (~ (r2_hidden @ X0 @ sk_A)
% 0.22/0.58          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 0.22/0.58      inference('demod', [status(thm)], ['29', '32', '33'])).
% 0.22/0.58  thf('35', plain,
% 0.22/0.58      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))),
% 0.22/0.58      inference('sup-', [status(thm)], ['1', '34'])).
% 0.22/0.58  thf('36', plain,
% 0.22/0.58      ((m1_subset_1 @ sk_D @ 
% 0.22/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.58  thf(dt_k2_relset_1, axiom,
% 0.22/0.58    (![A:$i,B:$i,C:$i]:
% 0.22/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.58       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.22/0.58  thf('37', plain,
% 0.22/0.58      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.22/0.58         ((m1_subset_1 @ (k2_relset_1 @ X34 @ X35 @ X36) @ (k1_zfmisc_1 @ X35))
% 0.22/0.58          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.22/0.58      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.22/0.58  thf('38', plain,
% 0.22/0.58      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D) @ 
% 0.22/0.58        (k1_zfmisc_1 @ (k1_tarski @ sk_B_1)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.58  thf('39', plain,
% 0.22/0.58      ((m1_subset_1 @ sk_D @ 
% 0.22/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.58  thf(redefinition_k2_relset_1, axiom,
% 0.22/0.58    (![A:$i,B:$i,C:$i]:
% 0.22/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.58       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.22/0.58  thf('40', plain,
% 0.22/0.58      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.22/0.58         (((k2_relset_1 @ X41 @ X42 @ X40) = (k2_relat_1 @ X40))
% 0.22/0.58          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 0.22/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.22/0.58  thf('41', plain,
% 0.22/0.58      (((k2_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D)
% 0.22/0.58         = (k2_relat_1 @ sk_D))),
% 0.22/0.58      inference('sup-', [status(thm)], ['39', '40'])).
% 0.22/0.58  thf('42', plain,
% 0.22/0.58      ((m1_subset_1 @ (k2_relat_1 @ sk_D) @ 
% 0.22/0.58        (k1_zfmisc_1 @ (k1_tarski @ sk_B_1)))),
% 0.22/0.58      inference('demod', [status(thm)], ['38', '41'])).
% 0.22/0.58  thf(t4_subset, axiom,
% 0.22/0.58    (![A:$i,B:$i,C:$i]:
% 0.22/0.58     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.22/0.58       ( m1_subset_1 @ A @ C ) ))).
% 0.22/0.58  thf('43', plain,
% 0.22/0.58      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.22/0.58         (~ (r2_hidden @ X24 @ X25)
% 0.22/0.58          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.22/0.58          | (m1_subset_1 @ X24 @ X26))),
% 0.22/0.58      inference('cnf', [status(esa)], [t4_subset])).
% 0.22/0.58  thf('44', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         ((m1_subset_1 @ X0 @ (k1_tarski @ sk_B_1))
% 0.22/0.58          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['42', '43'])).
% 0.22/0.58  thf('45', plain,
% 0.22/0.58      ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_C) @ (k1_tarski @ sk_B_1))),
% 0.22/0.58      inference('sup-', [status(thm)], ['35', '44'])).
% 0.22/0.58  thf(t2_subset, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( m1_subset_1 @ A @ B ) =>
% 0.22/0.58       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.22/0.58  thf('46', plain,
% 0.22/0.58      (![X22 : $i, X23 : $i]:
% 0.22/0.58         ((r2_hidden @ X22 @ X23)
% 0.22/0.58          | (v1_xboole_0 @ X23)
% 0.22/0.58          | ~ (m1_subset_1 @ X22 @ X23))),
% 0.22/0.58      inference('cnf', [status(esa)], [t2_subset])).
% 0.22/0.58  thf('47', plain,
% 0.22/0.58      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.22/0.58        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ (k1_tarski @ sk_B_1)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.58  thf('48', plain,
% 0.22/0.58      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.22/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.58  thf('49', plain,
% 0.22/0.58      (![X17 : $i, X18 : $i]:
% 0.22/0.58         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.22/0.58      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.58  thf('50', plain,
% 0.22/0.58      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.58         (~ (r2_hidden @ X14 @ X13)
% 0.22/0.58          | ~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 0.22/0.58          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.22/0.58  thf('51', plain,
% 0.22/0.58      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 0.22/0.58         (~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 0.22/0.58          | ~ (r2_hidden @ X14 @ (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.22/0.58      inference('simplify', [status(thm)], ['50'])).
% 0.22/0.58  thf('52', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.58         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.22/0.58          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.22/0.58      inference('sup-', [status(thm)], ['49', '51'])).
% 0.22/0.58  thf('53', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.22/0.58          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['48', '52'])).
% 0.22/0.58  thf('54', plain,
% 0.22/0.58      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.22/0.58        | ~ (zip_tseitin_0 @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B_1 @ sk_B_1 @ 
% 0.22/0.58             sk_B_1))),
% 0.22/0.58      inference('sup-', [status(thm)], ['47', '53'])).
% 0.22/0.58  thf('55', plain,
% 0.22/0.58      ((((k1_funct_1 @ sk_D @ sk_C) = (sk_B_1))
% 0.22/0.58        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B_1))
% 0.22/0.58        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B_1))
% 0.22/0.58        | (v1_xboole_0 @ (k1_tarski @ sk_B_1)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['0', '54'])).
% 0.22/0.58  thf('56', plain,
% 0.22/0.58      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.22/0.58        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B_1)))),
% 0.22/0.58      inference('simplify', [status(thm)], ['55'])).
% 0.22/0.58  thf('57', plain, (((k1_funct_1 @ sk_D @ sk_C) != (sk_B_1))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.58  thf('58', plain, ((v1_xboole_0 @ (k1_tarski @ sk_B_1))),
% 0.22/0.58      inference('simplify_reflect-', [status(thm)], ['56', '57'])).
% 0.22/0.58  thf('59', plain,
% 0.22/0.58      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.22/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.58  thf('60', plain,
% 0.22/0.58      (![X17 : $i, X18 : $i]:
% 0.22/0.58         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.22/0.58      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.58  thf('61', plain,
% 0.22/0.58      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.58         ((r2_hidden @ X9 @ (k1_enumset1 @ X12 @ X11 @ X10))
% 0.22/0.58          | (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12))),
% 0.22/0.58      inference('simplify', [status(thm)], ['14'])).
% 0.22/0.58  thf(d1_xboole_0, axiom,
% 0.22/0.58    (![A:$i]:
% 0.22/0.58     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.58  thf('62', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.58  thf('63', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.58         ((zip_tseitin_0 @ X3 @ X0 @ X1 @ X2)
% 0.22/0.58          | ~ (v1_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['61', '62'])).
% 0.22/0.58  thf('64', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.58         (~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))
% 0.22/0.58          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.22/0.58      inference('sup-', [status(thm)], ['60', '63'])).
% 0.22/0.58  thf('65', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (~ (v1_xboole_0 @ (k1_tarski @ X0))
% 0.22/0.58          | (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['59', '64'])).
% 0.22/0.58  thf('66', plain,
% 0.22/0.58      (![X0 : $i]: (zip_tseitin_0 @ X0 @ sk_B_1 @ sk_B_1 @ sk_B_1)),
% 0.22/0.58      inference('sup-', [status(thm)], ['58', '65'])).
% 0.22/0.58  thf('67', plain,
% 0.22/0.58      (![X4 : $i, X6 : $i, X7 : $i]: ~ (zip_tseitin_0 @ X4 @ X6 @ X7 @ X4)),
% 0.22/0.58      inference('simplify', [status(thm)], ['21'])).
% 0.22/0.58  thf('68', plain, ($false), inference('sup-', [status(thm)], ['66', '67'])).
% 0.22/0.58  
% 0.22/0.58  % SZS output end Refutation
% 0.22/0.58  
% 0.42/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
