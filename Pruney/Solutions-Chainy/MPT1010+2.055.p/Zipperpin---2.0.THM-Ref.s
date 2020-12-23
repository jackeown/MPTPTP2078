%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j3ARPXtJYC

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:20 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 124 expanded)
%              Number of leaves         :   45 (  57 expanded)
%              Depth                    :   17
%              Number of atoms          :  763 (1157 expanded)
%              Number of equality atoms :   53 (  75 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( zip_tseitin_0 @ X2 @ X3 @ X4 @ X5 )
      | ( X2 = X3 )
      | ( X2 = X4 )
      | ( X2 = X5 ) ) ),
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

thf('2',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ ( k1_tarski @ sk_B ) ),
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
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ( X42
        = ( k1_relset_1 @ X42 @ X43 @ X44 ) )
      | ~ ( zip_tseitin_2 @ X44 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
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

thf('6',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( zip_tseitin_1 @ X45 @ X46 )
      | ( zip_tseitin_2 @ X47 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('7',plain,
    ( ( zip_tseitin_2 @ sk_D_2 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_1 @ X40 @ X41 )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_enumset1 @ X14 @ X14 @ X15 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
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

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 )
      | ( r2_hidden @ X6 @ X10 )
      | ( X10
       != ( k1_enumset1 @ X9 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('14',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X6 @ ( k1_enumset1 @ X9 @ X8 @ X7 ) )
      | ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('15',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ~ ( r1_tarski @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ ( k1_tarski @ X1 ) @ X2 )
      | ( zip_tseitin_0 @ X0 @ X1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('20',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X2 != X1 )
      | ~ ( zip_tseitin_0 @ X2 @ X3 @ X4 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ~ ( zip_tseitin_0 @ X1 @ X3 @ X4 @ X1 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_1 @ ( k1_tarski @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    zip_tseitin_2 @ sk_D_2 @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['7','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k1_relset_1 @ X35 @ X36 @ X34 )
        = ( k1_relat_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('26',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['4','23','26'])).

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

thf('28',plain,(
    ! [X20: $i,X22: $i,X24: $i,X25: $i] :
      ( ( X22
       != ( k2_relat_1 @ X20 ) )
      | ( r2_hidden @ X24 @ X22 )
      | ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X20 ) )
      | ( X24
       != ( k1_funct_1 @ X20 @ X25 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('29',plain,(
    ! [X20: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X20 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X20 @ X25 ) @ ( k2_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ~ ( v1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('32',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('33',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('34',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['30','31','34'])).

thf('36',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) @ ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['1','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('38',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X31 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('39',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_2 ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('41',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k2_relset_1 @ X38 @ X39 @ X37 )
        = ( k2_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('42',plain,
    ( ( k2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','42'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('44',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ( r2_hidden @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['36','45'])).

thf('47',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('48',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_enumset1 @ X14 @ X14 @ X15 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('49',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ~ ( zip_tseitin_0 @ X11 @ X7 @ X8 @ X9 )
      | ( X10
       != ( k1_enumset1 @ X9 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('50',plain,(
    ! [X7: $i,X8: $i,X9: $i,X11: $i] :
      ( ~ ( zip_tseitin_0 @ X11 @ X7 @ X8 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k1_enumset1 @ X9 @ X8 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','51'])).

thf('53',plain,(
    ~ ( zip_tseitin_0 @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,
    ( ( ( k1_funct_1 @ sk_D_2 @ sk_C_1 )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D_2 @ sk_C_1 )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D_2 @ sk_C_1 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['0','53'])).

thf('55',plain,
    ( ( k1_funct_1 @ sk_D_2 @ sk_C_1 )
    = sk_B ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ( k1_funct_1 @ sk_D_2 @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('57',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['55','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j3ARPXtJYC
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:34:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.63  % Solved by: fo/fo7.sh
% 0.37/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.63  % done 88 iterations in 0.114s
% 0.37/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.63  % SZS output start Refutation
% 0.37/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.63  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.37/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.63  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.37/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.63  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.37/0.63  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.37/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.63  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.63  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.37/0.63  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.37/0.63  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.63  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.37/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.63  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.37/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.63  thf(d1_enumset1, axiom,
% 0.37/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.63     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.37/0.63       ( ![E:$i]:
% 0.37/0.63         ( ( r2_hidden @ E @ D ) <=>
% 0.37/0.63           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.37/0.63  thf(zf_stmt_0, axiom,
% 0.37/0.63    (![E:$i,C:$i,B:$i,A:$i]:
% 0.37/0.63     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.37/0.63       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.37/0.63  thf('0', plain,
% 0.37/0.63      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.63         ((zip_tseitin_0 @ X2 @ X3 @ X4 @ X5)
% 0.37/0.63          | ((X2) = (X3))
% 0.37/0.63          | ((X2) = (X4))
% 0.37/0.63          | ((X2) = (X5)))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf(t65_funct_2, conjecture,
% 0.37/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.63     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.37/0.63         ( m1_subset_1 @
% 0.37/0.63           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.37/0.63       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.37/0.63  thf(zf_stmt_1, negated_conjecture,
% 0.37/0.63    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.63        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.37/0.63            ( m1_subset_1 @
% 0.37/0.63              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.37/0.63          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.37/0.63    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.37/0.63  thf('1', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.63  thf('2', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ (k1_tarski @ sk_B))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.63  thf(d1_funct_2, axiom,
% 0.37/0.63    (![A:$i,B:$i,C:$i]:
% 0.37/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.63       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.37/0.63           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.37/0.63             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.37/0.63         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.63           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.37/0.63             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.37/0.63  thf(zf_stmt_2, axiom,
% 0.37/0.63    (![C:$i,B:$i,A:$i]:
% 0.37/0.63     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.37/0.63       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.37/0.63  thf('3', plain,
% 0.37/0.63      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.37/0.63         (~ (v1_funct_2 @ X44 @ X42 @ X43)
% 0.37/0.63          | ((X42) = (k1_relset_1 @ X42 @ X43 @ X44))
% 0.37/0.63          | ~ (zip_tseitin_2 @ X44 @ X43 @ X42))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.37/0.63  thf('4', plain,
% 0.37/0.63      ((~ (zip_tseitin_2 @ sk_D_2 @ (k1_tarski @ sk_B) @ sk_A)
% 0.37/0.63        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_2)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.63  thf('5', plain,
% 0.37/0.63      ((m1_subset_1 @ sk_D_2 @ 
% 0.37/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.63  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.37/0.63  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $o).
% 0.37/0.63  thf(zf_stmt_5, axiom,
% 0.37/0.63    (![B:$i,A:$i]:
% 0.37/0.63     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.63       ( zip_tseitin_1 @ B @ A ) ))).
% 0.37/0.63  thf(zf_stmt_6, axiom,
% 0.37/0.63    (![A:$i,B:$i,C:$i]:
% 0.37/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.63       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.37/0.63         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.37/0.63           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.37/0.63             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.37/0.63  thf('6', plain,
% 0.37/0.63      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.37/0.63         (~ (zip_tseitin_1 @ X45 @ X46)
% 0.37/0.63          | (zip_tseitin_2 @ X47 @ X45 @ X46)
% 0.37/0.63          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45))))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.37/0.63  thf('7', plain,
% 0.37/0.63      (((zip_tseitin_2 @ sk_D_2 @ (k1_tarski @ sk_B) @ sk_A)
% 0.37/0.63        | ~ (zip_tseitin_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.37/0.63      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.63  thf('8', plain,
% 0.37/0.63      (![X40 : $i, X41 : $i]:
% 0.37/0.63         ((zip_tseitin_1 @ X40 @ X41) | ((X40) = (k1_xboole_0)))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.37/0.63  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.37/0.63  thf('9', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.37/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.63  thf('10', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.63         ((r1_tarski @ X0 @ X1) | (zip_tseitin_1 @ X0 @ X2))),
% 0.37/0.63      inference('sup+', [status(thm)], ['8', '9'])).
% 0.37/0.63  thf(t69_enumset1, axiom,
% 0.37/0.63    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.37/0.63  thf('11', plain,
% 0.37/0.63      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.37/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.63  thf(t70_enumset1, axiom,
% 0.37/0.63    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.37/0.63  thf('12', plain,
% 0.37/0.63      (![X14 : $i, X15 : $i]:
% 0.37/0.63         ((k1_enumset1 @ X14 @ X14 @ X15) = (k2_tarski @ X14 @ X15))),
% 0.37/0.63      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.37/0.63  thf(zf_stmt_7, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.37/0.63  thf(zf_stmt_8, axiom,
% 0.37/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.63     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.37/0.63       ( ![E:$i]:
% 0.37/0.63         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.37/0.63  thf('13', plain,
% 0.37/0.63      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.63         ((zip_tseitin_0 @ X6 @ X7 @ X8 @ X9)
% 0.37/0.63          | (r2_hidden @ X6 @ X10)
% 0.37/0.63          | ((X10) != (k1_enumset1 @ X9 @ X8 @ X7)))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.37/0.63  thf('14', plain,
% 0.37/0.63      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.37/0.63         ((r2_hidden @ X6 @ (k1_enumset1 @ X9 @ X8 @ X7))
% 0.37/0.63          | (zip_tseitin_0 @ X6 @ X7 @ X8 @ X9))),
% 0.37/0.63      inference('simplify', [status(thm)], ['13'])).
% 0.37/0.63  thf(t7_ordinal1, axiom,
% 0.37/0.63    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.63  thf('15', plain,
% 0.37/0.63      (![X26 : $i, X27 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X26 @ X27) | ~ (r1_tarski @ X27 @ X26))),
% 0.37/0.63      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.37/0.63  thf('16', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.63         ((zip_tseitin_0 @ X3 @ X0 @ X1 @ X2)
% 0.37/0.63          | ~ (r1_tarski @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3))),
% 0.37/0.63      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.63  thf('17', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.63         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2)
% 0.37/0.63          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.37/0.63      inference('sup-', [status(thm)], ['12', '16'])).
% 0.37/0.63  thf('18', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         (~ (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.37/0.63          | (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.37/0.63      inference('sup-', [status(thm)], ['11', '17'])).
% 0.37/0.63  thf('19', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.63         ((zip_tseitin_1 @ (k1_tarski @ X1) @ X2)
% 0.37/0.63          | (zip_tseitin_0 @ X0 @ X1 @ X1 @ X1))),
% 0.37/0.63      inference('sup-', [status(thm)], ['10', '18'])).
% 0.37/0.63  thf('20', plain,
% 0.37/0.63      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.63         (((X2) != (X1)) | ~ (zip_tseitin_0 @ X2 @ X3 @ X4 @ X1))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('21', plain,
% 0.37/0.63      (![X1 : $i, X3 : $i, X4 : $i]: ~ (zip_tseitin_0 @ X1 @ X3 @ X4 @ X1)),
% 0.37/0.63      inference('simplify', [status(thm)], ['20'])).
% 0.37/0.63  thf('22', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]: (zip_tseitin_1 @ (k1_tarski @ X0) @ X1)),
% 0.37/0.63      inference('sup-', [status(thm)], ['19', '21'])).
% 0.37/0.63  thf('23', plain, ((zip_tseitin_2 @ sk_D_2 @ (k1_tarski @ sk_B) @ sk_A)),
% 0.37/0.63      inference('demod', [status(thm)], ['7', '22'])).
% 0.37/0.63  thf('24', plain,
% 0.37/0.63      ((m1_subset_1 @ sk_D_2 @ 
% 0.37/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.63  thf(redefinition_k1_relset_1, axiom,
% 0.37/0.63    (![A:$i,B:$i,C:$i]:
% 0.37/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.63       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.37/0.63  thf('25', plain,
% 0.37/0.63      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.37/0.63         (((k1_relset_1 @ X35 @ X36 @ X34) = (k1_relat_1 @ X34))
% 0.37/0.63          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.37/0.63      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.37/0.63  thf('26', plain,
% 0.37/0.63      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_2)
% 0.37/0.63         = (k1_relat_1 @ sk_D_2))),
% 0.37/0.63      inference('sup-', [status(thm)], ['24', '25'])).
% 0.37/0.63  thf('27', plain, (((sk_A) = (k1_relat_1 @ sk_D_2))),
% 0.37/0.63      inference('demod', [status(thm)], ['4', '23', '26'])).
% 0.37/0.63  thf(d5_funct_1, axiom,
% 0.37/0.63    (![A:$i]:
% 0.37/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.63       ( ![B:$i]:
% 0.37/0.63         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.37/0.63           ( ![C:$i]:
% 0.37/0.63             ( ( r2_hidden @ C @ B ) <=>
% 0.37/0.63               ( ?[D:$i]:
% 0.37/0.63                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.37/0.63                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.37/0.63  thf('28', plain,
% 0.37/0.63      (![X20 : $i, X22 : $i, X24 : $i, X25 : $i]:
% 0.37/0.63         (((X22) != (k2_relat_1 @ X20))
% 0.37/0.63          | (r2_hidden @ X24 @ X22)
% 0.37/0.63          | ~ (r2_hidden @ X25 @ (k1_relat_1 @ X20))
% 0.37/0.63          | ((X24) != (k1_funct_1 @ X20 @ X25))
% 0.37/0.63          | ~ (v1_funct_1 @ X20)
% 0.37/0.63          | ~ (v1_relat_1 @ X20))),
% 0.37/0.63      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.37/0.63  thf('29', plain,
% 0.37/0.63      (![X20 : $i, X25 : $i]:
% 0.37/0.63         (~ (v1_relat_1 @ X20)
% 0.37/0.63          | ~ (v1_funct_1 @ X20)
% 0.37/0.63          | ~ (r2_hidden @ X25 @ (k1_relat_1 @ X20))
% 0.37/0.63          | (r2_hidden @ (k1_funct_1 @ X20 @ X25) @ (k2_relat_1 @ X20)))),
% 0.37/0.63      inference('simplify', [status(thm)], ['28'])).
% 0.37/0.63  thf('30', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X0 @ sk_A)
% 0.37/0.63          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2))
% 0.37/0.63          | ~ (v1_funct_1 @ sk_D_2)
% 0.37/0.63          | ~ (v1_relat_1 @ sk_D_2))),
% 0.37/0.63      inference('sup-', [status(thm)], ['27', '29'])).
% 0.37/0.63  thf('31', plain, ((v1_funct_1 @ sk_D_2)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.63  thf('32', plain,
% 0.37/0.63      ((m1_subset_1 @ sk_D_2 @ 
% 0.37/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.63  thf(cc1_relset_1, axiom,
% 0.37/0.63    (![A:$i,B:$i,C:$i]:
% 0.37/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.63       ( v1_relat_1 @ C ) ))).
% 0.37/0.63  thf('33', plain,
% 0.37/0.63      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.37/0.63         ((v1_relat_1 @ X28)
% 0.37/0.63          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.37/0.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.37/0.63  thf('34', plain, ((v1_relat_1 @ sk_D_2)),
% 0.37/0.63      inference('sup-', [status(thm)], ['32', '33'])).
% 0.37/0.63  thf('35', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X0 @ sk_A)
% 0.37/0.63          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2)))),
% 0.37/0.63      inference('demod', [status(thm)], ['30', '31', '34'])).
% 0.37/0.63  thf('36', plain,
% 0.37/0.63      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_1) @ (k2_relat_1 @ sk_D_2))),
% 0.37/0.63      inference('sup-', [status(thm)], ['1', '35'])).
% 0.37/0.63  thf('37', plain,
% 0.37/0.63      ((m1_subset_1 @ sk_D_2 @ 
% 0.37/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.63  thf(dt_k2_relset_1, axiom,
% 0.37/0.63    (![A:$i,B:$i,C:$i]:
% 0.37/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.63       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.37/0.63  thf('38', plain,
% 0.37/0.63      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.37/0.63         ((m1_subset_1 @ (k2_relset_1 @ X31 @ X32 @ X33) @ (k1_zfmisc_1 @ X32))
% 0.37/0.63          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.37/0.63      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.37/0.63  thf('39', plain,
% 0.37/0.63      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_2) @ 
% 0.37/0.63        (k1_zfmisc_1 @ (k1_tarski @ sk_B)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['37', '38'])).
% 0.37/0.63  thf('40', plain,
% 0.37/0.63      ((m1_subset_1 @ sk_D_2 @ 
% 0.37/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.63  thf(redefinition_k2_relset_1, axiom,
% 0.37/0.63    (![A:$i,B:$i,C:$i]:
% 0.37/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.63       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.37/0.63  thf('41', plain,
% 0.37/0.63      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.37/0.63         (((k2_relset_1 @ X38 @ X39 @ X37) = (k2_relat_1 @ X37))
% 0.37/0.63          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.37/0.63      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.37/0.63  thf('42', plain,
% 0.37/0.63      (((k2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_2)
% 0.37/0.63         = (k2_relat_1 @ sk_D_2))),
% 0.37/0.63      inference('sup-', [status(thm)], ['40', '41'])).
% 0.37/0.63  thf('43', plain,
% 0.37/0.63      ((m1_subset_1 @ (k2_relat_1 @ sk_D_2) @ 
% 0.37/0.63        (k1_zfmisc_1 @ (k1_tarski @ sk_B)))),
% 0.37/0.63      inference('demod', [status(thm)], ['39', '42'])).
% 0.37/0.63  thf(l3_subset_1, axiom,
% 0.37/0.63    (![A:$i,B:$i]:
% 0.37/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.37/0.63  thf('44', plain,
% 0.37/0.63      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X16 @ X17)
% 0.37/0.63          | (r2_hidden @ X16 @ X18)
% 0.37/0.63          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.37/0.63      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.37/0.63  thf('45', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         ((r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.37/0.63          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['43', '44'])).
% 0.37/0.63  thf('46', plain,
% 0.37/0.63      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_1) @ (k1_tarski @ sk_B))),
% 0.37/0.63      inference('sup-', [status(thm)], ['36', '45'])).
% 0.37/0.63  thf('47', plain,
% 0.37/0.63      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.37/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.63  thf('48', plain,
% 0.37/0.63      (![X14 : $i, X15 : $i]:
% 0.37/0.63         ((k1_enumset1 @ X14 @ X14 @ X15) = (k2_tarski @ X14 @ X15))),
% 0.37/0.63      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.37/0.63  thf('49', plain,
% 0.37/0.63      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X11 @ X10)
% 0.37/0.63          | ~ (zip_tseitin_0 @ X11 @ X7 @ X8 @ X9)
% 0.37/0.63          | ((X10) != (k1_enumset1 @ X9 @ X8 @ X7)))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.37/0.63  thf('50', plain,
% 0.37/0.63      (![X7 : $i, X8 : $i, X9 : $i, X11 : $i]:
% 0.37/0.63         (~ (zip_tseitin_0 @ X11 @ X7 @ X8 @ X9)
% 0.37/0.63          | ~ (r2_hidden @ X11 @ (k1_enumset1 @ X9 @ X8 @ X7)))),
% 0.37/0.63      inference('simplify', [status(thm)], ['49'])).
% 0.37/0.63  thf('51', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.37/0.63          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.37/0.63      inference('sup-', [status(thm)], ['48', '50'])).
% 0.37/0.63  thf('52', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.37/0.63          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.37/0.63      inference('sup-', [status(thm)], ['47', '51'])).
% 0.37/0.63  thf('53', plain,
% 0.37/0.63      (~ (zip_tseitin_0 @ (k1_funct_1 @ sk_D_2 @ sk_C_1) @ sk_B @ sk_B @ sk_B)),
% 0.37/0.63      inference('sup-', [status(thm)], ['46', '52'])).
% 0.37/0.63  thf('54', plain,
% 0.37/0.63      ((((k1_funct_1 @ sk_D_2 @ sk_C_1) = (sk_B))
% 0.37/0.63        | ((k1_funct_1 @ sk_D_2 @ sk_C_1) = (sk_B))
% 0.37/0.63        | ((k1_funct_1 @ sk_D_2 @ sk_C_1) = (sk_B)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['0', '53'])).
% 0.37/0.63  thf('55', plain, (((k1_funct_1 @ sk_D_2 @ sk_C_1) = (sk_B))),
% 0.37/0.63      inference('simplify', [status(thm)], ['54'])).
% 0.37/0.63  thf('56', plain, (((k1_funct_1 @ sk_D_2 @ sk_C_1) != (sk_B))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.63  thf('57', plain, ($false),
% 0.37/0.63      inference('simplify_reflect-', [status(thm)], ['55', '56'])).
% 0.37/0.63  
% 0.37/0.63  % SZS output end Refutation
% 0.37/0.63  
% 0.37/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
