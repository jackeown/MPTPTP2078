%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4LW8H5THmK

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:13 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 152 expanded)
%              Number of leaves         :   49 (  67 expanded)
%              Depth                    :   20
%              Number of atoms          :  805 (1340 expanded)
%              Number of equality atoms :   50 (  82 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( zip_tseitin_0 @ X4 @ X5 @ X6 @ X7 )
      | ( X4 = X5 )
      | ( X4 = X6 )
      | ( X4 = X7 ) ) ),
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
    v1_funct_2 @ sk_D_2 @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
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
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( v1_funct_2 @ X51 @ X49 @ X50 )
      | ( X49
        = ( k1_relset_1 @ X49 @ X50 @ X51 ) )
      | ~ ( zip_tseitin_2 @ X51 @ X50 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
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
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( zip_tseitin_1 @ X52 @ X53 )
      | ( zip_tseitin_2 @ X54 @ X52 @ X53 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('7',plain,
    ( ( zip_tseitin_2 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X47: $i,X48: $i] :
      ( ( zip_tseitin_1 @ X47 @ X48 )
      | ( X47 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('9',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_1 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_enumset1 @ X16 @ X16 @ X17 )
      = ( k2_tarski @ X16 @ X17 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 )
      | ( r2_hidden @ X8 @ X12 )
      | ( X12
       != ( k1_enumset1 @ X11 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('14',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X8 @ ( k1_enumset1 @ X11 @ X10 @ X9 ) )
      | ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 )
      | ~ ( v1_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ ( k1_tarski @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('20',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X4 != X3 )
      | ~ ( zip_tseitin_0 @ X4 @ X5 @ X6 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ~ ( zip_tseitin_0 @ X3 @ X5 @ X6 @ X3 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_1 @ ( k1_tarski @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    zip_tseitin_2 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['7','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( ( k1_relset_1 @ X45 @ X46 @ X44 )
        = ( k1_relat_1 @ X44 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('26',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_2 )
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
    ! [X32: $i,X34: $i,X36: $i,X37: $i] :
      ( ( X34
       != ( k2_relat_1 @ X32 ) )
      | ( r2_hidden @ X36 @ X34 )
      | ~ ( r2_hidden @ X37 @ ( k1_relat_1 @ X32 ) )
      | ( X36
       != ( k1_funct_1 @ X32 @ X37 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('29',plain,(
    ! [X32: $i,X37: $i] :
      ( ~ ( v1_relat_1 @ X32 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( r2_hidden @ X37 @ ( k1_relat_1 @ X32 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X32 @ X37 ) @ ( k2_relat_1 @ X32 ) ) ) ),
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
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('33',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( v1_relat_1 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
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
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('38',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( v5_relat_1 @ X41 @ X43 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('39',plain,(
    v5_relat_1 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('40',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v5_relat_1 @ X29 @ X30 )
      | ( r1_tarski @ ( k2_relat_1 @ X29 ) @ X30 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('43',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('44',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('46',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ( m1_subset_1 @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['36','47'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('49',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r2_hidden @ X21 @ X22 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('52',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_enumset1 @ X16 @ X16 @ X17 )
      = ( k2_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('53',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( zip_tseitin_0 @ X13 @ X9 @ X10 @ X11 )
      | ( X12
       != ( k1_enumset1 @ X11 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('54',plain,(
    ! [X9: $i,X10: $i,X11: $i,X13: $i] :
      ( ~ ( zip_tseitin_0 @ X13 @ X9 @ X10 @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k1_enumset1 @ X11 @ X10 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ~ ( zip_tseitin_0 @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) @ sk_B_1 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['50','56'])).

thf('58',plain,
    ( ( ( k1_funct_1 @ sk_D_2 @ sk_C_1 )
      = sk_B_1 )
    | ( ( k1_funct_1 @ sk_D_2 @ sk_C_1 )
      = sk_B_1 )
    | ( ( k1_funct_1 @ sk_D_2 @ sk_C_1 )
      = sk_B_1 )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','57'])).

thf('59',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( ( k1_funct_1 @ sk_D_2 @ sk_C_1 )
      = sk_B_1 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ( k1_funct_1 @ sk_D_2 @ sk_C_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('61',plain,(
    v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('63',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ sk_B_1 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ~ ( zip_tseitin_0 @ X3 @ X5 @ X6 @ X3 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('65',plain,(
    $false ),
    inference('sup-',[status(thm)],['63','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4LW8H5THmK
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:21:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.42/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.61  % Solved by: fo/fo7.sh
% 0.42/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.61  % done 156 iterations in 0.182s
% 0.42/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.61  % SZS output start Refutation
% 0.42/0.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.42/0.61  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.42/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.42/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.42/0.61  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.42/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.42/0.61  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.42/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.42/0.61  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.42/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.42/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.42/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.61  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.42/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.42/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.61  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.42/0.61  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.42/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.42/0.61  thf(d1_enumset1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.61     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.42/0.61       ( ![E:$i]:
% 0.42/0.61         ( ( r2_hidden @ E @ D ) <=>
% 0.42/0.61           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.42/0.61  thf(zf_stmt_0, axiom,
% 0.42/0.61    (![E:$i,C:$i,B:$i,A:$i]:
% 0.42/0.61     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.42/0.61       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.42/0.61  thf('0', plain,
% 0.42/0.61      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.42/0.61         ((zip_tseitin_0 @ X4 @ X5 @ X6 @ X7)
% 0.42/0.61          | ((X4) = (X5))
% 0.42/0.61          | ((X4) = (X6))
% 0.42/0.61          | ((X4) = (X7)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(t65_funct_2, conjecture,
% 0.42/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.61     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.42/0.61         ( m1_subset_1 @
% 0.42/0.61           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.42/0.61       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.42/0.61  thf(zf_stmt_1, negated_conjecture,
% 0.42/0.61    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.61        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.42/0.61            ( m1_subset_1 @
% 0.42/0.61              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.42/0.61          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.42/0.61    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.42/0.61  thf('1', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.61  thf('2', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.61  thf(d1_funct_2, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.61       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.61           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.42/0.61             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.42/0.61         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.61           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.42/0.61             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.42/0.61  thf(zf_stmt_2, axiom,
% 0.42/0.61    (![C:$i,B:$i,A:$i]:
% 0.42/0.61     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.42/0.61       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.42/0.61  thf('3', plain,
% 0.42/0.61      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.42/0.61         (~ (v1_funct_2 @ X51 @ X49 @ X50)
% 0.42/0.61          | ((X49) = (k1_relset_1 @ X49 @ X50 @ X51))
% 0.42/0.61          | ~ (zip_tseitin_2 @ X51 @ X50 @ X49))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.42/0.61  thf('4', plain,
% 0.42/0.61      ((~ (zip_tseitin_2 @ sk_D_2 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.42/0.61        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_2)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.42/0.61  thf('5', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_D_2 @ 
% 0.42/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.61  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.42/0.61  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $o).
% 0.42/0.61  thf(zf_stmt_5, axiom,
% 0.42/0.61    (![B:$i,A:$i]:
% 0.42/0.61     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.61       ( zip_tseitin_1 @ B @ A ) ))).
% 0.42/0.61  thf(zf_stmt_6, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.61       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.42/0.61         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.61           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.42/0.61             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.42/0.61  thf('6', plain,
% 0.42/0.61      (![X52 : $i, X53 : $i, X54 : $i]:
% 0.42/0.61         (~ (zip_tseitin_1 @ X52 @ X53)
% 0.42/0.61          | (zip_tseitin_2 @ X54 @ X52 @ X53)
% 0.42/0.61          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X52))))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.42/0.61  thf('7', plain,
% 0.42/0.61      (((zip_tseitin_2 @ sk_D_2 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.42/0.61        | ~ (zip_tseitin_1 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.42/0.61  thf('8', plain,
% 0.42/0.61      (![X47 : $i, X48 : $i]:
% 0.42/0.61         ((zip_tseitin_1 @ X47 @ X48) | ((X47) = (k1_xboole_0)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.42/0.61  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.42/0.61  thf('9', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.42/0.61  thf('10', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_1 @ X0 @ X1))),
% 0.42/0.61      inference('sup+', [status(thm)], ['8', '9'])).
% 0.42/0.61  thf(t69_enumset1, axiom,
% 0.42/0.61    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.42/0.61  thf('11', plain,
% 0.42/0.61      (![X15 : $i]: ((k2_tarski @ X15 @ X15) = (k1_tarski @ X15))),
% 0.42/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.42/0.61  thf(t70_enumset1, axiom,
% 0.42/0.61    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.42/0.61  thf('12', plain,
% 0.42/0.61      (![X16 : $i, X17 : $i]:
% 0.42/0.61         ((k1_enumset1 @ X16 @ X16 @ X17) = (k2_tarski @ X16 @ X17))),
% 0.42/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.42/0.61  thf(zf_stmt_7, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.42/0.61  thf(zf_stmt_8, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.61     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.42/0.61       ( ![E:$i]:
% 0.42/0.61         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.42/0.61  thf('13', plain,
% 0.42/0.61      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.42/0.61         ((zip_tseitin_0 @ X8 @ X9 @ X10 @ X11)
% 0.42/0.61          | (r2_hidden @ X8 @ X12)
% 0.42/0.61          | ((X12) != (k1_enumset1 @ X11 @ X10 @ X9)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.42/0.61  thf('14', plain,
% 0.42/0.61      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.42/0.61         ((r2_hidden @ X8 @ (k1_enumset1 @ X11 @ X10 @ X9))
% 0.42/0.61          | (zip_tseitin_0 @ X8 @ X9 @ X10 @ X11))),
% 0.42/0.61      inference('simplify', [status(thm)], ['13'])).
% 0.42/0.61  thf(d1_xboole_0, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.42/0.61  thf('15', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.42/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.42/0.61  thf('16', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.42/0.61         ((zip_tseitin_0 @ X3 @ X0 @ X1 @ X2)
% 0.42/0.61          | ~ (v1_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['14', '15'])).
% 0.42/0.61  thf('17', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.61         (~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))
% 0.42/0.61          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.42/0.61      inference('sup-', [status(thm)], ['12', '16'])).
% 0.42/0.61  thf('18', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (~ (v1_xboole_0 @ (k1_tarski @ X0))
% 0.42/0.61          | (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['11', '17'])).
% 0.42/0.61  thf('19', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.61         ((zip_tseitin_1 @ (k1_tarski @ X0) @ X2)
% 0.42/0.61          | (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['10', '18'])).
% 0.42/0.61  thf('20', plain,
% 0.42/0.61      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.42/0.61         (((X4) != (X3)) | ~ (zip_tseitin_0 @ X4 @ X5 @ X6 @ X3))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('21', plain,
% 0.42/0.61      (![X3 : $i, X5 : $i, X6 : $i]: ~ (zip_tseitin_0 @ X3 @ X5 @ X6 @ X3)),
% 0.42/0.61      inference('simplify', [status(thm)], ['20'])).
% 0.42/0.61  thf('22', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]: (zip_tseitin_1 @ (k1_tarski @ X0) @ X1)),
% 0.42/0.61      inference('sup-', [status(thm)], ['19', '21'])).
% 0.42/0.61  thf('23', plain, ((zip_tseitin_2 @ sk_D_2 @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.42/0.61      inference('demod', [status(thm)], ['7', '22'])).
% 0.42/0.61  thf('24', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_D_2 @ 
% 0.42/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.61  thf(redefinition_k1_relset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.42/0.61  thf('25', plain,
% 0.42/0.61      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.42/0.61         (((k1_relset_1 @ X45 @ X46 @ X44) = (k1_relat_1 @ X44))
% 0.42/0.61          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46))))),
% 0.42/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.42/0.61  thf('26', plain,
% 0.42/0.61      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_2)
% 0.42/0.61         = (k1_relat_1 @ sk_D_2))),
% 0.42/0.61      inference('sup-', [status(thm)], ['24', '25'])).
% 0.42/0.61  thf('27', plain, (((sk_A) = (k1_relat_1 @ sk_D_2))),
% 0.42/0.61      inference('demod', [status(thm)], ['4', '23', '26'])).
% 0.42/0.61  thf(d5_funct_1, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.42/0.61       ( ![B:$i]:
% 0.42/0.61         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.42/0.61           ( ![C:$i]:
% 0.42/0.61             ( ( r2_hidden @ C @ B ) <=>
% 0.42/0.61               ( ?[D:$i]:
% 0.42/0.61                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.42/0.61                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.42/0.61  thf('28', plain,
% 0.42/0.61      (![X32 : $i, X34 : $i, X36 : $i, X37 : $i]:
% 0.42/0.61         (((X34) != (k2_relat_1 @ X32))
% 0.42/0.61          | (r2_hidden @ X36 @ X34)
% 0.42/0.61          | ~ (r2_hidden @ X37 @ (k1_relat_1 @ X32))
% 0.42/0.61          | ((X36) != (k1_funct_1 @ X32 @ X37))
% 0.42/0.61          | ~ (v1_funct_1 @ X32)
% 0.42/0.61          | ~ (v1_relat_1 @ X32))),
% 0.42/0.61      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.42/0.61  thf('29', plain,
% 0.42/0.61      (![X32 : $i, X37 : $i]:
% 0.42/0.61         (~ (v1_relat_1 @ X32)
% 0.42/0.61          | ~ (v1_funct_1 @ X32)
% 0.42/0.61          | ~ (r2_hidden @ X37 @ (k1_relat_1 @ X32))
% 0.42/0.61          | (r2_hidden @ (k1_funct_1 @ X32 @ X37) @ (k2_relat_1 @ X32)))),
% 0.42/0.61      inference('simplify', [status(thm)], ['28'])).
% 0.42/0.61  thf('30', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X0 @ sk_A)
% 0.42/0.61          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2))
% 0.42/0.61          | ~ (v1_funct_1 @ sk_D_2)
% 0.42/0.61          | ~ (v1_relat_1 @ sk_D_2))),
% 0.42/0.61      inference('sup-', [status(thm)], ['27', '29'])).
% 0.42/0.61  thf('31', plain, ((v1_funct_1 @ sk_D_2)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.61  thf('32', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_D_2 @ 
% 0.42/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.61  thf(cc1_relset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.61       ( v1_relat_1 @ C ) ))).
% 0.42/0.61  thf('33', plain,
% 0.42/0.61      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.42/0.61         ((v1_relat_1 @ X38)
% 0.42/0.61          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 0.42/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.42/0.61  thf('34', plain, ((v1_relat_1 @ sk_D_2)),
% 0.42/0.61      inference('sup-', [status(thm)], ['32', '33'])).
% 0.42/0.61  thf('35', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X0 @ sk_A)
% 0.42/0.61          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2)))),
% 0.42/0.61      inference('demod', [status(thm)], ['30', '31', '34'])).
% 0.42/0.61  thf('36', plain,
% 0.42/0.61      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_1) @ (k2_relat_1 @ sk_D_2))),
% 0.42/0.61      inference('sup-', [status(thm)], ['1', '35'])).
% 0.42/0.61  thf('37', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_D_2 @ 
% 0.42/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.61  thf(cc2_relset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.61       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.42/0.61  thf('38', plain,
% 0.42/0.61      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.42/0.61         ((v5_relat_1 @ X41 @ X43)
% 0.42/0.61          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43))))),
% 0.42/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.42/0.61  thf('39', plain, ((v5_relat_1 @ sk_D_2 @ (k1_tarski @ sk_B_1))),
% 0.42/0.61      inference('sup-', [status(thm)], ['37', '38'])).
% 0.42/0.61  thf(d19_relat_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( v1_relat_1 @ B ) =>
% 0.42/0.61       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.42/0.61  thf('40', plain,
% 0.42/0.61      (![X29 : $i, X30 : $i]:
% 0.42/0.61         (~ (v5_relat_1 @ X29 @ X30)
% 0.42/0.61          | (r1_tarski @ (k2_relat_1 @ X29) @ X30)
% 0.42/0.61          | ~ (v1_relat_1 @ X29))),
% 0.42/0.61      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.42/0.61  thf('41', plain,
% 0.42/0.61      ((~ (v1_relat_1 @ sk_D_2)
% 0.42/0.61        | (r1_tarski @ (k2_relat_1 @ sk_D_2) @ (k1_tarski @ sk_B_1)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['39', '40'])).
% 0.42/0.61  thf('42', plain, ((v1_relat_1 @ sk_D_2)),
% 0.42/0.61      inference('sup-', [status(thm)], ['32', '33'])).
% 0.42/0.61  thf('43', plain,
% 0.42/0.61      ((r1_tarski @ (k2_relat_1 @ sk_D_2) @ (k1_tarski @ sk_B_1))),
% 0.42/0.61      inference('demod', [status(thm)], ['41', '42'])).
% 0.42/0.61  thf(t3_subset, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.42/0.61  thf('44', plain,
% 0.42/0.61      (![X23 : $i, X25 : $i]:
% 0.42/0.61         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 0.42/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.61  thf('45', plain,
% 0.42/0.61      ((m1_subset_1 @ (k2_relat_1 @ sk_D_2) @ 
% 0.42/0.61        (k1_zfmisc_1 @ (k1_tarski @ sk_B_1)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['43', '44'])).
% 0.42/0.61  thf(t4_subset, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.42/0.61       ( m1_subset_1 @ A @ C ) ))).
% 0.42/0.61  thf('46', plain,
% 0.42/0.61      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X26 @ X27)
% 0.42/0.61          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 0.42/0.61          | (m1_subset_1 @ X26 @ X28))),
% 0.42/0.61      inference('cnf', [status(esa)], [t4_subset])).
% 0.42/0.61  thf('47', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((m1_subset_1 @ X0 @ (k1_tarski @ sk_B_1))
% 0.42/0.61          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['45', '46'])).
% 0.42/0.61  thf('48', plain,
% 0.42/0.61      ((m1_subset_1 @ (k1_funct_1 @ sk_D_2 @ sk_C_1) @ (k1_tarski @ sk_B_1))),
% 0.42/0.61      inference('sup-', [status(thm)], ['36', '47'])).
% 0.42/0.61  thf(t2_subset, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ A @ B ) =>
% 0.42/0.61       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.42/0.61  thf('49', plain,
% 0.42/0.61      (![X21 : $i, X22 : $i]:
% 0.42/0.61         ((r2_hidden @ X21 @ X22)
% 0.42/0.61          | (v1_xboole_0 @ X22)
% 0.42/0.61          | ~ (m1_subset_1 @ X21 @ X22))),
% 0.42/0.61      inference('cnf', [status(esa)], [t2_subset])).
% 0.42/0.61  thf('50', plain,
% 0.42/0.61      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.42/0.61        | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_1) @ (k1_tarski @ sk_B_1)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['48', '49'])).
% 0.42/0.61  thf('51', plain,
% 0.42/0.61      (![X15 : $i]: ((k2_tarski @ X15 @ X15) = (k1_tarski @ X15))),
% 0.42/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.42/0.61  thf('52', plain,
% 0.42/0.61      (![X16 : $i, X17 : $i]:
% 0.42/0.61         ((k1_enumset1 @ X16 @ X16 @ X17) = (k2_tarski @ X16 @ X17))),
% 0.42/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.42/0.61  thf('53', plain,
% 0.42/0.61      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X13 @ X12)
% 0.42/0.61          | ~ (zip_tseitin_0 @ X13 @ X9 @ X10 @ X11)
% 0.42/0.61          | ((X12) != (k1_enumset1 @ X11 @ X10 @ X9)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.42/0.61  thf('54', plain,
% 0.42/0.61      (![X9 : $i, X10 : $i, X11 : $i, X13 : $i]:
% 0.42/0.61         (~ (zip_tseitin_0 @ X13 @ X9 @ X10 @ X11)
% 0.42/0.61          | ~ (r2_hidden @ X13 @ (k1_enumset1 @ X11 @ X10 @ X9)))),
% 0.42/0.61      inference('simplify', [status(thm)], ['53'])).
% 0.42/0.61  thf('55', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.42/0.61          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.42/0.61      inference('sup-', [status(thm)], ['52', '54'])).
% 0.42/0.61  thf('56', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.42/0.61          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['51', '55'])).
% 0.42/0.61  thf('57', plain,
% 0.42/0.61      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.42/0.61        | ~ (zip_tseitin_0 @ (k1_funct_1 @ sk_D_2 @ sk_C_1) @ sk_B_1 @ 
% 0.42/0.61             sk_B_1 @ sk_B_1))),
% 0.42/0.61      inference('sup-', [status(thm)], ['50', '56'])).
% 0.42/0.61  thf('58', plain,
% 0.42/0.61      ((((k1_funct_1 @ sk_D_2 @ sk_C_1) = (sk_B_1))
% 0.42/0.61        | ((k1_funct_1 @ sk_D_2 @ sk_C_1) = (sk_B_1))
% 0.42/0.61        | ((k1_funct_1 @ sk_D_2 @ sk_C_1) = (sk_B_1))
% 0.42/0.61        | (v1_xboole_0 @ (k1_tarski @ sk_B_1)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['0', '57'])).
% 0.42/0.61  thf('59', plain,
% 0.42/0.61      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.42/0.61        | ((k1_funct_1 @ sk_D_2 @ sk_C_1) = (sk_B_1)))),
% 0.42/0.61      inference('simplify', [status(thm)], ['58'])).
% 0.42/0.61  thf('60', plain, (((k1_funct_1 @ sk_D_2 @ sk_C_1) != (sk_B_1))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.61  thf('61', plain, ((v1_xboole_0 @ (k1_tarski @ sk_B_1))),
% 0.42/0.61      inference('simplify_reflect-', [status(thm)], ['59', '60'])).
% 0.42/0.61  thf('62', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (~ (v1_xboole_0 @ (k1_tarski @ X0))
% 0.42/0.61          | (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['11', '17'])).
% 0.42/0.62  thf('63', plain,
% 0.42/0.62      (![X0 : $i]: (zip_tseitin_0 @ X0 @ sk_B_1 @ sk_B_1 @ sk_B_1)),
% 0.42/0.62      inference('sup-', [status(thm)], ['61', '62'])).
% 0.42/0.62  thf('64', plain,
% 0.42/0.62      (![X3 : $i, X5 : $i, X6 : $i]: ~ (zip_tseitin_0 @ X3 @ X5 @ X6 @ X3)),
% 0.42/0.62      inference('simplify', [status(thm)], ['20'])).
% 0.42/0.62  thf('65', plain, ($false), inference('sup-', [status(thm)], ['63', '64'])).
% 0.42/0.62  
% 0.42/0.62  % SZS output end Refutation
% 0.42/0.62  
% 0.42/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
