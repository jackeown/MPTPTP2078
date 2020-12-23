%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tOpIUiAGML

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:33 EST 2020

% Result     : Theorem 4.35s
% Output     : Refutation 4.35s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 432 expanded)
%              Number of leaves         :   35 ( 146 expanded)
%              Depth                    :   21
%              Number of atoms          :  888 (5675 expanded)
%              Number of equality atoms :   63 ( 234 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t18_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ! [E: $i] :
                ( ( r2_hidden @ E @ A )
               => ( ( k1_funct_1 @ C @ E )
                  = ( k1_funct_1 @ D @ E ) ) )
           => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ! [E: $i] :
                  ( ( r2_hidden @ E @ A )
                 => ( ( k1_funct_1 @ C @ E )
                    = ( k1_funct_1 @ D @ E ) ) )
             => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
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

thf('2',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ( X38
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('6',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('12',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('15',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X26 ) ) )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('16',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('22',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('23',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( r2_relset_1 @ X32 @ X33 @ X34 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X3 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','26'])).

thf('28',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ~ ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X26 ) ) )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['30','35'])).

thf('37',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['10','36'])).

thf('38',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','37'])).

thf('39',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ( X38
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('41',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('44',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('48',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['30','35'])).

thf('50',plain,(
    zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['45','50'])).

thf(t9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) )
           => ( A = B ) ) ) ) )).

thf('52',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( X19 = X18 )
      | ( r2_hidden @ ( sk_C_1 @ X18 @ X19 ) @ ( k1_relat_1 @ X19 ) )
      | ( ( k1_relat_1 @ X19 )
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('55',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('56',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','56','57','58'])).

thf('60',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['38','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('63',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['60','63','64'])).

thf('66',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X44: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X44 )
        = ( k1_funct_1 @ sk_D @ X44 ) )
      | ~ ( r2_hidden @ X44 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( sk_C_2 = sk_D )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ),
    inference(condensation,[status(thm)],['68'])).

thf('70',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( X19 = X18 )
      | ( ( k1_funct_1 @ X19 @ ( sk_C_1 @ X18 @ X19 ) )
       != ( k1_funct_1 @ X18 @ ( sk_C_1 @ X18 @ X19 ) ) )
      | ( ( k1_relat_1 @ X19 )
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('71',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['54','55'])).

thf('73',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('75',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','37'])).

thf('76',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['61','62'])).

thf('78',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['71','72','73','74','75','76','77'])).

thf('79',plain,(
    sk_C_2 = sk_D ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['23'])).

thf('82',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['0','79','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tOpIUiAGML
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:09:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.35/4.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.35/4.55  % Solved by: fo/fo7.sh
% 4.35/4.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.35/4.55  % done 3523 iterations in 4.098s
% 4.35/4.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.35/4.55  % SZS output start Refutation
% 4.35/4.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.35/4.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 4.35/4.55  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 4.35/4.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 4.35/4.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.35/4.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.35/4.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.35/4.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.35/4.55  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 4.35/4.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.35/4.55  thf(sk_C_2_type, type, sk_C_2: $i).
% 4.35/4.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.35/4.55  thf(sk_D_type, type, sk_D: $i).
% 4.35/4.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.35/4.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 4.35/4.55  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 4.35/4.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 4.35/4.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.35/4.55  thf(sk_A_type, type, sk_A: $i).
% 4.35/4.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.35/4.55  thf(t18_funct_2, conjecture,
% 4.35/4.55    (![A:$i,B:$i,C:$i]:
% 4.35/4.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.35/4.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.35/4.55       ( ![D:$i]:
% 4.35/4.55         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.35/4.55             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.35/4.55           ( ( ![E:$i]:
% 4.35/4.55               ( ( r2_hidden @ E @ A ) =>
% 4.35/4.55                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 4.35/4.55             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 4.35/4.55  thf(zf_stmt_0, negated_conjecture,
% 4.35/4.55    (~( ![A:$i,B:$i,C:$i]:
% 4.35/4.55        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.35/4.55            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.35/4.55          ( ![D:$i]:
% 4.35/4.55            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.35/4.55                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.35/4.55              ( ( ![E:$i]:
% 4.35/4.55                  ( ( r2_hidden @ E @ A ) =>
% 4.35/4.55                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 4.35/4.55                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 4.35/4.55    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 4.35/4.55  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 4.35/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.55  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 4.35/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.55  thf(d1_funct_2, axiom,
% 4.35/4.55    (![A:$i,B:$i,C:$i]:
% 4.35/4.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.35/4.55       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.35/4.55           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 4.35/4.55             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 4.35/4.55         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.35/4.55           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 4.35/4.55             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 4.35/4.55  thf(zf_stmt_1, axiom,
% 4.35/4.55    (![C:$i,B:$i,A:$i]:
% 4.35/4.55     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 4.35/4.55       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.35/4.55  thf('2', plain,
% 4.35/4.55      (![X38 : $i, X39 : $i, X40 : $i]:
% 4.35/4.55         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 4.35/4.55          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 4.35/4.55          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 4.35/4.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.35/4.55  thf('3', plain,
% 4.35/4.55      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 4.35/4.55        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 4.35/4.55      inference('sup-', [status(thm)], ['1', '2'])).
% 4.35/4.55  thf('4', plain,
% 4.35/4.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.35/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.55  thf(redefinition_k1_relset_1, axiom,
% 4.35/4.55    (![A:$i,B:$i,C:$i]:
% 4.35/4.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.35/4.55       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 4.35/4.55  thf('5', plain,
% 4.35/4.55      (![X29 : $i, X30 : $i, X31 : $i]:
% 4.35/4.55         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 4.35/4.55          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 4.35/4.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.35/4.55  thf('6', plain,
% 4.35/4.55      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 4.35/4.55      inference('sup-', [status(thm)], ['4', '5'])).
% 4.35/4.55  thf('7', plain,
% 4.35/4.55      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 4.35/4.55        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.35/4.55      inference('demod', [status(thm)], ['3', '6'])).
% 4.35/4.55  thf('8', plain,
% 4.35/4.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.35/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.55  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 4.35/4.55  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 4.35/4.55  thf(zf_stmt_4, axiom,
% 4.35/4.55    (![B:$i,A:$i]:
% 4.35/4.55     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.35/4.55       ( zip_tseitin_0 @ B @ A ) ))).
% 4.35/4.55  thf(zf_stmt_5, axiom,
% 4.35/4.55    (![A:$i,B:$i,C:$i]:
% 4.35/4.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.35/4.55       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 4.35/4.55         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.35/4.55           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 4.35/4.55             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 4.35/4.55  thf('9', plain,
% 4.35/4.55      (![X41 : $i, X42 : $i, X43 : $i]:
% 4.35/4.55         (~ (zip_tseitin_0 @ X41 @ X42)
% 4.35/4.55          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 4.35/4.55          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 4.35/4.55      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.35/4.55  thf('10', plain,
% 4.35/4.55      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 4.35/4.55        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 4.35/4.55      inference('sup-', [status(thm)], ['8', '9'])).
% 4.35/4.55  thf('11', plain,
% 4.35/4.55      (![X36 : $i, X37 : $i]:
% 4.35/4.55         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 4.35/4.55      inference('cnf', [status(esa)], [zf_stmt_4])).
% 4.35/4.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 4.35/4.55  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.35/4.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.35/4.55  thf('13', plain,
% 4.35/4.55      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 4.35/4.55      inference('sup+', [status(thm)], ['11', '12'])).
% 4.35/4.55  thf('14', plain,
% 4.35/4.55      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.35/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.55  thf(cc4_relset_1, axiom,
% 4.35/4.55    (![A:$i,B:$i]:
% 4.35/4.55     ( ( v1_xboole_0 @ A ) =>
% 4.35/4.55       ( ![C:$i]:
% 4.35/4.55         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 4.35/4.55           ( v1_xboole_0 @ C ) ) ) ))).
% 4.35/4.55  thf('15', plain,
% 4.35/4.55      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.35/4.55         (~ (v1_xboole_0 @ X26)
% 4.35/4.55          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X26)))
% 4.35/4.55          | (v1_xboole_0 @ X27))),
% 4.35/4.55      inference('cnf', [status(esa)], [cc4_relset_1])).
% 4.35/4.55  thf('16', plain, (((v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_B_1))),
% 4.35/4.55      inference('sup-', [status(thm)], ['14', '15'])).
% 4.35/4.55  thf('17', plain,
% 4.35/4.55      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_C_2))),
% 4.35/4.55      inference('sup-', [status(thm)], ['13', '16'])).
% 4.35/4.55  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.35/4.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.35/4.55  thf(t8_boole, axiom,
% 4.35/4.55    (![A:$i,B:$i]:
% 4.35/4.55     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 4.35/4.55  thf('19', plain,
% 4.35/4.55      (![X4 : $i, X5 : $i]:
% 4.35/4.55         (~ (v1_xboole_0 @ X4) | ~ (v1_xboole_0 @ X5) | ((X4) = (X5)))),
% 4.35/4.55      inference('cnf', [status(esa)], [t8_boole])).
% 4.35/4.55  thf('20', plain,
% 4.35/4.55      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 4.35/4.55      inference('sup-', [status(thm)], ['18', '19'])).
% 4.35/4.55  thf('21', plain,
% 4.35/4.55      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 4.35/4.55      inference('sup-', [status(thm)], ['18', '19'])).
% 4.35/4.55  thf(t4_subset_1, axiom,
% 4.35/4.55    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 4.35/4.55  thf('22', plain,
% 4.35/4.55      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 4.35/4.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.35/4.55  thf(reflexivity_r2_relset_1, axiom,
% 4.35/4.55    (![A:$i,B:$i,C:$i,D:$i]:
% 4.35/4.55     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.35/4.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.35/4.55       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 4.35/4.55  thf('23', plain,
% 4.35/4.55      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 4.35/4.55         ((r2_relset_1 @ X32 @ X33 @ X34 @ X34)
% 4.35/4.55          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 4.35/4.55          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 4.35/4.55      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 4.35/4.55  thf('24', plain,
% 4.35/4.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.35/4.55         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 4.35/4.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 4.35/4.55      inference('condensation', [status(thm)], ['23'])).
% 4.35/4.55  thf('25', plain,
% 4.35/4.55      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 4.35/4.55      inference('sup-', [status(thm)], ['22', '24'])).
% 4.35/4.55  thf('26', plain,
% 4.35/4.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.35/4.55         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 4.35/4.55      inference('sup+', [status(thm)], ['21', '25'])).
% 4.35/4.55  thf('27', plain,
% 4.35/4.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.35/4.55         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 4.35/4.55          | ~ (v1_xboole_0 @ X0)
% 4.35/4.55          | ~ (v1_xboole_0 @ X1))),
% 4.35/4.55      inference('sup+', [status(thm)], ['20', '26'])).
% 4.35/4.55  thf('28', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 4.35/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.55  thf('29', plain, ((~ (v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_D))),
% 4.35/4.55      inference('sup-', [status(thm)], ['27', '28'])).
% 4.35/4.55  thf('30', plain,
% 4.35/4.55      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | ~ (v1_xboole_0 @ sk_D))),
% 4.35/4.55      inference('sup-', [status(thm)], ['17', '29'])).
% 4.35/4.55  thf('31', plain,
% 4.35/4.55      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 4.35/4.55      inference('sup+', [status(thm)], ['11', '12'])).
% 4.35/4.55  thf('32', plain,
% 4.35/4.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.35/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.55  thf('33', plain,
% 4.35/4.55      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.35/4.55         (~ (v1_xboole_0 @ X26)
% 4.35/4.55          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X26)))
% 4.35/4.55          | (v1_xboole_0 @ X27))),
% 4.35/4.55      inference('cnf', [status(esa)], [cc4_relset_1])).
% 4.35/4.55  thf('34', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_B_1))),
% 4.35/4.55      inference('sup-', [status(thm)], ['32', '33'])).
% 4.35/4.55  thf('35', plain,
% 4.35/4.55      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_D))),
% 4.35/4.55      inference('sup-', [status(thm)], ['31', '34'])).
% 4.35/4.55  thf('36', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 4.35/4.55      inference('clc', [status(thm)], ['30', '35'])).
% 4.35/4.55  thf('37', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 4.35/4.55      inference('demod', [status(thm)], ['10', '36'])).
% 4.35/4.55  thf('38', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 4.35/4.55      inference('demod', [status(thm)], ['7', '37'])).
% 4.35/4.55  thf('39', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 4.35/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.55  thf('40', plain,
% 4.35/4.55      (![X38 : $i, X39 : $i, X40 : $i]:
% 4.35/4.55         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 4.35/4.55          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 4.35/4.55          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 4.35/4.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.35/4.55  thf('41', plain,
% 4.35/4.55      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 4.35/4.55        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 4.35/4.55      inference('sup-', [status(thm)], ['39', '40'])).
% 4.35/4.55  thf('42', plain,
% 4.35/4.55      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.35/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.55  thf('43', plain,
% 4.35/4.55      (![X29 : $i, X30 : $i, X31 : $i]:
% 4.35/4.55         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 4.35/4.55          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 4.35/4.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.35/4.55  thf('44', plain,
% 4.35/4.55      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 4.35/4.55      inference('sup-', [status(thm)], ['42', '43'])).
% 4.35/4.55  thf('45', plain,
% 4.35/4.55      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 4.35/4.55        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 4.35/4.55      inference('demod', [status(thm)], ['41', '44'])).
% 4.35/4.55  thf('46', plain,
% 4.35/4.55      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.35/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.55  thf('47', plain,
% 4.35/4.55      (![X41 : $i, X42 : $i, X43 : $i]:
% 4.35/4.55         (~ (zip_tseitin_0 @ X41 @ X42)
% 4.35/4.55          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 4.35/4.55          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 4.35/4.55      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.35/4.55  thf('48', plain,
% 4.35/4.55      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 4.35/4.55        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 4.35/4.55      inference('sup-', [status(thm)], ['46', '47'])).
% 4.35/4.55  thf('49', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 4.35/4.55      inference('clc', [status(thm)], ['30', '35'])).
% 4.35/4.55  thf('50', plain, ((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)),
% 4.35/4.55      inference('demod', [status(thm)], ['48', '49'])).
% 4.35/4.55  thf('51', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 4.35/4.55      inference('demod', [status(thm)], ['45', '50'])).
% 4.35/4.55  thf(t9_funct_1, axiom,
% 4.35/4.55    (![A:$i]:
% 4.35/4.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.35/4.55       ( ![B:$i]:
% 4.35/4.55         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.35/4.55           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 4.35/4.55               ( ![C:$i]:
% 4.35/4.55                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 4.35/4.55                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 4.35/4.55             ( ( A ) = ( B ) ) ) ) ) ))).
% 4.35/4.55  thf('52', plain,
% 4.35/4.55      (![X18 : $i, X19 : $i]:
% 4.35/4.55         (~ (v1_relat_1 @ X18)
% 4.35/4.55          | ~ (v1_funct_1 @ X18)
% 4.35/4.55          | ((X19) = (X18))
% 4.35/4.55          | (r2_hidden @ (sk_C_1 @ X18 @ X19) @ (k1_relat_1 @ X19))
% 4.35/4.55          | ((k1_relat_1 @ X19) != (k1_relat_1 @ X18))
% 4.35/4.55          | ~ (v1_funct_1 @ X19)
% 4.35/4.55          | ~ (v1_relat_1 @ X19))),
% 4.35/4.55      inference('cnf', [status(esa)], [t9_funct_1])).
% 4.35/4.55  thf('53', plain,
% 4.35/4.55      (![X0 : $i]:
% 4.35/4.55         (((sk_A) != (k1_relat_1 @ X0))
% 4.35/4.55          | ~ (v1_relat_1 @ sk_C_2)
% 4.35/4.55          | ~ (v1_funct_1 @ sk_C_2)
% 4.35/4.55          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 4.35/4.55          | ((sk_C_2) = (X0))
% 4.35/4.55          | ~ (v1_funct_1 @ X0)
% 4.35/4.55          | ~ (v1_relat_1 @ X0))),
% 4.35/4.55      inference('sup-', [status(thm)], ['51', '52'])).
% 4.35/4.55  thf('54', plain,
% 4.35/4.55      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.35/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.55  thf(cc1_relset_1, axiom,
% 4.35/4.55    (![A:$i,B:$i,C:$i]:
% 4.35/4.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.35/4.55       ( v1_relat_1 @ C ) ))).
% 4.35/4.55  thf('55', plain,
% 4.35/4.55      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.35/4.55         ((v1_relat_1 @ X20)
% 4.35/4.55          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 4.35/4.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.35/4.55  thf('56', plain, ((v1_relat_1 @ sk_C_2)),
% 4.35/4.55      inference('sup-', [status(thm)], ['54', '55'])).
% 4.35/4.55  thf('57', plain, ((v1_funct_1 @ sk_C_2)),
% 4.35/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.55  thf('58', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 4.35/4.55      inference('demod', [status(thm)], ['45', '50'])).
% 4.35/4.55  thf('59', plain,
% 4.35/4.55      (![X0 : $i]:
% 4.35/4.55         (((sk_A) != (k1_relat_1 @ X0))
% 4.35/4.55          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A)
% 4.35/4.55          | ((sk_C_2) = (X0))
% 4.35/4.55          | ~ (v1_funct_1 @ X0)
% 4.35/4.55          | ~ (v1_relat_1 @ X0))),
% 4.35/4.55      inference('demod', [status(thm)], ['53', '56', '57', '58'])).
% 4.35/4.55  thf('60', plain,
% 4.35/4.55      ((((sk_A) != (sk_A))
% 4.35/4.55        | ~ (v1_relat_1 @ sk_D)
% 4.35/4.55        | ~ (v1_funct_1 @ sk_D)
% 4.35/4.55        | ((sk_C_2) = (sk_D))
% 4.35/4.55        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 4.35/4.55      inference('sup-', [status(thm)], ['38', '59'])).
% 4.35/4.55  thf('61', plain,
% 4.35/4.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.35/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.55  thf('62', plain,
% 4.35/4.55      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.35/4.55         ((v1_relat_1 @ X20)
% 4.35/4.55          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 4.35/4.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.35/4.55  thf('63', plain, ((v1_relat_1 @ sk_D)),
% 4.35/4.55      inference('sup-', [status(thm)], ['61', '62'])).
% 4.35/4.55  thf('64', plain, ((v1_funct_1 @ sk_D)),
% 4.35/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.55  thf('65', plain,
% 4.35/4.55      ((((sk_A) != (sk_A))
% 4.35/4.55        | ((sk_C_2) = (sk_D))
% 4.35/4.55        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 4.35/4.55      inference('demod', [status(thm)], ['60', '63', '64'])).
% 4.35/4.55  thf('66', plain,
% 4.35/4.55      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A) | ((sk_C_2) = (sk_D)))),
% 4.35/4.55      inference('simplify', [status(thm)], ['65'])).
% 4.35/4.55  thf('67', plain,
% 4.35/4.55      (![X44 : $i]:
% 4.35/4.55         (((k1_funct_1 @ sk_C_2 @ X44) = (k1_funct_1 @ sk_D @ X44))
% 4.35/4.55          | ~ (r2_hidden @ X44 @ sk_A))),
% 4.35/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.55  thf('68', plain,
% 4.35/4.55      ((((sk_C_2) = (sk_D))
% 4.35/4.55        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 4.35/4.55            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 4.35/4.55      inference('sup-', [status(thm)], ['66', '67'])).
% 4.35/4.55  thf('69', plain,
% 4.35/4.55      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 4.35/4.55         = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))),
% 4.35/4.55      inference('condensation', [status(thm)], ['68'])).
% 4.35/4.55  thf('70', plain,
% 4.35/4.55      (![X18 : $i, X19 : $i]:
% 4.35/4.55         (~ (v1_relat_1 @ X18)
% 4.35/4.55          | ~ (v1_funct_1 @ X18)
% 4.35/4.55          | ((X19) = (X18))
% 4.35/4.55          | ((k1_funct_1 @ X19 @ (sk_C_1 @ X18 @ X19))
% 4.35/4.55              != (k1_funct_1 @ X18 @ (sk_C_1 @ X18 @ X19)))
% 4.35/4.55          | ((k1_relat_1 @ X19) != (k1_relat_1 @ X18))
% 4.35/4.55          | ~ (v1_funct_1 @ X19)
% 4.35/4.55          | ~ (v1_relat_1 @ X19))),
% 4.35/4.55      inference('cnf', [status(esa)], [t9_funct_1])).
% 4.35/4.55  thf('71', plain,
% 4.35/4.55      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 4.35/4.55          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 4.35/4.55        | ~ (v1_relat_1 @ sk_C_2)
% 4.35/4.55        | ~ (v1_funct_1 @ sk_C_2)
% 4.35/4.55        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 4.35/4.55        | ((sk_C_2) = (sk_D))
% 4.35/4.55        | ~ (v1_funct_1 @ sk_D)
% 4.35/4.55        | ~ (v1_relat_1 @ sk_D))),
% 4.35/4.55      inference('sup-', [status(thm)], ['69', '70'])).
% 4.35/4.55  thf('72', plain, ((v1_relat_1 @ sk_C_2)),
% 4.35/4.55      inference('sup-', [status(thm)], ['54', '55'])).
% 4.35/4.55  thf('73', plain, ((v1_funct_1 @ sk_C_2)),
% 4.35/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.55  thf('74', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 4.35/4.55      inference('demod', [status(thm)], ['45', '50'])).
% 4.35/4.55  thf('75', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 4.35/4.55      inference('demod', [status(thm)], ['7', '37'])).
% 4.35/4.55  thf('76', plain, ((v1_funct_1 @ sk_D)),
% 4.35/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.55  thf('77', plain, ((v1_relat_1 @ sk_D)),
% 4.35/4.55      inference('sup-', [status(thm)], ['61', '62'])).
% 4.35/4.55  thf('78', plain,
% 4.35/4.55      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 4.35/4.55          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 4.35/4.55        | ((sk_A) != (sk_A))
% 4.35/4.55        | ((sk_C_2) = (sk_D)))),
% 4.35/4.55      inference('demod', [status(thm)],
% 4.35/4.55                ['71', '72', '73', '74', '75', '76', '77'])).
% 4.35/4.55  thf('79', plain, (((sk_C_2) = (sk_D))),
% 4.35/4.55      inference('simplify', [status(thm)], ['78'])).
% 4.35/4.55  thf('80', plain,
% 4.35/4.55      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.35/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.55  thf('81', plain,
% 4.35/4.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.35/4.55         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 4.35/4.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 4.35/4.55      inference('condensation', [status(thm)], ['23'])).
% 4.35/4.55  thf('82', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2)),
% 4.35/4.55      inference('sup-', [status(thm)], ['80', '81'])).
% 4.35/4.55  thf('83', plain, ($false),
% 4.35/4.55      inference('demod', [status(thm)], ['0', '79', '82'])).
% 4.35/4.55  
% 4.35/4.55  % SZS output end Refutation
% 4.35/4.55  
% 4.42/4.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
