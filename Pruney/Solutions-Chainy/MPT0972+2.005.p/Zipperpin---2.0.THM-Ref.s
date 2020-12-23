%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uZozI9gcDB

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:33 EST 2020

% Result     : Theorem 3.82s
% Output     : Refutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 432 expanded)
%              Number of leaves         :   35 ( 146 expanded)
%              Depth                    :   21
%              Number of atoms          :  888 (5675 expanded)
%              Number of equality atoms :   63 ( 234 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

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
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ( X36
        = ( k1_relset_1 @ X36 @ X37 @ X38 ) )
      | ~ ( zip_tseitin_1 @ X38 @ X37 @ X36 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
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
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( zip_tseitin_0 @ X39 @ X40 )
      | ( zip_tseitin_1 @ X41 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 )
      | ( X34 = k1_xboole_0 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X24 ) ) )
      | ( v1_xboole_0 @ X25 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( r2_relset_1 @ X30 @ X31 @ X32 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X24 ) ) )
      | ( v1_xboole_0 @ X25 ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ( X36
        = ( k1_relset_1 @ X36 @ X37 @ X38 ) )
      | ~ ( zip_tseitin_1 @ X38 @ X37 @ X36 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
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
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( zip_tseitin_0 @ X39 @ X40 )
      | ( zip_tseitin_1 @ X41 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( X17 = X16 )
      | ( r2_hidden @ ( sk_C_1 @ X16 @ X17 ) @ ( k1_relat_1 @ X17 ) )
      | ( ( k1_relat_1 @ X17 )
       != ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X42: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X42 )
        = ( k1_funct_1 @ sk_D @ X42 ) )
      | ~ ( r2_hidden @ X42 @ sk_A ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( X17 = X16 )
      | ( ( k1_funct_1 @ X17 @ ( sk_C_1 @ X16 @ X17 ) )
       != ( k1_funct_1 @ X16 @ ( sk_C_1 @ X16 @ X17 ) ) )
      | ( ( k1_relat_1 @ X17 )
       != ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uZozI9gcDB
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:03:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.82/4.03  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.82/4.03  % Solved by: fo/fo7.sh
% 3.82/4.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.82/4.03  % done 3295 iterations in 3.572s
% 3.82/4.03  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.82/4.03  % SZS output start Refutation
% 3.82/4.03  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.82/4.03  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.82/4.03  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.82/4.03  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.82/4.03  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.82/4.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.82/4.03  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 3.82/4.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.82/4.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.82/4.03  thf(sk_C_2_type, type, sk_C_2: $i).
% 3.82/4.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.82/4.03  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.82/4.03  thf(sk_D_type, type, sk_D: $i).
% 3.82/4.03  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.82/4.03  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.82/4.03  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.82/4.03  thf(sk_A_type, type, sk_A: $i).
% 3.82/4.03  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.82/4.03  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 3.82/4.03  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.82/4.03  thf(t18_funct_2, conjecture,
% 3.82/4.03    (![A:$i,B:$i,C:$i]:
% 3.82/4.03     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.82/4.03         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.82/4.03       ( ![D:$i]:
% 3.82/4.03         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.82/4.03             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.82/4.03           ( ( ![E:$i]:
% 3.82/4.03               ( ( r2_hidden @ E @ A ) =>
% 3.82/4.03                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 3.82/4.03             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 3.82/4.03  thf(zf_stmt_0, negated_conjecture,
% 3.82/4.03    (~( ![A:$i,B:$i,C:$i]:
% 3.82/4.03        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.82/4.03            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.82/4.03          ( ![D:$i]:
% 3.82/4.03            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.82/4.03                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.82/4.03              ( ( ![E:$i]:
% 3.82/4.03                  ( ( r2_hidden @ E @ A ) =>
% 3.82/4.03                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 3.82/4.03                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 3.82/4.03    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 3.82/4.03  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 3.82/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.82/4.03  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 3.82/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.82/4.03  thf(d1_funct_2, axiom,
% 3.82/4.03    (![A:$i,B:$i,C:$i]:
% 3.82/4.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.82/4.03       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.82/4.03           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.82/4.03             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.82/4.03         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.82/4.03           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.82/4.03             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.82/4.03  thf(zf_stmt_1, axiom,
% 3.82/4.03    (![C:$i,B:$i,A:$i]:
% 3.82/4.03     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.82/4.03       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.82/4.03  thf('2', plain,
% 3.82/4.03      (![X36 : $i, X37 : $i, X38 : $i]:
% 3.82/4.03         (~ (v1_funct_2 @ X38 @ X36 @ X37)
% 3.82/4.03          | ((X36) = (k1_relset_1 @ X36 @ X37 @ X38))
% 3.82/4.03          | ~ (zip_tseitin_1 @ X38 @ X37 @ X36))),
% 3.82/4.03      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.82/4.03  thf('3', plain,
% 3.82/4.03      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.82/4.03        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 3.82/4.03      inference('sup-', [status(thm)], ['1', '2'])).
% 3.82/4.03  thf('4', plain,
% 3.82/4.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.82/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.82/4.03  thf(redefinition_k1_relset_1, axiom,
% 3.82/4.03    (![A:$i,B:$i,C:$i]:
% 3.82/4.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.82/4.03       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.82/4.03  thf('5', plain,
% 3.82/4.03      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.82/4.03         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 3.82/4.03          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 3.82/4.03      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.82/4.03  thf('6', plain,
% 3.82/4.03      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 3.82/4.03      inference('sup-', [status(thm)], ['4', '5'])).
% 3.82/4.03  thf('7', plain,
% 3.82/4.03      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.82/4.03        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.82/4.03      inference('demod', [status(thm)], ['3', '6'])).
% 3.82/4.03  thf('8', plain,
% 3.82/4.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.82/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.82/4.03  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.82/4.03  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 3.82/4.03  thf(zf_stmt_4, axiom,
% 3.82/4.03    (![B:$i,A:$i]:
% 3.82/4.03     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.82/4.03       ( zip_tseitin_0 @ B @ A ) ))).
% 3.82/4.03  thf(zf_stmt_5, axiom,
% 3.82/4.03    (![A:$i,B:$i,C:$i]:
% 3.82/4.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.82/4.03       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.82/4.03         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.82/4.03           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.82/4.03             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.82/4.03  thf('9', plain,
% 3.82/4.03      (![X39 : $i, X40 : $i, X41 : $i]:
% 3.82/4.03         (~ (zip_tseitin_0 @ X39 @ X40)
% 3.82/4.03          | (zip_tseitin_1 @ X41 @ X39 @ X40)
% 3.82/4.03          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39))))),
% 3.82/4.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.82/4.03  thf('10', plain,
% 3.82/4.03      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.82/4.03        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 3.82/4.03      inference('sup-', [status(thm)], ['8', '9'])).
% 3.82/4.03  thf('11', plain,
% 3.82/4.03      (![X34 : $i, X35 : $i]:
% 3.82/4.03         ((zip_tseitin_0 @ X34 @ X35) | ((X34) = (k1_xboole_0)))),
% 3.82/4.03      inference('cnf', [status(esa)], [zf_stmt_4])).
% 3.82/4.03  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.82/4.03  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.82/4.03      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.82/4.03  thf('13', plain,
% 3.82/4.03      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 3.82/4.03      inference('sup+', [status(thm)], ['11', '12'])).
% 3.82/4.03  thf('14', plain,
% 3.82/4.03      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.82/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.82/4.03  thf(cc4_relset_1, axiom,
% 3.82/4.03    (![A:$i,B:$i]:
% 3.82/4.03     ( ( v1_xboole_0 @ A ) =>
% 3.82/4.03       ( ![C:$i]:
% 3.82/4.03         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 3.82/4.03           ( v1_xboole_0 @ C ) ) ) ))).
% 3.82/4.03  thf('15', plain,
% 3.82/4.03      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.82/4.03         (~ (v1_xboole_0 @ X24)
% 3.82/4.03          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X24)))
% 3.82/4.03          | (v1_xboole_0 @ X25))),
% 3.82/4.03      inference('cnf', [status(esa)], [cc4_relset_1])).
% 3.82/4.03  thf('16', plain, (((v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_B_1))),
% 3.82/4.03      inference('sup-', [status(thm)], ['14', '15'])).
% 3.82/4.03  thf('17', plain,
% 3.82/4.03      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_C_2))),
% 3.82/4.03      inference('sup-', [status(thm)], ['13', '16'])).
% 3.82/4.03  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.82/4.03      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.82/4.03  thf(t8_boole, axiom,
% 3.82/4.03    (![A:$i,B:$i]:
% 3.82/4.03     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 3.82/4.03  thf('19', plain,
% 3.82/4.03      (![X4 : $i, X5 : $i]:
% 3.82/4.03         (~ (v1_xboole_0 @ X4) | ~ (v1_xboole_0 @ X5) | ((X4) = (X5)))),
% 3.82/4.03      inference('cnf', [status(esa)], [t8_boole])).
% 3.82/4.03  thf('20', plain,
% 3.82/4.03      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.82/4.03      inference('sup-', [status(thm)], ['18', '19'])).
% 3.82/4.03  thf('21', plain,
% 3.82/4.03      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.82/4.03      inference('sup-', [status(thm)], ['18', '19'])).
% 3.82/4.03  thf(t4_subset_1, axiom,
% 3.82/4.03    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 3.82/4.03  thf('22', plain,
% 3.82/4.03      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 3.82/4.03      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.82/4.03  thf(reflexivity_r2_relset_1, axiom,
% 3.82/4.03    (![A:$i,B:$i,C:$i,D:$i]:
% 3.82/4.03     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.82/4.03         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.82/4.03       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 3.82/4.03  thf('23', plain,
% 3.82/4.03      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 3.82/4.03         ((r2_relset_1 @ X30 @ X31 @ X32 @ X32)
% 3.82/4.03          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 3.82/4.03          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 3.82/4.03      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 3.82/4.03  thf('24', plain,
% 3.82/4.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.82/4.03         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 3.82/4.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 3.82/4.03      inference('condensation', [status(thm)], ['23'])).
% 3.82/4.03  thf('25', plain,
% 3.82/4.03      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 3.82/4.03      inference('sup-', [status(thm)], ['22', '24'])).
% 3.82/4.03  thf('26', plain,
% 3.82/4.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.82/4.03         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 3.82/4.03      inference('sup+', [status(thm)], ['21', '25'])).
% 3.82/4.03  thf('27', plain,
% 3.82/4.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.82/4.03         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 3.82/4.03          | ~ (v1_xboole_0 @ X0)
% 3.82/4.03          | ~ (v1_xboole_0 @ X1))),
% 3.82/4.03      inference('sup+', [status(thm)], ['20', '26'])).
% 3.82/4.03  thf('28', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 3.82/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.82/4.03  thf('29', plain, ((~ (v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_D))),
% 3.82/4.03      inference('sup-', [status(thm)], ['27', '28'])).
% 3.82/4.03  thf('30', plain,
% 3.82/4.03      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | ~ (v1_xboole_0 @ sk_D))),
% 3.82/4.03      inference('sup-', [status(thm)], ['17', '29'])).
% 3.82/4.03  thf('31', plain,
% 3.82/4.03      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 3.82/4.03      inference('sup+', [status(thm)], ['11', '12'])).
% 3.82/4.03  thf('32', plain,
% 3.82/4.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.82/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.82/4.03  thf('33', plain,
% 3.82/4.03      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.82/4.03         (~ (v1_xboole_0 @ X24)
% 3.82/4.03          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X24)))
% 3.82/4.03          | (v1_xboole_0 @ X25))),
% 3.82/4.03      inference('cnf', [status(esa)], [cc4_relset_1])).
% 3.82/4.03  thf('34', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_B_1))),
% 3.82/4.03      inference('sup-', [status(thm)], ['32', '33'])).
% 3.82/4.03  thf('35', plain,
% 3.82/4.03      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_D))),
% 3.82/4.03      inference('sup-', [status(thm)], ['31', '34'])).
% 3.82/4.03  thf('36', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 3.82/4.03      inference('clc', [status(thm)], ['30', '35'])).
% 3.82/4.03  thf('37', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 3.82/4.03      inference('demod', [status(thm)], ['10', '36'])).
% 3.82/4.03  thf('38', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 3.82/4.03      inference('demod', [status(thm)], ['7', '37'])).
% 3.82/4.03  thf('39', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 3.82/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.82/4.03  thf('40', plain,
% 3.82/4.03      (![X36 : $i, X37 : $i, X38 : $i]:
% 3.82/4.03         (~ (v1_funct_2 @ X38 @ X36 @ X37)
% 3.82/4.03          | ((X36) = (k1_relset_1 @ X36 @ X37 @ X38))
% 3.82/4.03          | ~ (zip_tseitin_1 @ X38 @ X37 @ X36))),
% 3.82/4.03      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.82/4.03  thf('41', plain,
% 3.82/4.03      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 3.82/4.03        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 3.82/4.03      inference('sup-', [status(thm)], ['39', '40'])).
% 3.82/4.03  thf('42', plain,
% 3.82/4.03      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.82/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.82/4.03  thf('43', plain,
% 3.82/4.03      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.82/4.03         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 3.82/4.03          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 3.82/4.03      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.82/4.03  thf('44', plain,
% 3.82/4.03      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 3.82/4.03      inference('sup-', [status(thm)], ['42', '43'])).
% 3.82/4.03  thf('45', plain,
% 3.82/4.03      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 3.82/4.03        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.82/4.03      inference('demod', [status(thm)], ['41', '44'])).
% 3.82/4.03  thf('46', plain,
% 3.82/4.03      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.82/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.82/4.03  thf('47', plain,
% 3.82/4.03      (![X39 : $i, X40 : $i, X41 : $i]:
% 3.82/4.03         (~ (zip_tseitin_0 @ X39 @ X40)
% 3.82/4.03          | (zip_tseitin_1 @ X41 @ X39 @ X40)
% 3.82/4.03          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39))))),
% 3.82/4.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.82/4.03  thf('48', plain,
% 3.82/4.03      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 3.82/4.03        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 3.82/4.03      inference('sup-', [status(thm)], ['46', '47'])).
% 3.82/4.03  thf('49', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 3.82/4.03      inference('clc', [status(thm)], ['30', '35'])).
% 3.82/4.03  thf('50', plain, ((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)),
% 3.82/4.03      inference('demod', [status(thm)], ['48', '49'])).
% 3.82/4.03  thf('51', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 3.82/4.03      inference('demod', [status(thm)], ['45', '50'])).
% 3.82/4.03  thf(t9_funct_1, axiom,
% 3.82/4.03    (![A:$i]:
% 3.82/4.03     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.82/4.03       ( ![B:$i]:
% 3.82/4.03         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.82/4.03           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 3.82/4.03               ( ![C:$i]:
% 3.82/4.03                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 3.82/4.03                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 3.82/4.03             ( ( A ) = ( B ) ) ) ) ) ))).
% 3.82/4.03  thf('52', plain,
% 3.82/4.03      (![X16 : $i, X17 : $i]:
% 3.82/4.03         (~ (v1_relat_1 @ X16)
% 3.82/4.03          | ~ (v1_funct_1 @ X16)
% 3.82/4.03          | ((X17) = (X16))
% 3.82/4.03          | (r2_hidden @ (sk_C_1 @ X16 @ X17) @ (k1_relat_1 @ X17))
% 3.82/4.03          | ((k1_relat_1 @ X17) != (k1_relat_1 @ X16))
% 3.82/4.03          | ~ (v1_funct_1 @ X17)
% 3.82/4.03          | ~ (v1_relat_1 @ X17))),
% 3.82/4.03      inference('cnf', [status(esa)], [t9_funct_1])).
% 3.82/4.03  thf('53', plain,
% 3.82/4.03      (![X0 : $i]:
% 3.82/4.03         (((sk_A) != (k1_relat_1 @ X0))
% 3.82/4.03          | ~ (v1_relat_1 @ sk_C_2)
% 3.82/4.03          | ~ (v1_funct_1 @ sk_C_2)
% 3.82/4.03          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 3.82/4.03          | ((sk_C_2) = (X0))
% 3.82/4.03          | ~ (v1_funct_1 @ X0)
% 3.82/4.03          | ~ (v1_relat_1 @ X0))),
% 3.82/4.03      inference('sup-', [status(thm)], ['51', '52'])).
% 3.82/4.03  thf('54', plain,
% 3.82/4.03      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.82/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.82/4.03  thf(cc1_relset_1, axiom,
% 3.82/4.03    (![A:$i,B:$i,C:$i]:
% 3.82/4.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.82/4.03       ( v1_relat_1 @ C ) ))).
% 3.82/4.03  thf('55', plain,
% 3.82/4.03      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.82/4.03         ((v1_relat_1 @ X18)
% 3.82/4.03          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 3.82/4.03      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.82/4.03  thf('56', plain, ((v1_relat_1 @ sk_C_2)),
% 3.82/4.03      inference('sup-', [status(thm)], ['54', '55'])).
% 3.82/4.03  thf('57', plain, ((v1_funct_1 @ sk_C_2)),
% 3.82/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.82/4.03  thf('58', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 3.82/4.03      inference('demod', [status(thm)], ['45', '50'])).
% 3.82/4.03  thf('59', plain,
% 3.82/4.03      (![X0 : $i]:
% 3.82/4.03         (((sk_A) != (k1_relat_1 @ X0))
% 3.82/4.03          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A)
% 3.82/4.03          | ((sk_C_2) = (X0))
% 3.82/4.03          | ~ (v1_funct_1 @ X0)
% 3.82/4.03          | ~ (v1_relat_1 @ X0))),
% 3.82/4.03      inference('demod', [status(thm)], ['53', '56', '57', '58'])).
% 3.82/4.03  thf('60', plain,
% 3.82/4.03      ((((sk_A) != (sk_A))
% 3.82/4.03        | ~ (v1_relat_1 @ sk_D)
% 3.82/4.03        | ~ (v1_funct_1 @ sk_D)
% 3.82/4.03        | ((sk_C_2) = (sk_D))
% 3.82/4.03        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 3.82/4.03      inference('sup-', [status(thm)], ['38', '59'])).
% 3.82/4.03  thf('61', plain,
% 3.82/4.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.82/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.82/4.03  thf('62', plain,
% 3.82/4.03      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.82/4.03         ((v1_relat_1 @ X18)
% 3.82/4.03          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 3.82/4.03      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.82/4.03  thf('63', plain, ((v1_relat_1 @ sk_D)),
% 3.82/4.03      inference('sup-', [status(thm)], ['61', '62'])).
% 3.82/4.03  thf('64', plain, ((v1_funct_1 @ sk_D)),
% 3.82/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.82/4.03  thf('65', plain,
% 3.82/4.03      ((((sk_A) != (sk_A))
% 3.82/4.03        | ((sk_C_2) = (sk_D))
% 3.82/4.03        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 3.82/4.03      inference('demod', [status(thm)], ['60', '63', '64'])).
% 3.82/4.03  thf('66', plain,
% 3.82/4.03      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A) | ((sk_C_2) = (sk_D)))),
% 3.82/4.03      inference('simplify', [status(thm)], ['65'])).
% 3.82/4.03  thf('67', plain,
% 3.82/4.03      (![X42 : $i]:
% 3.82/4.03         (((k1_funct_1 @ sk_C_2 @ X42) = (k1_funct_1 @ sk_D @ X42))
% 3.82/4.03          | ~ (r2_hidden @ X42 @ sk_A))),
% 3.82/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.82/4.03  thf('68', plain,
% 3.82/4.03      ((((sk_C_2) = (sk_D))
% 3.82/4.03        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 3.82/4.03            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 3.82/4.03      inference('sup-', [status(thm)], ['66', '67'])).
% 3.82/4.03  thf('69', plain,
% 3.82/4.03      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 3.82/4.03         = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))),
% 3.82/4.03      inference('condensation', [status(thm)], ['68'])).
% 3.82/4.03  thf('70', plain,
% 3.82/4.03      (![X16 : $i, X17 : $i]:
% 3.82/4.03         (~ (v1_relat_1 @ X16)
% 3.82/4.03          | ~ (v1_funct_1 @ X16)
% 3.82/4.03          | ((X17) = (X16))
% 3.82/4.03          | ((k1_funct_1 @ X17 @ (sk_C_1 @ X16 @ X17))
% 3.82/4.03              != (k1_funct_1 @ X16 @ (sk_C_1 @ X16 @ X17)))
% 3.82/4.03          | ((k1_relat_1 @ X17) != (k1_relat_1 @ X16))
% 3.82/4.03          | ~ (v1_funct_1 @ X17)
% 3.82/4.03          | ~ (v1_relat_1 @ X17))),
% 3.82/4.03      inference('cnf', [status(esa)], [t9_funct_1])).
% 3.82/4.03  thf('71', plain,
% 3.82/4.03      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 3.82/4.03          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 3.82/4.03        | ~ (v1_relat_1 @ sk_C_2)
% 3.82/4.03        | ~ (v1_funct_1 @ sk_C_2)
% 3.82/4.03        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 3.82/4.03        | ((sk_C_2) = (sk_D))
% 3.82/4.03        | ~ (v1_funct_1 @ sk_D)
% 3.82/4.03        | ~ (v1_relat_1 @ sk_D))),
% 3.82/4.03      inference('sup-', [status(thm)], ['69', '70'])).
% 3.82/4.03  thf('72', plain, ((v1_relat_1 @ sk_C_2)),
% 3.82/4.03      inference('sup-', [status(thm)], ['54', '55'])).
% 3.82/4.03  thf('73', plain, ((v1_funct_1 @ sk_C_2)),
% 3.82/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.82/4.03  thf('74', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 3.82/4.03      inference('demod', [status(thm)], ['45', '50'])).
% 3.82/4.03  thf('75', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 3.82/4.03      inference('demod', [status(thm)], ['7', '37'])).
% 3.82/4.03  thf('76', plain, ((v1_funct_1 @ sk_D)),
% 3.82/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.82/4.03  thf('77', plain, ((v1_relat_1 @ sk_D)),
% 3.82/4.03      inference('sup-', [status(thm)], ['61', '62'])).
% 3.82/4.03  thf('78', plain,
% 3.82/4.03      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 3.82/4.03          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 3.82/4.03        | ((sk_A) != (sk_A))
% 3.82/4.03        | ((sk_C_2) = (sk_D)))),
% 3.82/4.03      inference('demod', [status(thm)],
% 3.82/4.03                ['71', '72', '73', '74', '75', '76', '77'])).
% 3.82/4.03  thf('79', plain, (((sk_C_2) = (sk_D))),
% 3.82/4.03      inference('simplify', [status(thm)], ['78'])).
% 3.82/4.03  thf('80', plain,
% 3.82/4.03      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.82/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.82/4.03  thf('81', plain,
% 3.82/4.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.82/4.03         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 3.82/4.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 3.82/4.03      inference('condensation', [status(thm)], ['23'])).
% 3.82/4.03  thf('82', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2)),
% 3.82/4.03      inference('sup-', [status(thm)], ['80', '81'])).
% 3.82/4.03  thf('83', plain, ($false),
% 3.82/4.03      inference('demod', [status(thm)], ['0', '79', '82'])).
% 3.82/4.03  
% 3.82/4.03  % SZS output end Refutation
% 3.82/4.03  
% 3.82/4.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
