%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dJGho3WFDu

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:33 EST 2020

% Result     : Theorem 4.10s
% Output     : Refutation 4.10s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 432 expanded)
%              Number of leaves         :   35 ( 146 expanded)
%              Depth                    :   21
%              Number of atoms          :  888 (5675 expanded)
%              Number of equality atoms :   63 ( 234 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
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
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
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
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
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
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('15',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X23 ) ) )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('16',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
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
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('23',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r2_relset_1 @ X29 @ X30 @ X31 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
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
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X23 ) ) )
      | ( v1_xboole_0 @ X24 ) ) ),
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
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('41',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('44',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('48',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['30','35'])).

thf('50',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( X16 = X15 )
      | ( r2_hidden @ ( sk_C @ X15 @ X16 ) @ ( k1_relat_1 @ X16 ) )
      | ( ( k1_relat_1 @ X16 )
       != ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('55',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('56',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','56','57','58'])).

thf('60',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['38','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('63',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['60','63','64'])).

thf('66',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X41: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X41 )
        = ( k1_funct_1 @ sk_D @ X41 ) )
      | ~ ( r2_hidden @ X41 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( sk_C_1 = sk_D )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ),
    inference(condensation,[status(thm)],['68'])).

thf('70',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( X16 = X15 )
      | ( ( k1_funct_1 @ X16 @ ( sk_C @ X15 @ X16 ) )
       != ( k1_funct_1 @ X15 @ ( sk_C @ X15 @ X16 ) ) )
      | ( ( k1_relat_1 @ X16 )
       != ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('71',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['54','55'])).

thf('73',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
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
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(demod,[status(thm)],['71','72','73','74','75','76','77'])).

thf('79',plain,(
    sk_C_1 = sk_D ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['23'])).

thf('82',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['0','79','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dJGho3WFDu
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:40:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.10/4.34  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.10/4.34  % Solved by: fo/fo7.sh
% 4.10/4.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.10/4.34  % done 3710 iterations in 3.892s
% 4.10/4.34  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.10/4.34  % SZS output start Refutation
% 4.10/4.34  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.10/4.34  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.10/4.34  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.10/4.34  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.10/4.34  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.10/4.34  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.10/4.34  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.10/4.34  thf(sk_D_type, type, sk_D: $i).
% 4.10/4.34  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.10/4.34  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 4.10/4.34  thf(sk_A_type, type, sk_A: $i).
% 4.10/4.34  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 4.10/4.34  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.10/4.34  thf(sk_B_1_type, type, sk_B_1: $i).
% 4.10/4.34  thf(sk_C_1_type, type, sk_C_1: $i).
% 4.10/4.34  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 4.10/4.34  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.10/4.34  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 4.10/4.34  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 4.10/4.34  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.10/4.34  thf(t18_funct_2, conjecture,
% 4.10/4.34    (![A:$i,B:$i,C:$i]:
% 4.10/4.34     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.10/4.34         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.10/4.34       ( ![D:$i]:
% 4.10/4.34         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.10/4.34             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.10/4.34           ( ( ![E:$i]:
% 4.10/4.34               ( ( r2_hidden @ E @ A ) =>
% 4.10/4.34                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 4.10/4.34             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 4.10/4.34  thf(zf_stmt_0, negated_conjecture,
% 4.10/4.34    (~( ![A:$i,B:$i,C:$i]:
% 4.10/4.34        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.10/4.34            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.10/4.34          ( ![D:$i]:
% 4.10/4.34            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.10/4.34                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.10/4.34              ( ( ![E:$i]:
% 4.10/4.34                  ( ( r2_hidden @ E @ A ) =>
% 4.10/4.34                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 4.10/4.34                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 4.10/4.34    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 4.10/4.34  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)),
% 4.10/4.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.34  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 4.10/4.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.34  thf(d1_funct_2, axiom,
% 4.10/4.34    (![A:$i,B:$i,C:$i]:
% 4.10/4.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.10/4.34       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.10/4.34           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 4.10/4.34             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 4.10/4.34         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.10/4.34           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 4.10/4.34             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 4.10/4.34  thf(zf_stmt_1, axiom,
% 4.10/4.34    (![C:$i,B:$i,A:$i]:
% 4.10/4.34     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 4.10/4.34       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.10/4.34  thf('2', plain,
% 4.10/4.34      (![X35 : $i, X36 : $i, X37 : $i]:
% 4.10/4.34         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 4.10/4.34          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 4.10/4.34          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 4.10/4.34      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.10/4.34  thf('3', plain,
% 4.10/4.34      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 4.10/4.34        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 4.10/4.34      inference('sup-', [status(thm)], ['1', '2'])).
% 4.10/4.34  thf('4', plain,
% 4.10/4.34      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.10/4.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.34  thf(redefinition_k1_relset_1, axiom,
% 4.10/4.34    (![A:$i,B:$i,C:$i]:
% 4.10/4.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.10/4.34       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 4.10/4.34  thf('5', plain,
% 4.10/4.34      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.10/4.34         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 4.10/4.34          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 4.10/4.34      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.10/4.34  thf('6', plain,
% 4.10/4.34      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 4.10/4.34      inference('sup-', [status(thm)], ['4', '5'])).
% 4.10/4.34  thf('7', plain,
% 4.10/4.34      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 4.10/4.34        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.10/4.34      inference('demod', [status(thm)], ['3', '6'])).
% 4.10/4.34  thf('8', plain,
% 4.10/4.34      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.10/4.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.34  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 4.10/4.34  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 4.10/4.34  thf(zf_stmt_4, axiom,
% 4.10/4.34    (![B:$i,A:$i]:
% 4.10/4.34     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.10/4.34       ( zip_tseitin_0 @ B @ A ) ))).
% 4.10/4.34  thf(zf_stmt_5, axiom,
% 4.10/4.34    (![A:$i,B:$i,C:$i]:
% 4.10/4.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.10/4.34       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 4.10/4.34         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.10/4.34           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 4.10/4.34             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 4.10/4.34  thf('9', plain,
% 4.10/4.34      (![X38 : $i, X39 : $i, X40 : $i]:
% 4.10/4.34         (~ (zip_tseitin_0 @ X38 @ X39)
% 4.10/4.34          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 4.10/4.34          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 4.10/4.34      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.10/4.34  thf('10', plain,
% 4.10/4.34      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 4.10/4.34        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 4.10/4.34      inference('sup-', [status(thm)], ['8', '9'])).
% 4.10/4.34  thf('11', plain,
% 4.10/4.34      (![X33 : $i, X34 : $i]:
% 4.10/4.34         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 4.10/4.34      inference('cnf', [status(esa)], [zf_stmt_4])).
% 4.10/4.34  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 4.10/4.34  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.10/4.34      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.10/4.34  thf('13', plain,
% 4.10/4.34      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 4.10/4.34      inference('sup+', [status(thm)], ['11', '12'])).
% 4.10/4.34  thf('14', plain,
% 4.10/4.34      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.10/4.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.34  thf(cc4_relset_1, axiom,
% 4.10/4.34    (![A:$i,B:$i]:
% 4.10/4.34     ( ( v1_xboole_0 @ A ) =>
% 4.10/4.34       ( ![C:$i]:
% 4.10/4.34         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 4.10/4.34           ( v1_xboole_0 @ C ) ) ) ))).
% 4.10/4.34  thf('15', plain,
% 4.10/4.34      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.10/4.34         (~ (v1_xboole_0 @ X23)
% 4.10/4.34          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23)))
% 4.10/4.34          | (v1_xboole_0 @ X24))),
% 4.10/4.34      inference('cnf', [status(esa)], [cc4_relset_1])).
% 4.10/4.34  thf('16', plain, (((v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ sk_B_1))),
% 4.10/4.34      inference('sup-', [status(thm)], ['14', '15'])).
% 4.10/4.34  thf('17', plain,
% 4.10/4.34      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_C_1))),
% 4.10/4.34      inference('sup-', [status(thm)], ['13', '16'])).
% 4.10/4.34  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.10/4.34      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.10/4.34  thf(t8_boole, axiom,
% 4.10/4.34    (![A:$i,B:$i]:
% 4.10/4.34     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 4.10/4.34  thf('19', plain,
% 4.10/4.34      (![X0 : $i, X1 : $i]:
% 4.10/4.34         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 4.10/4.34      inference('cnf', [status(esa)], [t8_boole])).
% 4.10/4.34  thf('20', plain,
% 4.10/4.34      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 4.10/4.34      inference('sup-', [status(thm)], ['18', '19'])).
% 4.10/4.34  thf('21', plain,
% 4.10/4.34      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 4.10/4.34      inference('sup-', [status(thm)], ['18', '19'])).
% 4.10/4.34  thf(t4_subset_1, axiom,
% 4.10/4.34    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 4.10/4.34  thf('22', plain,
% 4.10/4.34      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 4.10/4.34      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.10/4.34  thf(reflexivity_r2_relset_1, axiom,
% 4.10/4.34    (![A:$i,B:$i,C:$i,D:$i]:
% 4.10/4.34     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.10/4.34         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.10/4.34       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 4.10/4.34  thf('23', plain,
% 4.10/4.34      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 4.10/4.34         ((r2_relset_1 @ X29 @ X30 @ X31 @ X31)
% 4.10/4.34          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 4.10/4.34          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 4.10/4.34      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 4.10/4.34  thf('24', plain,
% 4.10/4.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.10/4.34         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 4.10/4.34          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 4.10/4.34      inference('condensation', [status(thm)], ['23'])).
% 4.10/4.34  thf('25', plain,
% 4.10/4.34      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 4.10/4.34      inference('sup-', [status(thm)], ['22', '24'])).
% 4.10/4.34  thf('26', plain,
% 4.10/4.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.10/4.34         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 4.10/4.34      inference('sup+', [status(thm)], ['21', '25'])).
% 4.10/4.34  thf('27', plain,
% 4.10/4.34      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.10/4.34         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 4.10/4.34          | ~ (v1_xboole_0 @ X0)
% 4.10/4.34          | ~ (v1_xboole_0 @ X1))),
% 4.10/4.34      inference('sup+', [status(thm)], ['20', '26'])).
% 4.10/4.34  thf('28', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)),
% 4.10/4.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.34  thf('29', plain, ((~ (v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ sk_D))),
% 4.10/4.34      inference('sup-', [status(thm)], ['27', '28'])).
% 4.10/4.34  thf('30', plain,
% 4.10/4.34      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | ~ (v1_xboole_0 @ sk_D))),
% 4.10/4.34      inference('sup-', [status(thm)], ['17', '29'])).
% 4.10/4.34  thf('31', plain,
% 4.10/4.34      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 4.10/4.34      inference('sup+', [status(thm)], ['11', '12'])).
% 4.10/4.34  thf('32', plain,
% 4.10/4.34      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.10/4.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.34  thf('33', plain,
% 4.10/4.34      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.10/4.34         (~ (v1_xboole_0 @ X23)
% 4.10/4.34          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23)))
% 4.10/4.34          | (v1_xboole_0 @ X24))),
% 4.10/4.34      inference('cnf', [status(esa)], [cc4_relset_1])).
% 4.10/4.34  thf('34', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_B_1))),
% 4.10/4.34      inference('sup-', [status(thm)], ['32', '33'])).
% 4.10/4.34  thf('35', plain,
% 4.10/4.34      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_D))),
% 4.10/4.34      inference('sup-', [status(thm)], ['31', '34'])).
% 4.10/4.34  thf('36', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 4.10/4.34      inference('clc', [status(thm)], ['30', '35'])).
% 4.10/4.34  thf('37', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 4.10/4.34      inference('demod', [status(thm)], ['10', '36'])).
% 4.10/4.34  thf('38', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 4.10/4.34      inference('demod', [status(thm)], ['7', '37'])).
% 4.10/4.34  thf('39', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 4.10/4.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.34  thf('40', plain,
% 4.10/4.34      (![X35 : $i, X36 : $i, X37 : $i]:
% 4.10/4.34         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 4.10/4.34          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 4.10/4.34          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 4.10/4.34      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.10/4.34  thf('41', plain,
% 4.10/4.34      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 4.10/4.34        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 4.10/4.34      inference('sup-', [status(thm)], ['39', '40'])).
% 4.10/4.34  thf('42', plain,
% 4.10/4.34      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.10/4.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.34  thf('43', plain,
% 4.10/4.34      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.10/4.34         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 4.10/4.34          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 4.10/4.34      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.10/4.34  thf('44', plain,
% 4.10/4.34      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 4.10/4.34      inference('sup-', [status(thm)], ['42', '43'])).
% 4.10/4.34  thf('45', plain,
% 4.10/4.34      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 4.10/4.34        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 4.10/4.34      inference('demod', [status(thm)], ['41', '44'])).
% 4.10/4.34  thf('46', plain,
% 4.10/4.34      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.10/4.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.34  thf('47', plain,
% 4.10/4.34      (![X38 : $i, X39 : $i, X40 : $i]:
% 4.10/4.34         (~ (zip_tseitin_0 @ X38 @ X39)
% 4.10/4.34          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 4.10/4.34          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 4.10/4.34      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.10/4.34  thf('48', plain,
% 4.10/4.34      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 4.10/4.34        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 4.10/4.34      inference('sup-', [status(thm)], ['46', '47'])).
% 4.10/4.34  thf('49', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 4.10/4.34      inference('clc', [status(thm)], ['30', '35'])).
% 4.10/4.34  thf('50', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)),
% 4.10/4.34      inference('demod', [status(thm)], ['48', '49'])).
% 4.10/4.34  thf('51', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 4.10/4.34      inference('demod', [status(thm)], ['45', '50'])).
% 4.10/4.34  thf(t9_funct_1, axiom,
% 4.10/4.34    (![A:$i]:
% 4.10/4.34     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.10/4.34       ( ![B:$i]:
% 4.10/4.34         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.10/4.34           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 4.10/4.34               ( ![C:$i]:
% 4.10/4.34                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 4.10/4.34                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 4.10/4.34             ( ( A ) = ( B ) ) ) ) ) ))).
% 4.10/4.34  thf('52', plain,
% 4.10/4.34      (![X15 : $i, X16 : $i]:
% 4.10/4.34         (~ (v1_relat_1 @ X15)
% 4.10/4.34          | ~ (v1_funct_1 @ X15)
% 4.10/4.34          | ((X16) = (X15))
% 4.10/4.34          | (r2_hidden @ (sk_C @ X15 @ X16) @ (k1_relat_1 @ X16))
% 4.10/4.34          | ((k1_relat_1 @ X16) != (k1_relat_1 @ X15))
% 4.10/4.34          | ~ (v1_funct_1 @ X16)
% 4.10/4.34          | ~ (v1_relat_1 @ X16))),
% 4.10/4.34      inference('cnf', [status(esa)], [t9_funct_1])).
% 4.10/4.34  thf('53', plain,
% 4.10/4.34      (![X0 : $i]:
% 4.10/4.34         (((sk_A) != (k1_relat_1 @ X0))
% 4.10/4.34          | ~ (v1_relat_1 @ sk_C_1)
% 4.10/4.34          | ~ (v1_funct_1 @ sk_C_1)
% 4.10/4.34          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 4.10/4.34          | ((sk_C_1) = (X0))
% 4.10/4.34          | ~ (v1_funct_1 @ X0)
% 4.10/4.34          | ~ (v1_relat_1 @ X0))),
% 4.10/4.34      inference('sup-', [status(thm)], ['51', '52'])).
% 4.10/4.34  thf('54', plain,
% 4.10/4.34      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.10/4.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.34  thf(cc1_relset_1, axiom,
% 4.10/4.34    (![A:$i,B:$i,C:$i]:
% 4.10/4.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.10/4.34       ( v1_relat_1 @ C ) ))).
% 4.10/4.34  thf('55', plain,
% 4.10/4.34      (![X17 : $i, X18 : $i, X19 : $i]:
% 4.10/4.34         ((v1_relat_1 @ X17)
% 4.10/4.34          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 4.10/4.34      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.10/4.34  thf('56', plain, ((v1_relat_1 @ sk_C_1)),
% 4.10/4.34      inference('sup-', [status(thm)], ['54', '55'])).
% 4.10/4.34  thf('57', plain, ((v1_funct_1 @ sk_C_1)),
% 4.10/4.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.34  thf('58', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 4.10/4.34      inference('demod', [status(thm)], ['45', '50'])).
% 4.10/4.34  thf('59', plain,
% 4.10/4.34      (![X0 : $i]:
% 4.10/4.34         (((sk_A) != (k1_relat_1 @ X0))
% 4.10/4.34          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A)
% 4.10/4.34          | ((sk_C_1) = (X0))
% 4.10/4.34          | ~ (v1_funct_1 @ X0)
% 4.10/4.34          | ~ (v1_relat_1 @ X0))),
% 4.10/4.34      inference('demod', [status(thm)], ['53', '56', '57', '58'])).
% 4.10/4.34  thf('60', plain,
% 4.10/4.34      ((((sk_A) != (sk_A))
% 4.10/4.34        | ~ (v1_relat_1 @ sk_D)
% 4.10/4.34        | ~ (v1_funct_1 @ sk_D)
% 4.10/4.34        | ((sk_C_1) = (sk_D))
% 4.10/4.34        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 4.10/4.34      inference('sup-', [status(thm)], ['38', '59'])).
% 4.10/4.34  thf('61', plain,
% 4.10/4.34      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.10/4.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.34  thf('62', plain,
% 4.10/4.34      (![X17 : $i, X18 : $i, X19 : $i]:
% 4.10/4.34         ((v1_relat_1 @ X17)
% 4.10/4.34          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 4.10/4.34      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.10/4.34  thf('63', plain, ((v1_relat_1 @ sk_D)),
% 4.10/4.34      inference('sup-', [status(thm)], ['61', '62'])).
% 4.10/4.34  thf('64', plain, ((v1_funct_1 @ sk_D)),
% 4.10/4.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.34  thf('65', plain,
% 4.10/4.34      ((((sk_A) != (sk_A))
% 4.10/4.34        | ((sk_C_1) = (sk_D))
% 4.10/4.34        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 4.10/4.34      inference('demod', [status(thm)], ['60', '63', '64'])).
% 4.10/4.34  thf('66', plain,
% 4.10/4.34      (((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A) | ((sk_C_1) = (sk_D)))),
% 4.10/4.34      inference('simplify', [status(thm)], ['65'])).
% 4.10/4.34  thf('67', plain,
% 4.10/4.34      (![X41 : $i]:
% 4.10/4.34         (((k1_funct_1 @ sk_C_1 @ X41) = (k1_funct_1 @ sk_D @ X41))
% 4.10/4.34          | ~ (r2_hidden @ X41 @ sk_A))),
% 4.10/4.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.34  thf('68', plain,
% 4.10/4.34      ((((sk_C_1) = (sk_D))
% 4.10/4.34        | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 4.10/4.34            = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))))),
% 4.10/4.34      inference('sup-', [status(thm)], ['66', '67'])).
% 4.10/4.34  thf('69', plain,
% 4.10/4.34      (((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 4.10/4.34         = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))),
% 4.10/4.34      inference('condensation', [status(thm)], ['68'])).
% 4.10/4.34  thf('70', plain,
% 4.10/4.34      (![X15 : $i, X16 : $i]:
% 4.10/4.34         (~ (v1_relat_1 @ X15)
% 4.10/4.34          | ~ (v1_funct_1 @ X15)
% 4.10/4.34          | ((X16) = (X15))
% 4.10/4.34          | ((k1_funct_1 @ X16 @ (sk_C @ X15 @ X16))
% 4.10/4.34              != (k1_funct_1 @ X15 @ (sk_C @ X15 @ X16)))
% 4.10/4.34          | ((k1_relat_1 @ X16) != (k1_relat_1 @ X15))
% 4.10/4.34          | ~ (v1_funct_1 @ X16)
% 4.10/4.34          | ~ (v1_relat_1 @ X16))),
% 4.10/4.34      inference('cnf', [status(esa)], [t9_funct_1])).
% 4.10/4.34  thf('71', plain,
% 4.10/4.34      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 4.10/4.34          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 4.10/4.34        | ~ (v1_relat_1 @ sk_C_1)
% 4.10/4.34        | ~ (v1_funct_1 @ sk_C_1)
% 4.10/4.34        | ((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_D))
% 4.10/4.34        | ((sk_C_1) = (sk_D))
% 4.10/4.34        | ~ (v1_funct_1 @ sk_D)
% 4.10/4.34        | ~ (v1_relat_1 @ sk_D))),
% 4.10/4.34      inference('sup-', [status(thm)], ['69', '70'])).
% 4.10/4.34  thf('72', plain, ((v1_relat_1 @ sk_C_1)),
% 4.10/4.34      inference('sup-', [status(thm)], ['54', '55'])).
% 4.10/4.34  thf('73', plain, ((v1_funct_1 @ sk_C_1)),
% 4.10/4.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.34  thf('74', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 4.10/4.34      inference('demod', [status(thm)], ['45', '50'])).
% 4.10/4.34  thf('75', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 4.10/4.34      inference('demod', [status(thm)], ['7', '37'])).
% 4.10/4.34  thf('76', plain, ((v1_funct_1 @ sk_D)),
% 4.10/4.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.34  thf('77', plain, ((v1_relat_1 @ sk_D)),
% 4.10/4.34      inference('sup-', [status(thm)], ['61', '62'])).
% 4.10/4.34  thf('78', plain,
% 4.10/4.34      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 4.10/4.34          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 4.10/4.34        | ((sk_A) != (sk_A))
% 4.10/4.34        | ((sk_C_1) = (sk_D)))),
% 4.10/4.34      inference('demod', [status(thm)],
% 4.10/4.34                ['71', '72', '73', '74', '75', '76', '77'])).
% 4.10/4.34  thf('79', plain, (((sk_C_1) = (sk_D))),
% 4.10/4.34      inference('simplify', [status(thm)], ['78'])).
% 4.10/4.34  thf('80', plain,
% 4.10/4.34      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.10/4.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.10/4.34  thf('81', plain,
% 4.10/4.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.10/4.34         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 4.10/4.34          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 4.10/4.34      inference('condensation', [status(thm)], ['23'])).
% 4.10/4.34  thf('82', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_C_1)),
% 4.10/4.34      inference('sup-', [status(thm)], ['80', '81'])).
% 4.10/4.34  thf('83', plain, ($false),
% 4.10/4.34      inference('demod', [status(thm)], ['0', '79', '82'])).
% 4.10/4.34  
% 4.10/4.34  % SZS output end Refutation
% 4.10/4.34  
% 4.10/4.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
