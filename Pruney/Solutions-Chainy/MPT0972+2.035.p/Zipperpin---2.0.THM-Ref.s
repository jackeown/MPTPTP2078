%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XO4GtwAZIZ

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:38 EST 2020

% Result     : Theorem 6.39s
% Output     : Refutation 6.39s
% Verified   : 
% Statistics : Number of formulae       :  190 (1130 expanded)
%              Number of leaves         :   39 ( 353 expanded)
%              Depth                    :   22
%              Number of atoms          : 1447 (14566 expanded)
%              Number of equality atoms :  127 ( 834 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('1',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X4 = X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relset_1 @ X2 @ X1 @ X0 )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('14',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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

thf('17',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('18',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('22',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('25',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['19','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('31',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k1_relset_1 @ X0 @ k1_xboole_0 @ X1 )
        = ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relset_1 @ X0 @ k1_xboole_0 @ sk_C_2 )
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = ( k1_relat_1 @ sk_C_2 ) )
    | ~ ( v1_xboole_0 @ sk_C_2 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['11','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('36',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('37',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('38',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( r2_hidden @ ( sk_B @ sk_C_2 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('42',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf('44',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('47',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('49',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['34','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('52',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('54',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('58',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('61',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['55','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_C_2 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( sk_C_2 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_C_2 = X0 ) ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_C_2 = X0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('74',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('75',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( r2_relset_1 @ X23 @ X24 @ X25 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['73','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X3 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['72','78'])).

thf('80',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['71','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_D )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(condensation,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('86',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('87',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( r2_hidden @ ( sk_B @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('92',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['85','92'])).

thf('94',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('97',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['58','61'])).

thf('99',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['84','99'])).

thf('101',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = sk_A ) ),
    inference(demod,[status(thm)],['50','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relset_1 @ X2 @ X1 @ X0 )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['19','26'])).

thf('104',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k1_relset_1 @ X0 @ k1_xboole_0 @ X1 )
        = ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relset_1 @ X0 @ k1_xboole_0 @ sk_D )
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['102','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('110',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('111',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('113',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(clc,[status(thm)],['108','113'])).

thf('115',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(eq_fact,[status(thm)],['114'])).

thf('116',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['101','115'])).

thf('117',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['84','99'])).

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

thf('118',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( X16 = X15 )
      | ( r2_hidden @ ( sk_C_1 @ X15 @ X16 ) @ ( k1_relat_1 @ X16 ) )
      | ( ( k1_relat_1 @ X16 )
       != ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('121',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('122',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['84','99'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['119','122','123','124'])).

thf('126',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['116','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('129',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['126','129','130'])).

thf('132',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X35: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X35 )
        = ( k1_funct_1 @ sk_D @ X35 ) )
      | ~ ( r2_hidden @ X35 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( sk_C_2 = sk_D )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ),
    inference(condensation,[status(thm)],['134'])).

thf('136',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( X16 = X15 )
      | ( ( k1_funct_1 @ X16 @ ( sk_C_1 @ X15 @ X16 ) )
       != ( k1_funct_1 @ X15 @ ( sk_C_1 @ X15 @ X16 ) ) )
      | ( ( k1_relat_1 @ X16 )
       != ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('137',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['120','121'])).

thf('139',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['84','99'])).

thf('141',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['101','115'])).

thf('142',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['127','128'])).

thf('144',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['137','138','139','140','141','142','143'])).

thf('145',plain,(
    sk_C_2 = sk_D ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['75'])).

thf('148',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    $false ),
    inference(demod,[status(thm)],['0','145','148'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XO4GtwAZIZ
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:17:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 6.39/6.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.39/6.65  % Solved by: fo/fo7.sh
% 6.39/6.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.39/6.65  % done 5309 iterations in 6.198s
% 6.39/6.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.39/6.65  % SZS output start Refutation
% 6.39/6.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.39/6.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.39/6.65  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 6.39/6.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.39/6.65  thf(sk_A_type, type, sk_A: $i).
% 6.39/6.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.39/6.65  thf(sk_B_type, type, sk_B: $i > $i).
% 6.39/6.65  thf(sk_B_1_type, type, sk_B_1: $i).
% 6.39/6.65  thf(sk_C_2_type, type, sk_C_2: $i).
% 6.39/6.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.39/6.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.39/6.65  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 6.39/6.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.39/6.65  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 6.39/6.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.39/6.65  thf(sk_D_type, type, sk_D: $i).
% 6.39/6.65  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 6.39/6.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.39/6.65  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 6.39/6.65  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 6.39/6.65  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 6.39/6.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.39/6.65  thf(t18_funct_2, conjecture,
% 6.39/6.65    (![A:$i,B:$i,C:$i]:
% 6.39/6.65     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.39/6.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.39/6.65       ( ![D:$i]:
% 6.39/6.65         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 6.39/6.65             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.39/6.65           ( ( ![E:$i]:
% 6.39/6.65               ( ( r2_hidden @ E @ A ) =>
% 6.39/6.65                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 6.39/6.65             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 6.39/6.65  thf(zf_stmt_0, negated_conjecture,
% 6.39/6.65    (~( ![A:$i,B:$i,C:$i]:
% 6.39/6.65        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.39/6.65            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.39/6.65          ( ![D:$i]:
% 6.39/6.65            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 6.39/6.65                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.39/6.65              ( ( ![E:$i]:
% 6.39/6.65                  ( ( r2_hidden @ E @ A ) =>
% 6.39/6.65                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 6.39/6.65                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 6.39/6.65    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 6.39/6.65  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 6.39/6.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.39/6.65  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 6.39/6.65  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.39/6.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.39/6.65  thf(t2_tarski, axiom,
% 6.39/6.65    (![A:$i,B:$i]:
% 6.39/6.65     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 6.39/6.65       ( ( A ) = ( B ) ) ))).
% 6.39/6.65  thf('2', plain,
% 6.39/6.65      (![X3 : $i, X4 : $i]:
% 6.39/6.65         (((X4) = (X3))
% 6.39/6.65          | (r2_hidden @ (sk_C @ X3 @ X4) @ X3)
% 6.39/6.65          | (r2_hidden @ (sk_C @ X3 @ X4) @ X4))),
% 6.39/6.65      inference('cnf', [status(esa)], [t2_tarski])).
% 6.39/6.65  thf(d1_xboole_0, axiom,
% 6.39/6.65    (![A:$i]:
% 6.39/6.65     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 6.39/6.65  thf('3', plain,
% 6.39/6.65      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 6.39/6.65      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.39/6.65  thf('4', plain,
% 6.39/6.65      (![X0 : $i, X1 : $i]:
% 6.39/6.65         ((r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 6.39/6.65          | ((X1) = (X0))
% 6.39/6.65          | ~ (v1_xboole_0 @ X0))),
% 6.39/6.65      inference('sup-', [status(thm)], ['2', '3'])).
% 6.39/6.65  thf('5', plain,
% 6.39/6.65      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 6.39/6.65      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.39/6.65  thf('6', plain,
% 6.39/6.65      (![X0 : $i, X1 : $i]:
% 6.39/6.65         (~ (v1_xboole_0 @ X1) | ((X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 6.39/6.65      inference('sup-', [status(thm)], ['4', '5'])).
% 6.39/6.65  thf('7', plain,
% 6.39/6.65      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 6.39/6.65      inference('sup-', [status(thm)], ['1', '6'])).
% 6.39/6.65  thf(t4_subset_1, axiom,
% 6.39/6.65    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 6.39/6.65  thf('8', plain,
% 6.39/6.65      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 6.39/6.65      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.39/6.65  thf(redefinition_k1_relset_1, axiom,
% 6.39/6.65    (![A:$i,B:$i,C:$i]:
% 6.39/6.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.39/6.65       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 6.39/6.65  thf('9', plain,
% 6.39/6.65      (![X20 : $i, X21 : $i, X22 : $i]:
% 6.39/6.65         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 6.39/6.65          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 6.39/6.65      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.39/6.65  thf('10', plain,
% 6.39/6.65      (![X0 : $i, X1 : $i]:
% 6.39/6.65         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 6.39/6.65      inference('sup-', [status(thm)], ['8', '9'])).
% 6.39/6.65  thf('11', plain,
% 6.39/6.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.39/6.65         (((k1_relset_1 @ X2 @ X1 @ X0) = (k1_relat_1 @ k1_xboole_0))
% 6.39/6.65          | ~ (v1_xboole_0 @ X0))),
% 6.39/6.65      inference('sup+', [status(thm)], ['7', '10'])).
% 6.39/6.65  thf(d1_funct_2, axiom,
% 6.39/6.65    (![A:$i,B:$i,C:$i]:
% 6.39/6.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.39/6.65       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.39/6.65           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 6.39/6.65             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 6.39/6.65         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.39/6.65           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 6.39/6.65             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 6.39/6.65  thf(zf_stmt_1, axiom,
% 6.39/6.65    (![B:$i,A:$i]:
% 6.39/6.65     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.39/6.65       ( zip_tseitin_0 @ B @ A ) ))).
% 6.39/6.65  thf('12', plain,
% 6.39/6.65      (![X27 : $i, X28 : $i]:
% 6.39/6.65         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 6.39/6.65      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.39/6.65  thf(t113_zfmisc_1, axiom,
% 6.39/6.65    (![A:$i,B:$i]:
% 6.39/6.65     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 6.39/6.65       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 6.39/6.65  thf('13', plain,
% 6.39/6.65      (![X6 : $i, X7 : $i]:
% 6.39/6.65         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 6.39/6.65      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 6.39/6.65  thf('14', plain,
% 6.39/6.65      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 6.39/6.65      inference('simplify', [status(thm)], ['13'])).
% 6.39/6.65  thf('15', plain,
% 6.39/6.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.39/6.65         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 6.39/6.65      inference('sup+', [status(thm)], ['12', '14'])).
% 6.39/6.65  thf('16', plain,
% 6.39/6.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.39/6.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.39/6.65  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 6.39/6.65  thf(zf_stmt_3, axiom,
% 6.39/6.65    (![C:$i,B:$i,A:$i]:
% 6.39/6.65     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 6.39/6.65       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 6.39/6.65  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 6.39/6.65  thf(zf_stmt_5, axiom,
% 6.39/6.65    (![A:$i,B:$i,C:$i]:
% 6.39/6.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.39/6.65       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 6.39/6.65         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.39/6.65           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 6.39/6.65             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 6.39/6.65  thf('17', plain,
% 6.39/6.65      (![X32 : $i, X33 : $i, X34 : $i]:
% 6.39/6.65         (~ (zip_tseitin_0 @ X32 @ X33)
% 6.39/6.65          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 6.39/6.65          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 6.39/6.65      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.39/6.65  thf('18', plain,
% 6.39/6.65      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 6.39/6.65        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 6.39/6.65      inference('sup-', [status(thm)], ['16', '17'])).
% 6.39/6.65  thf('19', plain,
% 6.39/6.65      (![X0 : $i]:
% 6.39/6.65         (((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0))
% 6.39/6.65          | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 6.39/6.65      inference('sup-', [status(thm)], ['15', '18'])).
% 6.39/6.65  thf('20', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 6.39/6.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.39/6.65  thf('21', plain,
% 6.39/6.65      (![X29 : $i, X30 : $i, X31 : $i]:
% 6.39/6.65         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 6.39/6.65          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 6.39/6.65          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 6.39/6.65      inference('cnf', [status(esa)], [zf_stmt_3])).
% 6.39/6.65  thf('22', plain,
% 6.39/6.65      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 6.39/6.65        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 6.39/6.65      inference('sup-', [status(thm)], ['20', '21'])).
% 6.39/6.65  thf('23', plain,
% 6.39/6.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.39/6.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.39/6.65  thf('24', plain,
% 6.39/6.65      (![X20 : $i, X21 : $i, X22 : $i]:
% 6.39/6.65         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 6.39/6.65          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 6.39/6.65      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.39/6.65  thf('25', plain,
% 6.39/6.65      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 6.39/6.65      inference('sup-', [status(thm)], ['23', '24'])).
% 6.39/6.65  thf('26', plain,
% 6.39/6.65      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 6.39/6.65        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 6.39/6.65      inference('demod', [status(thm)], ['22', '25'])).
% 6.39/6.65  thf('27', plain,
% 6.39/6.65      (![X0 : $i]:
% 6.39/6.65         (((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0))
% 6.39/6.65          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 6.39/6.65      inference('sup-', [status(thm)], ['19', '26'])).
% 6.39/6.65  thf('28', plain,
% 6.39/6.65      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.39/6.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.39/6.65  thf('29', plain,
% 6.39/6.65      (((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ k1_xboole_0))
% 6.39/6.65        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 6.39/6.65      inference('sup+', [status(thm)], ['27', '28'])).
% 6.39/6.65  thf('30', plain,
% 6.39/6.65      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 6.39/6.65      inference('simplify', [status(thm)], ['13'])).
% 6.39/6.65  thf('31', plain,
% 6.39/6.65      (![X20 : $i, X21 : $i, X22 : $i]:
% 6.39/6.65         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 6.39/6.65          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 6.39/6.65      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.39/6.65  thf('32', plain,
% 6.39/6.65      (![X0 : $i, X1 : $i]:
% 6.39/6.65         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 6.39/6.65          | ((k1_relset_1 @ X0 @ k1_xboole_0 @ X1) = (k1_relat_1 @ X1)))),
% 6.39/6.65      inference('sup-', [status(thm)], ['30', '31'])).
% 6.39/6.65  thf('33', plain,
% 6.39/6.65      (![X0 : $i]:
% 6.39/6.65         (((sk_A) = (k1_relat_1 @ sk_D))
% 6.39/6.65          | ((k1_relset_1 @ X0 @ k1_xboole_0 @ sk_C_2) = (k1_relat_1 @ sk_C_2)))),
% 6.39/6.65      inference('sup-', [status(thm)], ['29', '32'])).
% 6.39/6.65  thf('34', plain,
% 6.39/6.65      ((((k1_relat_1 @ k1_xboole_0) = (k1_relat_1 @ sk_C_2))
% 6.39/6.65        | ~ (v1_xboole_0 @ sk_C_2)
% 6.39/6.65        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 6.39/6.65      inference('sup+', [status(thm)], ['11', '33'])).
% 6.39/6.65  thf('35', plain,
% 6.39/6.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.39/6.65         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 6.39/6.65      inference('sup+', [status(thm)], ['12', '14'])).
% 6.39/6.65  thf('36', plain,
% 6.39/6.65      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 6.39/6.65      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.39/6.65  thf('37', plain,
% 6.39/6.65      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.39/6.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.39/6.65  thf(l3_subset_1, axiom,
% 6.39/6.65    (![A:$i,B:$i]:
% 6.39/6.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.39/6.65       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 6.39/6.65  thf('38', plain,
% 6.39/6.65      (![X8 : $i, X9 : $i, X10 : $i]:
% 6.39/6.65         (~ (r2_hidden @ X8 @ X9)
% 6.39/6.65          | (r2_hidden @ X8 @ X10)
% 6.39/6.65          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 6.39/6.65      inference('cnf', [status(esa)], [l3_subset_1])).
% 6.39/6.65  thf('39', plain,
% 6.39/6.65      (![X0 : $i]:
% 6.39/6.65         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 6.39/6.65          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 6.39/6.65      inference('sup-', [status(thm)], ['37', '38'])).
% 6.39/6.65  thf('40', plain,
% 6.39/6.65      (((v1_xboole_0 @ sk_C_2)
% 6.39/6.65        | (r2_hidden @ (sk_B @ sk_C_2) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.39/6.65      inference('sup-', [status(thm)], ['36', '39'])).
% 6.39/6.65  thf('41', plain,
% 6.39/6.65      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 6.39/6.65      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.39/6.65  thf('42', plain,
% 6.39/6.65      (((v1_xboole_0 @ sk_C_2)
% 6.39/6.65        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.39/6.65      inference('sup-', [status(thm)], ['40', '41'])).
% 6.39/6.65  thf('43', plain,
% 6.39/6.65      (![X0 : $i]:
% 6.39/6.65         (~ (v1_xboole_0 @ k1_xboole_0)
% 6.39/6.65          | (zip_tseitin_0 @ sk_B_1 @ X0)
% 6.39/6.65          | (v1_xboole_0 @ sk_C_2))),
% 6.39/6.65      inference('sup-', [status(thm)], ['35', '42'])).
% 6.39/6.65  thf('44', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.39/6.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.39/6.65  thf('45', plain,
% 6.39/6.65      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_C_2))),
% 6.39/6.65      inference('demod', [status(thm)], ['43', '44'])).
% 6.39/6.65  thf('46', plain,
% 6.39/6.65      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 6.39/6.65        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 6.39/6.65      inference('sup-', [status(thm)], ['16', '17'])).
% 6.39/6.65  thf('47', plain,
% 6.39/6.65      (((v1_xboole_0 @ sk_C_2) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 6.39/6.65      inference('sup-', [status(thm)], ['45', '46'])).
% 6.39/6.65  thf('48', plain,
% 6.39/6.65      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 6.39/6.65        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 6.39/6.65      inference('demod', [status(thm)], ['22', '25'])).
% 6.39/6.65  thf('49', plain, (((v1_xboole_0 @ sk_C_2) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 6.39/6.65      inference('sup-', [status(thm)], ['47', '48'])).
% 6.39/6.65  thf('50', plain,
% 6.39/6.65      ((((sk_A) = (k1_relat_1 @ sk_D))
% 6.39/6.65        | ((k1_relat_1 @ k1_xboole_0) = (k1_relat_1 @ sk_C_2)))),
% 6.39/6.65      inference('clc', [status(thm)], ['34', '49'])).
% 6.39/6.65  thf('51', plain,
% 6.39/6.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.39/6.65         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 6.39/6.65      inference('sup+', [status(thm)], ['12', '14'])).
% 6.39/6.65  thf('52', plain,
% 6.39/6.65      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.39/6.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.39/6.65  thf('53', plain,
% 6.39/6.65      (![X32 : $i, X33 : $i, X34 : $i]:
% 6.39/6.65         (~ (zip_tseitin_0 @ X32 @ X33)
% 6.39/6.65          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 6.39/6.65          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 6.39/6.65      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.39/6.65  thf('54', plain,
% 6.39/6.65      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 6.39/6.65        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 6.39/6.65      inference('sup-', [status(thm)], ['52', '53'])).
% 6.39/6.65  thf('55', plain,
% 6.39/6.65      (![X0 : $i]:
% 6.39/6.65         (((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0))
% 6.39/6.65          | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 6.39/6.65      inference('sup-', [status(thm)], ['51', '54'])).
% 6.39/6.65  thf('56', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 6.39/6.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.39/6.65  thf('57', plain,
% 6.39/6.65      (![X29 : $i, X30 : $i, X31 : $i]:
% 6.39/6.65         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 6.39/6.65          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 6.39/6.65          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 6.39/6.65      inference('cnf', [status(esa)], [zf_stmt_3])).
% 6.39/6.65  thf('58', plain,
% 6.39/6.65      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 6.39/6.65        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 6.39/6.65      inference('sup-', [status(thm)], ['56', '57'])).
% 6.39/6.65  thf('59', plain,
% 6.39/6.65      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.39/6.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.39/6.65  thf('60', plain,
% 6.39/6.65      (![X20 : $i, X21 : $i, X22 : $i]:
% 6.39/6.65         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 6.39/6.65          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 6.39/6.65      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.39/6.65  thf('61', plain,
% 6.39/6.65      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 6.39/6.65      inference('sup-', [status(thm)], ['59', '60'])).
% 6.39/6.65  thf('62', plain,
% 6.39/6.65      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 6.39/6.65        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 6.39/6.65      inference('demod', [status(thm)], ['58', '61'])).
% 6.39/6.65  thf('63', plain,
% 6.39/6.65      (![X0 : $i]:
% 6.39/6.65         (((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0))
% 6.39/6.65          | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 6.39/6.65      inference('sup-', [status(thm)], ['55', '62'])).
% 6.39/6.65  thf('64', plain,
% 6.39/6.65      (![X0 : $i, X1 : $i]:
% 6.39/6.65         ((r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 6.39/6.65          | ((X1) = (X0))
% 6.39/6.65          | ~ (v1_xboole_0 @ X0))),
% 6.39/6.65      inference('sup-', [status(thm)], ['2', '3'])).
% 6.39/6.65  thf('65', plain,
% 6.39/6.65      (![X0 : $i]:
% 6.39/6.65         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 6.39/6.65          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 6.39/6.65      inference('sup-', [status(thm)], ['37', '38'])).
% 6.39/6.65  thf('66', plain,
% 6.39/6.65      (![X0 : $i]:
% 6.39/6.65         (~ (v1_xboole_0 @ X0)
% 6.39/6.65          | ((sk_C_2) = (X0))
% 6.39/6.65          | (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.39/6.65      inference('sup-', [status(thm)], ['64', '65'])).
% 6.39/6.65  thf('67', plain,
% 6.39/6.65      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 6.39/6.65      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.39/6.65  thf('68', plain,
% 6.39/6.65      (![X0 : $i]:
% 6.39/6.65         (((sk_C_2) = (X0))
% 6.39/6.65          | ~ (v1_xboole_0 @ X0)
% 6.39/6.65          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.39/6.65      inference('sup-', [status(thm)], ['66', '67'])).
% 6.39/6.65  thf('69', plain,
% 6.39/6.65      (![X0 : $i]:
% 6.39/6.65         (~ (v1_xboole_0 @ k1_xboole_0)
% 6.39/6.65          | ((sk_A) = (k1_relat_1 @ sk_C_2))
% 6.39/6.65          | ~ (v1_xboole_0 @ X0)
% 6.39/6.65          | ((sk_C_2) = (X0)))),
% 6.39/6.65      inference('sup-', [status(thm)], ['63', '68'])).
% 6.39/6.65  thf('70', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.39/6.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.39/6.65  thf('71', plain,
% 6.39/6.65      (![X0 : $i]:
% 6.39/6.65         (((sk_A) = (k1_relat_1 @ sk_C_2))
% 6.39/6.65          | ~ (v1_xboole_0 @ X0)
% 6.39/6.65          | ((sk_C_2) = (X0)))),
% 6.39/6.65      inference('demod', [status(thm)], ['69', '70'])).
% 6.39/6.65  thf('72', plain,
% 6.39/6.65      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 6.39/6.65      inference('sup-', [status(thm)], ['1', '6'])).
% 6.39/6.65  thf('73', plain,
% 6.39/6.65      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 6.39/6.65      inference('sup-', [status(thm)], ['1', '6'])).
% 6.39/6.65  thf('74', plain,
% 6.39/6.65      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 6.39/6.65      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.39/6.65  thf(reflexivity_r2_relset_1, axiom,
% 6.39/6.65    (![A:$i,B:$i,C:$i,D:$i]:
% 6.39/6.65     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.39/6.65         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.39/6.65       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 6.39/6.65  thf('75', plain,
% 6.39/6.65      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 6.39/6.65         ((r2_relset_1 @ X23 @ X24 @ X25 @ X25)
% 6.39/6.65          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 6.39/6.65          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 6.39/6.65      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 6.39/6.65  thf('76', plain,
% 6.39/6.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.39/6.65         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 6.39/6.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 6.39/6.65      inference('condensation', [status(thm)], ['75'])).
% 6.39/6.65  thf('77', plain,
% 6.39/6.65      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 6.39/6.65      inference('sup-', [status(thm)], ['74', '76'])).
% 6.39/6.65  thf('78', plain,
% 6.39/6.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.39/6.65         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 6.39/6.65      inference('sup+', [status(thm)], ['73', '77'])).
% 6.39/6.65  thf('79', plain,
% 6.39/6.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.39/6.65         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 6.39/6.65          | ~ (v1_xboole_0 @ X0)
% 6.39/6.65          | ~ (v1_xboole_0 @ X1))),
% 6.39/6.65      inference('sup+', [status(thm)], ['72', '78'])).
% 6.39/6.65  thf('80', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 6.39/6.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.39/6.65  thf('81', plain, ((~ (v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_D))),
% 6.39/6.65      inference('sup-', [status(thm)], ['79', '80'])).
% 6.39/6.65  thf('82', plain,
% 6.39/6.65      (![X0 : $i]:
% 6.39/6.65         (~ (v1_xboole_0 @ X0)
% 6.39/6.65          | ~ (v1_xboole_0 @ X0)
% 6.39/6.65          | ((sk_A) = (k1_relat_1 @ sk_C_2))
% 6.39/6.65          | ~ (v1_xboole_0 @ sk_D))),
% 6.39/6.65      inference('sup-', [status(thm)], ['71', '81'])).
% 6.39/6.65  thf('83', plain,
% 6.39/6.65      (![X0 : $i]:
% 6.39/6.65         (~ (v1_xboole_0 @ sk_D)
% 6.39/6.65          | ((sk_A) = (k1_relat_1 @ sk_C_2))
% 6.39/6.65          | ~ (v1_xboole_0 @ X0))),
% 6.39/6.65      inference('simplify', [status(thm)], ['82'])).
% 6.39/6.65  thf('84', plain,
% 6.39/6.65      ((~ (v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 6.39/6.65      inference('condensation', [status(thm)], ['83'])).
% 6.39/6.65  thf('85', plain,
% 6.39/6.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.39/6.65         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 6.39/6.65      inference('sup+', [status(thm)], ['12', '14'])).
% 6.39/6.65  thf('86', plain,
% 6.39/6.65      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 6.39/6.65      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.39/6.65  thf('87', plain,
% 6.39/6.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.39/6.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.39/6.65  thf('88', plain,
% 6.39/6.65      (![X8 : $i, X9 : $i, X10 : $i]:
% 6.39/6.65         (~ (r2_hidden @ X8 @ X9)
% 6.39/6.65          | (r2_hidden @ X8 @ X10)
% 6.39/6.65          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 6.39/6.65      inference('cnf', [status(esa)], [l3_subset_1])).
% 6.39/6.65  thf('89', plain,
% 6.39/6.65      (![X0 : $i]:
% 6.39/6.65         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 6.39/6.65          | ~ (r2_hidden @ X0 @ sk_D))),
% 6.39/6.65      inference('sup-', [status(thm)], ['87', '88'])).
% 6.39/6.65  thf('90', plain,
% 6.39/6.65      (((v1_xboole_0 @ sk_D)
% 6.39/6.65        | (r2_hidden @ (sk_B @ sk_D) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.39/6.65      inference('sup-', [status(thm)], ['86', '89'])).
% 6.39/6.65  thf('91', plain,
% 6.39/6.65      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 6.39/6.65      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.39/6.65  thf('92', plain,
% 6.39/6.65      (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.39/6.65      inference('sup-', [status(thm)], ['90', '91'])).
% 6.39/6.65  thf('93', plain,
% 6.39/6.65      (![X0 : $i]:
% 6.39/6.65         (~ (v1_xboole_0 @ k1_xboole_0)
% 6.39/6.65          | (zip_tseitin_0 @ sk_B_1 @ X0)
% 6.39/6.65          | (v1_xboole_0 @ sk_D))),
% 6.39/6.65      inference('sup-', [status(thm)], ['85', '92'])).
% 6.39/6.65  thf('94', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.39/6.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.39/6.65  thf('95', plain,
% 6.39/6.65      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_D))),
% 6.39/6.65      inference('demod', [status(thm)], ['93', '94'])).
% 6.39/6.65  thf('96', plain,
% 6.39/6.65      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 6.39/6.65        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 6.39/6.65      inference('sup-', [status(thm)], ['52', '53'])).
% 6.39/6.65  thf('97', plain,
% 6.39/6.65      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 6.39/6.65      inference('sup-', [status(thm)], ['95', '96'])).
% 6.39/6.65  thf('98', plain,
% 6.39/6.65      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 6.39/6.65        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 6.39/6.65      inference('demod', [status(thm)], ['58', '61'])).
% 6.39/6.65  thf('99', plain, (((v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 6.39/6.65      inference('sup-', [status(thm)], ['97', '98'])).
% 6.39/6.65  thf('100', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 6.39/6.65      inference('clc', [status(thm)], ['84', '99'])).
% 6.39/6.65  thf('101', plain,
% 6.39/6.65      ((((sk_A) = (k1_relat_1 @ sk_D)) | ((k1_relat_1 @ k1_xboole_0) = (sk_A)))),
% 6.39/6.65      inference('demod', [status(thm)], ['50', '100'])).
% 6.39/6.65  thf('102', plain,
% 6.39/6.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.39/6.65         (((k1_relset_1 @ X2 @ X1 @ X0) = (k1_relat_1 @ k1_xboole_0))
% 6.39/6.65          | ~ (v1_xboole_0 @ X0))),
% 6.39/6.65      inference('sup+', [status(thm)], ['7', '10'])).
% 6.39/6.65  thf('103', plain,
% 6.39/6.65      (![X0 : $i]:
% 6.39/6.65         (((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0))
% 6.39/6.65          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 6.39/6.65      inference('sup-', [status(thm)], ['19', '26'])).
% 6.39/6.65  thf('104', plain,
% 6.39/6.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.39/6.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.39/6.65  thf('105', plain,
% 6.39/6.65      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0))
% 6.39/6.65        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 6.39/6.65      inference('sup+', [status(thm)], ['103', '104'])).
% 6.39/6.65  thf('106', plain,
% 6.39/6.65      (![X0 : $i, X1 : $i]:
% 6.39/6.65         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 6.39/6.65          | ((k1_relset_1 @ X0 @ k1_xboole_0 @ X1) = (k1_relat_1 @ X1)))),
% 6.39/6.65      inference('sup-', [status(thm)], ['30', '31'])).
% 6.39/6.65  thf('107', plain,
% 6.39/6.65      (![X0 : $i]:
% 6.39/6.65         (((sk_A) = (k1_relat_1 @ sk_D))
% 6.39/6.65          | ((k1_relset_1 @ X0 @ k1_xboole_0 @ sk_D) = (k1_relat_1 @ sk_D)))),
% 6.39/6.65      inference('sup-', [status(thm)], ['105', '106'])).
% 6.39/6.65  thf('108', plain,
% 6.39/6.65      ((((k1_relat_1 @ k1_xboole_0) = (k1_relat_1 @ sk_D))
% 6.39/6.65        | ~ (v1_xboole_0 @ sk_D)
% 6.39/6.65        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 6.39/6.65      inference('sup+', [status(thm)], ['102', '107'])).
% 6.39/6.65  thf('109', plain,
% 6.39/6.65      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_D))),
% 6.39/6.65      inference('demod', [status(thm)], ['93', '94'])).
% 6.39/6.65  thf('110', plain,
% 6.39/6.65      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 6.39/6.65        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 6.39/6.65      inference('sup-', [status(thm)], ['16', '17'])).
% 6.39/6.65  thf('111', plain,
% 6.39/6.65      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 6.39/6.65      inference('sup-', [status(thm)], ['109', '110'])).
% 6.39/6.65  thf('112', plain,
% 6.39/6.65      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 6.39/6.65        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 6.39/6.65      inference('demod', [status(thm)], ['22', '25'])).
% 6.39/6.65  thf('113', plain, (((v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 6.39/6.65      inference('sup-', [status(thm)], ['111', '112'])).
% 6.39/6.65  thf('114', plain,
% 6.39/6.65      ((((sk_A) = (k1_relat_1 @ sk_D))
% 6.39/6.65        | ((k1_relat_1 @ k1_xboole_0) = (k1_relat_1 @ sk_D)))),
% 6.39/6.65      inference('clc', [status(thm)], ['108', '113'])).
% 6.39/6.65  thf('115', plain,
% 6.39/6.65      ((((k1_relat_1 @ k1_xboole_0) != (sk_A)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 6.39/6.65      inference('eq_fact', [status(thm)], ['114'])).
% 6.39/6.65  thf('116', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 6.39/6.65      inference('clc', [status(thm)], ['101', '115'])).
% 6.39/6.65  thf('117', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 6.39/6.65      inference('clc', [status(thm)], ['84', '99'])).
% 6.39/6.65  thf(t9_funct_1, axiom,
% 6.39/6.65    (![A:$i]:
% 6.39/6.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.39/6.65       ( ![B:$i]:
% 6.39/6.65         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.39/6.65           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 6.39/6.65               ( ![C:$i]:
% 6.39/6.65                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 6.39/6.65                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 6.39/6.65             ( ( A ) = ( B ) ) ) ) ) ))).
% 6.39/6.65  thf('118', plain,
% 6.39/6.65      (![X15 : $i, X16 : $i]:
% 6.39/6.65         (~ (v1_relat_1 @ X15)
% 6.39/6.65          | ~ (v1_funct_1 @ X15)
% 6.39/6.65          | ((X16) = (X15))
% 6.39/6.65          | (r2_hidden @ (sk_C_1 @ X15 @ X16) @ (k1_relat_1 @ X16))
% 6.39/6.65          | ((k1_relat_1 @ X16) != (k1_relat_1 @ X15))
% 6.39/6.65          | ~ (v1_funct_1 @ X16)
% 6.39/6.65          | ~ (v1_relat_1 @ X16))),
% 6.39/6.65      inference('cnf', [status(esa)], [t9_funct_1])).
% 6.39/6.65  thf('119', plain,
% 6.39/6.65      (![X0 : $i]:
% 6.39/6.65         (((sk_A) != (k1_relat_1 @ X0))
% 6.39/6.65          | ~ (v1_relat_1 @ sk_C_2)
% 6.39/6.65          | ~ (v1_funct_1 @ sk_C_2)
% 6.39/6.65          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 6.39/6.65          | ((sk_C_2) = (X0))
% 6.39/6.65          | ~ (v1_funct_1 @ X0)
% 6.39/6.65          | ~ (v1_relat_1 @ X0))),
% 6.39/6.65      inference('sup-', [status(thm)], ['117', '118'])).
% 6.39/6.65  thf('120', plain,
% 6.39/6.65      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.39/6.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.39/6.65  thf(cc1_relset_1, axiom,
% 6.39/6.65    (![A:$i,B:$i,C:$i]:
% 6.39/6.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.39/6.65       ( v1_relat_1 @ C ) ))).
% 6.39/6.65  thf('121', plain,
% 6.39/6.65      (![X17 : $i, X18 : $i, X19 : $i]:
% 6.39/6.65         ((v1_relat_1 @ X17)
% 6.39/6.65          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 6.39/6.65      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.39/6.65  thf('122', plain, ((v1_relat_1 @ sk_C_2)),
% 6.39/6.65      inference('sup-', [status(thm)], ['120', '121'])).
% 6.39/6.65  thf('123', plain, ((v1_funct_1 @ sk_C_2)),
% 6.39/6.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.39/6.65  thf('124', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 6.39/6.65      inference('clc', [status(thm)], ['84', '99'])).
% 6.39/6.65  thf('125', plain,
% 6.39/6.65      (![X0 : $i]:
% 6.39/6.65         (((sk_A) != (k1_relat_1 @ X0))
% 6.39/6.65          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A)
% 6.39/6.65          | ((sk_C_2) = (X0))
% 6.39/6.65          | ~ (v1_funct_1 @ X0)
% 6.39/6.65          | ~ (v1_relat_1 @ X0))),
% 6.39/6.65      inference('demod', [status(thm)], ['119', '122', '123', '124'])).
% 6.39/6.65  thf('126', plain,
% 6.39/6.65      ((((sk_A) != (sk_A))
% 6.39/6.65        | ~ (v1_relat_1 @ sk_D)
% 6.39/6.65        | ~ (v1_funct_1 @ sk_D)
% 6.39/6.65        | ((sk_C_2) = (sk_D))
% 6.39/6.65        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 6.39/6.65      inference('sup-', [status(thm)], ['116', '125'])).
% 6.39/6.65  thf('127', plain,
% 6.39/6.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.39/6.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.39/6.65  thf('128', plain,
% 6.39/6.65      (![X17 : $i, X18 : $i, X19 : $i]:
% 6.39/6.65         ((v1_relat_1 @ X17)
% 6.39/6.65          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 6.39/6.65      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.39/6.65  thf('129', plain, ((v1_relat_1 @ sk_D)),
% 6.39/6.65      inference('sup-', [status(thm)], ['127', '128'])).
% 6.39/6.65  thf('130', plain, ((v1_funct_1 @ sk_D)),
% 6.39/6.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.39/6.65  thf('131', plain,
% 6.39/6.65      ((((sk_A) != (sk_A))
% 6.39/6.65        | ((sk_C_2) = (sk_D))
% 6.39/6.65        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 6.39/6.65      inference('demod', [status(thm)], ['126', '129', '130'])).
% 6.39/6.65  thf('132', plain,
% 6.39/6.65      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A) | ((sk_C_2) = (sk_D)))),
% 6.39/6.65      inference('simplify', [status(thm)], ['131'])).
% 6.39/6.65  thf('133', plain,
% 6.39/6.65      (![X35 : $i]:
% 6.39/6.65         (((k1_funct_1 @ sk_C_2 @ X35) = (k1_funct_1 @ sk_D @ X35))
% 6.39/6.65          | ~ (r2_hidden @ X35 @ sk_A))),
% 6.39/6.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.39/6.65  thf('134', plain,
% 6.39/6.65      ((((sk_C_2) = (sk_D))
% 6.39/6.65        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 6.39/6.65            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 6.39/6.65      inference('sup-', [status(thm)], ['132', '133'])).
% 6.39/6.65  thf('135', plain,
% 6.39/6.65      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 6.39/6.65         = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))),
% 6.39/6.65      inference('condensation', [status(thm)], ['134'])).
% 6.39/6.65  thf('136', plain,
% 6.39/6.65      (![X15 : $i, X16 : $i]:
% 6.39/6.65         (~ (v1_relat_1 @ X15)
% 6.39/6.65          | ~ (v1_funct_1 @ X15)
% 6.39/6.65          | ((X16) = (X15))
% 6.39/6.65          | ((k1_funct_1 @ X16 @ (sk_C_1 @ X15 @ X16))
% 6.39/6.65              != (k1_funct_1 @ X15 @ (sk_C_1 @ X15 @ X16)))
% 6.39/6.65          | ((k1_relat_1 @ X16) != (k1_relat_1 @ X15))
% 6.39/6.65          | ~ (v1_funct_1 @ X16)
% 6.39/6.65          | ~ (v1_relat_1 @ X16))),
% 6.39/6.65      inference('cnf', [status(esa)], [t9_funct_1])).
% 6.39/6.65  thf('137', plain,
% 6.39/6.65      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 6.39/6.65          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 6.39/6.65        | ~ (v1_relat_1 @ sk_C_2)
% 6.39/6.65        | ~ (v1_funct_1 @ sk_C_2)
% 6.39/6.65        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 6.39/6.65        | ((sk_C_2) = (sk_D))
% 6.39/6.65        | ~ (v1_funct_1 @ sk_D)
% 6.39/6.65        | ~ (v1_relat_1 @ sk_D))),
% 6.39/6.65      inference('sup-', [status(thm)], ['135', '136'])).
% 6.39/6.65  thf('138', plain, ((v1_relat_1 @ sk_C_2)),
% 6.39/6.65      inference('sup-', [status(thm)], ['120', '121'])).
% 6.39/6.65  thf('139', plain, ((v1_funct_1 @ sk_C_2)),
% 6.39/6.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.39/6.65  thf('140', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 6.39/6.65      inference('clc', [status(thm)], ['84', '99'])).
% 6.39/6.65  thf('141', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 6.39/6.65      inference('clc', [status(thm)], ['101', '115'])).
% 6.39/6.65  thf('142', plain, ((v1_funct_1 @ sk_D)),
% 6.39/6.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.39/6.65  thf('143', plain, ((v1_relat_1 @ sk_D)),
% 6.39/6.65      inference('sup-', [status(thm)], ['127', '128'])).
% 6.39/6.65  thf('144', plain,
% 6.39/6.65      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 6.39/6.65          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 6.39/6.65        | ((sk_A) != (sk_A))
% 6.39/6.65        | ((sk_C_2) = (sk_D)))),
% 6.39/6.65      inference('demod', [status(thm)],
% 6.39/6.65                ['137', '138', '139', '140', '141', '142', '143'])).
% 6.39/6.65  thf('145', plain, (((sk_C_2) = (sk_D))),
% 6.39/6.65      inference('simplify', [status(thm)], ['144'])).
% 6.39/6.65  thf('146', plain,
% 6.39/6.65      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.39/6.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.39/6.65  thf('147', plain,
% 6.39/6.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.39/6.65         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 6.39/6.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 6.39/6.65      inference('condensation', [status(thm)], ['75'])).
% 6.39/6.65  thf('148', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2)),
% 6.39/6.65      inference('sup-', [status(thm)], ['146', '147'])).
% 6.39/6.65  thf('149', plain, ($false),
% 6.39/6.65      inference('demod', [status(thm)], ['0', '145', '148'])).
% 6.39/6.65  
% 6.39/6.65  % SZS output end Refutation
% 6.39/6.65  
% 6.39/6.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
