%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZSkwBY1YBP

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:31 EST 2020

% Result     : Theorem 2.54s
% Output     : Refutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 628 expanded)
%              Number of leaves         :   42 ( 210 expanded)
%              Depth                    :   24
%              Number of atoms          : 1045 (7091 expanded)
%              Number of equality atoms :   76 ( 337 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(t113_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ! [E: $i] :
                ( ( m1_subset_1 @ E @ A )
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
                  ( ( m1_subset_1 @ E @ A )
                 => ( ( k1_funct_1 @ C @ E )
                    = ( k1_funct_1 @ D @ E ) ) )
             => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t113_funct_2])).

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
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_2 @ X41 @ X39 @ X40 )
      | ( X39
        = ( k1_relset_1 @ X39 @ X40 @ X41 ) )
      | ~ ( zip_tseitin_1 @ X41 @ X40 @ X39 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
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
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( zip_tseitin_0 @ X42 @ X43 )
      | ( zip_tseitin_1 @ X44 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('11',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('12',plain,(
    ! [X37: $i,X38: $i] :
      ( ( zip_tseitin_0 @ X37 @ X38 )
      | ( X37 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('14',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('17',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C_2 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','21'])).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('33',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('34',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( r2_relset_1 @ X34 @ X35 @ X33 @ X36 )
      | ( X33 != X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('35',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( r2_relset_1 @ X34 @ X35 @ X36 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X3 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','37'])).

thf('39',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ~ ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['22','40'])).

thf('42',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_D )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['41','50'])).

thf('52',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['10','51'])).

thf('53',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','52'])).

thf('54',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_2 @ X41 @ X39 @ X40 )
      | ( X39
        = ( k1_relset_1 @ X39 @ X40 @ X41 ) )
      | ~ ( zip_tseitin_1 @ X41 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('56',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('59',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( zip_tseitin_0 @ X42 @ X43 )
      | ( zip_tseitin_1 @ X44 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('63',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['41','50'])).

thf('65',plain,(
    zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['60','65'])).

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

thf('67',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ( X23 = X22 )
      | ( r2_hidden @ ( sk_C_1 @ X22 @ X23 ) @ ( k1_relat_1 @ X23 ) )
      | ( ( k1_relat_1 @ X23 )
       != ( k1_relat_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('70',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('71',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['60','65'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['68','71','72','73'])).

thf('75',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['53','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('78',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['75','78','79'])).

thf('81',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['80'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('82',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ X14 @ X15 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('83',plain,
    ( ( sk_C_2 = sk_D )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X45: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X45 )
        = ( k1_funct_1 @ sk_D @ X45 ) )
      | ~ ( m1_subset_1 @ X45 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( sk_C_2 = sk_D )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ),
    inference(condensation,[status(thm)],['85'])).

thf('87',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ( X23 = X22 )
      | ( ( k1_funct_1 @ X23 @ ( sk_C_1 @ X22 @ X23 ) )
       != ( k1_funct_1 @ X22 @ ( sk_C_1 @ X22 @ X23 ) ) )
      | ( ( k1_relat_1 @ X23 )
       != ( k1_relat_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('88',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['69','70'])).

thf('90',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['60','65'])).

thf('92',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','52'])).

thf('93',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['76','77'])).

thf('95',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['88','89','90','91','92','93','94'])).

thf('96',plain,(
    sk_C_2 = sk_D ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( r2_relset_1 @ X34 @ X35 @ X36 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('99',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    $false ),
    inference(demod,[status(thm)],['0','96','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZSkwBY1YBP
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:10:39 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 2.54/2.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.54/2.78  % Solved by: fo/fo7.sh
% 2.54/2.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.54/2.78  % done 3067 iterations in 2.327s
% 2.54/2.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.54/2.78  % SZS output start Refutation
% 2.54/2.78  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.54/2.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.54/2.78  thf(sk_A_type, type, sk_A: $i).
% 2.54/2.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.54/2.78  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.54/2.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.54/2.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.54/2.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.54/2.78  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.54/2.78  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.54/2.78  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.54/2.78  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.54/2.78  thf(sk_C_2_type, type, sk_C_2: $i).
% 2.54/2.78  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.54/2.78  thf(sk_D_type, type, sk_D: $i).
% 2.54/2.78  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.54/2.78  thf(sk_B_type, type, sk_B: $i > $i).
% 2.54/2.78  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 2.54/2.78  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.54/2.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.54/2.78  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 2.54/2.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.54/2.78  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.54/2.78  thf(t113_funct_2, conjecture,
% 2.54/2.78    (![A:$i,B:$i,C:$i]:
% 2.54/2.78     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.54/2.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.54/2.78       ( ![D:$i]:
% 2.54/2.78         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.54/2.78             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.54/2.78           ( ( ![E:$i]:
% 2.54/2.78               ( ( m1_subset_1 @ E @ A ) =>
% 2.54/2.78                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 2.54/2.78             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 2.54/2.78  thf(zf_stmt_0, negated_conjecture,
% 2.54/2.78    (~( ![A:$i,B:$i,C:$i]:
% 2.54/2.78        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.54/2.78            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.54/2.78          ( ![D:$i]:
% 2.54/2.78            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.54/2.78                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.54/2.78              ( ( ![E:$i]:
% 2.54/2.78                  ( ( m1_subset_1 @ E @ A ) =>
% 2.54/2.78                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 2.54/2.78                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 2.54/2.78    inference('cnf.neg', [status(esa)], [t113_funct_2])).
% 2.54/2.78  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 2.54/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.78  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 2.54/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.78  thf(d1_funct_2, axiom,
% 2.54/2.78    (![A:$i,B:$i,C:$i]:
% 2.54/2.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.54/2.78       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.54/2.78           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.54/2.78             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.54/2.78         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.54/2.78           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.54/2.78             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.54/2.78  thf(zf_stmt_1, axiom,
% 2.54/2.78    (![C:$i,B:$i,A:$i]:
% 2.54/2.78     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.54/2.78       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.54/2.78  thf('2', plain,
% 2.54/2.78      (![X39 : $i, X40 : $i, X41 : $i]:
% 2.54/2.78         (~ (v1_funct_2 @ X41 @ X39 @ X40)
% 2.54/2.78          | ((X39) = (k1_relset_1 @ X39 @ X40 @ X41))
% 2.54/2.78          | ~ (zip_tseitin_1 @ X41 @ X40 @ X39))),
% 2.54/2.78      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.54/2.78  thf('3', plain,
% 2.54/2.78      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 2.54/2.78        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 2.54/2.78      inference('sup-', [status(thm)], ['1', '2'])).
% 2.54/2.78  thf('4', plain,
% 2.54/2.78      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.54/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.78  thf(redefinition_k1_relset_1, axiom,
% 2.54/2.78    (![A:$i,B:$i,C:$i]:
% 2.54/2.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.54/2.78       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.54/2.78  thf('5', plain,
% 2.54/2.78      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.54/2.78         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 2.54/2.78          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 2.54/2.78      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.54/2.78  thf('6', plain,
% 2.54/2.78      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 2.54/2.78      inference('sup-', [status(thm)], ['4', '5'])).
% 2.54/2.78  thf('7', plain,
% 2.54/2.78      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 2.54/2.78        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.54/2.78      inference('demod', [status(thm)], ['3', '6'])).
% 2.54/2.78  thf('8', plain,
% 2.54/2.78      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.54/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.78  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.54/2.78  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 2.54/2.78  thf(zf_stmt_4, axiom,
% 2.54/2.78    (![B:$i,A:$i]:
% 2.54/2.78     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.54/2.78       ( zip_tseitin_0 @ B @ A ) ))).
% 2.54/2.78  thf(zf_stmt_5, axiom,
% 2.54/2.78    (![A:$i,B:$i,C:$i]:
% 2.54/2.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.54/2.78       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.54/2.78         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.54/2.78           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.54/2.78             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.54/2.78  thf('9', plain,
% 2.54/2.78      (![X42 : $i, X43 : $i, X44 : $i]:
% 2.54/2.78         (~ (zip_tseitin_0 @ X42 @ X43)
% 2.54/2.78          | (zip_tseitin_1 @ X44 @ X42 @ X43)
% 2.54/2.78          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42))))),
% 2.54/2.78      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.54/2.78  thf('10', plain,
% 2.54/2.78      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 2.54/2.78        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 2.54/2.78      inference('sup-', [status(thm)], ['8', '9'])).
% 2.54/2.78  thf(d1_xboole_0, axiom,
% 2.54/2.78    (![A:$i]:
% 2.54/2.78     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.54/2.78  thf('11', plain,
% 2.54/2.78      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.54/2.78      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.54/2.78  thf('12', plain,
% 2.54/2.78      (![X37 : $i, X38 : $i]:
% 2.54/2.78         ((zip_tseitin_0 @ X37 @ X38) | ((X37) = (k1_xboole_0)))),
% 2.54/2.78      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.54/2.78  thf(t113_zfmisc_1, axiom,
% 2.54/2.78    (![A:$i,B:$i]:
% 2.54/2.78     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.54/2.78       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.54/2.78  thf('13', plain,
% 2.54/2.78      (![X11 : $i, X12 : $i]:
% 2.54/2.78         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 2.54/2.78          | ((X12) != (k1_xboole_0)))),
% 2.54/2.78      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.54/2.78  thf('14', plain,
% 2.54/2.78      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 2.54/2.78      inference('simplify', [status(thm)], ['13'])).
% 2.54/2.78  thf('15', plain,
% 2.54/2.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.54/2.78         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 2.54/2.78      inference('sup+', [status(thm)], ['12', '14'])).
% 2.54/2.78  thf('16', plain,
% 2.54/2.78      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.54/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.78  thf(t5_subset, axiom,
% 2.54/2.78    (![A:$i,B:$i,C:$i]:
% 2.54/2.78     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 2.54/2.78          ( v1_xboole_0 @ C ) ) ))).
% 2.54/2.78  thf('17', plain,
% 2.54/2.78      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.54/2.78         (~ (r2_hidden @ X19 @ X20)
% 2.54/2.78          | ~ (v1_xboole_0 @ X21)
% 2.54/2.78          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 2.54/2.78      inference('cnf', [status(esa)], [t5_subset])).
% 2.54/2.78  thf('18', plain,
% 2.54/2.78      (![X0 : $i]:
% 2.54/2.78         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 2.54/2.78          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 2.54/2.78      inference('sup-', [status(thm)], ['16', '17'])).
% 2.54/2.78  thf('19', plain,
% 2.54/2.78      (![X0 : $i, X1 : $i]:
% 2.54/2.78         (~ (v1_xboole_0 @ k1_xboole_0)
% 2.54/2.78          | (zip_tseitin_0 @ sk_B_1 @ X1)
% 2.54/2.78          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 2.54/2.78      inference('sup-', [status(thm)], ['15', '18'])).
% 2.54/2.78  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.54/2.78  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.54/2.78      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.54/2.78  thf('21', plain,
% 2.54/2.78      (![X0 : $i, X1 : $i]:
% 2.54/2.78         ((zip_tseitin_0 @ sk_B_1 @ X1) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 2.54/2.78      inference('demod', [status(thm)], ['19', '20'])).
% 2.54/2.78  thf('22', plain,
% 2.54/2.78      (![X0 : $i]: ((v1_xboole_0 @ sk_C_2) | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 2.54/2.78      inference('sup-', [status(thm)], ['11', '21'])).
% 2.54/2.78  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.54/2.78      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.54/2.78  thf(d3_tarski, axiom,
% 2.54/2.78    (![A:$i,B:$i]:
% 2.54/2.78     ( ( r1_tarski @ A @ B ) <=>
% 2.54/2.78       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.54/2.78  thf('24', plain,
% 2.54/2.78      (![X4 : $i, X6 : $i]:
% 2.54/2.78         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 2.54/2.78      inference('cnf', [status(esa)], [d3_tarski])).
% 2.54/2.78  thf('25', plain,
% 2.54/2.78      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.54/2.78      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.54/2.78  thf('26', plain,
% 2.54/2.78      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 2.54/2.78      inference('sup-', [status(thm)], ['24', '25'])).
% 2.54/2.78  thf('27', plain,
% 2.54/2.78      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 2.54/2.78      inference('sup-', [status(thm)], ['24', '25'])).
% 2.54/2.78  thf(d10_xboole_0, axiom,
% 2.54/2.78    (![A:$i,B:$i]:
% 2.54/2.78     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.54/2.78  thf('28', plain,
% 2.54/2.78      (![X7 : $i, X9 : $i]:
% 2.54/2.78         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 2.54/2.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.54/2.78  thf('29', plain,
% 2.54/2.78      (![X0 : $i, X1 : $i]:
% 2.54/2.78         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 2.54/2.78      inference('sup-', [status(thm)], ['27', '28'])).
% 2.54/2.78  thf('30', plain,
% 2.54/2.78      (![X0 : $i, X1 : $i]:
% 2.54/2.78         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.54/2.78      inference('sup-', [status(thm)], ['26', '29'])).
% 2.54/2.78  thf('31', plain,
% 2.54/2.78      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 2.54/2.78      inference('sup-', [status(thm)], ['23', '30'])).
% 2.54/2.78  thf('32', plain,
% 2.54/2.78      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 2.54/2.78      inference('sup-', [status(thm)], ['23', '30'])).
% 2.54/2.78  thf(t4_subset_1, axiom,
% 2.54/2.78    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 2.54/2.78  thf('33', plain,
% 2.54/2.78      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 2.54/2.78      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.54/2.78  thf(redefinition_r2_relset_1, axiom,
% 2.54/2.78    (![A:$i,B:$i,C:$i,D:$i]:
% 2.54/2.78     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.54/2.78         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.54/2.78       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.54/2.78  thf('34', plain,
% 2.54/2.78      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 2.54/2.78         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 2.54/2.78          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 2.54/2.78          | (r2_relset_1 @ X34 @ X35 @ X33 @ X36)
% 2.54/2.78          | ((X33) != (X36)))),
% 2.54/2.78      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.54/2.78  thf('35', plain,
% 2.54/2.78      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.54/2.78         ((r2_relset_1 @ X34 @ X35 @ X36 @ X36)
% 2.54/2.78          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 2.54/2.78      inference('simplify', [status(thm)], ['34'])).
% 2.54/2.78  thf('36', plain,
% 2.54/2.78      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 2.54/2.78      inference('sup-', [status(thm)], ['33', '35'])).
% 2.54/2.78  thf('37', plain,
% 2.54/2.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.54/2.78         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 2.54/2.78      inference('sup+', [status(thm)], ['32', '36'])).
% 2.54/2.78  thf('38', plain,
% 2.54/2.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.54/2.78         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 2.54/2.78          | ~ (v1_xboole_0 @ X0)
% 2.54/2.78          | ~ (v1_xboole_0 @ X1))),
% 2.54/2.78      inference('sup+', [status(thm)], ['31', '37'])).
% 2.54/2.78  thf('39', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 2.54/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.78  thf('40', plain, ((~ (v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_D))),
% 2.54/2.78      inference('sup-', [status(thm)], ['38', '39'])).
% 2.54/2.78  thf('41', plain,
% 2.54/2.78      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | ~ (v1_xboole_0 @ sk_D))),
% 2.54/2.78      inference('sup-', [status(thm)], ['22', '40'])).
% 2.54/2.78  thf('42', plain,
% 2.54/2.78      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.54/2.78      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.54/2.78  thf('43', plain,
% 2.54/2.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.54/2.78         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 2.54/2.78      inference('sup+', [status(thm)], ['12', '14'])).
% 2.54/2.78  thf('44', plain,
% 2.54/2.78      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.54/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.78  thf('45', plain,
% 2.54/2.78      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.54/2.78         (~ (r2_hidden @ X19 @ X20)
% 2.54/2.78          | ~ (v1_xboole_0 @ X21)
% 2.54/2.78          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 2.54/2.78      inference('cnf', [status(esa)], [t5_subset])).
% 2.54/2.78  thf('46', plain,
% 2.54/2.78      (![X0 : $i]:
% 2.54/2.78         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 2.54/2.78          | ~ (r2_hidden @ X0 @ sk_D))),
% 2.54/2.78      inference('sup-', [status(thm)], ['44', '45'])).
% 2.54/2.78  thf('47', plain,
% 2.54/2.78      (![X0 : $i, X1 : $i]:
% 2.54/2.78         (~ (v1_xboole_0 @ k1_xboole_0)
% 2.54/2.78          | (zip_tseitin_0 @ sk_B_1 @ X1)
% 2.54/2.78          | ~ (r2_hidden @ X0 @ sk_D))),
% 2.54/2.78      inference('sup-', [status(thm)], ['43', '46'])).
% 2.54/2.78  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.54/2.78      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.54/2.78  thf('49', plain,
% 2.54/2.78      (![X0 : $i, X1 : $i]:
% 2.54/2.78         ((zip_tseitin_0 @ sk_B_1 @ X1) | ~ (r2_hidden @ X0 @ sk_D))),
% 2.54/2.78      inference('demod', [status(thm)], ['47', '48'])).
% 2.54/2.78  thf('50', plain,
% 2.54/2.78      (![X0 : $i]: ((v1_xboole_0 @ sk_D) | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 2.54/2.78      inference('sup-', [status(thm)], ['42', '49'])).
% 2.54/2.78  thf('51', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 2.54/2.78      inference('clc', [status(thm)], ['41', '50'])).
% 2.54/2.78  thf('52', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 2.54/2.78      inference('demod', [status(thm)], ['10', '51'])).
% 2.54/2.78  thf('53', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 2.54/2.78      inference('demod', [status(thm)], ['7', '52'])).
% 2.54/2.78  thf('54', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 2.54/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.78  thf('55', plain,
% 2.54/2.78      (![X39 : $i, X40 : $i, X41 : $i]:
% 2.54/2.78         (~ (v1_funct_2 @ X41 @ X39 @ X40)
% 2.54/2.78          | ((X39) = (k1_relset_1 @ X39 @ X40 @ X41))
% 2.54/2.78          | ~ (zip_tseitin_1 @ X41 @ X40 @ X39))),
% 2.54/2.78      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.54/2.78  thf('56', plain,
% 2.54/2.78      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 2.54/2.78        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 2.54/2.78      inference('sup-', [status(thm)], ['54', '55'])).
% 2.54/2.78  thf('57', plain,
% 2.54/2.78      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.54/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.78  thf('58', plain,
% 2.54/2.78      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.54/2.78         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 2.54/2.78          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 2.54/2.78      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.54/2.78  thf('59', plain,
% 2.54/2.78      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 2.54/2.78      inference('sup-', [status(thm)], ['57', '58'])).
% 2.54/2.78  thf('60', plain,
% 2.54/2.78      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 2.54/2.78        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 2.54/2.78      inference('demod', [status(thm)], ['56', '59'])).
% 2.54/2.78  thf('61', plain,
% 2.54/2.78      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.54/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.78  thf('62', plain,
% 2.54/2.78      (![X42 : $i, X43 : $i, X44 : $i]:
% 2.54/2.78         (~ (zip_tseitin_0 @ X42 @ X43)
% 2.54/2.78          | (zip_tseitin_1 @ X44 @ X42 @ X43)
% 2.54/2.78          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42))))),
% 2.54/2.78      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.54/2.78  thf('63', plain,
% 2.54/2.78      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 2.54/2.78        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 2.54/2.78      inference('sup-', [status(thm)], ['61', '62'])).
% 2.54/2.78  thf('64', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 2.54/2.78      inference('clc', [status(thm)], ['41', '50'])).
% 2.54/2.78  thf('65', plain, ((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)),
% 2.54/2.78      inference('demod', [status(thm)], ['63', '64'])).
% 2.54/2.78  thf('66', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 2.54/2.78      inference('demod', [status(thm)], ['60', '65'])).
% 2.54/2.78  thf(t9_funct_1, axiom,
% 2.54/2.78    (![A:$i]:
% 2.54/2.78     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.54/2.78       ( ![B:$i]:
% 2.54/2.78         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.54/2.78           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 2.54/2.78               ( ![C:$i]:
% 2.54/2.78                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 2.54/2.78                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 2.54/2.78             ( ( A ) = ( B ) ) ) ) ) ))).
% 2.54/2.78  thf('67', plain,
% 2.54/2.78      (![X22 : $i, X23 : $i]:
% 2.54/2.78         (~ (v1_relat_1 @ X22)
% 2.54/2.78          | ~ (v1_funct_1 @ X22)
% 2.54/2.78          | ((X23) = (X22))
% 2.54/2.78          | (r2_hidden @ (sk_C_1 @ X22 @ X23) @ (k1_relat_1 @ X23))
% 2.54/2.78          | ((k1_relat_1 @ X23) != (k1_relat_1 @ X22))
% 2.54/2.78          | ~ (v1_funct_1 @ X23)
% 2.54/2.78          | ~ (v1_relat_1 @ X23))),
% 2.54/2.78      inference('cnf', [status(esa)], [t9_funct_1])).
% 2.54/2.78  thf('68', plain,
% 2.54/2.78      (![X0 : $i]:
% 2.54/2.78         (((sk_A) != (k1_relat_1 @ X0))
% 2.54/2.78          | ~ (v1_relat_1 @ sk_C_2)
% 2.54/2.78          | ~ (v1_funct_1 @ sk_C_2)
% 2.54/2.78          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 2.54/2.78          | ((sk_C_2) = (X0))
% 2.54/2.78          | ~ (v1_funct_1 @ X0)
% 2.54/2.78          | ~ (v1_relat_1 @ X0))),
% 2.54/2.78      inference('sup-', [status(thm)], ['66', '67'])).
% 2.54/2.78  thf('69', plain,
% 2.54/2.78      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.54/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.78  thf(cc1_relset_1, axiom,
% 2.54/2.78    (![A:$i,B:$i,C:$i]:
% 2.54/2.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.54/2.78       ( v1_relat_1 @ C ) ))).
% 2.54/2.78  thf('70', plain,
% 2.54/2.78      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.54/2.78         ((v1_relat_1 @ X24)
% 2.54/2.78          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 2.54/2.78      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.54/2.78  thf('71', plain, ((v1_relat_1 @ sk_C_2)),
% 2.54/2.78      inference('sup-', [status(thm)], ['69', '70'])).
% 2.54/2.78  thf('72', plain, ((v1_funct_1 @ sk_C_2)),
% 2.54/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.78  thf('73', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 2.54/2.78      inference('demod', [status(thm)], ['60', '65'])).
% 2.54/2.78  thf('74', plain,
% 2.54/2.78      (![X0 : $i]:
% 2.54/2.78         (((sk_A) != (k1_relat_1 @ X0))
% 2.54/2.78          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A)
% 2.54/2.78          | ((sk_C_2) = (X0))
% 2.54/2.78          | ~ (v1_funct_1 @ X0)
% 2.54/2.78          | ~ (v1_relat_1 @ X0))),
% 2.54/2.78      inference('demod', [status(thm)], ['68', '71', '72', '73'])).
% 2.54/2.78  thf('75', plain,
% 2.54/2.78      ((((sk_A) != (sk_A))
% 2.54/2.78        | ~ (v1_relat_1 @ sk_D)
% 2.54/2.78        | ~ (v1_funct_1 @ sk_D)
% 2.54/2.78        | ((sk_C_2) = (sk_D))
% 2.54/2.78        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 2.54/2.78      inference('sup-', [status(thm)], ['53', '74'])).
% 2.54/2.78  thf('76', plain,
% 2.54/2.78      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.54/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.78  thf('77', plain,
% 2.54/2.78      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.54/2.78         ((v1_relat_1 @ X24)
% 2.54/2.78          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 2.54/2.78      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.54/2.78  thf('78', plain, ((v1_relat_1 @ sk_D)),
% 2.54/2.78      inference('sup-', [status(thm)], ['76', '77'])).
% 2.54/2.78  thf('79', plain, ((v1_funct_1 @ sk_D)),
% 2.54/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.78  thf('80', plain,
% 2.54/2.78      ((((sk_A) != (sk_A))
% 2.54/2.78        | ((sk_C_2) = (sk_D))
% 2.54/2.78        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 2.54/2.78      inference('demod', [status(thm)], ['75', '78', '79'])).
% 2.54/2.78  thf('81', plain,
% 2.54/2.78      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A) | ((sk_C_2) = (sk_D)))),
% 2.54/2.78      inference('simplify', [status(thm)], ['80'])).
% 2.54/2.78  thf(t1_subset, axiom,
% 2.54/2.78    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 2.54/2.78  thf('82', plain,
% 2.54/2.78      (![X14 : $i, X15 : $i]:
% 2.54/2.78         ((m1_subset_1 @ X14 @ X15) | ~ (r2_hidden @ X14 @ X15))),
% 2.54/2.78      inference('cnf', [status(esa)], [t1_subset])).
% 2.54/2.78  thf('83', plain,
% 2.54/2.78      ((((sk_C_2) = (sk_D)) | (m1_subset_1 @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 2.54/2.78      inference('sup-', [status(thm)], ['81', '82'])).
% 2.54/2.78  thf('84', plain,
% 2.54/2.78      (![X45 : $i]:
% 2.54/2.78         (((k1_funct_1 @ sk_C_2 @ X45) = (k1_funct_1 @ sk_D @ X45))
% 2.54/2.78          | ~ (m1_subset_1 @ X45 @ sk_A))),
% 2.54/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.78  thf('85', plain,
% 2.54/2.78      ((((sk_C_2) = (sk_D))
% 2.54/2.78        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 2.54/2.78            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 2.54/2.78      inference('sup-', [status(thm)], ['83', '84'])).
% 2.54/2.78  thf('86', plain,
% 2.54/2.78      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 2.54/2.78         = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))),
% 2.54/2.78      inference('condensation', [status(thm)], ['85'])).
% 2.54/2.78  thf('87', plain,
% 2.54/2.78      (![X22 : $i, X23 : $i]:
% 2.54/2.78         (~ (v1_relat_1 @ X22)
% 2.54/2.78          | ~ (v1_funct_1 @ X22)
% 2.54/2.78          | ((X23) = (X22))
% 2.54/2.78          | ((k1_funct_1 @ X23 @ (sk_C_1 @ X22 @ X23))
% 2.54/2.78              != (k1_funct_1 @ X22 @ (sk_C_1 @ X22 @ X23)))
% 2.54/2.78          | ((k1_relat_1 @ X23) != (k1_relat_1 @ X22))
% 2.54/2.78          | ~ (v1_funct_1 @ X23)
% 2.54/2.78          | ~ (v1_relat_1 @ X23))),
% 2.54/2.78      inference('cnf', [status(esa)], [t9_funct_1])).
% 2.54/2.78  thf('88', plain,
% 2.54/2.78      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 2.54/2.78          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 2.54/2.78        | ~ (v1_relat_1 @ sk_C_2)
% 2.54/2.78        | ~ (v1_funct_1 @ sk_C_2)
% 2.54/2.78        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 2.54/2.78        | ((sk_C_2) = (sk_D))
% 2.54/2.78        | ~ (v1_funct_1 @ sk_D)
% 2.54/2.78        | ~ (v1_relat_1 @ sk_D))),
% 2.54/2.78      inference('sup-', [status(thm)], ['86', '87'])).
% 2.54/2.78  thf('89', plain, ((v1_relat_1 @ sk_C_2)),
% 2.54/2.78      inference('sup-', [status(thm)], ['69', '70'])).
% 2.54/2.78  thf('90', plain, ((v1_funct_1 @ sk_C_2)),
% 2.54/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.78  thf('91', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 2.54/2.78      inference('demod', [status(thm)], ['60', '65'])).
% 2.54/2.78  thf('92', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 2.54/2.78      inference('demod', [status(thm)], ['7', '52'])).
% 2.54/2.78  thf('93', plain, ((v1_funct_1 @ sk_D)),
% 2.54/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.78  thf('94', plain, ((v1_relat_1 @ sk_D)),
% 2.54/2.78      inference('sup-', [status(thm)], ['76', '77'])).
% 2.54/2.78  thf('95', plain,
% 2.54/2.78      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 2.54/2.78          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 2.54/2.78        | ((sk_A) != (sk_A))
% 2.54/2.78        | ((sk_C_2) = (sk_D)))),
% 2.54/2.78      inference('demod', [status(thm)],
% 2.54/2.78                ['88', '89', '90', '91', '92', '93', '94'])).
% 2.54/2.78  thf('96', plain, (((sk_C_2) = (sk_D))),
% 2.54/2.78      inference('simplify', [status(thm)], ['95'])).
% 2.54/2.78  thf('97', plain,
% 2.54/2.78      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.54/2.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.78  thf('98', plain,
% 2.54/2.78      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.54/2.78         ((r2_relset_1 @ X34 @ X35 @ X36 @ X36)
% 2.54/2.78          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 2.54/2.78      inference('simplify', [status(thm)], ['34'])).
% 2.54/2.78  thf('99', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2)),
% 2.54/2.78      inference('sup-', [status(thm)], ['97', '98'])).
% 2.54/2.78  thf('100', plain, ($false),
% 2.54/2.78      inference('demod', [status(thm)], ['0', '96', '99'])).
% 2.54/2.78  
% 2.54/2.78  % SZS output end Refutation
% 2.54/2.78  
% 2.54/2.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
