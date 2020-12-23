%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9gkyZlVscc

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:34 EST 2020

% Result     : Theorem 1.94s
% Output     : Refutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 559 expanded)
%              Number of leaves         :   38 ( 183 expanded)
%              Depth                    :   21
%              Number of atoms          : 1024 (8321 expanded)
%              Number of equality atoms :   82 ( 366 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ~ ( r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('2',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( r2_relset_1 @ X26 @ X27 @ X25 @ X28 )
      | ( X25 != X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('3',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_relset_1 @ X26 @ X27 @ X28 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    r2_relset_1 @ sk_A @ sk_B_2 @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['1','3'])).

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

thf('5',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('6',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
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

thf('9',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('14',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('16',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('17',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('21',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X19 ) ) )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('22',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['19','22'])).

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

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

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
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_C_2 = X0 ) ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_B_2 @ X0 @ sk_D )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','33'])).

thf('35',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X19 ) ) )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('38',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['34','39'])).

thf('41',plain,(
    r2_relset_1 @ sk_A @ sk_B_2 @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['1','3'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('43',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('45',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('49',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('52',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['46','53'])).

thf('55',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('56',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_C_2 = X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_B_2 @ X0 @ sk_D )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['41','60'])).

thf('62',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['46','53'])).

thf('63',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('64',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['61','64'])).

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

thf('66',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( X15 = X14 )
      | ( r2_hidden @ ( sk_C_1 @ X14 @ X15 ) @ ( k1_relat_1 @ X15 ) )
      | ( ( k1_relat_1 @ X15 )
       != ( k1_relat_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('69',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('70',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['61','64'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','70','71','72'])).

thf('74',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['40','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('77',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['74','77','78'])).

thf('80',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X37: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X37 )
        = ( k1_funct_1 @ sk_D @ X37 ) )
      | ~ ( r2_hidden @ X37 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( sk_C_2 = sk_D )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ),
    inference(condensation,[status(thm)],['82'])).

thf('84',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( X15 = X14 )
      | ( ( k1_funct_1 @ X15 @ ( sk_C_1 @ X14 @ X15 ) )
       != ( k1_funct_1 @ X14 @ ( sk_C_1 @ X14 @ X15 ) ) )
      | ( ( k1_relat_1 @ X15 )
       != ( k1_relat_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('85',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['68','69'])).

thf('87',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['61','64'])).

thf('89',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['34','39'])).

thf('90',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['75','76'])).

thf('92',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['85','86','87','88','89','90','91'])).

thf('93',plain,(
    sk_C_2 = sk_D ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_relset_1 @ X26 @ X27 @ X28 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('96',plain,(
    r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    $false ),
    inference(demod,[status(thm)],['0','93','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9gkyZlVscc
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:28:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.94/2.13  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.94/2.13  % Solved by: fo/fo7.sh
% 1.94/2.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.94/2.13  % done 1889 iterations in 1.695s
% 1.94/2.13  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.94/2.13  % SZS output start Refutation
% 1.94/2.13  thf(sk_A_type, type, sk_A: $i).
% 1.94/2.13  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.94/2.13  thf(sk_B_2_type, type, sk_B_2: $i).
% 1.94/2.13  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.94/2.13  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.94/2.13  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.94/2.13  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.94/2.13  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.94/2.13  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.94/2.13  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.94/2.13  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.94/2.13  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.94/2.13  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.94/2.13  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.94/2.13  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.94/2.13  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.94/2.13  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.94/2.13  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.94/2.13  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.94/2.13  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.94/2.13  thf(sk_D_type, type, sk_D: $i).
% 1.94/2.13  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.94/2.13  thf(t18_funct_2, conjecture,
% 1.94/2.13    (![A:$i,B:$i,C:$i]:
% 1.94/2.13     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.94/2.13         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.94/2.13       ( ![D:$i]:
% 1.94/2.13         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.94/2.13             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.94/2.13           ( ( ![E:$i]:
% 1.94/2.13               ( ( r2_hidden @ E @ A ) =>
% 1.94/2.13                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 1.94/2.13             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 1.94/2.13  thf(zf_stmt_0, negated_conjecture,
% 1.94/2.13    (~( ![A:$i,B:$i,C:$i]:
% 1.94/2.13        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.94/2.13            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.94/2.13          ( ![D:$i]:
% 1.94/2.13            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.94/2.13                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.94/2.13              ( ( ![E:$i]:
% 1.94/2.13                  ( ( r2_hidden @ E @ A ) =>
% 1.94/2.13                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 1.94/2.13                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 1.94/2.13    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 1.94/2.13  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_2 @ sk_D)),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf('1', plain,
% 1.94/2.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf(redefinition_r2_relset_1, axiom,
% 1.94/2.13    (![A:$i,B:$i,C:$i,D:$i]:
% 1.94/2.13     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.94/2.13         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.94/2.13       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.94/2.13  thf('2', plain,
% 1.94/2.13      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.94/2.13         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.94/2.13          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.94/2.13          | (r2_relset_1 @ X26 @ X27 @ X25 @ X28)
% 1.94/2.13          | ((X25) != (X28)))),
% 1.94/2.13      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.94/2.13  thf('3', plain,
% 1.94/2.13      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.94/2.13         ((r2_relset_1 @ X26 @ X27 @ X28 @ X28)
% 1.94/2.13          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.94/2.13      inference('simplify', [status(thm)], ['2'])).
% 1.94/2.13  thf('4', plain, ((r2_relset_1 @ sk_A @ sk_B_2 @ sk_D @ sk_D)),
% 1.94/2.13      inference('sup-', [status(thm)], ['1', '3'])).
% 1.94/2.13  thf(d1_funct_2, axiom,
% 1.94/2.13    (![A:$i,B:$i,C:$i]:
% 1.94/2.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.94/2.13       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.94/2.13           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.94/2.13             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.94/2.13         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.94/2.13           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.94/2.13             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.94/2.13  thf(zf_stmt_1, axiom,
% 1.94/2.13    (![B:$i,A:$i]:
% 1.94/2.13     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.94/2.13       ( zip_tseitin_0 @ B @ A ) ))).
% 1.94/2.13  thf('5', plain,
% 1.94/2.13      (![X29 : $i, X30 : $i]:
% 1.94/2.13         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.94/2.13  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.94/2.13  thf('6', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.94/2.13      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.94/2.13  thf('7', plain,
% 1.94/2.13      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.94/2.13      inference('sup+', [status(thm)], ['5', '6'])).
% 1.94/2.13  thf('8', plain,
% 1.94/2.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.94/2.13  thf(zf_stmt_3, axiom,
% 1.94/2.13    (![C:$i,B:$i,A:$i]:
% 1.94/2.13     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.94/2.13       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.94/2.13  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.94/2.13  thf(zf_stmt_5, axiom,
% 1.94/2.13    (![A:$i,B:$i,C:$i]:
% 1.94/2.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.94/2.13       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.94/2.13         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.94/2.13           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.94/2.13             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.94/2.13  thf('9', plain,
% 1.94/2.13      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.94/2.13         (~ (zip_tseitin_0 @ X34 @ X35)
% 1.94/2.13          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 1.94/2.13          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.94/2.13  thf('10', plain,
% 1.94/2.13      (((zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 1.94/2.13        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 1.94/2.13      inference('sup-', [status(thm)], ['8', '9'])).
% 1.94/2.13  thf('11', plain,
% 1.94/2.13      (((v1_xboole_0 @ sk_B_2) | (zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A))),
% 1.94/2.13      inference('sup-', [status(thm)], ['7', '10'])).
% 1.94/2.13  thf('12', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_2)),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf('13', plain,
% 1.94/2.13      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.94/2.13         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 1.94/2.13          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 1.94/2.13          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.94/2.13  thf('14', plain,
% 1.94/2.13      ((~ (zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 1.94/2.13        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_2 @ sk_D)))),
% 1.94/2.13      inference('sup-', [status(thm)], ['12', '13'])).
% 1.94/2.13  thf('15', plain,
% 1.94/2.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf(redefinition_k1_relset_1, axiom,
% 1.94/2.13    (![A:$i,B:$i,C:$i]:
% 1.94/2.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.94/2.13       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.94/2.13  thf('16', plain,
% 1.94/2.13      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.94/2.13         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 1.94/2.13          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.94/2.13      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.94/2.13  thf('17', plain,
% 1.94/2.13      (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.94/2.13      inference('sup-', [status(thm)], ['15', '16'])).
% 1.94/2.13  thf('18', plain,
% 1.94/2.13      ((~ (zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 1.94/2.13        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.94/2.13      inference('demod', [status(thm)], ['14', '17'])).
% 1.94/2.13  thf('19', plain, (((v1_xboole_0 @ sk_B_2) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.94/2.13      inference('sup-', [status(thm)], ['11', '18'])).
% 1.94/2.13  thf('20', plain,
% 1.94/2.13      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf(cc4_relset_1, axiom,
% 1.94/2.13    (![A:$i,B:$i]:
% 1.94/2.13     ( ( v1_xboole_0 @ A ) =>
% 1.94/2.13       ( ![C:$i]:
% 1.94/2.13         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.94/2.13           ( v1_xboole_0 @ C ) ) ) ))).
% 1.94/2.13  thf('21', plain,
% 1.94/2.13      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.94/2.13         (~ (v1_xboole_0 @ X19)
% 1.94/2.13          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X19)))
% 1.94/2.13          | (v1_xboole_0 @ X20))),
% 1.94/2.13      inference('cnf', [status(esa)], [cc4_relset_1])).
% 1.94/2.13  thf('22', plain, (((v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_B_2))),
% 1.94/2.13      inference('sup-', [status(thm)], ['20', '21'])).
% 1.94/2.13  thf('23', plain, ((((sk_A) = (k1_relat_1 @ sk_D)) | (v1_xboole_0 @ sk_C_2))),
% 1.94/2.13      inference('sup-', [status(thm)], ['19', '22'])).
% 1.94/2.13  thf(d3_tarski, axiom,
% 1.94/2.13    (![A:$i,B:$i]:
% 1.94/2.13     ( ( r1_tarski @ A @ B ) <=>
% 1.94/2.13       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.94/2.13  thf('24', plain,
% 1.94/2.13      (![X4 : $i, X6 : $i]:
% 1.94/2.13         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.94/2.13      inference('cnf', [status(esa)], [d3_tarski])).
% 1.94/2.13  thf(d1_xboole_0, axiom,
% 1.94/2.13    (![A:$i]:
% 1.94/2.13     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.94/2.13  thf('25', plain,
% 1.94/2.13      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.94/2.13      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.94/2.13  thf('26', plain,
% 1.94/2.13      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.94/2.13      inference('sup-', [status(thm)], ['24', '25'])).
% 1.94/2.13  thf('27', plain,
% 1.94/2.13      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.94/2.13      inference('sup-', [status(thm)], ['24', '25'])).
% 1.94/2.13  thf(d10_xboole_0, axiom,
% 1.94/2.13    (![A:$i,B:$i]:
% 1.94/2.13     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.94/2.13  thf('28', plain,
% 1.94/2.13      (![X7 : $i, X9 : $i]:
% 1.94/2.13         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 1.94/2.13      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.94/2.13  thf('29', plain,
% 1.94/2.13      (![X0 : $i, X1 : $i]:
% 1.94/2.13         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 1.94/2.13      inference('sup-', [status(thm)], ['27', '28'])).
% 1.94/2.13  thf('30', plain,
% 1.94/2.13      (![X0 : $i, X1 : $i]:
% 1.94/2.13         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.94/2.13      inference('sup-', [status(thm)], ['26', '29'])).
% 1.94/2.13  thf('31', plain,
% 1.94/2.13      (![X0 : $i]:
% 1.94/2.13         (((sk_A) = (k1_relat_1 @ sk_D))
% 1.94/2.13          | ~ (v1_xboole_0 @ X0)
% 1.94/2.13          | ((sk_C_2) = (X0)))),
% 1.94/2.13      inference('sup-', [status(thm)], ['23', '30'])).
% 1.94/2.13  thf('32', plain, (~ (r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_2 @ sk_D)),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf('33', plain,
% 1.94/2.13      (![X0 : $i]:
% 1.94/2.13         (~ (r2_relset_1 @ sk_A @ sk_B_2 @ X0 @ sk_D)
% 1.94/2.13          | ~ (v1_xboole_0 @ X0)
% 1.94/2.13          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.94/2.13      inference('sup-', [status(thm)], ['31', '32'])).
% 1.94/2.13  thf('34', plain, ((((sk_A) = (k1_relat_1 @ sk_D)) | ~ (v1_xboole_0 @ sk_D))),
% 1.94/2.13      inference('sup-', [status(thm)], ['4', '33'])).
% 1.94/2.13  thf('35', plain, (((v1_xboole_0 @ sk_B_2) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.94/2.13      inference('sup-', [status(thm)], ['11', '18'])).
% 1.94/2.13  thf('36', plain,
% 1.94/2.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf('37', plain,
% 1.94/2.13      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.94/2.13         (~ (v1_xboole_0 @ X19)
% 1.94/2.13          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X19)))
% 1.94/2.13          | (v1_xboole_0 @ X20))),
% 1.94/2.13      inference('cnf', [status(esa)], [cc4_relset_1])).
% 1.94/2.13  thf('38', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_B_2))),
% 1.94/2.13      inference('sup-', [status(thm)], ['36', '37'])).
% 1.94/2.13  thf('39', plain, ((((sk_A) = (k1_relat_1 @ sk_D)) | (v1_xboole_0 @ sk_D))),
% 1.94/2.13      inference('sup-', [status(thm)], ['35', '38'])).
% 1.94/2.13  thf('40', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 1.94/2.13      inference('clc', [status(thm)], ['34', '39'])).
% 1.94/2.13  thf('41', plain, ((r2_relset_1 @ sk_A @ sk_B_2 @ sk_D @ sk_D)),
% 1.94/2.13      inference('sup-', [status(thm)], ['1', '3'])).
% 1.94/2.13  thf('42', plain,
% 1.94/2.13      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.94/2.13      inference('sup+', [status(thm)], ['5', '6'])).
% 1.94/2.13  thf('43', plain,
% 1.94/2.13      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf('44', plain,
% 1.94/2.13      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.94/2.13         (~ (zip_tseitin_0 @ X34 @ X35)
% 1.94/2.13          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 1.94/2.13          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.94/2.13  thf('45', plain,
% 1.94/2.13      (((zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ sk_A)
% 1.94/2.13        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 1.94/2.13      inference('sup-', [status(thm)], ['43', '44'])).
% 1.94/2.13  thf('46', plain,
% 1.94/2.13      (((v1_xboole_0 @ sk_B_2) | (zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ sk_A))),
% 1.94/2.13      inference('sup-', [status(thm)], ['42', '45'])).
% 1.94/2.13  thf('47', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_2)),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf('48', plain,
% 1.94/2.13      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.94/2.13         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 1.94/2.13          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 1.94/2.13          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.94/2.13  thf('49', plain,
% 1.94/2.13      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ sk_A)
% 1.94/2.13        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_2)))),
% 1.94/2.13      inference('sup-', [status(thm)], ['47', '48'])).
% 1.94/2.13  thf('50', plain,
% 1.94/2.13      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf('51', plain,
% 1.94/2.13      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.94/2.13         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 1.94/2.13          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.94/2.13      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.94/2.13  thf('52', plain,
% 1.94/2.13      (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 1.94/2.13      inference('sup-', [status(thm)], ['50', '51'])).
% 1.94/2.13  thf('53', plain,
% 1.94/2.13      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ sk_A)
% 1.94/2.13        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 1.94/2.13      inference('demod', [status(thm)], ['49', '52'])).
% 1.94/2.13  thf('54', plain,
% 1.94/2.13      (((v1_xboole_0 @ sk_B_2) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 1.94/2.13      inference('sup-', [status(thm)], ['46', '53'])).
% 1.94/2.13  thf('55', plain, (((v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_B_2))),
% 1.94/2.13      inference('sup-', [status(thm)], ['20', '21'])).
% 1.94/2.13  thf('56', plain,
% 1.94/2.13      ((((sk_A) = (k1_relat_1 @ sk_C_2)) | (v1_xboole_0 @ sk_C_2))),
% 1.94/2.13      inference('sup-', [status(thm)], ['54', '55'])).
% 1.94/2.13  thf('57', plain,
% 1.94/2.13      (![X0 : $i, X1 : $i]:
% 1.94/2.13         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.94/2.13      inference('sup-', [status(thm)], ['26', '29'])).
% 1.94/2.13  thf('58', plain,
% 1.94/2.13      (![X0 : $i]:
% 1.94/2.13         (((sk_A) = (k1_relat_1 @ sk_C_2))
% 1.94/2.13          | ~ (v1_xboole_0 @ X0)
% 1.94/2.13          | ((sk_C_2) = (X0)))),
% 1.94/2.13      inference('sup-', [status(thm)], ['56', '57'])).
% 1.94/2.13  thf('59', plain, (~ (r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_2 @ sk_D)),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf('60', plain,
% 1.94/2.13      (![X0 : $i]:
% 1.94/2.13         (~ (r2_relset_1 @ sk_A @ sk_B_2 @ X0 @ sk_D)
% 1.94/2.13          | ~ (v1_xboole_0 @ X0)
% 1.94/2.13          | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 1.94/2.13      inference('sup-', [status(thm)], ['58', '59'])).
% 1.94/2.13  thf('61', plain,
% 1.94/2.13      ((((sk_A) = (k1_relat_1 @ sk_C_2)) | ~ (v1_xboole_0 @ sk_D))),
% 1.94/2.13      inference('sup-', [status(thm)], ['41', '60'])).
% 1.94/2.13  thf('62', plain,
% 1.94/2.13      (((v1_xboole_0 @ sk_B_2) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 1.94/2.13      inference('sup-', [status(thm)], ['46', '53'])).
% 1.94/2.13  thf('63', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_B_2))),
% 1.94/2.13      inference('sup-', [status(thm)], ['36', '37'])).
% 1.94/2.13  thf('64', plain, ((((sk_A) = (k1_relat_1 @ sk_C_2)) | (v1_xboole_0 @ sk_D))),
% 1.94/2.13      inference('sup-', [status(thm)], ['62', '63'])).
% 1.94/2.13  thf('65', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 1.94/2.13      inference('clc', [status(thm)], ['61', '64'])).
% 1.94/2.13  thf(t9_funct_1, axiom,
% 1.94/2.13    (![A:$i]:
% 1.94/2.13     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.94/2.13       ( ![B:$i]:
% 1.94/2.13         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.94/2.13           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 1.94/2.13               ( ![C:$i]:
% 1.94/2.13                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 1.94/2.13                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 1.94/2.13             ( ( A ) = ( B ) ) ) ) ) ))).
% 1.94/2.13  thf('66', plain,
% 1.94/2.13      (![X14 : $i, X15 : $i]:
% 1.94/2.13         (~ (v1_relat_1 @ X14)
% 1.94/2.13          | ~ (v1_funct_1 @ X14)
% 1.94/2.13          | ((X15) = (X14))
% 1.94/2.13          | (r2_hidden @ (sk_C_1 @ X14 @ X15) @ (k1_relat_1 @ X15))
% 1.94/2.13          | ((k1_relat_1 @ X15) != (k1_relat_1 @ X14))
% 1.94/2.13          | ~ (v1_funct_1 @ X15)
% 1.94/2.13          | ~ (v1_relat_1 @ X15))),
% 1.94/2.13      inference('cnf', [status(esa)], [t9_funct_1])).
% 1.94/2.13  thf('67', plain,
% 1.94/2.13      (![X0 : $i]:
% 1.94/2.13         (((sk_A) != (k1_relat_1 @ X0))
% 1.94/2.13          | ~ (v1_relat_1 @ sk_C_2)
% 1.94/2.13          | ~ (v1_funct_1 @ sk_C_2)
% 1.94/2.13          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 1.94/2.13          | ((sk_C_2) = (X0))
% 1.94/2.13          | ~ (v1_funct_1 @ X0)
% 1.94/2.13          | ~ (v1_relat_1 @ X0))),
% 1.94/2.13      inference('sup-', [status(thm)], ['65', '66'])).
% 1.94/2.13  thf('68', plain,
% 1.94/2.13      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf(cc1_relset_1, axiom,
% 1.94/2.13    (![A:$i,B:$i,C:$i]:
% 1.94/2.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.94/2.13       ( v1_relat_1 @ C ) ))).
% 1.94/2.13  thf('69', plain,
% 1.94/2.13      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.94/2.13         ((v1_relat_1 @ X16)
% 1.94/2.13          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.94/2.13      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.94/2.13  thf('70', plain, ((v1_relat_1 @ sk_C_2)),
% 1.94/2.13      inference('sup-', [status(thm)], ['68', '69'])).
% 1.94/2.13  thf('71', plain, ((v1_funct_1 @ sk_C_2)),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf('72', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 1.94/2.13      inference('clc', [status(thm)], ['61', '64'])).
% 1.94/2.13  thf('73', plain,
% 1.94/2.13      (![X0 : $i]:
% 1.94/2.13         (((sk_A) != (k1_relat_1 @ X0))
% 1.94/2.13          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A)
% 1.94/2.13          | ((sk_C_2) = (X0))
% 1.94/2.13          | ~ (v1_funct_1 @ X0)
% 1.94/2.13          | ~ (v1_relat_1 @ X0))),
% 1.94/2.13      inference('demod', [status(thm)], ['67', '70', '71', '72'])).
% 1.94/2.13  thf('74', plain,
% 1.94/2.13      ((((sk_A) != (sk_A))
% 1.94/2.13        | ~ (v1_relat_1 @ sk_D)
% 1.94/2.13        | ~ (v1_funct_1 @ sk_D)
% 1.94/2.13        | ((sk_C_2) = (sk_D))
% 1.94/2.13        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 1.94/2.13      inference('sup-', [status(thm)], ['40', '73'])).
% 1.94/2.13  thf('75', plain,
% 1.94/2.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf('76', plain,
% 1.94/2.13      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.94/2.13         ((v1_relat_1 @ X16)
% 1.94/2.13          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.94/2.13      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.94/2.13  thf('77', plain, ((v1_relat_1 @ sk_D)),
% 1.94/2.13      inference('sup-', [status(thm)], ['75', '76'])).
% 1.94/2.13  thf('78', plain, ((v1_funct_1 @ sk_D)),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf('79', plain,
% 1.94/2.13      ((((sk_A) != (sk_A))
% 1.94/2.13        | ((sk_C_2) = (sk_D))
% 1.94/2.13        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 1.94/2.13      inference('demod', [status(thm)], ['74', '77', '78'])).
% 1.94/2.13  thf('80', plain,
% 1.94/2.13      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A) | ((sk_C_2) = (sk_D)))),
% 1.94/2.13      inference('simplify', [status(thm)], ['79'])).
% 1.94/2.13  thf('81', plain,
% 1.94/2.13      (![X37 : $i]:
% 1.94/2.13         (((k1_funct_1 @ sk_C_2 @ X37) = (k1_funct_1 @ sk_D @ X37))
% 1.94/2.13          | ~ (r2_hidden @ X37 @ sk_A))),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf('82', plain,
% 1.94/2.13      ((((sk_C_2) = (sk_D))
% 1.94/2.13        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 1.94/2.13            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 1.94/2.13      inference('sup-', [status(thm)], ['80', '81'])).
% 1.94/2.13  thf('83', plain,
% 1.94/2.13      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 1.94/2.13         = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))),
% 1.94/2.13      inference('condensation', [status(thm)], ['82'])).
% 1.94/2.13  thf('84', plain,
% 1.94/2.13      (![X14 : $i, X15 : $i]:
% 1.94/2.13         (~ (v1_relat_1 @ X14)
% 1.94/2.13          | ~ (v1_funct_1 @ X14)
% 1.94/2.13          | ((X15) = (X14))
% 1.94/2.13          | ((k1_funct_1 @ X15 @ (sk_C_1 @ X14 @ X15))
% 1.94/2.13              != (k1_funct_1 @ X14 @ (sk_C_1 @ X14 @ X15)))
% 1.94/2.13          | ((k1_relat_1 @ X15) != (k1_relat_1 @ X14))
% 1.94/2.13          | ~ (v1_funct_1 @ X15)
% 1.94/2.13          | ~ (v1_relat_1 @ X15))),
% 1.94/2.13      inference('cnf', [status(esa)], [t9_funct_1])).
% 1.94/2.13  thf('85', plain,
% 1.94/2.13      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 1.94/2.13          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 1.94/2.13        | ~ (v1_relat_1 @ sk_C_2)
% 1.94/2.13        | ~ (v1_funct_1 @ sk_C_2)
% 1.94/2.13        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 1.94/2.13        | ((sk_C_2) = (sk_D))
% 1.94/2.13        | ~ (v1_funct_1 @ sk_D)
% 1.94/2.13        | ~ (v1_relat_1 @ sk_D))),
% 1.94/2.13      inference('sup-', [status(thm)], ['83', '84'])).
% 1.94/2.13  thf('86', plain, ((v1_relat_1 @ sk_C_2)),
% 1.94/2.13      inference('sup-', [status(thm)], ['68', '69'])).
% 1.94/2.13  thf('87', plain, ((v1_funct_1 @ sk_C_2)),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf('88', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 1.94/2.13      inference('clc', [status(thm)], ['61', '64'])).
% 1.94/2.13  thf('89', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 1.94/2.13      inference('clc', [status(thm)], ['34', '39'])).
% 1.94/2.13  thf('90', plain, ((v1_funct_1 @ sk_D)),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf('91', plain, ((v1_relat_1 @ sk_D)),
% 1.94/2.13      inference('sup-', [status(thm)], ['75', '76'])).
% 1.94/2.13  thf('92', plain,
% 1.94/2.13      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 1.94/2.13          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 1.94/2.13        | ((sk_A) != (sk_A))
% 1.94/2.13        | ((sk_C_2) = (sk_D)))),
% 1.94/2.13      inference('demod', [status(thm)],
% 1.94/2.13                ['85', '86', '87', '88', '89', '90', '91'])).
% 1.94/2.13  thf('93', plain, (((sk_C_2) = (sk_D))),
% 1.94/2.13      inference('simplify', [status(thm)], ['92'])).
% 1.94/2.13  thf('94', plain,
% 1.94/2.13      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf('95', plain,
% 1.94/2.13      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.94/2.13         ((r2_relset_1 @ X26 @ X27 @ X28 @ X28)
% 1.94/2.13          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.94/2.13      inference('simplify', [status(thm)], ['2'])).
% 1.94/2.13  thf('96', plain, ((r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_2 @ sk_C_2)),
% 1.94/2.13      inference('sup-', [status(thm)], ['94', '95'])).
% 1.94/2.13  thf('97', plain, ($false),
% 1.94/2.13      inference('demod', [status(thm)], ['0', '93', '96'])).
% 1.94/2.13  
% 1.94/2.13  % SZS output end Refutation
% 1.94/2.13  
% 1.94/2.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
