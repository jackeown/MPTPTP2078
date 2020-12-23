%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oOFOJqy5dZ

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:29 EST 2020

% Result     : Theorem 15.24s
% Output     : Refutation 15.24s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 562 expanded)
%              Number of leaves         :   39 ( 184 expanded)
%              Depth                    :   22
%              Number of atoms          : 1072 (8356 expanded)
%              Number of equality atoms :   82 ( 362 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( r2_relset_1 @ X27 @ X28 @ X26 @ X29 )
      | ( X26 != X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('3',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r2_relset_1 @ X27 @ X28 @ X29 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_D @ sk_D ),
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
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
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
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X20 ) ) )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('10',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_C_2 = X0 ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('22',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( sk_C_2 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('26',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('28',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('29',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_C_2 = X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ X0 @ sk_D )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X20 ) ) )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('38',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('41',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('43',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['34','43'])).

thf('45',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['1','3'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_C_2 = X0 ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('47',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('49',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( sk_C_2 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('53',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('56',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_C_2 = X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ X0 @ sk_D )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['45','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('63',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('64',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('66',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['61','66'])).

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

thf('68',plain,(
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

thf('69',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('71',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('72',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['61','66'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','72','73','74'])).

thf('76',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['44','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('79',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['76','79','80'])).

thf('82',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['81'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('83',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('84',plain,
    ( ( sk_C_2 = sk_D )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X38: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X38 )
        = ( k1_funct_1 @ sk_D @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( sk_C_2 = sk_D )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ),
    inference(condensation,[status(thm)],['86'])).

thf('88',plain,(
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

thf('89',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['70','71'])).

thf('91',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['61','66'])).

thf('93',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['34','43'])).

thf('94',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['77','78'])).

thf('96',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['89','90','91','92','93','94','95'])).

thf('97',plain,(
    sk_C_2 = sk_D ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r2_relset_1 @ X27 @ X28 @ X29 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('100',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    $false ),
    inference(demod,[status(thm)],['0','97','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oOFOJqy5dZ
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:55:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 15.24/15.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 15.24/15.47  % Solved by: fo/fo7.sh
% 15.24/15.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 15.24/15.47  % done 6602 iterations in 15.014s
% 15.24/15.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 15.24/15.47  % SZS output start Refutation
% 15.24/15.47  thf(sk_C_2_type, type, sk_C_2: $i).
% 15.24/15.47  thf(sk_D_type, type, sk_D: $i).
% 15.24/15.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 15.24/15.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 15.24/15.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 15.24/15.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 15.24/15.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 15.24/15.47  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 15.24/15.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 15.24/15.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 15.24/15.47  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 15.24/15.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 15.24/15.47  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 15.24/15.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 15.24/15.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 15.24/15.47  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 15.24/15.47  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 15.24/15.47  thf(sk_A_type, type, sk_A: $i).
% 15.24/15.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 15.24/15.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 15.24/15.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 15.24/15.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 15.24/15.47  thf(t113_funct_2, conjecture,
% 15.24/15.47    (![A:$i,B:$i,C:$i]:
% 15.24/15.47     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 15.24/15.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 15.24/15.47       ( ![D:$i]:
% 15.24/15.47         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 15.24/15.47             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 15.24/15.47           ( ( ![E:$i]:
% 15.24/15.47               ( ( m1_subset_1 @ E @ A ) =>
% 15.24/15.47                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 15.24/15.47             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 15.24/15.47  thf(zf_stmt_0, negated_conjecture,
% 15.24/15.47    (~( ![A:$i,B:$i,C:$i]:
% 15.24/15.47        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 15.24/15.47            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 15.24/15.47          ( ![D:$i]:
% 15.24/15.47            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 15.24/15.47                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 15.24/15.47              ( ( ![E:$i]:
% 15.24/15.47                  ( ( m1_subset_1 @ E @ A ) =>
% 15.24/15.47                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 15.24/15.47                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 15.24/15.47    inference('cnf.neg', [status(esa)], [t113_funct_2])).
% 15.24/15.47  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 15.24/15.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.24/15.47  thf('1', plain,
% 15.24/15.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 15.24/15.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.24/15.47  thf(redefinition_r2_relset_1, axiom,
% 15.24/15.47    (![A:$i,B:$i,C:$i,D:$i]:
% 15.24/15.47     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 15.24/15.47         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 15.24/15.47       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 15.24/15.47  thf('2', plain,
% 15.24/15.47      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 15.24/15.47         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 15.24/15.47          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 15.24/15.47          | (r2_relset_1 @ X27 @ X28 @ X26 @ X29)
% 15.24/15.47          | ((X26) != (X29)))),
% 15.24/15.47      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 15.24/15.47  thf('3', plain,
% 15.24/15.47      (![X27 : $i, X28 : $i, X29 : $i]:
% 15.24/15.47         ((r2_relset_1 @ X27 @ X28 @ X29 @ X29)
% 15.24/15.47          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 15.24/15.47      inference('simplify', [status(thm)], ['2'])).
% 15.24/15.47  thf('4', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_D @ sk_D)),
% 15.24/15.47      inference('sup-', [status(thm)], ['1', '3'])).
% 15.24/15.47  thf(d1_funct_2, axiom,
% 15.24/15.47    (![A:$i,B:$i,C:$i]:
% 15.24/15.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.24/15.47       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 15.24/15.47           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 15.24/15.47             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 15.24/15.47         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 15.24/15.47           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 15.24/15.47             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 15.24/15.47  thf(zf_stmt_1, axiom,
% 15.24/15.47    (![B:$i,A:$i]:
% 15.24/15.47     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 15.24/15.47       ( zip_tseitin_0 @ B @ A ) ))).
% 15.24/15.47  thf('5', plain,
% 15.24/15.47      (![X30 : $i, X31 : $i]:
% 15.24/15.47         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 15.24/15.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 15.24/15.47  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 15.24/15.47  thf('6', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 15.24/15.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 15.24/15.47  thf('7', plain,
% 15.24/15.47      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 15.24/15.47      inference('sup+', [status(thm)], ['5', '6'])).
% 15.24/15.47  thf('8', plain,
% 15.24/15.47      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 15.24/15.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.24/15.47  thf(cc4_relset_1, axiom,
% 15.24/15.47    (![A:$i,B:$i]:
% 15.24/15.47     ( ( v1_xboole_0 @ A ) =>
% 15.24/15.47       ( ![C:$i]:
% 15.24/15.47         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 15.24/15.47           ( v1_xboole_0 @ C ) ) ) ))).
% 15.24/15.47  thf('9', plain,
% 15.24/15.47      (![X20 : $i, X21 : $i, X22 : $i]:
% 15.24/15.47         (~ (v1_xboole_0 @ X20)
% 15.24/15.47          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X20)))
% 15.24/15.47          | (v1_xboole_0 @ X21))),
% 15.24/15.47      inference('cnf', [status(esa)], [cc4_relset_1])).
% 15.24/15.47  thf('10', plain, (((v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_B_1))),
% 15.24/15.47      inference('sup-', [status(thm)], ['8', '9'])).
% 15.24/15.47  thf('11', plain,
% 15.24/15.47      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_C_2))),
% 15.24/15.47      inference('sup-', [status(thm)], ['7', '10'])).
% 15.24/15.47  thf(d3_tarski, axiom,
% 15.24/15.47    (![A:$i,B:$i]:
% 15.24/15.47     ( ( r1_tarski @ A @ B ) <=>
% 15.24/15.47       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 15.24/15.47  thf('12', plain,
% 15.24/15.47      (![X4 : $i, X6 : $i]:
% 15.24/15.47         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 15.24/15.47      inference('cnf', [status(esa)], [d3_tarski])).
% 15.24/15.47  thf(d1_xboole_0, axiom,
% 15.24/15.47    (![A:$i]:
% 15.24/15.47     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 15.24/15.47  thf('13', plain,
% 15.24/15.47      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 15.24/15.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 15.24/15.47  thf('14', plain,
% 15.24/15.47      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 15.24/15.47      inference('sup-', [status(thm)], ['12', '13'])).
% 15.24/15.47  thf('15', plain,
% 15.24/15.47      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 15.24/15.47      inference('sup-', [status(thm)], ['12', '13'])).
% 15.24/15.47  thf(d10_xboole_0, axiom,
% 15.24/15.47    (![A:$i,B:$i]:
% 15.24/15.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 15.24/15.47  thf('16', plain,
% 15.24/15.47      (![X7 : $i, X9 : $i]:
% 15.24/15.47         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 15.24/15.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 15.24/15.47  thf('17', plain,
% 15.24/15.47      (![X0 : $i, X1 : $i]:
% 15.24/15.47         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 15.24/15.47      inference('sup-', [status(thm)], ['15', '16'])).
% 15.24/15.47  thf('18', plain,
% 15.24/15.47      (![X0 : $i, X1 : $i]:
% 15.24/15.47         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 15.24/15.47      inference('sup-', [status(thm)], ['14', '17'])).
% 15.24/15.47  thf('19', plain,
% 15.24/15.47      (![X0 : $i, X1 : $i]:
% 15.24/15.47         ((zip_tseitin_0 @ sk_B_1 @ X1)
% 15.24/15.47          | ~ (v1_xboole_0 @ X0)
% 15.24/15.47          | ((sk_C_2) = (X0)))),
% 15.24/15.47      inference('sup-', [status(thm)], ['11', '18'])).
% 15.24/15.47  thf('20', plain,
% 15.24/15.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 15.24/15.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.24/15.47  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 15.24/15.47  thf(zf_stmt_3, axiom,
% 15.24/15.47    (![C:$i,B:$i,A:$i]:
% 15.24/15.47     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 15.24/15.47       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 15.24/15.47  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 15.24/15.47  thf(zf_stmt_5, axiom,
% 15.24/15.47    (![A:$i,B:$i,C:$i]:
% 15.24/15.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.24/15.47       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 15.24/15.47         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 15.24/15.47           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 15.24/15.47             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 15.24/15.47  thf('21', plain,
% 15.24/15.47      (![X35 : $i, X36 : $i, X37 : $i]:
% 15.24/15.47         (~ (zip_tseitin_0 @ X35 @ X36)
% 15.24/15.47          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 15.24/15.47          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 15.24/15.47      inference('cnf', [status(esa)], [zf_stmt_5])).
% 15.24/15.47  thf('22', plain,
% 15.24/15.47      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 15.24/15.47        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 15.24/15.47      inference('sup-', [status(thm)], ['20', '21'])).
% 15.24/15.47  thf('23', plain,
% 15.24/15.47      (![X0 : $i]:
% 15.24/15.47         (((sk_C_2) = (X0))
% 15.24/15.47          | ~ (v1_xboole_0 @ X0)
% 15.24/15.47          | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 15.24/15.47      inference('sup-', [status(thm)], ['19', '22'])).
% 15.24/15.47  thf('24', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 15.24/15.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.24/15.47  thf('25', plain,
% 15.24/15.47      (![X32 : $i, X33 : $i, X34 : $i]:
% 15.24/15.47         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 15.24/15.47          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 15.24/15.47          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 15.24/15.47      inference('cnf', [status(esa)], [zf_stmt_3])).
% 15.24/15.47  thf('26', plain,
% 15.24/15.47      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 15.24/15.47        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 15.24/15.47      inference('sup-', [status(thm)], ['24', '25'])).
% 15.24/15.47  thf('27', plain,
% 15.24/15.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 15.24/15.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.24/15.47  thf(redefinition_k1_relset_1, axiom,
% 15.24/15.47    (![A:$i,B:$i,C:$i]:
% 15.24/15.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.24/15.47       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 15.24/15.47  thf('28', plain,
% 15.24/15.47      (![X23 : $i, X24 : $i, X25 : $i]:
% 15.24/15.47         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 15.24/15.47          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 15.24/15.47      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 15.24/15.47  thf('29', plain,
% 15.24/15.47      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 15.24/15.47      inference('sup-', [status(thm)], ['27', '28'])).
% 15.24/15.47  thf('30', plain,
% 15.24/15.47      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 15.24/15.47        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 15.24/15.47      inference('demod', [status(thm)], ['26', '29'])).
% 15.24/15.47  thf('31', plain,
% 15.24/15.47      (![X0 : $i]:
% 15.24/15.47         (~ (v1_xboole_0 @ X0)
% 15.24/15.47          | ((sk_C_2) = (X0))
% 15.24/15.47          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 15.24/15.47      inference('sup-', [status(thm)], ['23', '30'])).
% 15.24/15.47  thf('32', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 15.24/15.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.24/15.47  thf('33', plain,
% 15.24/15.47      (![X0 : $i]:
% 15.24/15.47         (~ (r2_relset_1 @ sk_A @ sk_B_1 @ X0 @ sk_D)
% 15.24/15.47          | ((sk_A) = (k1_relat_1 @ sk_D))
% 15.24/15.47          | ~ (v1_xboole_0 @ X0))),
% 15.24/15.47      inference('sup-', [status(thm)], ['31', '32'])).
% 15.24/15.47  thf('34', plain, ((~ (v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 15.24/15.47      inference('sup-', [status(thm)], ['4', '33'])).
% 15.24/15.47  thf('35', plain,
% 15.24/15.47      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 15.24/15.47      inference('sup+', [status(thm)], ['5', '6'])).
% 15.24/15.47  thf('36', plain,
% 15.24/15.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 15.24/15.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.24/15.47  thf('37', plain,
% 15.24/15.47      (![X20 : $i, X21 : $i, X22 : $i]:
% 15.24/15.47         (~ (v1_xboole_0 @ X20)
% 15.24/15.47          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X20)))
% 15.24/15.47          | (v1_xboole_0 @ X21))),
% 15.24/15.47      inference('cnf', [status(esa)], [cc4_relset_1])).
% 15.24/15.47  thf('38', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_B_1))),
% 15.24/15.47      inference('sup-', [status(thm)], ['36', '37'])).
% 15.24/15.47  thf('39', plain,
% 15.24/15.47      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_D))),
% 15.24/15.47      inference('sup-', [status(thm)], ['35', '38'])).
% 15.24/15.47  thf('40', plain,
% 15.24/15.47      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 15.24/15.47        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 15.24/15.47      inference('sup-', [status(thm)], ['20', '21'])).
% 15.24/15.47  thf('41', plain,
% 15.24/15.47      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 15.24/15.47      inference('sup-', [status(thm)], ['39', '40'])).
% 15.24/15.47  thf('42', plain,
% 15.24/15.47      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 15.24/15.47        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 15.24/15.47      inference('demod', [status(thm)], ['26', '29'])).
% 15.24/15.47  thf('43', plain, (((v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 15.24/15.47      inference('sup-', [status(thm)], ['41', '42'])).
% 15.24/15.47  thf('44', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 15.24/15.47      inference('clc', [status(thm)], ['34', '43'])).
% 15.24/15.47  thf('45', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_D @ sk_D)),
% 15.24/15.47      inference('sup-', [status(thm)], ['1', '3'])).
% 15.24/15.47  thf('46', plain,
% 15.24/15.47      (![X0 : $i, X1 : $i]:
% 15.24/15.47         ((zip_tseitin_0 @ sk_B_1 @ X1)
% 15.24/15.47          | ~ (v1_xboole_0 @ X0)
% 15.24/15.47          | ((sk_C_2) = (X0)))),
% 15.24/15.47      inference('sup-', [status(thm)], ['11', '18'])).
% 15.24/15.47  thf('47', plain,
% 15.24/15.47      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 15.24/15.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.24/15.47  thf('48', plain,
% 15.24/15.47      (![X35 : $i, X36 : $i, X37 : $i]:
% 15.24/15.47         (~ (zip_tseitin_0 @ X35 @ X36)
% 15.24/15.47          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 15.24/15.47          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 15.24/15.47      inference('cnf', [status(esa)], [zf_stmt_5])).
% 15.24/15.47  thf('49', plain,
% 15.24/15.47      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 15.24/15.47        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 15.24/15.47      inference('sup-', [status(thm)], ['47', '48'])).
% 15.24/15.47  thf('50', plain,
% 15.24/15.47      (![X0 : $i]:
% 15.24/15.47         (((sk_C_2) = (X0))
% 15.24/15.47          | ~ (v1_xboole_0 @ X0)
% 15.24/15.47          | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 15.24/15.47      inference('sup-', [status(thm)], ['46', '49'])).
% 15.24/15.47  thf('51', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 15.24/15.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.24/15.47  thf('52', plain,
% 15.24/15.47      (![X32 : $i, X33 : $i, X34 : $i]:
% 15.24/15.47         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 15.24/15.47          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 15.24/15.47          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 15.24/15.47      inference('cnf', [status(esa)], [zf_stmt_3])).
% 15.24/15.47  thf('53', plain,
% 15.24/15.47      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 15.24/15.47        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 15.24/15.47      inference('sup-', [status(thm)], ['51', '52'])).
% 15.24/15.47  thf('54', plain,
% 15.24/15.47      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 15.24/15.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.24/15.47  thf('55', plain,
% 15.24/15.47      (![X23 : $i, X24 : $i, X25 : $i]:
% 15.24/15.47         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 15.24/15.47          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 15.24/15.47      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 15.24/15.47  thf('56', plain,
% 15.24/15.47      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 15.24/15.47      inference('sup-', [status(thm)], ['54', '55'])).
% 15.24/15.47  thf('57', plain,
% 15.24/15.47      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 15.24/15.47        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 15.24/15.47      inference('demod', [status(thm)], ['53', '56'])).
% 15.24/15.47  thf('58', plain,
% 15.24/15.47      (![X0 : $i]:
% 15.24/15.47         (~ (v1_xboole_0 @ X0)
% 15.24/15.47          | ((sk_C_2) = (X0))
% 15.24/15.47          | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 15.24/15.47      inference('sup-', [status(thm)], ['50', '57'])).
% 15.24/15.47  thf('59', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 15.24/15.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.24/15.47  thf('60', plain,
% 15.24/15.47      (![X0 : $i]:
% 15.24/15.47         (~ (r2_relset_1 @ sk_A @ sk_B_1 @ X0 @ sk_D)
% 15.24/15.47          | ((sk_A) = (k1_relat_1 @ sk_C_2))
% 15.24/15.47          | ~ (v1_xboole_0 @ X0))),
% 15.24/15.47      inference('sup-', [status(thm)], ['58', '59'])).
% 15.24/15.47  thf('61', plain,
% 15.24/15.47      ((~ (v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 15.24/15.47      inference('sup-', [status(thm)], ['45', '60'])).
% 15.24/15.47  thf('62', plain,
% 15.24/15.47      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_D))),
% 15.24/15.47      inference('sup-', [status(thm)], ['35', '38'])).
% 15.24/15.47  thf('63', plain,
% 15.24/15.47      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 15.24/15.47        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 15.24/15.47      inference('sup-', [status(thm)], ['47', '48'])).
% 15.24/15.47  thf('64', plain,
% 15.24/15.47      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 15.24/15.47      inference('sup-', [status(thm)], ['62', '63'])).
% 15.24/15.47  thf('65', plain,
% 15.24/15.47      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 15.24/15.47        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 15.24/15.47      inference('demod', [status(thm)], ['53', '56'])).
% 15.24/15.47  thf('66', plain, (((v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 15.24/15.47      inference('sup-', [status(thm)], ['64', '65'])).
% 15.24/15.47  thf('67', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 15.24/15.47      inference('clc', [status(thm)], ['61', '66'])).
% 15.24/15.47  thf(t9_funct_1, axiom,
% 15.24/15.47    (![A:$i]:
% 15.24/15.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 15.24/15.47       ( ![B:$i]:
% 15.24/15.47         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 15.24/15.47           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 15.24/15.47               ( ![C:$i]:
% 15.24/15.47                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 15.24/15.47                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 15.24/15.47             ( ( A ) = ( B ) ) ) ) ) ))).
% 15.24/15.47  thf('68', plain,
% 15.24/15.47      (![X15 : $i, X16 : $i]:
% 15.24/15.47         (~ (v1_relat_1 @ X15)
% 15.24/15.47          | ~ (v1_funct_1 @ X15)
% 15.24/15.47          | ((X16) = (X15))
% 15.24/15.47          | (r2_hidden @ (sk_C_1 @ X15 @ X16) @ (k1_relat_1 @ X16))
% 15.24/15.47          | ((k1_relat_1 @ X16) != (k1_relat_1 @ X15))
% 15.24/15.47          | ~ (v1_funct_1 @ X16)
% 15.24/15.47          | ~ (v1_relat_1 @ X16))),
% 15.24/15.47      inference('cnf', [status(esa)], [t9_funct_1])).
% 15.24/15.47  thf('69', plain,
% 15.24/15.47      (![X0 : $i]:
% 15.24/15.47         (((sk_A) != (k1_relat_1 @ X0))
% 15.24/15.47          | ~ (v1_relat_1 @ sk_C_2)
% 15.24/15.47          | ~ (v1_funct_1 @ sk_C_2)
% 15.24/15.47          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 15.24/15.47          | ((sk_C_2) = (X0))
% 15.24/15.47          | ~ (v1_funct_1 @ X0)
% 15.24/15.47          | ~ (v1_relat_1 @ X0))),
% 15.24/15.47      inference('sup-', [status(thm)], ['67', '68'])).
% 15.24/15.47  thf('70', plain,
% 15.24/15.47      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 15.24/15.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.24/15.47  thf(cc1_relset_1, axiom,
% 15.24/15.47    (![A:$i,B:$i,C:$i]:
% 15.24/15.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.24/15.47       ( v1_relat_1 @ C ) ))).
% 15.24/15.47  thf('71', plain,
% 15.24/15.47      (![X17 : $i, X18 : $i, X19 : $i]:
% 15.24/15.47         ((v1_relat_1 @ X17)
% 15.24/15.47          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 15.24/15.47      inference('cnf', [status(esa)], [cc1_relset_1])).
% 15.24/15.47  thf('72', plain, ((v1_relat_1 @ sk_C_2)),
% 15.24/15.47      inference('sup-', [status(thm)], ['70', '71'])).
% 15.24/15.47  thf('73', plain, ((v1_funct_1 @ sk_C_2)),
% 15.24/15.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.24/15.47  thf('74', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 15.24/15.47      inference('clc', [status(thm)], ['61', '66'])).
% 15.24/15.47  thf('75', plain,
% 15.24/15.47      (![X0 : $i]:
% 15.24/15.47         (((sk_A) != (k1_relat_1 @ X0))
% 15.24/15.47          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A)
% 15.24/15.47          | ((sk_C_2) = (X0))
% 15.24/15.47          | ~ (v1_funct_1 @ X0)
% 15.24/15.47          | ~ (v1_relat_1 @ X0))),
% 15.24/15.47      inference('demod', [status(thm)], ['69', '72', '73', '74'])).
% 15.24/15.47  thf('76', plain,
% 15.24/15.47      ((((sk_A) != (sk_A))
% 15.24/15.47        | ~ (v1_relat_1 @ sk_D)
% 15.24/15.47        | ~ (v1_funct_1 @ sk_D)
% 15.24/15.47        | ((sk_C_2) = (sk_D))
% 15.24/15.47        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 15.24/15.47      inference('sup-', [status(thm)], ['44', '75'])).
% 15.24/15.47  thf('77', plain,
% 15.24/15.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 15.24/15.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.24/15.47  thf('78', plain,
% 15.24/15.47      (![X17 : $i, X18 : $i, X19 : $i]:
% 15.24/15.47         ((v1_relat_1 @ X17)
% 15.24/15.47          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 15.24/15.47      inference('cnf', [status(esa)], [cc1_relset_1])).
% 15.24/15.47  thf('79', plain, ((v1_relat_1 @ sk_D)),
% 15.24/15.47      inference('sup-', [status(thm)], ['77', '78'])).
% 15.24/15.47  thf('80', plain, ((v1_funct_1 @ sk_D)),
% 15.24/15.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.24/15.47  thf('81', plain,
% 15.24/15.47      ((((sk_A) != (sk_A))
% 15.24/15.47        | ((sk_C_2) = (sk_D))
% 15.24/15.47        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 15.24/15.47      inference('demod', [status(thm)], ['76', '79', '80'])).
% 15.24/15.47  thf('82', plain,
% 15.24/15.47      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A) | ((sk_C_2) = (sk_D)))),
% 15.24/15.47      inference('simplify', [status(thm)], ['81'])).
% 15.24/15.47  thf(t1_subset, axiom,
% 15.24/15.47    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 15.24/15.47  thf('83', plain,
% 15.24/15.47      (![X10 : $i, X11 : $i]:
% 15.24/15.47         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 15.24/15.47      inference('cnf', [status(esa)], [t1_subset])).
% 15.24/15.47  thf('84', plain,
% 15.24/15.47      ((((sk_C_2) = (sk_D)) | (m1_subset_1 @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 15.24/15.47      inference('sup-', [status(thm)], ['82', '83'])).
% 15.24/15.47  thf('85', plain,
% 15.24/15.47      (![X38 : $i]:
% 15.24/15.47         (((k1_funct_1 @ sk_C_2 @ X38) = (k1_funct_1 @ sk_D @ X38))
% 15.24/15.47          | ~ (m1_subset_1 @ X38 @ sk_A))),
% 15.24/15.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.24/15.47  thf('86', plain,
% 15.24/15.47      ((((sk_C_2) = (sk_D))
% 15.24/15.47        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 15.24/15.47            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 15.24/15.47      inference('sup-', [status(thm)], ['84', '85'])).
% 15.24/15.47  thf('87', plain,
% 15.24/15.47      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 15.24/15.47         = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))),
% 15.24/15.47      inference('condensation', [status(thm)], ['86'])).
% 15.24/15.47  thf('88', plain,
% 15.24/15.47      (![X15 : $i, X16 : $i]:
% 15.24/15.47         (~ (v1_relat_1 @ X15)
% 15.24/15.47          | ~ (v1_funct_1 @ X15)
% 15.24/15.47          | ((X16) = (X15))
% 15.24/15.47          | ((k1_funct_1 @ X16 @ (sk_C_1 @ X15 @ X16))
% 15.24/15.47              != (k1_funct_1 @ X15 @ (sk_C_1 @ X15 @ X16)))
% 15.24/15.47          | ((k1_relat_1 @ X16) != (k1_relat_1 @ X15))
% 15.24/15.47          | ~ (v1_funct_1 @ X16)
% 15.24/15.47          | ~ (v1_relat_1 @ X16))),
% 15.24/15.47      inference('cnf', [status(esa)], [t9_funct_1])).
% 15.24/15.47  thf('89', plain,
% 15.24/15.47      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 15.24/15.47          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 15.24/15.47        | ~ (v1_relat_1 @ sk_C_2)
% 15.24/15.47        | ~ (v1_funct_1 @ sk_C_2)
% 15.24/15.47        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 15.24/15.47        | ((sk_C_2) = (sk_D))
% 15.24/15.47        | ~ (v1_funct_1 @ sk_D)
% 15.24/15.47        | ~ (v1_relat_1 @ sk_D))),
% 15.24/15.47      inference('sup-', [status(thm)], ['87', '88'])).
% 15.24/15.47  thf('90', plain, ((v1_relat_1 @ sk_C_2)),
% 15.24/15.47      inference('sup-', [status(thm)], ['70', '71'])).
% 15.24/15.47  thf('91', plain, ((v1_funct_1 @ sk_C_2)),
% 15.24/15.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.24/15.47  thf('92', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 15.24/15.47      inference('clc', [status(thm)], ['61', '66'])).
% 15.24/15.47  thf('93', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 15.24/15.47      inference('clc', [status(thm)], ['34', '43'])).
% 15.24/15.47  thf('94', plain, ((v1_funct_1 @ sk_D)),
% 15.24/15.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.24/15.47  thf('95', plain, ((v1_relat_1 @ sk_D)),
% 15.24/15.47      inference('sup-', [status(thm)], ['77', '78'])).
% 15.24/15.47  thf('96', plain,
% 15.24/15.47      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 15.24/15.47          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 15.24/15.47        | ((sk_A) != (sk_A))
% 15.24/15.47        | ((sk_C_2) = (sk_D)))),
% 15.24/15.47      inference('demod', [status(thm)],
% 15.24/15.47                ['89', '90', '91', '92', '93', '94', '95'])).
% 15.24/15.47  thf('97', plain, (((sk_C_2) = (sk_D))),
% 15.24/15.47      inference('simplify', [status(thm)], ['96'])).
% 15.24/15.47  thf('98', plain,
% 15.24/15.47      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 15.24/15.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.24/15.47  thf('99', plain,
% 15.24/15.47      (![X27 : $i, X28 : $i, X29 : $i]:
% 15.24/15.47         ((r2_relset_1 @ X27 @ X28 @ X29 @ X29)
% 15.24/15.47          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 15.24/15.47      inference('simplify', [status(thm)], ['2'])).
% 15.24/15.47  thf('100', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2)),
% 15.24/15.47      inference('sup-', [status(thm)], ['98', '99'])).
% 15.24/15.47  thf('101', plain, ($false),
% 15.24/15.47      inference('demod', [status(thm)], ['0', '97', '100'])).
% 15.24/15.47  
% 15.24/15.47  % SZS output end Refutation
% 15.24/15.47  
% 15.31/15.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
