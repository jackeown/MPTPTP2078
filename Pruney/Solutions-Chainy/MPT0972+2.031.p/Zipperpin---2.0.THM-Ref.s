%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0RJeYIwEYD

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:37 EST 2020

% Result     : Theorem 3.50s
% Output     : Refutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 945 expanded)
%              Number of leaves         :   40 ( 309 expanded)
%              Depth                    :   23
%              Number of atoms          : 1234 (10026 expanded)
%              Number of equality atoms :   84 ( 476 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

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

thf('1',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('2',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( zip_tseitin_1 @ X2 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ( zip_tseitin_1 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('14',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('17',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('23',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('29',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('33',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('39',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('40',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('41',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( r2_relset_1 @ X23 @ X24 @ X22 @ X25 )
      | ( X22 != X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('42',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_relset_1 @ X23 @ X24 @ X25 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( r2_relset_1 @ X0 @ k1_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X3 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','46'])).

thf('48',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('51',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('54',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('56',plain,(
    r1_tarski @ sk_C_2 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( r2_hidden @ ( sk_B @ sk_C_2 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('61',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['52','61'])).

thf('63',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('64',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['49','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('67',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('68',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('70',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( r2_hidden @ ( sk_B @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['67','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('75',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['66','75'])).

thf('77',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('78',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['65','78'])).

thf('80',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['27','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ( zip_tseitin_1 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('82',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('84',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('87',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['84','87'])).

thf('89',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['81','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('91',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('93',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['84','87'])).

thf('96',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['89','96'])).

thf('98',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['65','78'])).

thf('99',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['97','98'])).

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

thf('100',plain,(
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

thf('101',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('103',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('104',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','104','105','106'])).

thf('108',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['80','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('111',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['108','111','112'])).

thf('114',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X34: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X34 )
        = ( k1_funct_1 @ sk_D @ X34 ) )
      | ~ ( r2_hidden @ X34 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( sk_C_2 = sk_D )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ),
    inference(condensation,[status(thm)],['116'])).

thf('118',plain,(
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

thf('119',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['102','103'])).

thf('121',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('123',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['27','79'])).

thf('124',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['109','110'])).

thf('126',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['119','120','121','122','123','124','125'])).

thf('127',plain,(
    sk_C_2 = sk_D ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_relset_1 @ X23 @ X24 @ X25 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('130',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    $false ),
    inference(demod,[status(thm)],['0','127','130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0RJeYIwEYD
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:14:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 3.50/3.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.50/3.74  % Solved by: fo/fo7.sh
% 3.50/3.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.50/3.74  % done 3924 iterations in 3.282s
% 3.50/3.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.50/3.74  % SZS output start Refutation
% 3.50/3.74  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.50/3.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.50/3.74  thf(sk_D_type, type, sk_D: $i).
% 3.50/3.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.50/3.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.50/3.74  thf(sk_B_type, type, sk_B: $i > $i).
% 3.50/3.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.50/3.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.50/3.74  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.50/3.74  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 3.50/3.74  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.50/3.74  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 3.50/3.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.50/3.74  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.50/3.74  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.50/3.74  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.50/3.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.50/3.74  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.50/3.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.50/3.74  thf(sk_A_type, type, sk_A: $i).
% 3.50/3.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.50/3.74  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.50/3.74  thf(sk_C_2_type, type, sk_C_2: $i).
% 3.50/3.74  thf(t18_funct_2, conjecture,
% 3.50/3.74    (![A:$i,B:$i,C:$i]:
% 3.50/3.74     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.50/3.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.50/3.74       ( ![D:$i]:
% 3.50/3.74         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.50/3.74             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.50/3.74           ( ( ![E:$i]:
% 3.50/3.74               ( ( r2_hidden @ E @ A ) =>
% 3.50/3.74                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 3.50/3.74             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 3.50/3.74  thf(zf_stmt_0, negated_conjecture,
% 3.50/3.74    (~( ![A:$i,B:$i,C:$i]:
% 3.50/3.74        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.50/3.74            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.50/3.74          ( ![D:$i]:
% 3.50/3.74            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.50/3.74                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.50/3.74              ( ( ![E:$i]:
% 3.50/3.74                  ( ( r2_hidden @ E @ A ) =>
% 3.50/3.74                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 3.50/3.74                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 3.50/3.74    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 3.50/3.74  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 3.50/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.74  thf(d1_funct_2, axiom,
% 3.50/3.74    (![A:$i,B:$i,C:$i]:
% 3.50/3.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.50/3.74       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.50/3.74           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.50/3.74             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.50/3.74         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.50/3.74           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.50/3.74             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.50/3.74  thf(zf_stmt_1, axiom,
% 3.50/3.74    (![B:$i,A:$i]:
% 3.50/3.74     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.50/3.74       ( zip_tseitin_0 @ B @ A ) ))).
% 3.50/3.74  thf('1', plain,
% 3.50/3.74      (![X26 : $i, X27 : $i]:
% 3.50/3.74         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 3.50/3.74      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.50/3.74  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.50/3.74  thf('2', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.50/3.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.50/3.74  thf('3', plain,
% 3.50/3.74      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 3.50/3.74      inference('sup+', [status(thm)], ['1', '2'])).
% 3.50/3.74  thf(d3_tarski, axiom,
% 3.50/3.74    (![A:$i,B:$i]:
% 3.50/3.74     ( ( r1_tarski @ A @ B ) <=>
% 3.50/3.74       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.50/3.74  thf('4', plain,
% 3.50/3.74      (![X4 : $i, X6 : $i]:
% 3.50/3.74         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 3.50/3.74      inference('cnf', [status(esa)], [d3_tarski])).
% 3.50/3.74  thf(d1_xboole_0, axiom,
% 3.50/3.74    (![A:$i]:
% 3.50/3.74     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 3.50/3.74  thf('5', plain,
% 3.50/3.74      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.50/3.74      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.50/3.74  thf('6', plain,
% 3.50/3.74      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.50/3.74      inference('sup-', [status(thm)], ['4', '5'])).
% 3.50/3.74  thf(t3_subset, axiom,
% 3.50/3.74    (![A:$i,B:$i]:
% 3.50/3.74     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.50/3.74  thf('7', plain,
% 3.50/3.74      (![X11 : $i, X13 : $i]:
% 3.50/3.74         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 3.50/3.74      inference('cnf', [status(esa)], [t3_subset])).
% 3.50/3.74  thf('8', plain,
% 3.50/3.74      (![X0 : $i, X1 : $i]:
% 3.50/3.74         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 3.50/3.74      inference('sup-', [status(thm)], ['6', '7'])).
% 3.50/3.74  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.50/3.74  thf(zf_stmt_3, axiom,
% 3.50/3.74    (![C:$i,B:$i,A:$i]:
% 3.50/3.74     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.50/3.74       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.50/3.74  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.50/3.74  thf(zf_stmt_5, axiom,
% 3.50/3.74    (![A:$i,B:$i,C:$i]:
% 3.50/3.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.50/3.74       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.50/3.74         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.50/3.74           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.50/3.74             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.50/3.74  thf('9', plain,
% 3.50/3.74      (![X31 : $i, X32 : $i, X33 : $i]:
% 3.50/3.74         (~ (zip_tseitin_0 @ X31 @ X32)
% 3.50/3.74          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 3.50/3.74          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 3.50/3.74      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.50/3.74  thf('10', plain,
% 3.50/3.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.74         (~ (v1_xboole_0 @ X2)
% 3.50/3.74          | (zip_tseitin_1 @ X2 @ X0 @ X1)
% 3.50/3.74          | ~ (zip_tseitin_0 @ X0 @ X1))),
% 3.50/3.74      inference('sup-', [status(thm)], ['8', '9'])).
% 3.50/3.74  thf('11', plain,
% 3.50/3.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.74         ((v1_xboole_0 @ X1)
% 3.50/3.74          | (zip_tseitin_1 @ X2 @ X1 @ X0)
% 3.50/3.74          | ~ (v1_xboole_0 @ X2))),
% 3.50/3.74      inference('sup-', [status(thm)], ['3', '10'])).
% 3.50/3.74  thf('12', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 3.50/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.74  thf('13', plain,
% 3.50/3.74      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.50/3.74         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 3.50/3.74          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 3.50/3.74          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 3.50/3.74      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.50/3.74  thf('14', plain,
% 3.50/3.74      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.50/3.74        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 3.50/3.74      inference('sup-', [status(thm)], ['12', '13'])).
% 3.50/3.74  thf('15', plain,
% 3.50/3.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.50/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.74  thf(redefinition_k1_relset_1, axiom,
% 3.50/3.74    (![A:$i,B:$i,C:$i]:
% 3.50/3.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.50/3.74       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.50/3.74  thf('16', plain,
% 3.50/3.74      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.50/3.74         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 3.50/3.74          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 3.50/3.74      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.50/3.74  thf('17', plain,
% 3.50/3.74      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 3.50/3.74      inference('sup-', [status(thm)], ['15', '16'])).
% 3.50/3.74  thf('18', plain,
% 3.50/3.74      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.50/3.74        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.50/3.74      inference('demod', [status(thm)], ['14', '17'])).
% 3.50/3.74  thf('19', plain,
% 3.50/3.74      ((~ (v1_xboole_0 @ sk_D)
% 3.50/3.74        | (v1_xboole_0 @ sk_B_1)
% 3.50/3.74        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.50/3.74      inference('sup-', [status(thm)], ['11', '18'])).
% 3.50/3.74  thf('20', plain,
% 3.50/3.74      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 3.50/3.74      inference('sup+', [status(thm)], ['1', '2'])).
% 3.50/3.74  thf('21', plain,
% 3.50/3.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.50/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.74  thf('22', plain,
% 3.50/3.74      (![X31 : $i, X32 : $i, X33 : $i]:
% 3.50/3.74         (~ (zip_tseitin_0 @ X31 @ X32)
% 3.50/3.74          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 3.50/3.74          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 3.50/3.74      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.50/3.74  thf('23', plain,
% 3.50/3.74      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.50/3.74        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 3.50/3.74      inference('sup-', [status(thm)], ['21', '22'])).
% 3.50/3.74  thf('24', plain,
% 3.50/3.74      (((v1_xboole_0 @ sk_B_1) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 3.50/3.74      inference('sup-', [status(thm)], ['20', '23'])).
% 3.50/3.74  thf('25', plain,
% 3.50/3.74      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.50/3.74        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.50/3.74      inference('demod', [status(thm)], ['14', '17'])).
% 3.50/3.74  thf('26', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.50/3.74      inference('sup-', [status(thm)], ['24', '25'])).
% 3.50/3.74  thf('27', plain, ((((sk_A) = (k1_relat_1 @ sk_D)) | (v1_xboole_0 @ sk_B_1))),
% 3.50/3.74      inference('clc', [status(thm)], ['19', '26'])).
% 3.50/3.74  thf('28', plain,
% 3.50/3.74      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.50/3.74      inference('sup-', [status(thm)], ['4', '5'])).
% 3.50/3.74  thf(t3_xboole_1, axiom,
% 3.50/3.74    (![A:$i]:
% 3.50/3.74     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.50/3.74  thf('29', plain,
% 3.50/3.74      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ k1_xboole_0))),
% 3.50/3.74      inference('cnf', [status(esa)], [t3_xboole_1])).
% 3.50/3.74  thf('30', plain,
% 3.50/3.74      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 3.50/3.74      inference('sup-', [status(thm)], ['28', '29'])).
% 3.50/3.74  thf('31', plain,
% 3.50/3.74      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 3.50/3.74      inference('sup-', [status(thm)], ['28', '29'])).
% 3.50/3.74  thf('32', plain,
% 3.50/3.74      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 3.50/3.74      inference('sup-', [status(thm)], ['28', '29'])).
% 3.50/3.74  thf('33', plain,
% 3.50/3.74      (![X4 : $i, X6 : $i]:
% 3.50/3.74         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 3.50/3.74      inference('cnf', [status(esa)], [d3_tarski])).
% 3.50/3.74  thf('34', plain,
% 3.50/3.74      (![X4 : $i, X6 : $i]:
% 3.50/3.74         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 3.50/3.74      inference('cnf', [status(esa)], [d3_tarski])).
% 3.50/3.74  thf('35', plain,
% 3.50/3.74      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 3.50/3.74      inference('sup-', [status(thm)], ['33', '34'])).
% 3.50/3.74  thf('36', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 3.50/3.74      inference('simplify', [status(thm)], ['35'])).
% 3.50/3.74  thf('37', plain,
% 3.50/3.74      (![X11 : $i, X13 : $i]:
% 3.50/3.74         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 3.50/3.74      inference('cnf', [status(esa)], [t3_subset])).
% 3.50/3.74  thf('38', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 3.50/3.74      inference('sup-', [status(thm)], ['36', '37'])).
% 3.50/3.74  thf(t113_zfmisc_1, axiom,
% 3.50/3.74    (![A:$i,B:$i]:
% 3.50/3.74     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.50/3.74       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.50/3.74  thf('39', plain,
% 3.50/3.74      (![X9 : $i, X10 : $i]:
% 3.50/3.74         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X10) != (k1_xboole_0)))),
% 3.50/3.74      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.50/3.74  thf('40', plain,
% 3.50/3.74      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 3.50/3.74      inference('simplify', [status(thm)], ['39'])).
% 3.50/3.74  thf(redefinition_r2_relset_1, axiom,
% 3.50/3.74    (![A:$i,B:$i,C:$i,D:$i]:
% 3.50/3.74     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.50/3.74         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.50/3.74       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.50/3.74  thf('41', plain,
% 3.50/3.74      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 3.50/3.74         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 3.50/3.74          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 3.50/3.74          | (r2_relset_1 @ X23 @ X24 @ X22 @ X25)
% 3.50/3.74          | ((X22) != (X25)))),
% 3.50/3.74      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.50/3.74  thf('42', plain,
% 3.50/3.74      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.50/3.74         ((r2_relset_1 @ X23 @ X24 @ X25 @ X25)
% 3.50/3.74          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 3.50/3.74      inference('simplify', [status(thm)], ['41'])).
% 3.50/3.74  thf('43', plain,
% 3.50/3.74      (![X0 : $i, X1 : $i]:
% 3.50/3.74         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.50/3.74          | (r2_relset_1 @ X0 @ k1_xboole_0 @ X1 @ X1))),
% 3.50/3.74      inference('sup-', [status(thm)], ['40', '42'])).
% 3.50/3.74  thf('44', plain,
% 3.50/3.74      (![X0 : $i]: (r2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 3.50/3.74      inference('sup-', [status(thm)], ['38', '43'])).
% 3.50/3.74  thf('45', plain,
% 3.50/3.74      (![X0 : $i, X1 : $i]:
% 3.50/3.74         ((r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 3.50/3.74          | ~ (v1_xboole_0 @ X0))),
% 3.50/3.74      inference('sup+', [status(thm)], ['32', '44'])).
% 3.50/3.74  thf('46', plain,
% 3.50/3.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.74         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0)
% 3.50/3.74          | ~ (v1_xboole_0 @ X0)
% 3.50/3.74          | ~ (v1_xboole_0 @ X1))),
% 3.50/3.74      inference('sup+', [status(thm)], ['31', '45'])).
% 3.50/3.74  thf('47', plain,
% 3.50/3.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.50/3.74         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 3.50/3.74          | ~ (v1_xboole_0 @ X0)
% 3.50/3.74          | ~ (v1_xboole_0 @ X2)
% 3.50/3.74          | ~ (v1_xboole_0 @ X1))),
% 3.50/3.74      inference('sup+', [status(thm)], ['30', '46'])).
% 3.50/3.74  thf('48', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 3.50/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.74  thf('49', plain,
% 3.50/3.74      ((~ (v1_xboole_0 @ sk_C_2)
% 3.50/3.74        | ~ (v1_xboole_0 @ sk_B_1)
% 3.50/3.74        | ~ (v1_xboole_0 @ sk_D))),
% 3.50/3.74      inference('sup-', [status(thm)], ['47', '48'])).
% 3.50/3.74  thf('50', plain,
% 3.50/3.74      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 3.50/3.74      inference('sup-', [status(thm)], ['28', '29'])).
% 3.50/3.74  thf('51', plain,
% 3.50/3.74      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 3.50/3.74      inference('simplify', [status(thm)], ['39'])).
% 3.50/3.74  thf('52', plain,
% 3.50/3.74      (![X0 : $i, X1 : $i]:
% 3.50/3.74         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.50/3.74      inference('sup+', [status(thm)], ['50', '51'])).
% 3.50/3.74  thf('53', plain,
% 3.50/3.74      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.50/3.74      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.50/3.74  thf('54', plain,
% 3.50/3.74      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.50/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.74  thf('55', plain,
% 3.50/3.74      (![X11 : $i, X12 : $i]:
% 3.50/3.74         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 3.50/3.74      inference('cnf', [status(esa)], [t3_subset])).
% 3.50/3.74  thf('56', plain, ((r1_tarski @ sk_C_2 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 3.50/3.74      inference('sup-', [status(thm)], ['54', '55'])).
% 3.50/3.74  thf('57', plain,
% 3.50/3.74      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.50/3.74         (~ (r2_hidden @ X3 @ X4)
% 3.50/3.74          | (r2_hidden @ X3 @ X5)
% 3.50/3.74          | ~ (r1_tarski @ X4 @ X5))),
% 3.50/3.74      inference('cnf', [status(esa)], [d3_tarski])).
% 3.50/3.74  thf('58', plain,
% 3.50/3.74      (![X0 : $i]:
% 3.50/3.74         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 3.50/3.74          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 3.50/3.74      inference('sup-', [status(thm)], ['56', '57'])).
% 3.50/3.74  thf('59', plain,
% 3.50/3.74      (((v1_xboole_0 @ sk_C_2)
% 3.50/3.74        | (r2_hidden @ (sk_B @ sk_C_2) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.50/3.74      inference('sup-', [status(thm)], ['53', '58'])).
% 3.50/3.74  thf('60', plain,
% 3.50/3.74      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.50/3.74      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.50/3.74  thf('61', plain,
% 3.50/3.74      (((v1_xboole_0 @ sk_C_2)
% 3.50/3.74        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.50/3.74      inference('sup-', [status(thm)], ['59', '60'])).
% 3.50/3.74  thf('62', plain,
% 3.50/3.74      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.50/3.74        | ~ (v1_xboole_0 @ sk_B_1)
% 3.50/3.74        | (v1_xboole_0 @ sk_C_2))),
% 3.50/3.74      inference('sup-', [status(thm)], ['52', '61'])).
% 3.50/3.74  thf('63', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.50/3.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.50/3.74  thf('64', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_C_2))),
% 3.50/3.74      inference('demod', [status(thm)], ['62', '63'])).
% 3.50/3.74  thf('65', plain, ((~ (v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_B_1))),
% 3.50/3.74      inference('clc', [status(thm)], ['49', '64'])).
% 3.50/3.74  thf('66', plain,
% 3.50/3.74      (![X0 : $i, X1 : $i]:
% 3.50/3.74         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.50/3.74      inference('sup+', [status(thm)], ['50', '51'])).
% 3.50/3.74  thf('67', plain,
% 3.50/3.74      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.50/3.74      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.50/3.74  thf('68', plain,
% 3.50/3.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.50/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.74  thf('69', plain,
% 3.50/3.74      (![X11 : $i, X12 : $i]:
% 3.50/3.74         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 3.50/3.74      inference('cnf', [status(esa)], [t3_subset])).
% 3.50/3.74  thf('70', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 3.50/3.74      inference('sup-', [status(thm)], ['68', '69'])).
% 3.50/3.74  thf('71', plain,
% 3.50/3.74      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.50/3.74         (~ (r2_hidden @ X3 @ X4)
% 3.50/3.74          | (r2_hidden @ X3 @ X5)
% 3.50/3.74          | ~ (r1_tarski @ X4 @ X5))),
% 3.50/3.74      inference('cnf', [status(esa)], [d3_tarski])).
% 3.50/3.74  thf('72', plain,
% 3.50/3.74      (![X0 : $i]:
% 3.50/3.74         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 3.50/3.74          | ~ (r2_hidden @ X0 @ sk_D))),
% 3.50/3.74      inference('sup-', [status(thm)], ['70', '71'])).
% 3.50/3.74  thf('73', plain,
% 3.50/3.74      (((v1_xboole_0 @ sk_D)
% 3.50/3.74        | (r2_hidden @ (sk_B @ sk_D) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.50/3.74      inference('sup-', [status(thm)], ['67', '72'])).
% 3.50/3.74  thf('74', plain,
% 3.50/3.74      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.50/3.74      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.50/3.74  thf('75', plain,
% 3.50/3.74      (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.50/3.74      inference('sup-', [status(thm)], ['73', '74'])).
% 3.50/3.74  thf('76', plain,
% 3.50/3.74      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.50/3.74        | ~ (v1_xboole_0 @ sk_B_1)
% 3.50/3.74        | (v1_xboole_0 @ sk_D))),
% 3.50/3.74      inference('sup-', [status(thm)], ['66', '75'])).
% 3.50/3.74  thf('77', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.50/3.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.50/3.74  thf('78', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_D))),
% 3.50/3.74      inference('demod', [status(thm)], ['76', '77'])).
% 3.50/3.74  thf('79', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 3.50/3.74      inference('clc', [status(thm)], ['65', '78'])).
% 3.50/3.74  thf('80', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 3.50/3.74      inference('clc', [status(thm)], ['27', '79'])).
% 3.50/3.74  thf('81', plain,
% 3.50/3.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.74         ((v1_xboole_0 @ X1)
% 3.50/3.74          | (zip_tseitin_1 @ X2 @ X1 @ X0)
% 3.50/3.74          | ~ (v1_xboole_0 @ X2))),
% 3.50/3.74      inference('sup-', [status(thm)], ['3', '10'])).
% 3.50/3.74  thf('82', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 3.50/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.74  thf('83', plain,
% 3.50/3.74      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.50/3.74         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 3.50/3.74          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 3.50/3.74          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 3.50/3.74      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.50/3.74  thf('84', plain,
% 3.50/3.74      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 3.50/3.74        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 3.50/3.74      inference('sup-', [status(thm)], ['82', '83'])).
% 3.50/3.74  thf('85', plain,
% 3.50/3.74      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.50/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.74  thf('86', plain,
% 3.50/3.74      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.50/3.74         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 3.50/3.74          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 3.50/3.74      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.50/3.74  thf('87', plain,
% 3.50/3.74      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 3.50/3.74      inference('sup-', [status(thm)], ['85', '86'])).
% 3.50/3.74  thf('88', plain,
% 3.50/3.74      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 3.50/3.74        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.50/3.74      inference('demod', [status(thm)], ['84', '87'])).
% 3.50/3.74  thf('89', plain,
% 3.50/3.74      ((~ (v1_xboole_0 @ sk_C_2)
% 3.50/3.74        | (v1_xboole_0 @ sk_B_1)
% 3.50/3.74        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.50/3.74      inference('sup-', [status(thm)], ['81', '88'])).
% 3.50/3.74  thf('90', plain,
% 3.50/3.74      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 3.50/3.74      inference('sup+', [status(thm)], ['1', '2'])).
% 3.50/3.74  thf('91', plain,
% 3.50/3.74      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.50/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.74  thf('92', plain,
% 3.50/3.74      (![X31 : $i, X32 : $i, X33 : $i]:
% 3.50/3.74         (~ (zip_tseitin_0 @ X31 @ X32)
% 3.50/3.74          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 3.50/3.74          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 3.50/3.74      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.50/3.74  thf('93', plain,
% 3.50/3.74      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 3.50/3.74        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 3.50/3.74      inference('sup-', [status(thm)], ['91', '92'])).
% 3.50/3.74  thf('94', plain,
% 3.50/3.74      (((v1_xboole_0 @ sk_B_1) | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 3.50/3.74      inference('sup-', [status(thm)], ['90', '93'])).
% 3.50/3.74  thf('95', plain,
% 3.50/3.74      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 3.50/3.74        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.50/3.74      inference('demod', [status(thm)], ['84', '87'])).
% 3.50/3.74  thf('96', plain,
% 3.50/3.74      (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.50/3.74      inference('sup-', [status(thm)], ['94', '95'])).
% 3.50/3.74  thf('97', plain,
% 3.50/3.74      ((((sk_A) = (k1_relat_1 @ sk_C_2)) | (v1_xboole_0 @ sk_B_1))),
% 3.50/3.74      inference('clc', [status(thm)], ['89', '96'])).
% 3.50/3.74  thf('98', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 3.50/3.74      inference('clc', [status(thm)], ['65', '78'])).
% 3.50/3.74  thf('99', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 3.50/3.74      inference('clc', [status(thm)], ['97', '98'])).
% 3.50/3.74  thf(t9_funct_1, axiom,
% 3.50/3.74    (![A:$i]:
% 3.50/3.74     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.50/3.74       ( ![B:$i]:
% 3.50/3.74         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.50/3.74           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 3.50/3.74               ( ![C:$i]:
% 3.50/3.74                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 3.50/3.74                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 3.50/3.74             ( ( A ) = ( B ) ) ) ) ) ))).
% 3.50/3.74  thf('100', plain,
% 3.50/3.74      (![X14 : $i, X15 : $i]:
% 3.50/3.74         (~ (v1_relat_1 @ X14)
% 3.50/3.74          | ~ (v1_funct_1 @ X14)
% 3.50/3.74          | ((X15) = (X14))
% 3.50/3.74          | (r2_hidden @ (sk_C_1 @ X14 @ X15) @ (k1_relat_1 @ X15))
% 3.50/3.74          | ((k1_relat_1 @ X15) != (k1_relat_1 @ X14))
% 3.50/3.74          | ~ (v1_funct_1 @ X15)
% 3.50/3.74          | ~ (v1_relat_1 @ X15))),
% 3.50/3.74      inference('cnf', [status(esa)], [t9_funct_1])).
% 3.50/3.74  thf('101', plain,
% 3.50/3.74      (![X0 : $i]:
% 3.50/3.74         (((sk_A) != (k1_relat_1 @ X0))
% 3.50/3.74          | ~ (v1_relat_1 @ sk_C_2)
% 3.50/3.74          | ~ (v1_funct_1 @ sk_C_2)
% 3.50/3.74          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 3.50/3.74          | ((sk_C_2) = (X0))
% 3.50/3.74          | ~ (v1_funct_1 @ X0)
% 3.50/3.74          | ~ (v1_relat_1 @ X0))),
% 3.50/3.74      inference('sup-', [status(thm)], ['99', '100'])).
% 3.50/3.74  thf('102', plain,
% 3.50/3.74      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.50/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.74  thf(cc1_relset_1, axiom,
% 3.50/3.74    (![A:$i,B:$i,C:$i]:
% 3.50/3.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.50/3.74       ( v1_relat_1 @ C ) ))).
% 3.50/3.74  thf('103', plain,
% 3.50/3.74      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.50/3.74         ((v1_relat_1 @ X16)
% 3.50/3.74          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 3.50/3.74      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.50/3.74  thf('104', plain, ((v1_relat_1 @ sk_C_2)),
% 3.50/3.74      inference('sup-', [status(thm)], ['102', '103'])).
% 3.50/3.74  thf('105', plain, ((v1_funct_1 @ sk_C_2)),
% 3.50/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.74  thf('106', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 3.50/3.74      inference('clc', [status(thm)], ['97', '98'])).
% 3.50/3.74  thf('107', plain,
% 3.50/3.74      (![X0 : $i]:
% 3.50/3.74         (((sk_A) != (k1_relat_1 @ X0))
% 3.50/3.74          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A)
% 3.50/3.74          | ((sk_C_2) = (X0))
% 3.50/3.74          | ~ (v1_funct_1 @ X0)
% 3.50/3.74          | ~ (v1_relat_1 @ X0))),
% 3.50/3.74      inference('demod', [status(thm)], ['101', '104', '105', '106'])).
% 3.50/3.74  thf('108', plain,
% 3.50/3.74      ((((sk_A) != (sk_A))
% 3.50/3.74        | ~ (v1_relat_1 @ sk_D)
% 3.50/3.74        | ~ (v1_funct_1 @ sk_D)
% 3.50/3.74        | ((sk_C_2) = (sk_D))
% 3.50/3.74        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 3.50/3.74      inference('sup-', [status(thm)], ['80', '107'])).
% 3.50/3.74  thf('109', plain,
% 3.50/3.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.50/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.74  thf('110', plain,
% 3.50/3.74      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.50/3.74         ((v1_relat_1 @ X16)
% 3.50/3.74          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 3.50/3.74      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.50/3.74  thf('111', plain, ((v1_relat_1 @ sk_D)),
% 3.50/3.74      inference('sup-', [status(thm)], ['109', '110'])).
% 3.50/3.74  thf('112', plain, ((v1_funct_1 @ sk_D)),
% 3.50/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.74  thf('113', plain,
% 3.50/3.74      ((((sk_A) != (sk_A))
% 3.50/3.74        | ((sk_C_2) = (sk_D))
% 3.50/3.74        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 3.50/3.74      inference('demod', [status(thm)], ['108', '111', '112'])).
% 3.50/3.74  thf('114', plain,
% 3.50/3.74      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A) | ((sk_C_2) = (sk_D)))),
% 3.50/3.74      inference('simplify', [status(thm)], ['113'])).
% 3.50/3.74  thf('115', plain,
% 3.50/3.74      (![X34 : $i]:
% 3.50/3.74         (((k1_funct_1 @ sk_C_2 @ X34) = (k1_funct_1 @ sk_D @ X34))
% 3.50/3.74          | ~ (r2_hidden @ X34 @ sk_A))),
% 3.50/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.74  thf('116', plain,
% 3.50/3.74      ((((sk_C_2) = (sk_D))
% 3.50/3.74        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 3.50/3.74            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 3.50/3.74      inference('sup-', [status(thm)], ['114', '115'])).
% 3.50/3.74  thf('117', plain,
% 3.50/3.74      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 3.50/3.74         = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))),
% 3.50/3.74      inference('condensation', [status(thm)], ['116'])).
% 3.50/3.74  thf('118', plain,
% 3.50/3.74      (![X14 : $i, X15 : $i]:
% 3.50/3.74         (~ (v1_relat_1 @ X14)
% 3.50/3.74          | ~ (v1_funct_1 @ X14)
% 3.50/3.74          | ((X15) = (X14))
% 3.50/3.74          | ((k1_funct_1 @ X15 @ (sk_C_1 @ X14 @ X15))
% 3.50/3.74              != (k1_funct_1 @ X14 @ (sk_C_1 @ X14 @ X15)))
% 3.50/3.74          | ((k1_relat_1 @ X15) != (k1_relat_1 @ X14))
% 3.50/3.74          | ~ (v1_funct_1 @ X15)
% 3.50/3.74          | ~ (v1_relat_1 @ X15))),
% 3.50/3.74      inference('cnf', [status(esa)], [t9_funct_1])).
% 3.50/3.74  thf('119', plain,
% 3.50/3.74      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 3.50/3.74          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 3.50/3.74        | ~ (v1_relat_1 @ sk_C_2)
% 3.50/3.74        | ~ (v1_funct_1 @ sk_C_2)
% 3.50/3.74        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 3.50/3.74        | ((sk_C_2) = (sk_D))
% 3.50/3.74        | ~ (v1_funct_1 @ sk_D)
% 3.50/3.74        | ~ (v1_relat_1 @ sk_D))),
% 3.50/3.74      inference('sup-', [status(thm)], ['117', '118'])).
% 3.50/3.74  thf('120', plain, ((v1_relat_1 @ sk_C_2)),
% 3.50/3.74      inference('sup-', [status(thm)], ['102', '103'])).
% 3.50/3.74  thf('121', plain, ((v1_funct_1 @ sk_C_2)),
% 3.50/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.74  thf('122', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 3.50/3.74      inference('clc', [status(thm)], ['97', '98'])).
% 3.50/3.74  thf('123', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 3.50/3.74      inference('clc', [status(thm)], ['27', '79'])).
% 3.50/3.74  thf('124', plain, ((v1_funct_1 @ sk_D)),
% 3.50/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.74  thf('125', plain, ((v1_relat_1 @ sk_D)),
% 3.50/3.74      inference('sup-', [status(thm)], ['109', '110'])).
% 3.50/3.74  thf('126', plain,
% 3.50/3.74      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 3.50/3.74          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 3.50/3.74        | ((sk_A) != (sk_A))
% 3.50/3.74        | ((sk_C_2) = (sk_D)))),
% 3.50/3.74      inference('demod', [status(thm)],
% 3.50/3.74                ['119', '120', '121', '122', '123', '124', '125'])).
% 3.50/3.74  thf('127', plain, (((sk_C_2) = (sk_D))),
% 3.50/3.74      inference('simplify', [status(thm)], ['126'])).
% 3.50/3.74  thf('128', plain,
% 3.50/3.74      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.50/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.74  thf('129', plain,
% 3.50/3.74      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.50/3.74         ((r2_relset_1 @ X23 @ X24 @ X25 @ X25)
% 3.50/3.74          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 3.50/3.74      inference('simplify', [status(thm)], ['41'])).
% 3.50/3.74  thf('130', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2)),
% 3.50/3.74      inference('sup-', [status(thm)], ['128', '129'])).
% 3.50/3.74  thf('131', plain, ($false),
% 3.50/3.74      inference('demod', [status(thm)], ['0', '127', '130'])).
% 3.50/3.74  
% 3.50/3.74  % SZS output end Refutation
% 3.50/3.74  
% 3.50/3.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
