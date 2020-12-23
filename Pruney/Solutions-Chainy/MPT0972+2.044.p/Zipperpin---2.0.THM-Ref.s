%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qQtiG4VrlF

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:39 EST 2020

% Result     : Theorem 2.86s
% Output     : Refutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :  190 (1322 expanded)
%              Number of leaves         :   41 ( 428 expanded)
%              Depth                    :   26
%              Number of atoms          : 1345 (13147 expanded)
%              Number of equality atoms :  102 ( 641 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('3',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('11',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('14',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('18',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    r1_tarski @ sk_C_2 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( r2_hidden @ ( sk_B @ sk_C_2 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('25',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['16','25'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('28',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('30',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['29','36'])).

thf('38',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_B_1 = X0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['29','36'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['29','36'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['29','36'])).

thf('45',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('50',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( r2_relset_1 @ X26 @ X27 @ X25 @ X28 )
      | ( X25 != X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('51',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_relset_1 @ X26 @ X27 @ X28 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( r2_relset_1 @ X0 @ k1_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X3 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','55'])).

thf('57',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['29','36'])).

thf('60',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('63',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('65',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['58','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('68',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('69',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('71',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( r2_hidden @ ( sk_B @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['68','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('76',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['67','76'])).

thf('78',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('79',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['66','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['28','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('87',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('89',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('93',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('96',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['93','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['90','97'])).

thf('99',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('100',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('102',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('104',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_B_1 = X0 )
      | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['66','79'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['93','96'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['102','110'])).

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

thf('112',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( X21 = X20 )
      | ( r2_hidden @ ( sk_C_1 @ X20 @ X21 ) @ ( k1_relat_1 @ X21 ) )
      | ( ( k1_relat_1 @ X21 )
       != ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('115',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('116',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('117',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('118',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['102','110'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['113','118','119','120'])).

thf('122',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['85','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('125',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('127',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['122','127','128'])).

thf('130',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X37: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X37 )
        = ( k1_funct_1 @ sk_D @ X37 ) )
      | ~ ( r2_hidden @ X37 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( sk_C_2 = sk_D )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ),
    inference(condensation,[status(thm)],['132'])).

thf('134',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( X21 = X20 )
      | ( ( k1_funct_1 @ X21 @ ( sk_C_1 @ X20 @ X21 ) )
       != ( k1_funct_1 @ X20 @ ( sk_C_1 @ X20 @ X21 ) ) )
      | ( ( k1_relat_1 @ X21 )
       != ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('135',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['116','117'])).

thf('137',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['102','110'])).

thf('139',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['28','84'])).

thf('140',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['125','126'])).

thf('142',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['135','136','137','138','139','140','141'])).

thf('143',plain,(
    sk_C_2 = sk_D ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_relset_1 @ X26 @ X27 @ X28 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('146',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    $false ),
    inference(demod,[status(thm)],['0','143','146'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qQtiG4VrlF
% 0.16/0.38  % Computer   : n006.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 11:28:53 EST 2020
% 0.16/0.39  % CPUTime    : 
% 0.16/0.39  % Running portfolio for 600 s
% 0.16/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.39  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 2.86/3.06  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.86/3.06  % Solved by: fo/fo7.sh
% 2.86/3.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.86/3.06  % done 3007 iterations in 2.553s
% 2.86/3.06  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.86/3.06  % SZS output start Refutation
% 2.86/3.06  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 2.86/3.06  thf(sk_C_2_type, type, sk_C_2: $i).
% 2.86/3.06  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.86/3.06  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.86/3.06  thf(sk_D_type, type, sk_D: $i).
% 2.86/3.06  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.86/3.06  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.86/3.06  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.86/3.06  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 2.86/3.06  thf(sk_B_type, type, sk_B: $i > $i).
% 2.86/3.06  thf(sk_A_type, type, sk_A: $i).
% 2.86/3.06  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.86/3.06  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.86/3.06  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.86/3.06  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.86/3.06  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.86/3.06  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.86/3.06  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.86/3.06  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.86/3.06  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.86/3.06  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.86/3.06  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.86/3.06  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.86/3.06  thf(t18_funct_2, conjecture,
% 2.86/3.06    (![A:$i,B:$i,C:$i]:
% 2.86/3.06     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.86/3.06         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.86/3.06       ( ![D:$i]:
% 2.86/3.06         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.86/3.06             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.86/3.06           ( ( ![E:$i]:
% 2.86/3.06               ( ( r2_hidden @ E @ A ) =>
% 2.86/3.06                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 2.86/3.06             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 2.86/3.06  thf(zf_stmt_0, negated_conjecture,
% 2.86/3.06    (~( ![A:$i,B:$i,C:$i]:
% 2.86/3.06        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.86/3.06            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.86/3.06          ( ![D:$i]:
% 2.86/3.06            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.86/3.06                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.86/3.06              ( ( ![E:$i]:
% 2.86/3.06                  ( ( r2_hidden @ E @ A ) =>
% 2.86/3.06                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 2.86/3.06                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 2.86/3.06    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 2.86/3.06  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 2.86/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.06  thf(d1_funct_2, axiom,
% 2.86/3.06    (![A:$i,B:$i,C:$i]:
% 2.86/3.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.86/3.06       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.86/3.06           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.86/3.06             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.86/3.06         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.86/3.06           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.86/3.06             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.86/3.06  thf(zf_stmt_1, axiom,
% 2.86/3.06    (![B:$i,A:$i]:
% 2.86/3.06     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.86/3.06       ( zip_tseitin_0 @ B @ A ) ))).
% 2.86/3.06  thf('1', plain,
% 2.86/3.06      (![X29 : $i, X30 : $i]:
% 2.86/3.06         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 2.86/3.06      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.86/3.06  thf(t113_zfmisc_1, axiom,
% 2.86/3.06    (![A:$i,B:$i]:
% 2.86/3.06     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.86/3.06       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.86/3.06  thf('2', plain,
% 2.86/3.06      (![X11 : $i, X12 : $i]:
% 2.86/3.06         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 2.86/3.06          | ((X12) != (k1_xboole_0)))),
% 2.86/3.06      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.86/3.06  thf('3', plain,
% 2.86/3.06      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 2.86/3.06      inference('simplify', [status(thm)], ['2'])).
% 2.86/3.06  thf('4', plain,
% 2.86/3.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.86/3.06         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 2.86/3.06      inference('sup+', [status(thm)], ['1', '3'])).
% 2.86/3.06  thf('5', plain,
% 2.86/3.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.86/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.06  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.86/3.06  thf(zf_stmt_3, axiom,
% 2.86/3.06    (![C:$i,B:$i,A:$i]:
% 2.86/3.06     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.86/3.06       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.86/3.06  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.86/3.06  thf(zf_stmt_5, axiom,
% 2.86/3.06    (![A:$i,B:$i,C:$i]:
% 2.86/3.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.86/3.06       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.86/3.06         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.86/3.06           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.86/3.06             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.86/3.06  thf('6', plain,
% 2.86/3.06      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.86/3.06         (~ (zip_tseitin_0 @ X34 @ X35)
% 2.86/3.06          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 2.86/3.06          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 2.86/3.06      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.86/3.06  thf('7', plain,
% 2.86/3.06      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 2.86/3.06        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 2.86/3.06      inference('sup-', [status(thm)], ['5', '6'])).
% 2.86/3.06  thf('8', plain,
% 2.86/3.06      (![X0 : $i]:
% 2.86/3.06         (((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0))
% 2.86/3.06          | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 2.86/3.06      inference('sup-', [status(thm)], ['4', '7'])).
% 2.86/3.06  thf('9', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 2.86/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.06  thf('10', plain,
% 2.86/3.06      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.86/3.06         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 2.86/3.06          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 2.86/3.06          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 2.86/3.06      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.86/3.06  thf('11', plain,
% 2.86/3.06      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 2.86/3.06        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 2.86/3.06      inference('sup-', [status(thm)], ['9', '10'])).
% 2.86/3.06  thf('12', plain,
% 2.86/3.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.86/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.06  thf(redefinition_k1_relset_1, axiom,
% 2.86/3.06    (![A:$i,B:$i,C:$i]:
% 2.86/3.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.86/3.06       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.86/3.06  thf('13', plain,
% 2.86/3.06      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.86/3.06         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 2.86/3.06          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 2.86/3.06      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.86/3.06  thf('14', plain,
% 2.86/3.06      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 2.86/3.06      inference('sup-', [status(thm)], ['12', '13'])).
% 2.86/3.06  thf('15', plain,
% 2.86/3.06      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 2.86/3.06        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.86/3.06      inference('demod', [status(thm)], ['11', '14'])).
% 2.86/3.06  thf('16', plain,
% 2.86/3.06      (![X0 : $i]:
% 2.86/3.06         (((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0))
% 2.86/3.06          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.86/3.06      inference('sup-', [status(thm)], ['8', '15'])).
% 2.86/3.06  thf(d1_xboole_0, axiom,
% 2.86/3.06    (![A:$i]:
% 2.86/3.06     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.86/3.06  thf('17', plain,
% 2.86/3.06      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.86/3.06      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.86/3.06  thf('18', plain,
% 2.86/3.06      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.86/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.06  thf(t3_subset, axiom,
% 2.86/3.06    (![A:$i,B:$i]:
% 2.86/3.06     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.86/3.06  thf('19', plain,
% 2.86/3.06      (![X13 : $i, X14 : $i]:
% 2.86/3.06         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 2.86/3.06      inference('cnf', [status(esa)], [t3_subset])).
% 2.86/3.06  thf('20', plain, ((r1_tarski @ sk_C_2 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 2.86/3.06      inference('sup-', [status(thm)], ['18', '19'])).
% 2.86/3.06  thf(d3_tarski, axiom,
% 2.86/3.06    (![A:$i,B:$i]:
% 2.86/3.06     ( ( r1_tarski @ A @ B ) <=>
% 2.86/3.06       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.86/3.06  thf('21', plain,
% 2.86/3.06      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.86/3.06         (~ (r2_hidden @ X3 @ X4)
% 2.86/3.06          | (r2_hidden @ X3 @ X5)
% 2.86/3.06          | ~ (r1_tarski @ X4 @ X5))),
% 2.86/3.06      inference('cnf', [status(esa)], [d3_tarski])).
% 2.86/3.06  thf('22', plain,
% 2.86/3.06      (![X0 : $i]:
% 2.86/3.06         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 2.86/3.06          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 2.86/3.06      inference('sup-', [status(thm)], ['20', '21'])).
% 2.86/3.06  thf('23', plain,
% 2.86/3.06      (((v1_xboole_0 @ sk_C_2)
% 2.86/3.06        | (r2_hidden @ (sk_B @ sk_C_2) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.86/3.06      inference('sup-', [status(thm)], ['17', '22'])).
% 2.86/3.06  thf('24', plain,
% 2.86/3.06      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.86/3.06      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.86/3.06  thf('25', plain,
% 2.86/3.06      (((v1_xboole_0 @ sk_C_2)
% 2.86/3.06        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.86/3.06      inference('sup-', [status(thm)], ['23', '24'])).
% 2.86/3.06  thf('26', plain,
% 2.86/3.06      ((~ (v1_xboole_0 @ k1_xboole_0)
% 2.86/3.06        | ((sk_A) = (k1_relat_1 @ sk_D))
% 2.86/3.06        | (v1_xboole_0 @ sk_C_2))),
% 2.86/3.06      inference('sup-', [status(thm)], ['16', '25'])).
% 2.86/3.06  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.86/3.06  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.86/3.06      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.86/3.06  thf('28', plain, ((((sk_A) = (k1_relat_1 @ sk_D)) | (v1_xboole_0 @ sk_C_2))),
% 2.86/3.06      inference('demod', [status(thm)], ['26', '27'])).
% 2.86/3.06  thf('29', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.86/3.06      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.86/3.06  thf('30', plain,
% 2.86/3.06      (![X4 : $i, X6 : $i]:
% 2.86/3.06         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 2.86/3.06      inference('cnf', [status(esa)], [d3_tarski])).
% 2.86/3.06  thf('31', plain,
% 2.86/3.06      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.86/3.06      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.86/3.06  thf('32', plain,
% 2.86/3.06      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 2.86/3.06      inference('sup-', [status(thm)], ['30', '31'])).
% 2.86/3.06  thf('33', plain,
% 2.86/3.06      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 2.86/3.06      inference('sup-', [status(thm)], ['30', '31'])).
% 2.86/3.06  thf(d10_xboole_0, axiom,
% 2.86/3.06    (![A:$i,B:$i]:
% 2.86/3.06     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.86/3.06  thf('34', plain,
% 2.86/3.06      (![X7 : $i, X9 : $i]:
% 2.86/3.06         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 2.86/3.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.86/3.06  thf('35', plain,
% 2.86/3.06      (![X0 : $i, X1 : $i]:
% 2.86/3.06         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 2.86/3.06      inference('sup-', [status(thm)], ['33', '34'])).
% 2.86/3.06  thf('36', plain,
% 2.86/3.06      (![X0 : $i, X1 : $i]:
% 2.86/3.06         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.86/3.06      inference('sup-', [status(thm)], ['32', '35'])).
% 2.86/3.06  thf('37', plain,
% 2.86/3.06      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 2.86/3.06      inference('sup-', [status(thm)], ['29', '36'])).
% 2.86/3.06  thf('38', plain,
% 2.86/3.06      (![X29 : $i, X30 : $i]:
% 2.86/3.06         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 2.86/3.06      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.86/3.06  thf('39', plain,
% 2.86/3.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.86/3.06         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | (zip_tseitin_0 @ X1 @ X2))),
% 2.86/3.06      inference('sup+', [status(thm)], ['37', '38'])).
% 2.86/3.06  thf('40', plain,
% 2.86/3.06      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 2.86/3.06        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 2.86/3.06      inference('sup-', [status(thm)], ['5', '6'])).
% 2.86/3.06  thf('41', plain,
% 2.86/3.06      (![X0 : $i]:
% 2.86/3.06         (~ (v1_xboole_0 @ X0)
% 2.86/3.06          | ((sk_B_1) = (X0))
% 2.86/3.06          | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 2.86/3.06      inference('sup-', [status(thm)], ['39', '40'])).
% 2.86/3.06  thf('42', plain,
% 2.86/3.06      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 2.86/3.06      inference('sup-', [status(thm)], ['29', '36'])).
% 2.86/3.06  thf('43', plain,
% 2.86/3.06      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 2.86/3.06      inference('sup-', [status(thm)], ['29', '36'])).
% 2.86/3.06  thf('44', plain,
% 2.86/3.06      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 2.86/3.06      inference('sup-', [status(thm)], ['29', '36'])).
% 2.86/3.06  thf('45', plain,
% 2.86/3.06      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 2.86/3.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.86/3.06  thf('46', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 2.86/3.06      inference('simplify', [status(thm)], ['45'])).
% 2.86/3.06  thf('47', plain,
% 2.86/3.06      (![X13 : $i, X15 : $i]:
% 2.86/3.06         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 2.86/3.06      inference('cnf', [status(esa)], [t3_subset])).
% 2.86/3.06  thf('48', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.86/3.06      inference('sup-', [status(thm)], ['46', '47'])).
% 2.86/3.06  thf('49', plain,
% 2.86/3.06      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 2.86/3.06      inference('simplify', [status(thm)], ['2'])).
% 2.86/3.06  thf(redefinition_r2_relset_1, axiom,
% 2.86/3.06    (![A:$i,B:$i,C:$i,D:$i]:
% 2.86/3.06     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.86/3.06         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.86/3.06       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.86/3.06  thf('50', plain,
% 2.86/3.06      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 2.86/3.06         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 2.86/3.06          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 2.86/3.06          | (r2_relset_1 @ X26 @ X27 @ X25 @ X28)
% 2.86/3.06          | ((X25) != (X28)))),
% 2.86/3.06      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.86/3.06  thf('51', plain,
% 2.86/3.06      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.86/3.06         ((r2_relset_1 @ X26 @ X27 @ X28 @ X28)
% 2.86/3.06          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 2.86/3.06      inference('simplify', [status(thm)], ['50'])).
% 2.86/3.06  thf('52', plain,
% 2.86/3.06      (![X0 : $i, X1 : $i]:
% 2.86/3.06         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.86/3.06          | (r2_relset_1 @ X0 @ k1_xboole_0 @ X1 @ X1))),
% 2.86/3.06      inference('sup-', [status(thm)], ['49', '51'])).
% 2.86/3.06  thf('53', plain,
% 2.86/3.06      (![X0 : $i]: (r2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 2.86/3.06      inference('sup-', [status(thm)], ['48', '52'])).
% 2.86/3.06  thf('54', plain,
% 2.86/3.06      (![X0 : $i, X1 : $i]:
% 2.86/3.06         ((r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 2.86/3.06          | ~ (v1_xboole_0 @ X0))),
% 2.86/3.06      inference('sup+', [status(thm)], ['44', '53'])).
% 2.86/3.06  thf('55', plain,
% 2.86/3.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.86/3.06         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0)
% 2.86/3.06          | ~ (v1_xboole_0 @ X0)
% 2.86/3.06          | ~ (v1_xboole_0 @ X1))),
% 2.86/3.06      inference('sup+', [status(thm)], ['43', '54'])).
% 2.86/3.06  thf('56', plain,
% 2.86/3.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.86/3.06         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 2.86/3.06          | ~ (v1_xboole_0 @ X0)
% 2.86/3.06          | ~ (v1_xboole_0 @ X2)
% 2.86/3.06          | ~ (v1_xboole_0 @ X1))),
% 2.86/3.06      inference('sup+', [status(thm)], ['42', '55'])).
% 2.86/3.06  thf('57', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 2.86/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.06  thf('58', plain,
% 2.86/3.06      ((~ (v1_xboole_0 @ sk_C_2)
% 2.86/3.06        | ~ (v1_xboole_0 @ sk_B_1)
% 2.86/3.06        | ~ (v1_xboole_0 @ sk_D))),
% 2.86/3.06      inference('sup-', [status(thm)], ['56', '57'])).
% 2.86/3.06  thf('59', plain,
% 2.86/3.06      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 2.86/3.06      inference('sup-', [status(thm)], ['29', '36'])).
% 2.86/3.06  thf('60', plain,
% 2.86/3.06      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 2.86/3.06      inference('simplify', [status(thm)], ['2'])).
% 2.86/3.06  thf('61', plain,
% 2.86/3.06      (![X0 : $i, X1 : $i]:
% 2.86/3.06         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.86/3.06      inference('sup+', [status(thm)], ['59', '60'])).
% 2.86/3.06  thf('62', plain,
% 2.86/3.06      (((v1_xboole_0 @ sk_C_2)
% 2.86/3.06        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.86/3.06      inference('sup-', [status(thm)], ['23', '24'])).
% 2.86/3.06  thf('63', plain,
% 2.86/3.06      ((~ (v1_xboole_0 @ k1_xboole_0)
% 2.86/3.06        | ~ (v1_xboole_0 @ sk_B_1)
% 2.86/3.06        | (v1_xboole_0 @ sk_C_2))),
% 2.86/3.06      inference('sup-', [status(thm)], ['61', '62'])).
% 2.86/3.06  thf('64', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.86/3.06      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.86/3.06  thf('65', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_C_2))),
% 2.86/3.06      inference('demod', [status(thm)], ['63', '64'])).
% 2.86/3.06  thf('66', plain, ((~ (v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_B_1))),
% 2.86/3.06      inference('clc', [status(thm)], ['58', '65'])).
% 2.86/3.06  thf('67', plain,
% 2.86/3.06      (![X0 : $i, X1 : $i]:
% 2.86/3.06         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.86/3.06      inference('sup+', [status(thm)], ['59', '60'])).
% 2.86/3.06  thf('68', plain,
% 2.86/3.06      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.86/3.06      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.86/3.06  thf('69', plain,
% 2.86/3.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.86/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.06  thf('70', plain,
% 2.86/3.06      (![X13 : $i, X14 : $i]:
% 2.86/3.06         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 2.86/3.06      inference('cnf', [status(esa)], [t3_subset])).
% 2.86/3.06  thf('71', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 2.86/3.06      inference('sup-', [status(thm)], ['69', '70'])).
% 2.86/3.06  thf('72', plain,
% 2.86/3.06      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.86/3.06         (~ (r2_hidden @ X3 @ X4)
% 2.86/3.06          | (r2_hidden @ X3 @ X5)
% 2.86/3.06          | ~ (r1_tarski @ X4 @ X5))),
% 2.86/3.06      inference('cnf', [status(esa)], [d3_tarski])).
% 2.86/3.06  thf('73', plain,
% 2.86/3.06      (![X0 : $i]:
% 2.86/3.06         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 2.86/3.06          | ~ (r2_hidden @ X0 @ sk_D))),
% 2.86/3.06      inference('sup-', [status(thm)], ['71', '72'])).
% 2.86/3.06  thf('74', plain,
% 2.86/3.06      (((v1_xboole_0 @ sk_D)
% 2.86/3.06        | (r2_hidden @ (sk_B @ sk_D) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.86/3.06      inference('sup-', [status(thm)], ['68', '73'])).
% 2.86/3.06  thf('75', plain,
% 2.86/3.06      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.86/3.06      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.86/3.06  thf('76', plain,
% 2.86/3.06      (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.86/3.06      inference('sup-', [status(thm)], ['74', '75'])).
% 2.86/3.06  thf('77', plain,
% 2.86/3.06      ((~ (v1_xboole_0 @ k1_xboole_0)
% 2.86/3.06        | ~ (v1_xboole_0 @ sk_B_1)
% 2.86/3.06        | (v1_xboole_0 @ sk_D))),
% 2.86/3.06      inference('sup-', [status(thm)], ['67', '76'])).
% 2.86/3.06  thf('78', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.86/3.06      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.86/3.06  thf('79', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_D))),
% 2.86/3.06      inference('demod', [status(thm)], ['77', '78'])).
% 2.86/3.06  thf('80', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 2.86/3.06      inference('clc', [status(thm)], ['66', '79'])).
% 2.86/3.06  thf('81', plain,
% 2.86/3.06      (![X0 : $i]:
% 2.86/3.06         (~ (v1_xboole_0 @ X0)
% 2.86/3.06          | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 2.86/3.06          | ~ (v1_xboole_0 @ X0))),
% 2.86/3.06      inference('sup-', [status(thm)], ['41', '80'])).
% 2.86/3.06  thf('82', plain,
% 2.86/3.06      (![X0 : $i]:
% 2.86/3.06         ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 2.86/3.06      inference('simplify', [status(thm)], ['81'])).
% 2.86/3.06  thf('83', plain,
% 2.86/3.06      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 2.86/3.06        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.86/3.06      inference('demod', [status(thm)], ['11', '14'])).
% 2.86/3.06  thf('84', plain,
% 2.86/3.06      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.86/3.06      inference('sup-', [status(thm)], ['82', '83'])).
% 2.86/3.06  thf('85', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 2.86/3.06      inference('clc', [status(thm)], ['28', '84'])).
% 2.86/3.06  thf('86', plain,
% 2.86/3.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.86/3.06         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 2.86/3.06      inference('sup+', [status(thm)], ['1', '3'])).
% 2.86/3.06  thf('87', plain,
% 2.86/3.06      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.86/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.06  thf('88', plain,
% 2.86/3.06      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.86/3.06         (~ (zip_tseitin_0 @ X34 @ X35)
% 2.86/3.06          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 2.86/3.06          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 2.86/3.06      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.86/3.06  thf('89', plain,
% 2.86/3.06      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 2.86/3.06        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 2.86/3.06      inference('sup-', [status(thm)], ['87', '88'])).
% 2.86/3.06  thf('90', plain,
% 2.86/3.06      (![X0 : $i]:
% 2.86/3.06         (((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0))
% 2.86/3.06          | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 2.86/3.06      inference('sup-', [status(thm)], ['86', '89'])).
% 2.86/3.06  thf('91', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 2.86/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.06  thf('92', plain,
% 2.86/3.06      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.86/3.06         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 2.86/3.06          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 2.86/3.06          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 2.86/3.06      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.86/3.06  thf('93', plain,
% 2.86/3.06      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 2.86/3.06        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 2.86/3.06      inference('sup-', [status(thm)], ['91', '92'])).
% 2.86/3.06  thf('94', plain,
% 2.86/3.06      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.86/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.06  thf('95', plain,
% 2.86/3.06      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.86/3.06         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 2.86/3.06          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 2.86/3.06      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.86/3.06  thf('96', plain,
% 2.86/3.06      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 2.86/3.06      inference('sup-', [status(thm)], ['94', '95'])).
% 2.86/3.06  thf('97', plain,
% 2.86/3.06      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 2.86/3.06        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 2.86/3.06      inference('demod', [status(thm)], ['93', '96'])).
% 2.86/3.06  thf('98', plain,
% 2.86/3.06      (![X0 : $i]:
% 2.86/3.06         (((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0))
% 2.86/3.06          | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 2.86/3.06      inference('sup-', [status(thm)], ['90', '97'])).
% 2.86/3.06  thf('99', plain,
% 2.86/3.06      (((v1_xboole_0 @ sk_C_2)
% 2.86/3.06        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.86/3.06      inference('sup-', [status(thm)], ['23', '24'])).
% 2.86/3.06  thf('100', plain,
% 2.86/3.06      ((~ (v1_xboole_0 @ k1_xboole_0)
% 2.86/3.06        | ((sk_A) = (k1_relat_1 @ sk_C_2))
% 2.86/3.06        | (v1_xboole_0 @ sk_C_2))),
% 2.86/3.06      inference('sup-', [status(thm)], ['98', '99'])).
% 2.86/3.06  thf('101', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.86/3.06      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.86/3.06  thf('102', plain,
% 2.86/3.06      ((((sk_A) = (k1_relat_1 @ sk_C_2)) | (v1_xboole_0 @ sk_C_2))),
% 2.86/3.06      inference('demod', [status(thm)], ['100', '101'])).
% 2.86/3.06  thf('103', plain,
% 2.86/3.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.86/3.06         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | (zip_tseitin_0 @ X1 @ X2))),
% 2.86/3.06      inference('sup+', [status(thm)], ['37', '38'])).
% 2.86/3.06  thf('104', plain,
% 2.86/3.06      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 2.86/3.06        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 2.86/3.06      inference('sup-', [status(thm)], ['87', '88'])).
% 2.86/3.06  thf('105', plain,
% 2.86/3.06      (![X0 : $i]:
% 2.86/3.06         (~ (v1_xboole_0 @ X0)
% 2.86/3.06          | ((sk_B_1) = (X0))
% 2.86/3.06          | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 2.86/3.06      inference('sup-', [status(thm)], ['103', '104'])).
% 2.86/3.06  thf('106', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 2.86/3.06      inference('clc', [status(thm)], ['66', '79'])).
% 2.86/3.06  thf('107', plain,
% 2.86/3.06      (![X0 : $i]:
% 2.86/3.06         (~ (v1_xboole_0 @ X0)
% 2.86/3.06          | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 2.86/3.06          | ~ (v1_xboole_0 @ X0))),
% 2.86/3.06      inference('sup-', [status(thm)], ['105', '106'])).
% 2.86/3.06  thf('108', plain,
% 2.86/3.06      (![X0 : $i]:
% 2.86/3.06         ((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 2.86/3.06      inference('simplify', [status(thm)], ['107'])).
% 2.86/3.06  thf('109', plain,
% 2.86/3.06      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 2.86/3.06        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 2.86/3.06      inference('demod', [status(thm)], ['93', '96'])).
% 2.86/3.06  thf('110', plain,
% 2.86/3.06      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 2.86/3.06      inference('sup-', [status(thm)], ['108', '109'])).
% 2.86/3.06  thf('111', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 2.86/3.06      inference('clc', [status(thm)], ['102', '110'])).
% 2.86/3.06  thf(t9_funct_1, axiom,
% 2.86/3.06    (![A:$i]:
% 2.86/3.06     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.86/3.06       ( ![B:$i]:
% 2.86/3.06         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.86/3.06           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 2.86/3.06               ( ![C:$i]:
% 2.86/3.06                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 2.86/3.06                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 2.86/3.06             ( ( A ) = ( B ) ) ) ) ) ))).
% 2.86/3.06  thf('112', plain,
% 2.86/3.06      (![X20 : $i, X21 : $i]:
% 2.86/3.06         (~ (v1_relat_1 @ X20)
% 2.86/3.06          | ~ (v1_funct_1 @ X20)
% 2.86/3.06          | ((X21) = (X20))
% 2.86/3.06          | (r2_hidden @ (sk_C_1 @ X20 @ X21) @ (k1_relat_1 @ X21))
% 2.86/3.06          | ((k1_relat_1 @ X21) != (k1_relat_1 @ X20))
% 2.86/3.06          | ~ (v1_funct_1 @ X21)
% 2.86/3.06          | ~ (v1_relat_1 @ X21))),
% 2.86/3.06      inference('cnf', [status(esa)], [t9_funct_1])).
% 2.86/3.06  thf('113', plain,
% 2.86/3.06      (![X0 : $i]:
% 2.86/3.06         (((sk_A) != (k1_relat_1 @ X0))
% 2.86/3.06          | ~ (v1_relat_1 @ sk_C_2)
% 2.86/3.06          | ~ (v1_funct_1 @ sk_C_2)
% 2.86/3.06          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 2.86/3.06          | ((sk_C_2) = (X0))
% 2.86/3.06          | ~ (v1_funct_1 @ X0)
% 2.86/3.06          | ~ (v1_relat_1 @ X0))),
% 2.86/3.06      inference('sup-', [status(thm)], ['111', '112'])).
% 2.86/3.06  thf('114', plain,
% 2.86/3.06      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.86/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.06  thf(cc2_relat_1, axiom,
% 2.86/3.06    (![A:$i]:
% 2.86/3.06     ( ( v1_relat_1 @ A ) =>
% 2.86/3.06       ( ![B:$i]:
% 2.86/3.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.86/3.06  thf('115', plain,
% 2.86/3.06      (![X16 : $i, X17 : $i]:
% 2.86/3.06         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 2.86/3.06          | (v1_relat_1 @ X16)
% 2.86/3.06          | ~ (v1_relat_1 @ X17))),
% 2.86/3.06      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.86/3.06  thf('116', plain,
% 2.86/3.06      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C_2))),
% 2.86/3.06      inference('sup-', [status(thm)], ['114', '115'])).
% 2.86/3.06  thf(fc6_relat_1, axiom,
% 2.86/3.06    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.86/3.06  thf('117', plain,
% 2.86/3.06      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 2.86/3.06      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.86/3.06  thf('118', plain, ((v1_relat_1 @ sk_C_2)),
% 2.86/3.06      inference('demod', [status(thm)], ['116', '117'])).
% 2.86/3.06  thf('119', plain, ((v1_funct_1 @ sk_C_2)),
% 2.86/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.06  thf('120', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 2.86/3.06      inference('clc', [status(thm)], ['102', '110'])).
% 2.86/3.06  thf('121', plain,
% 2.86/3.06      (![X0 : $i]:
% 2.86/3.06         (((sk_A) != (k1_relat_1 @ X0))
% 2.86/3.06          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A)
% 2.86/3.06          | ((sk_C_2) = (X0))
% 2.86/3.06          | ~ (v1_funct_1 @ X0)
% 2.86/3.06          | ~ (v1_relat_1 @ X0))),
% 2.86/3.06      inference('demod', [status(thm)], ['113', '118', '119', '120'])).
% 2.86/3.06  thf('122', plain,
% 2.86/3.06      ((((sk_A) != (sk_A))
% 2.86/3.06        | ~ (v1_relat_1 @ sk_D)
% 2.86/3.06        | ~ (v1_funct_1 @ sk_D)
% 2.86/3.06        | ((sk_C_2) = (sk_D))
% 2.86/3.06        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 2.86/3.06      inference('sup-', [status(thm)], ['85', '121'])).
% 2.86/3.06  thf('123', plain,
% 2.86/3.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.86/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.06  thf('124', plain,
% 2.86/3.06      (![X16 : $i, X17 : $i]:
% 2.86/3.06         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 2.86/3.06          | (v1_relat_1 @ X16)
% 2.86/3.06          | ~ (v1_relat_1 @ X17))),
% 2.86/3.06      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.86/3.06  thf('125', plain,
% 2.86/3.06      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D))),
% 2.86/3.06      inference('sup-', [status(thm)], ['123', '124'])).
% 2.86/3.06  thf('126', plain,
% 2.86/3.06      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 2.86/3.06      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.86/3.06  thf('127', plain, ((v1_relat_1 @ sk_D)),
% 2.86/3.06      inference('demod', [status(thm)], ['125', '126'])).
% 2.86/3.06  thf('128', plain, ((v1_funct_1 @ sk_D)),
% 2.86/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.06  thf('129', plain,
% 2.86/3.06      ((((sk_A) != (sk_A))
% 2.86/3.06        | ((sk_C_2) = (sk_D))
% 2.86/3.06        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 2.86/3.06      inference('demod', [status(thm)], ['122', '127', '128'])).
% 2.86/3.06  thf('130', plain,
% 2.86/3.06      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A) | ((sk_C_2) = (sk_D)))),
% 2.86/3.06      inference('simplify', [status(thm)], ['129'])).
% 2.86/3.06  thf('131', plain,
% 2.86/3.06      (![X37 : $i]:
% 2.86/3.06         (((k1_funct_1 @ sk_C_2 @ X37) = (k1_funct_1 @ sk_D @ X37))
% 2.86/3.06          | ~ (r2_hidden @ X37 @ sk_A))),
% 2.86/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.06  thf('132', plain,
% 2.86/3.06      ((((sk_C_2) = (sk_D))
% 2.86/3.06        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 2.86/3.06            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 2.86/3.06      inference('sup-', [status(thm)], ['130', '131'])).
% 2.86/3.06  thf('133', plain,
% 2.86/3.06      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 2.86/3.06         = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))),
% 2.86/3.06      inference('condensation', [status(thm)], ['132'])).
% 2.86/3.06  thf('134', plain,
% 2.86/3.06      (![X20 : $i, X21 : $i]:
% 2.86/3.06         (~ (v1_relat_1 @ X20)
% 2.86/3.06          | ~ (v1_funct_1 @ X20)
% 2.86/3.06          | ((X21) = (X20))
% 2.86/3.06          | ((k1_funct_1 @ X21 @ (sk_C_1 @ X20 @ X21))
% 2.86/3.06              != (k1_funct_1 @ X20 @ (sk_C_1 @ X20 @ X21)))
% 2.86/3.06          | ((k1_relat_1 @ X21) != (k1_relat_1 @ X20))
% 2.86/3.06          | ~ (v1_funct_1 @ X21)
% 2.86/3.06          | ~ (v1_relat_1 @ X21))),
% 2.86/3.06      inference('cnf', [status(esa)], [t9_funct_1])).
% 2.86/3.06  thf('135', plain,
% 2.86/3.06      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 2.86/3.06          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 2.86/3.06        | ~ (v1_relat_1 @ sk_C_2)
% 2.86/3.06        | ~ (v1_funct_1 @ sk_C_2)
% 2.86/3.06        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 2.86/3.06        | ((sk_C_2) = (sk_D))
% 2.86/3.06        | ~ (v1_funct_1 @ sk_D)
% 2.86/3.06        | ~ (v1_relat_1 @ sk_D))),
% 2.86/3.06      inference('sup-', [status(thm)], ['133', '134'])).
% 2.86/3.06  thf('136', plain, ((v1_relat_1 @ sk_C_2)),
% 2.86/3.06      inference('demod', [status(thm)], ['116', '117'])).
% 2.86/3.06  thf('137', plain, ((v1_funct_1 @ sk_C_2)),
% 2.86/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.06  thf('138', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 2.86/3.06      inference('clc', [status(thm)], ['102', '110'])).
% 2.86/3.06  thf('139', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 2.86/3.06      inference('clc', [status(thm)], ['28', '84'])).
% 2.86/3.06  thf('140', plain, ((v1_funct_1 @ sk_D)),
% 2.86/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.06  thf('141', plain, ((v1_relat_1 @ sk_D)),
% 2.86/3.06      inference('demod', [status(thm)], ['125', '126'])).
% 2.86/3.06  thf('142', plain,
% 2.86/3.06      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 2.86/3.06          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 2.86/3.06        | ((sk_A) != (sk_A))
% 2.86/3.06        | ((sk_C_2) = (sk_D)))),
% 2.86/3.06      inference('demod', [status(thm)],
% 2.86/3.06                ['135', '136', '137', '138', '139', '140', '141'])).
% 2.86/3.06  thf('143', plain, (((sk_C_2) = (sk_D))),
% 2.86/3.06      inference('simplify', [status(thm)], ['142'])).
% 2.86/3.06  thf('144', plain,
% 2.86/3.06      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.86/3.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.06  thf('145', plain,
% 2.86/3.06      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.86/3.06         ((r2_relset_1 @ X26 @ X27 @ X28 @ X28)
% 2.86/3.06          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 2.86/3.06      inference('simplify', [status(thm)], ['50'])).
% 2.86/3.06  thf('146', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2)),
% 2.86/3.06      inference('sup-', [status(thm)], ['144', '145'])).
% 2.86/3.06  thf('147', plain, ($false),
% 2.86/3.06      inference('demod', [status(thm)], ['0', '143', '146'])).
% 2.86/3.06  
% 2.86/3.06  % SZS output end Refutation
% 2.86/3.06  
% 2.86/3.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
