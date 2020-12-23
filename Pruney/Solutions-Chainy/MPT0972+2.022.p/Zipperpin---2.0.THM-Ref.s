%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.w1z9xf1ih5

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:36 EST 2020

% Result     : Theorem 3.34s
% Output     : Refutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  190 (1328 expanded)
%              Number of leaves         :   40 ( 430 expanded)
%              Depth                    :   24
%              Number of atoms          : 1353 (13217 expanded)
%              Number of equality atoms :  109 ( 683 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( r2_relset_1 @ X25 @ X26 @ X24 @ X27 )
      | ( X24 != X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('51',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_relset_1 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
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

thf('99',plain,(
    r1_tarski @ sk_C_2 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('101',plain,
    ( ( sk_C_2
      = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_C_2
      = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('104',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_C_2
      = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('106',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['66','79'])).

thf('108',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('110',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('113',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['93','96'])).

thf('115',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['108','115'])).

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

thf('117',plain,(
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

thf('118',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('120',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('121',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['108','115'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['118','121','122','123'])).

thf('125',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['85','124'])).

thf('126',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('128',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['125','128','129'])).

thf('131',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ! [X36: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X36 )
        = ( k1_funct_1 @ sk_D @ X36 ) )
      | ~ ( r2_hidden @ X36 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( sk_C_2 = sk_D )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ),
    inference(condensation,[status(thm)],['133'])).

thf('135',plain,(
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

thf('136',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['119','120'])).

thf('138',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['108','115'])).

thf('140',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['28','84'])).

thf('141',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['126','127'])).

thf('143',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['136','137','138','139','140','141','142'])).

thf('144',plain,(
    sk_C_2 = sk_D ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_relset_1 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('147',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    $false ),
    inference(demod,[status(thm)],['0','144','147'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.w1z9xf1ih5
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:03:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 3.34/3.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.34/3.55  % Solved by: fo/fo7.sh
% 3.34/3.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.34/3.55  % done 3371 iterations in 3.083s
% 3.34/3.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.34/3.55  % SZS output start Refutation
% 3.34/3.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 3.34/3.55  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 3.34/3.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.34/3.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.34/3.55  thf(sk_A_type, type, sk_A: $i).
% 3.34/3.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.34/3.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.34/3.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.34/3.55  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.34/3.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.34/3.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.34/3.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.34/3.55  thf(sk_C_2_type, type, sk_C_2: $i).
% 3.34/3.55  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.34/3.55  thf(sk_D_type, type, sk_D: $i).
% 3.34/3.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.34/3.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.34/3.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.34/3.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.34/3.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.34/3.55  thf(sk_B_type, type, sk_B: $i > $i).
% 3.34/3.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.34/3.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.34/3.55  thf(t18_funct_2, conjecture,
% 3.34/3.55    (![A:$i,B:$i,C:$i]:
% 3.34/3.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.34/3.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.34/3.55       ( ![D:$i]:
% 3.34/3.55         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.34/3.55             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.34/3.55           ( ( ![E:$i]:
% 3.34/3.55               ( ( r2_hidden @ E @ A ) =>
% 3.34/3.55                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 3.34/3.55             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 3.34/3.55  thf(zf_stmt_0, negated_conjecture,
% 3.34/3.55    (~( ![A:$i,B:$i,C:$i]:
% 3.34/3.55        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.34/3.55            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.34/3.55          ( ![D:$i]:
% 3.34/3.55            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.34/3.55                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.34/3.55              ( ( ![E:$i]:
% 3.34/3.55                  ( ( r2_hidden @ E @ A ) =>
% 3.34/3.55                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 3.34/3.55                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 3.34/3.55    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 3.34/3.55  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 3.34/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.55  thf(d1_funct_2, axiom,
% 3.34/3.55    (![A:$i,B:$i,C:$i]:
% 3.34/3.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.34/3.55       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.34/3.55           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.34/3.55             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.34/3.55         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.34/3.55           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.34/3.55             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.34/3.55  thf(zf_stmt_1, axiom,
% 3.34/3.55    (![B:$i,A:$i]:
% 3.34/3.55     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.34/3.55       ( zip_tseitin_0 @ B @ A ) ))).
% 3.34/3.55  thf('1', plain,
% 3.34/3.55      (![X28 : $i, X29 : $i]:
% 3.34/3.55         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 3.34/3.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.34/3.55  thf(t113_zfmisc_1, axiom,
% 3.34/3.55    (![A:$i,B:$i]:
% 3.34/3.55     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.34/3.55       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.34/3.55  thf('2', plain,
% 3.34/3.55      (![X11 : $i, X12 : $i]:
% 3.34/3.55         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 3.34/3.55          | ((X12) != (k1_xboole_0)))),
% 3.34/3.55      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.34/3.55  thf('3', plain,
% 3.34/3.55      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 3.34/3.55      inference('simplify', [status(thm)], ['2'])).
% 3.34/3.55  thf('4', plain,
% 3.34/3.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.34/3.55         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 3.34/3.55      inference('sup+', [status(thm)], ['1', '3'])).
% 3.34/3.55  thf('5', plain,
% 3.34/3.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.34/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.55  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.34/3.55  thf(zf_stmt_3, axiom,
% 3.34/3.55    (![C:$i,B:$i,A:$i]:
% 3.34/3.55     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.34/3.55       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.34/3.55  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.34/3.55  thf(zf_stmt_5, axiom,
% 3.34/3.55    (![A:$i,B:$i,C:$i]:
% 3.34/3.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.34/3.55       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.34/3.55         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.34/3.55           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.34/3.55             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.34/3.55  thf('6', plain,
% 3.34/3.55      (![X33 : $i, X34 : $i, X35 : $i]:
% 3.34/3.55         (~ (zip_tseitin_0 @ X33 @ X34)
% 3.34/3.55          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 3.34/3.55          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 3.34/3.55      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.34/3.55  thf('7', plain,
% 3.34/3.55      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.34/3.55        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 3.34/3.55      inference('sup-', [status(thm)], ['5', '6'])).
% 3.34/3.55  thf('8', plain,
% 3.34/3.55      (![X0 : $i]:
% 3.34/3.55         (((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0))
% 3.34/3.55          | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 3.34/3.55      inference('sup-', [status(thm)], ['4', '7'])).
% 3.34/3.55  thf('9', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 3.34/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.55  thf('10', plain,
% 3.34/3.55      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.34/3.55         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 3.34/3.55          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 3.34/3.55          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 3.34/3.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.34/3.55  thf('11', plain,
% 3.34/3.55      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.34/3.55        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 3.34/3.55      inference('sup-', [status(thm)], ['9', '10'])).
% 3.34/3.55  thf('12', plain,
% 3.34/3.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.34/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.55  thf(redefinition_k1_relset_1, axiom,
% 3.34/3.55    (![A:$i,B:$i,C:$i]:
% 3.34/3.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.34/3.55       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.34/3.55  thf('13', plain,
% 3.34/3.55      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.34/3.55         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 3.34/3.55          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 3.34/3.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.34/3.55  thf('14', plain,
% 3.34/3.55      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 3.34/3.55      inference('sup-', [status(thm)], ['12', '13'])).
% 3.34/3.55  thf('15', plain,
% 3.34/3.55      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.34/3.55        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.34/3.55      inference('demod', [status(thm)], ['11', '14'])).
% 3.34/3.55  thf('16', plain,
% 3.34/3.55      (![X0 : $i]:
% 3.34/3.55         (((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0))
% 3.34/3.55          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.34/3.55      inference('sup-', [status(thm)], ['8', '15'])).
% 3.34/3.55  thf(d1_xboole_0, axiom,
% 3.34/3.55    (![A:$i]:
% 3.34/3.55     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 3.34/3.55  thf('17', plain,
% 3.34/3.55      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.34/3.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.34/3.55  thf('18', plain,
% 3.34/3.55      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.34/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.55  thf(t3_subset, axiom,
% 3.34/3.55    (![A:$i,B:$i]:
% 3.34/3.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.34/3.55  thf('19', plain,
% 3.34/3.55      (![X13 : $i, X14 : $i]:
% 3.34/3.55         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 3.34/3.55      inference('cnf', [status(esa)], [t3_subset])).
% 3.34/3.55  thf('20', plain, ((r1_tarski @ sk_C_2 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 3.34/3.55      inference('sup-', [status(thm)], ['18', '19'])).
% 3.34/3.55  thf(d3_tarski, axiom,
% 3.34/3.55    (![A:$i,B:$i]:
% 3.34/3.55     ( ( r1_tarski @ A @ B ) <=>
% 3.34/3.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.34/3.55  thf('21', plain,
% 3.34/3.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.34/3.55         (~ (r2_hidden @ X3 @ X4)
% 3.34/3.55          | (r2_hidden @ X3 @ X5)
% 3.34/3.55          | ~ (r1_tarski @ X4 @ X5))),
% 3.34/3.55      inference('cnf', [status(esa)], [d3_tarski])).
% 3.34/3.55  thf('22', plain,
% 3.34/3.55      (![X0 : $i]:
% 3.34/3.55         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 3.34/3.55          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 3.34/3.55      inference('sup-', [status(thm)], ['20', '21'])).
% 3.34/3.55  thf('23', plain,
% 3.34/3.55      (((v1_xboole_0 @ sk_C_2)
% 3.34/3.55        | (r2_hidden @ (sk_B @ sk_C_2) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.34/3.55      inference('sup-', [status(thm)], ['17', '22'])).
% 3.34/3.55  thf('24', plain,
% 3.34/3.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.34/3.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.34/3.55  thf('25', plain,
% 3.34/3.55      (((v1_xboole_0 @ sk_C_2)
% 3.34/3.55        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.34/3.55      inference('sup-', [status(thm)], ['23', '24'])).
% 3.34/3.55  thf('26', plain,
% 3.34/3.55      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.34/3.55        | ((sk_A) = (k1_relat_1 @ sk_D))
% 3.34/3.55        | (v1_xboole_0 @ sk_C_2))),
% 3.34/3.55      inference('sup-', [status(thm)], ['16', '25'])).
% 3.34/3.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.34/3.55  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.34/3.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.34/3.55  thf('28', plain, ((((sk_A) = (k1_relat_1 @ sk_D)) | (v1_xboole_0 @ sk_C_2))),
% 3.34/3.55      inference('demod', [status(thm)], ['26', '27'])).
% 3.34/3.55  thf('29', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.34/3.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.34/3.55  thf('30', plain,
% 3.34/3.55      (![X4 : $i, X6 : $i]:
% 3.34/3.55         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 3.34/3.55      inference('cnf', [status(esa)], [d3_tarski])).
% 3.34/3.55  thf('31', plain,
% 3.34/3.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.34/3.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.34/3.55  thf('32', plain,
% 3.34/3.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.34/3.55      inference('sup-', [status(thm)], ['30', '31'])).
% 3.34/3.55  thf('33', plain,
% 3.34/3.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.34/3.55      inference('sup-', [status(thm)], ['30', '31'])).
% 3.34/3.55  thf(d10_xboole_0, axiom,
% 3.34/3.55    (![A:$i,B:$i]:
% 3.34/3.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.34/3.55  thf('34', plain,
% 3.34/3.55      (![X7 : $i, X9 : $i]:
% 3.34/3.55         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 3.34/3.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.34/3.55  thf('35', plain,
% 3.34/3.55      (![X0 : $i, X1 : $i]:
% 3.34/3.55         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 3.34/3.55      inference('sup-', [status(thm)], ['33', '34'])).
% 3.34/3.55  thf('36', plain,
% 3.34/3.55      (![X0 : $i, X1 : $i]:
% 3.34/3.55         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.34/3.55      inference('sup-', [status(thm)], ['32', '35'])).
% 3.34/3.55  thf('37', plain,
% 3.34/3.55      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 3.34/3.55      inference('sup-', [status(thm)], ['29', '36'])).
% 3.34/3.55  thf('38', plain,
% 3.34/3.55      (![X28 : $i, X29 : $i]:
% 3.34/3.55         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 3.34/3.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.34/3.55  thf('39', plain,
% 3.34/3.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.34/3.55         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | (zip_tseitin_0 @ X1 @ X2))),
% 3.34/3.55      inference('sup+', [status(thm)], ['37', '38'])).
% 3.34/3.55  thf('40', plain,
% 3.34/3.55      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.34/3.55        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 3.34/3.55      inference('sup-', [status(thm)], ['5', '6'])).
% 3.34/3.55  thf('41', plain,
% 3.34/3.55      (![X0 : $i]:
% 3.34/3.55         (~ (v1_xboole_0 @ X0)
% 3.34/3.55          | ((sk_B_1) = (X0))
% 3.34/3.55          | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 3.34/3.55      inference('sup-', [status(thm)], ['39', '40'])).
% 3.34/3.55  thf('42', plain,
% 3.34/3.55      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 3.34/3.55      inference('sup-', [status(thm)], ['29', '36'])).
% 3.34/3.55  thf('43', plain,
% 3.34/3.55      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 3.34/3.55      inference('sup-', [status(thm)], ['29', '36'])).
% 3.34/3.55  thf('44', plain,
% 3.34/3.55      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 3.34/3.55      inference('sup-', [status(thm)], ['29', '36'])).
% 3.34/3.55  thf('45', plain,
% 3.34/3.55      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 3.34/3.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.34/3.55  thf('46', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 3.34/3.55      inference('simplify', [status(thm)], ['45'])).
% 3.34/3.55  thf('47', plain,
% 3.34/3.55      (![X13 : $i, X15 : $i]:
% 3.34/3.55         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 3.34/3.55      inference('cnf', [status(esa)], [t3_subset])).
% 3.34/3.55  thf('48', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 3.34/3.55      inference('sup-', [status(thm)], ['46', '47'])).
% 3.34/3.55  thf('49', plain,
% 3.34/3.55      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 3.34/3.55      inference('simplify', [status(thm)], ['2'])).
% 3.34/3.55  thf(redefinition_r2_relset_1, axiom,
% 3.34/3.55    (![A:$i,B:$i,C:$i,D:$i]:
% 3.34/3.55     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.34/3.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.34/3.55       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.34/3.55  thf('50', plain,
% 3.34/3.55      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 3.34/3.55         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 3.34/3.55          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 3.34/3.55          | (r2_relset_1 @ X25 @ X26 @ X24 @ X27)
% 3.34/3.55          | ((X24) != (X27)))),
% 3.34/3.55      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.34/3.55  thf('51', plain,
% 3.34/3.55      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.34/3.55         ((r2_relset_1 @ X25 @ X26 @ X27 @ X27)
% 3.34/3.55          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 3.34/3.55      inference('simplify', [status(thm)], ['50'])).
% 3.34/3.55  thf('52', plain,
% 3.34/3.55      (![X0 : $i, X1 : $i]:
% 3.34/3.55         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.34/3.55          | (r2_relset_1 @ X0 @ k1_xboole_0 @ X1 @ X1))),
% 3.34/3.55      inference('sup-', [status(thm)], ['49', '51'])).
% 3.34/3.55  thf('53', plain,
% 3.34/3.55      (![X0 : $i]: (r2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 3.34/3.55      inference('sup-', [status(thm)], ['48', '52'])).
% 3.34/3.55  thf('54', plain,
% 3.34/3.55      (![X0 : $i, X1 : $i]:
% 3.34/3.55         ((r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 3.34/3.55          | ~ (v1_xboole_0 @ X0))),
% 3.34/3.55      inference('sup+', [status(thm)], ['44', '53'])).
% 3.34/3.55  thf('55', plain,
% 3.34/3.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.34/3.55         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0)
% 3.34/3.55          | ~ (v1_xboole_0 @ X0)
% 3.34/3.55          | ~ (v1_xboole_0 @ X1))),
% 3.34/3.55      inference('sup+', [status(thm)], ['43', '54'])).
% 3.34/3.55  thf('56', plain,
% 3.34/3.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.34/3.55         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 3.34/3.55          | ~ (v1_xboole_0 @ X0)
% 3.34/3.55          | ~ (v1_xboole_0 @ X2)
% 3.34/3.55          | ~ (v1_xboole_0 @ X1))),
% 3.34/3.55      inference('sup+', [status(thm)], ['42', '55'])).
% 3.34/3.55  thf('57', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 3.34/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.55  thf('58', plain,
% 3.34/3.55      ((~ (v1_xboole_0 @ sk_C_2)
% 3.34/3.55        | ~ (v1_xboole_0 @ sk_B_1)
% 3.34/3.55        | ~ (v1_xboole_0 @ sk_D))),
% 3.34/3.55      inference('sup-', [status(thm)], ['56', '57'])).
% 3.34/3.55  thf('59', plain,
% 3.34/3.55      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 3.34/3.55      inference('sup-', [status(thm)], ['29', '36'])).
% 3.34/3.55  thf('60', plain,
% 3.34/3.55      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 3.34/3.55      inference('simplify', [status(thm)], ['2'])).
% 3.34/3.55  thf('61', plain,
% 3.34/3.55      (![X0 : $i, X1 : $i]:
% 3.34/3.55         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.34/3.55      inference('sup+', [status(thm)], ['59', '60'])).
% 3.34/3.55  thf('62', plain,
% 3.34/3.55      (((v1_xboole_0 @ sk_C_2)
% 3.34/3.55        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.34/3.55      inference('sup-', [status(thm)], ['23', '24'])).
% 3.34/3.55  thf('63', plain,
% 3.34/3.55      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.34/3.55        | ~ (v1_xboole_0 @ sk_B_1)
% 3.34/3.55        | (v1_xboole_0 @ sk_C_2))),
% 3.34/3.55      inference('sup-', [status(thm)], ['61', '62'])).
% 3.34/3.55  thf('64', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.34/3.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.34/3.55  thf('65', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_C_2))),
% 3.34/3.55      inference('demod', [status(thm)], ['63', '64'])).
% 3.34/3.55  thf('66', plain, ((~ (v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_B_1))),
% 3.34/3.55      inference('clc', [status(thm)], ['58', '65'])).
% 3.34/3.55  thf('67', plain,
% 3.34/3.55      (![X0 : $i, X1 : $i]:
% 3.34/3.55         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.34/3.55      inference('sup+', [status(thm)], ['59', '60'])).
% 3.34/3.55  thf('68', plain,
% 3.34/3.55      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.34/3.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.34/3.55  thf('69', plain,
% 3.34/3.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.34/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.55  thf('70', plain,
% 3.34/3.55      (![X13 : $i, X14 : $i]:
% 3.34/3.55         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 3.34/3.55      inference('cnf', [status(esa)], [t3_subset])).
% 3.34/3.55  thf('71', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 3.34/3.55      inference('sup-', [status(thm)], ['69', '70'])).
% 3.34/3.55  thf('72', plain,
% 3.34/3.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.34/3.55         (~ (r2_hidden @ X3 @ X4)
% 3.34/3.55          | (r2_hidden @ X3 @ X5)
% 3.34/3.55          | ~ (r1_tarski @ X4 @ X5))),
% 3.34/3.55      inference('cnf', [status(esa)], [d3_tarski])).
% 3.34/3.55  thf('73', plain,
% 3.34/3.55      (![X0 : $i]:
% 3.34/3.55         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 3.34/3.55          | ~ (r2_hidden @ X0 @ sk_D))),
% 3.34/3.55      inference('sup-', [status(thm)], ['71', '72'])).
% 3.34/3.55  thf('74', plain,
% 3.34/3.55      (((v1_xboole_0 @ sk_D)
% 3.34/3.55        | (r2_hidden @ (sk_B @ sk_D) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.34/3.55      inference('sup-', [status(thm)], ['68', '73'])).
% 3.34/3.55  thf('75', plain,
% 3.34/3.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.34/3.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.34/3.55  thf('76', plain,
% 3.34/3.55      (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.34/3.55      inference('sup-', [status(thm)], ['74', '75'])).
% 3.34/3.55  thf('77', plain,
% 3.34/3.55      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.34/3.55        | ~ (v1_xboole_0 @ sk_B_1)
% 3.34/3.55        | (v1_xboole_0 @ sk_D))),
% 3.34/3.55      inference('sup-', [status(thm)], ['67', '76'])).
% 3.34/3.55  thf('78', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.34/3.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.34/3.55  thf('79', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_D))),
% 3.34/3.55      inference('demod', [status(thm)], ['77', '78'])).
% 3.34/3.55  thf('80', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 3.34/3.55      inference('clc', [status(thm)], ['66', '79'])).
% 3.34/3.55  thf('81', plain,
% 3.34/3.55      (![X0 : $i]:
% 3.34/3.55         (~ (v1_xboole_0 @ X0)
% 3.34/3.55          | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.34/3.55          | ~ (v1_xboole_0 @ X0))),
% 3.34/3.55      inference('sup-', [status(thm)], ['41', '80'])).
% 3.34/3.55  thf('82', plain,
% 3.34/3.55      (![X0 : $i]:
% 3.34/3.55         ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 3.34/3.55      inference('simplify', [status(thm)], ['81'])).
% 3.34/3.55  thf('83', plain,
% 3.34/3.55      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.34/3.55        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.34/3.55      inference('demod', [status(thm)], ['11', '14'])).
% 3.34/3.55  thf('84', plain,
% 3.34/3.55      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.34/3.55      inference('sup-', [status(thm)], ['82', '83'])).
% 3.34/3.55  thf('85', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 3.34/3.55      inference('clc', [status(thm)], ['28', '84'])).
% 3.34/3.55  thf('86', plain,
% 3.34/3.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.34/3.55         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 3.34/3.55      inference('sup+', [status(thm)], ['1', '3'])).
% 3.34/3.55  thf('87', plain,
% 3.34/3.55      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.34/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.55  thf('88', plain,
% 3.34/3.55      (![X33 : $i, X34 : $i, X35 : $i]:
% 3.34/3.55         (~ (zip_tseitin_0 @ X33 @ X34)
% 3.34/3.55          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 3.34/3.55          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 3.34/3.55      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.34/3.55  thf('89', plain,
% 3.34/3.55      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 3.34/3.55        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 3.34/3.55      inference('sup-', [status(thm)], ['87', '88'])).
% 3.34/3.55  thf('90', plain,
% 3.34/3.55      (![X0 : $i]:
% 3.34/3.55         (((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0))
% 3.34/3.55          | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 3.34/3.55      inference('sup-', [status(thm)], ['86', '89'])).
% 3.34/3.55  thf('91', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 3.34/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.55  thf('92', plain,
% 3.34/3.55      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.34/3.55         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 3.34/3.55          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 3.34/3.55          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 3.34/3.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.34/3.55  thf('93', plain,
% 3.34/3.55      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 3.34/3.55        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 3.34/3.55      inference('sup-', [status(thm)], ['91', '92'])).
% 3.34/3.55  thf('94', plain,
% 3.34/3.55      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.34/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.55  thf('95', plain,
% 3.34/3.55      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.34/3.55         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 3.34/3.55          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 3.34/3.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.34/3.55  thf('96', plain,
% 3.34/3.55      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 3.34/3.55      inference('sup-', [status(thm)], ['94', '95'])).
% 3.34/3.55  thf('97', plain,
% 3.34/3.55      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 3.34/3.55        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.34/3.55      inference('demod', [status(thm)], ['93', '96'])).
% 3.34/3.55  thf('98', plain,
% 3.34/3.55      (![X0 : $i]:
% 3.34/3.55         (((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0))
% 3.34/3.55          | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.34/3.55      inference('sup-', [status(thm)], ['90', '97'])).
% 3.34/3.55  thf('99', plain, ((r1_tarski @ sk_C_2 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 3.34/3.55      inference('sup-', [status(thm)], ['18', '19'])).
% 3.34/3.55  thf('100', plain,
% 3.34/3.55      (![X0 : $i, X1 : $i]:
% 3.34/3.55         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 3.34/3.55      inference('sup-', [status(thm)], ['33', '34'])).
% 3.34/3.55  thf('101', plain,
% 3.34/3.55      ((((sk_C_2) = (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 3.34/3.55        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.34/3.55      inference('sup-', [status(thm)], ['99', '100'])).
% 3.34/3.55  thf('102', plain,
% 3.34/3.55      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.34/3.55        | ((sk_A) = (k1_relat_1 @ sk_C_2))
% 3.34/3.55        | ((sk_C_2) = (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.34/3.55      inference('sup-', [status(thm)], ['98', '101'])).
% 3.34/3.55  thf('103', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.34/3.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.34/3.55  thf('104', plain,
% 3.34/3.55      ((((sk_A) = (k1_relat_1 @ sk_C_2))
% 3.34/3.55        | ((sk_C_2) = (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.34/3.55      inference('demod', [status(thm)], ['102', '103'])).
% 3.34/3.55  thf('105', plain,
% 3.34/3.55      (![X0 : $i, X1 : $i]:
% 3.34/3.55         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.34/3.55      inference('sup+', [status(thm)], ['59', '60'])).
% 3.34/3.55  thf('106', plain,
% 3.34/3.55      ((((sk_C_2) = (k1_xboole_0))
% 3.34/3.55        | ((sk_A) = (k1_relat_1 @ sk_C_2))
% 3.34/3.55        | ~ (v1_xboole_0 @ sk_B_1))),
% 3.34/3.55      inference('sup+', [status(thm)], ['104', '105'])).
% 3.34/3.55  thf('107', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 3.34/3.55      inference('clc', [status(thm)], ['66', '79'])).
% 3.34/3.55  thf('108', plain,
% 3.34/3.55      ((~ (v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.34/3.55      inference('clc', [status(thm)], ['106', '107'])).
% 3.34/3.55  thf('109', plain,
% 3.34/3.55      (![X28 : $i, X29 : $i]:
% 3.34/3.55         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 3.34/3.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.34/3.55  thf('110', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.34/3.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.34/3.55  thf('111', plain,
% 3.34/3.55      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 3.34/3.55      inference('sup+', [status(thm)], ['109', '110'])).
% 3.34/3.55  thf('112', plain,
% 3.34/3.55      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 3.34/3.55        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 3.34/3.55      inference('sup-', [status(thm)], ['87', '88'])).
% 3.34/3.55  thf('113', plain,
% 3.34/3.55      (((v1_xboole_0 @ sk_B_1) | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 3.34/3.55      inference('sup-', [status(thm)], ['111', '112'])).
% 3.34/3.55  thf('114', plain,
% 3.34/3.55      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 3.34/3.55        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.34/3.55      inference('demod', [status(thm)], ['93', '96'])).
% 3.34/3.55  thf('115', plain,
% 3.34/3.55      (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.34/3.55      inference('sup-', [status(thm)], ['113', '114'])).
% 3.34/3.55  thf('116', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 3.34/3.55      inference('clc', [status(thm)], ['108', '115'])).
% 3.34/3.55  thf(t9_funct_1, axiom,
% 3.34/3.55    (![A:$i]:
% 3.34/3.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.34/3.55       ( ![B:$i]:
% 3.34/3.55         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.34/3.55           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 3.34/3.55               ( ![C:$i]:
% 3.34/3.55                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 3.34/3.55                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 3.34/3.55             ( ( A ) = ( B ) ) ) ) ) ))).
% 3.34/3.55  thf('117', plain,
% 3.34/3.55      (![X16 : $i, X17 : $i]:
% 3.34/3.55         (~ (v1_relat_1 @ X16)
% 3.34/3.55          | ~ (v1_funct_1 @ X16)
% 3.34/3.55          | ((X17) = (X16))
% 3.34/3.55          | (r2_hidden @ (sk_C_1 @ X16 @ X17) @ (k1_relat_1 @ X17))
% 3.34/3.55          | ((k1_relat_1 @ X17) != (k1_relat_1 @ X16))
% 3.34/3.55          | ~ (v1_funct_1 @ X17)
% 3.34/3.55          | ~ (v1_relat_1 @ X17))),
% 3.34/3.55      inference('cnf', [status(esa)], [t9_funct_1])).
% 3.34/3.55  thf('118', plain,
% 3.34/3.55      (![X0 : $i]:
% 3.34/3.55         (((sk_A) != (k1_relat_1 @ X0))
% 3.34/3.55          | ~ (v1_relat_1 @ sk_C_2)
% 3.34/3.55          | ~ (v1_funct_1 @ sk_C_2)
% 3.34/3.55          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 3.34/3.55          | ((sk_C_2) = (X0))
% 3.34/3.55          | ~ (v1_funct_1 @ X0)
% 3.34/3.55          | ~ (v1_relat_1 @ X0))),
% 3.34/3.55      inference('sup-', [status(thm)], ['116', '117'])).
% 3.34/3.55  thf('119', plain,
% 3.34/3.55      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.34/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.55  thf(cc1_relset_1, axiom,
% 3.34/3.55    (![A:$i,B:$i,C:$i]:
% 3.34/3.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.34/3.55       ( v1_relat_1 @ C ) ))).
% 3.34/3.55  thf('120', plain,
% 3.34/3.55      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.34/3.55         ((v1_relat_1 @ X18)
% 3.34/3.55          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 3.34/3.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.34/3.55  thf('121', plain, ((v1_relat_1 @ sk_C_2)),
% 3.34/3.55      inference('sup-', [status(thm)], ['119', '120'])).
% 3.34/3.55  thf('122', plain, ((v1_funct_1 @ sk_C_2)),
% 3.34/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.55  thf('123', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 3.34/3.55      inference('clc', [status(thm)], ['108', '115'])).
% 3.34/3.55  thf('124', plain,
% 3.34/3.55      (![X0 : $i]:
% 3.34/3.55         (((sk_A) != (k1_relat_1 @ X0))
% 3.34/3.55          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A)
% 3.34/3.55          | ((sk_C_2) = (X0))
% 3.34/3.55          | ~ (v1_funct_1 @ X0)
% 3.34/3.55          | ~ (v1_relat_1 @ X0))),
% 3.34/3.55      inference('demod', [status(thm)], ['118', '121', '122', '123'])).
% 3.34/3.55  thf('125', plain,
% 3.34/3.55      ((((sk_A) != (sk_A))
% 3.34/3.55        | ~ (v1_relat_1 @ sk_D)
% 3.34/3.55        | ~ (v1_funct_1 @ sk_D)
% 3.34/3.55        | ((sk_C_2) = (sk_D))
% 3.34/3.55        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 3.34/3.55      inference('sup-', [status(thm)], ['85', '124'])).
% 3.34/3.55  thf('126', plain,
% 3.34/3.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.34/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.55  thf('127', plain,
% 3.34/3.55      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.34/3.55         ((v1_relat_1 @ X18)
% 3.34/3.55          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 3.34/3.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.34/3.55  thf('128', plain, ((v1_relat_1 @ sk_D)),
% 3.34/3.55      inference('sup-', [status(thm)], ['126', '127'])).
% 3.34/3.55  thf('129', plain, ((v1_funct_1 @ sk_D)),
% 3.34/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.55  thf('130', plain,
% 3.34/3.55      ((((sk_A) != (sk_A))
% 3.34/3.55        | ((sk_C_2) = (sk_D))
% 3.34/3.55        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 3.34/3.55      inference('demod', [status(thm)], ['125', '128', '129'])).
% 3.34/3.55  thf('131', plain,
% 3.34/3.55      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A) | ((sk_C_2) = (sk_D)))),
% 3.34/3.55      inference('simplify', [status(thm)], ['130'])).
% 3.34/3.55  thf('132', plain,
% 3.34/3.55      (![X36 : $i]:
% 3.34/3.55         (((k1_funct_1 @ sk_C_2 @ X36) = (k1_funct_1 @ sk_D @ X36))
% 3.34/3.55          | ~ (r2_hidden @ X36 @ sk_A))),
% 3.34/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.55  thf('133', plain,
% 3.34/3.55      ((((sk_C_2) = (sk_D))
% 3.34/3.55        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 3.34/3.55            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 3.34/3.55      inference('sup-', [status(thm)], ['131', '132'])).
% 3.34/3.55  thf('134', plain,
% 3.34/3.55      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 3.34/3.55         = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))),
% 3.34/3.55      inference('condensation', [status(thm)], ['133'])).
% 3.34/3.55  thf('135', plain,
% 3.34/3.55      (![X16 : $i, X17 : $i]:
% 3.34/3.55         (~ (v1_relat_1 @ X16)
% 3.34/3.55          | ~ (v1_funct_1 @ X16)
% 3.34/3.55          | ((X17) = (X16))
% 3.34/3.55          | ((k1_funct_1 @ X17 @ (sk_C_1 @ X16 @ X17))
% 3.34/3.55              != (k1_funct_1 @ X16 @ (sk_C_1 @ X16 @ X17)))
% 3.34/3.55          | ((k1_relat_1 @ X17) != (k1_relat_1 @ X16))
% 3.34/3.55          | ~ (v1_funct_1 @ X17)
% 3.34/3.55          | ~ (v1_relat_1 @ X17))),
% 3.34/3.55      inference('cnf', [status(esa)], [t9_funct_1])).
% 3.34/3.55  thf('136', plain,
% 3.34/3.55      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 3.34/3.55          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 3.34/3.55        | ~ (v1_relat_1 @ sk_C_2)
% 3.34/3.55        | ~ (v1_funct_1 @ sk_C_2)
% 3.34/3.55        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 3.34/3.55        | ((sk_C_2) = (sk_D))
% 3.34/3.55        | ~ (v1_funct_1 @ sk_D)
% 3.34/3.55        | ~ (v1_relat_1 @ sk_D))),
% 3.34/3.55      inference('sup-', [status(thm)], ['134', '135'])).
% 3.34/3.55  thf('137', plain, ((v1_relat_1 @ sk_C_2)),
% 3.34/3.55      inference('sup-', [status(thm)], ['119', '120'])).
% 3.34/3.55  thf('138', plain, ((v1_funct_1 @ sk_C_2)),
% 3.34/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.55  thf('139', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 3.34/3.55      inference('clc', [status(thm)], ['108', '115'])).
% 3.34/3.55  thf('140', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 3.34/3.55      inference('clc', [status(thm)], ['28', '84'])).
% 3.34/3.55  thf('141', plain, ((v1_funct_1 @ sk_D)),
% 3.34/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.55  thf('142', plain, ((v1_relat_1 @ sk_D)),
% 3.34/3.55      inference('sup-', [status(thm)], ['126', '127'])).
% 3.34/3.55  thf('143', plain,
% 3.34/3.55      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 3.34/3.55          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 3.34/3.55        | ((sk_A) != (sk_A))
% 3.34/3.55        | ((sk_C_2) = (sk_D)))),
% 3.34/3.55      inference('demod', [status(thm)],
% 3.34/3.55                ['136', '137', '138', '139', '140', '141', '142'])).
% 3.34/3.55  thf('144', plain, (((sk_C_2) = (sk_D))),
% 3.34/3.55      inference('simplify', [status(thm)], ['143'])).
% 3.34/3.55  thf('145', plain,
% 3.34/3.55      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.34/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.55  thf('146', plain,
% 3.34/3.55      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.34/3.55         ((r2_relset_1 @ X25 @ X26 @ X27 @ X27)
% 3.34/3.55          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 3.34/3.55      inference('simplify', [status(thm)], ['50'])).
% 3.34/3.55  thf('147', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2)),
% 3.34/3.55      inference('sup-', [status(thm)], ['145', '146'])).
% 3.34/3.55  thf('148', plain, ($false),
% 3.34/3.55      inference('demod', [status(thm)], ['0', '144', '147'])).
% 3.34/3.55  
% 3.34/3.55  % SZS output end Refutation
% 3.34/3.55  
% 3.34/3.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
