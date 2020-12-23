%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a7Qlygf44Z

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:31 EST 2020

% Result     : Theorem 21.45s
% Output     : Refutation 21.45s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 590 expanded)
%              Number of leaves         :   38 ( 189 expanded)
%              Depth                    :   24
%              Number of atoms          : 1396 (8284 expanded)
%              Number of equality atoms :  133 ( 478 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
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
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_zfmisc_1 @ X7 @ X8 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('3',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ X7 @ k1_xboole_0 )
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
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
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

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_D ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_D ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('23',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('24',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_D ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('28',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C_1 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('35',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_C_1 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('40',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( r2_relset_1 @ X28 @ X29 @ X27 @ X30 )
      | ( X27 != X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('41',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r2_relset_1 @ X28 @ X29 @ X30 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,
    ( ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['35','42'])).

thf('44',plain,
    ( ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['26','43'])).

thf('45',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('49',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C_1 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C_1 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = sk_C_1 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ sk_C_1 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ~ ( r1_tarski @ sk_C_1 @ sk_D )
      | ( sk_C_1 = sk_D ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('58',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_D ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = sk_D ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = sk_D ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ sk_D )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = sk_D )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['56','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('67',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( sk_C_1 = sk_D )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('71',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('74',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['71','74'])).

thf('76',plain,
    ( ( sk_C_1 = sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['68','75'])).

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

thf('77',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( X20 = X19 )
      | ( r2_hidden @ ( sk_C @ X19 @ X20 ) @ ( k1_relat_1 @ X20 ) )
      | ( ( k1_relat_1 @ X20 )
       != ( k1_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( sk_C_1 = sk_D )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('80',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('81',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( sk_C_1 = sk_D )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['78','81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('85',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['71','74'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_D ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('90',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_D ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('92',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_D ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('94',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C_1 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('95',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('97',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_C_1 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('99',plain,
    ( ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['92','99'])).

thf('101',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( sk_C_1 = sk_D )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','103'])).

thf('105',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference('sup-',[status(thm)],['47','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('108',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(demod,[status(thm)],['105','108','109'])).

thf('111',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['110'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('112',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( m1_subset_1 @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('114',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( sk_C_1 = sk_D )
    | ( m1_subset_1 @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['111','114'])).

thf('116',plain,(
    ! [X39: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X39 )
        = ( k1_funct_1 @ sk_D @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( sk_C_1 = sk_D )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ),
    inference(condensation,[status(thm)],['117'])).

thf('119',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( X20 = X19 )
      | ( ( k1_funct_1 @ X20 @ ( sk_C @ X19 @ X20 ) )
       != ( k1_funct_1 @ X19 @ ( sk_C @ X19 @ X20 ) ) )
      | ( ( k1_relat_1 @ X20 )
       != ( k1_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('120',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['79','80'])).

thf('122',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('124',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('125',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['106','107'])).

thf('127',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(demod,[status(thm)],['120','121','122','123','124','125','126'])).

thf('128',plain,(
    sk_C_1 = sk_D ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r2_relset_1 @ X28 @ X29 @ X30 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('131',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    $false ),
    inference(demod,[status(thm)],['0','128','131'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a7Qlygf44Z
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:05:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 21.45/21.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 21.45/21.66  % Solved by: fo/fo7.sh
% 21.45/21.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 21.45/21.66  % done 8672 iterations in 21.197s
% 21.45/21.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 21.45/21.66  % SZS output start Refutation
% 21.45/21.66  thf(sk_C_1_type, type, sk_C_1: $i).
% 21.45/21.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 21.45/21.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 21.45/21.66  thf(sk_D_type, type, sk_D: $i).
% 21.45/21.66  thf(sk_B_1_type, type, sk_B_1: $i).
% 21.45/21.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 21.45/21.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 21.45/21.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 21.45/21.66  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 21.45/21.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 21.45/21.66  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 21.45/21.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 21.45/21.66  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 21.45/21.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 21.45/21.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 21.45/21.66  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 21.45/21.66  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 21.45/21.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 21.45/21.66  thf(sk_A_type, type, sk_A: $i).
% 21.45/21.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 21.45/21.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 21.45/21.66  thf(t113_funct_2, conjecture,
% 21.45/21.66    (![A:$i,B:$i,C:$i]:
% 21.45/21.66     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 21.45/21.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 21.45/21.66       ( ![D:$i]:
% 21.45/21.66         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 21.45/21.66             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 21.45/21.66           ( ( ![E:$i]:
% 21.45/21.66               ( ( m1_subset_1 @ E @ A ) =>
% 21.45/21.66                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 21.45/21.66             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 21.45/21.66  thf(zf_stmt_0, negated_conjecture,
% 21.45/21.66    (~( ![A:$i,B:$i,C:$i]:
% 21.45/21.66        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 21.45/21.66            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 21.45/21.66          ( ![D:$i]:
% 21.45/21.66            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 21.45/21.66                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 21.45/21.66              ( ( ![E:$i]:
% 21.45/21.66                  ( ( m1_subset_1 @ E @ A ) =>
% 21.45/21.66                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 21.45/21.66                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 21.45/21.66    inference('cnf.neg', [status(esa)], [t113_funct_2])).
% 21.45/21.66  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)),
% 21.45/21.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.45/21.66  thf(d1_funct_2, axiom,
% 21.45/21.66    (![A:$i,B:$i,C:$i]:
% 21.45/21.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.45/21.66       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 21.45/21.66           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 21.45/21.66             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 21.45/21.66         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 21.45/21.66           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 21.45/21.66             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 21.45/21.66  thf(zf_stmt_1, axiom,
% 21.45/21.66    (![B:$i,A:$i]:
% 21.45/21.66     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 21.45/21.66       ( zip_tseitin_0 @ B @ A ) ))).
% 21.45/21.66  thf('1', plain,
% 21.45/21.66      (![X31 : $i, X32 : $i]:
% 21.45/21.66         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 21.45/21.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 21.45/21.66  thf(t113_zfmisc_1, axiom,
% 21.45/21.66    (![A:$i,B:$i]:
% 21.45/21.66     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 21.45/21.66       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 21.45/21.66  thf('2', plain,
% 21.45/21.66      (![X7 : $i, X8 : $i]:
% 21.45/21.66         (((k2_zfmisc_1 @ X7 @ X8) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 21.45/21.66      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 21.45/21.66  thf('3', plain,
% 21.45/21.66      (![X7 : $i]: ((k2_zfmisc_1 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 21.45/21.66      inference('simplify', [status(thm)], ['2'])).
% 21.45/21.66  thf('4', plain,
% 21.45/21.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.45/21.66         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 21.45/21.66      inference('sup+', [status(thm)], ['1', '3'])).
% 21.45/21.66  thf('5', plain,
% 21.45/21.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 21.45/21.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.45/21.66  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 21.45/21.66  thf(zf_stmt_3, axiom,
% 21.45/21.66    (![C:$i,B:$i,A:$i]:
% 21.45/21.66     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 21.45/21.66       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 21.45/21.66  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 21.45/21.66  thf(zf_stmt_5, axiom,
% 21.45/21.66    (![A:$i,B:$i,C:$i]:
% 21.45/21.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.45/21.66       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 21.45/21.66         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 21.45/21.66           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 21.45/21.66             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 21.45/21.66  thf('6', plain,
% 21.45/21.66      (![X36 : $i, X37 : $i, X38 : $i]:
% 21.45/21.66         (~ (zip_tseitin_0 @ X36 @ X37)
% 21.45/21.66          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 21.45/21.66          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 21.45/21.66      inference('cnf', [status(esa)], [zf_stmt_5])).
% 21.45/21.66  thf('7', plain,
% 21.45/21.66      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 21.45/21.66        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 21.45/21.66      inference('sup-', [status(thm)], ['5', '6'])).
% 21.45/21.66  thf('8', plain,
% 21.45/21.66      (![X0 : $i]:
% 21.45/21.66         (((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0))
% 21.45/21.66          | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 21.45/21.66      inference('sup-', [status(thm)], ['4', '7'])).
% 21.45/21.66  thf('9', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 21.45/21.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.45/21.66  thf('10', plain,
% 21.45/21.66      (![X33 : $i, X34 : $i, X35 : $i]:
% 21.45/21.66         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 21.45/21.66          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 21.45/21.66          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 21.45/21.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 21.45/21.66  thf('11', plain,
% 21.45/21.66      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 21.45/21.66        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 21.45/21.66      inference('sup-', [status(thm)], ['9', '10'])).
% 21.45/21.66  thf('12', plain,
% 21.45/21.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 21.45/21.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.45/21.66  thf(redefinition_k1_relset_1, axiom,
% 21.45/21.66    (![A:$i,B:$i,C:$i]:
% 21.45/21.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.45/21.66       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 21.45/21.66  thf('13', plain,
% 21.45/21.66      (![X24 : $i, X25 : $i, X26 : $i]:
% 21.45/21.66         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 21.45/21.66          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 21.45/21.66      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 21.45/21.66  thf('14', plain,
% 21.45/21.66      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 21.45/21.66      inference('sup-', [status(thm)], ['12', '13'])).
% 21.45/21.66  thf('15', plain,
% 21.45/21.66      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 21.45/21.66        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 21.45/21.66      inference('demod', [status(thm)], ['11', '14'])).
% 21.45/21.66  thf('16', plain,
% 21.45/21.66      (![X0 : $i]:
% 21.45/21.66         (((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0))
% 21.45/21.66          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 21.45/21.66      inference('sup-', [status(thm)], ['8', '15'])).
% 21.45/21.66  thf('17', plain,
% 21.45/21.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 21.45/21.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.45/21.66  thf(t3_subset, axiom,
% 21.45/21.66    (![A:$i,B:$i]:
% 21.45/21.66     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 21.45/21.66  thf('18', plain,
% 21.45/21.66      (![X13 : $i, X14 : $i]:
% 21.45/21.66         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 21.45/21.66      inference('cnf', [status(esa)], [t3_subset])).
% 21.45/21.66  thf('19', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 21.45/21.66      inference('sup-', [status(thm)], ['17', '18'])).
% 21.45/21.66  thf(d10_xboole_0, axiom,
% 21.45/21.66    (![A:$i,B:$i]:
% 21.45/21.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 21.45/21.66  thf('20', plain,
% 21.45/21.66      (![X3 : $i, X5 : $i]:
% 21.45/21.66         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 21.45/21.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 21.45/21.66  thf('21', plain,
% 21.45/21.66      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_D)
% 21.45/21.66        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_D)))),
% 21.45/21.66      inference('sup-', [status(thm)], ['19', '20'])).
% 21.45/21.66  thf('22', plain,
% 21.45/21.66      ((~ (r1_tarski @ k1_xboole_0 @ sk_D)
% 21.45/21.66        | ((sk_A) = (k1_relat_1 @ sk_D))
% 21.45/21.66        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_D)))),
% 21.45/21.66      inference('sup-', [status(thm)], ['16', '21'])).
% 21.45/21.66  thf(t4_subset_1, axiom,
% 21.45/21.66    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 21.45/21.66  thf('23', plain,
% 21.45/21.66      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 21.45/21.66      inference('cnf', [status(esa)], [t4_subset_1])).
% 21.45/21.66  thf('24', plain,
% 21.45/21.66      (![X13 : $i, X14 : $i]:
% 21.45/21.66         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 21.45/21.66      inference('cnf', [status(esa)], [t3_subset])).
% 21.45/21.66  thf('25', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 21.45/21.66      inference('sup-', [status(thm)], ['23', '24'])).
% 21.45/21.66  thf('26', plain,
% 21.45/21.66      ((((sk_A) = (k1_relat_1 @ sk_D))
% 21.45/21.66        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_D)))),
% 21.45/21.66      inference('demod', [status(thm)], ['22', '25'])).
% 21.45/21.66  thf('27', plain,
% 21.45/21.66      (![X0 : $i]:
% 21.45/21.66         (((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0))
% 21.45/21.66          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 21.45/21.66      inference('sup-', [status(thm)], ['8', '15'])).
% 21.45/21.66  thf('28', plain,
% 21.45/21.66      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 21.45/21.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.45/21.66  thf('29', plain,
% 21.45/21.66      (![X13 : $i, X14 : $i]:
% 21.45/21.66         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 21.45/21.66      inference('cnf', [status(esa)], [t3_subset])).
% 21.45/21.66  thf('30', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 21.45/21.66      inference('sup-', [status(thm)], ['28', '29'])).
% 21.45/21.66  thf('31', plain,
% 21.45/21.66      (![X3 : $i, X5 : $i]:
% 21.45/21.66         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 21.45/21.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 21.45/21.66  thf('32', plain,
% 21.45/21.66      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C_1)
% 21.45/21.66        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_C_1)))),
% 21.45/21.66      inference('sup-', [status(thm)], ['30', '31'])).
% 21.45/21.66  thf('33', plain,
% 21.45/21.66      ((~ (r1_tarski @ k1_xboole_0 @ sk_C_1)
% 21.45/21.66        | ((sk_A) = (k1_relat_1 @ sk_D))
% 21.45/21.66        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_C_1)))),
% 21.45/21.66      inference('sup-', [status(thm)], ['27', '32'])).
% 21.45/21.66  thf('34', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 21.45/21.66      inference('sup-', [status(thm)], ['23', '24'])).
% 21.45/21.66  thf('35', plain,
% 21.45/21.66      ((((sk_A) = (k1_relat_1 @ sk_D))
% 21.45/21.66        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_C_1)))),
% 21.45/21.66      inference('demod', [status(thm)], ['33', '34'])).
% 21.45/21.66  thf('36', plain,
% 21.45/21.66      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 21.45/21.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 21.45/21.66  thf('37', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 21.45/21.66      inference('simplify', [status(thm)], ['36'])).
% 21.45/21.66  thf('38', plain,
% 21.45/21.66      (![X13 : $i, X15 : $i]:
% 21.45/21.66         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 21.45/21.66      inference('cnf', [status(esa)], [t3_subset])).
% 21.45/21.66  thf('39', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 21.45/21.66      inference('sup-', [status(thm)], ['37', '38'])).
% 21.45/21.66  thf(redefinition_r2_relset_1, axiom,
% 21.45/21.66    (![A:$i,B:$i,C:$i,D:$i]:
% 21.45/21.66     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 21.45/21.66         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 21.45/21.66       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 21.45/21.66  thf('40', plain,
% 21.45/21.66      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 21.45/21.66         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 21.45/21.66          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 21.45/21.66          | (r2_relset_1 @ X28 @ X29 @ X27 @ X30)
% 21.45/21.66          | ((X27) != (X30)))),
% 21.45/21.66      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 21.45/21.66  thf('41', plain,
% 21.45/21.66      (![X28 : $i, X29 : $i, X30 : $i]:
% 21.45/21.66         ((r2_relset_1 @ X28 @ X29 @ X30 @ X30)
% 21.45/21.66          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 21.45/21.66      inference('simplify', [status(thm)], ['40'])).
% 21.45/21.66  thf('42', plain,
% 21.45/21.66      (![X0 : $i, X1 : $i]:
% 21.45/21.66         (r2_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 21.45/21.66          (k2_zfmisc_1 @ X1 @ X0))),
% 21.45/21.66      inference('sup-', [status(thm)], ['39', '41'])).
% 21.45/21.66  thf('43', plain,
% 21.45/21.66      (((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 21.45/21.66        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 21.45/21.66      inference('sup+', [status(thm)], ['35', '42'])).
% 21.45/21.66  thf('44', plain,
% 21.45/21.66      (((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)
% 21.45/21.66        | ((sk_A) = (k1_relat_1 @ sk_D))
% 21.45/21.66        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 21.45/21.66      inference('sup+', [status(thm)], ['26', '43'])).
% 21.45/21.66  thf('45', plain,
% 21.45/21.66      ((((sk_A) = (k1_relat_1 @ sk_D))
% 21.45/21.66        | (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))),
% 21.45/21.66      inference('simplify', [status(thm)], ['44'])).
% 21.45/21.66  thf('46', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)),
% 21.45/21.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.45/21.66  thf('47', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 21.45/21.66      inference('clc', [status(thm)], ['45', '46'])).
% 21.45/21.66  thf('48', plain,
% 21.45/21.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.45/21.66         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 21.45/21.66      inference('sup+', [status(thm)], ['1', '3'])).
% 21.45/21.66  thf('49', plain,
% 21.45/21.66      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C_1)
% 21.45/21.66        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_C_1)))),
% 21.45/21.66      inference('sup-', [status(thm)], ['30', '31'])).
% 21.45/21.66  thf('50', plain,
% 21.45/21.66      (![X0 : $i]:
% 21.45/21.66         (~ (r1_tarski @ k1_xboole_0 @ sk_C_1)
% 21.45/21.66          | (zip_tseitin_0 @ sk_B_1 @ X0)
% 21.45/21.66          | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_C_1)))),
% 21.45/21.66      inference('sup-', [status(thm)], ['48', '49'])).
% 21.45/21.66  thf('51', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 21.45/21.66      inference('sup-', [status(thm)], ['23', '24'])).
% 21.45/21.66  thf('52', plain,
% 21.45/21.66      (![X0 : $i]:
% 21.45/21.66         ((zip_tseitin_0 @ sk_B_1 @ X0)
% 21.45/21.66          | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_C_1)))),
% 21.45/21.66      inference('demod', [status(thm)], ['50', '51'])).
% 21.45/21.66  thf('53', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 21.45/21.66      inference('sup-', [status(thm)], ['17', '18'])).
% 21.45/21.66  thf('54', plain,
% 21.45/21.66      (![X0 : $i]:
% 21.45/21.66         ((r1_tarski @ sk_D @ sk_C_1) | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 21.45/21.66      inference('sup+', [status(thm)], ['52', '53'])).
% 21.45/21.66  thf('55', plain,
% 21.45/21.66      (![X3 : $i, X5 : $i]:
% 21.45/21.66         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 21.45/21.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 21.45/21.66  thf('56', plain,
% 21.45/21.66      (![X0 : $i]:
% 21.45/21.66         ((zip_tseitin_0 @ sk_B_1 @ X0)
% 21.45/21.66          | ~ (r1_tarski @ sk_C_1 @ sk_D)
% 21.45/21.66          | ((sk_C_1) = (sk_D)))),
% 21.45/21.66      inference('sup-', [status(thm)], ['54', '55'])).
% 21.45/21.66  thf('57', plain,
% 21.45/21.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.45/21.66         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 21.45/21.66      inference('sup+', [status(thm)], ['1', '3'])).
% 21.45/21.66  thf('58', plain,
% 21.45/21.66      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_D)
% 21.45/21.66        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_D)))),
% 21.45/21.66      inference('sup-', [status(thm)], ['19', '20'])).
% 21.45/21.66  thf('59', plain,
% 21.45/21.66      (![X0 : $i]:
% 21.45/21.66         (~ (r1_tarski @ k1_xboole_0 @ sk_D)
% 21.45/21.66          | (zip_tseitin_0 @ sk_B_1 @ X0)
% 21.45/21.66          | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_D)))),
% 21.45/21.66      inference('sup-', [status(thm)], ['57', '58'])).
% 21.45/21.66  thf('60', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 21.45/21.66      inference('sup-', [status(thm)], ['23', '24'])).
% 21.45/21.66  thf('61', plain,
% 21.45/21.66      (![X0 : $i]:
% 21.45/21.66         ((zip_tseitin_0 @ sk_B_1 @ X0)
% 21.45/21.66          | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_D)))),
% 21.45/21.66      inference('demod', [status(thm)], ['59', '60'])).
% 21.45/21.66  thf('62', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 21.45/21.66      inference('sup-', [status(thm)], ['28', '29'])).
% 21.45/21.66  thf('63', plain,
% 21.45/21.66      (![X0 : $i]:
% 21.45/21.66         ((r1_tarski @ sk_C_1 @ sk_D) | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 21.45/21.66      inference('sup+', [status(thm)], ['61', '62'])).
% 21.45/21.66  thf('64', plain,
% 21.45/21.66      (![X0 : $i]: (((sk_C_1) = (sk_D)) | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 21.45/21.66      inference('clc', [status(thm)], ['56', '63'])).
% 21.45/21.66  thf('65', plain,
% 21.45/21.66      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 21.45/21.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.45/21.66  thf('66', plain,
% 21.45/21.66      (![X36 : $i, X37 : $i, X38 : $i]:
% 21.45/21.66         (~ (zip_tseitin_0 @ X36 @ X37)
% 21.45/21.66          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 21.45/21.66          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 21.45/21.66      inference('cnf', [status(esa)], [zf_stmt_5])).
% 21.45/21.66  thf('67', plain,
% 21.45/21.66      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 21.45/21.66        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 21.45/21.66      inference('sup-', [status(thm)], ['65', '66'])).
% 21.45/21.66  thf('68', plain,
% 21.45/21.66      ((((sk_C_1) = (sk_D)) | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A))),
% 21.45/21.66      inference('sup-', [status(thm)], ['64', '67'])).
% 21.45/21.66  thf('69', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 21.45/21.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.45/21.66  thf('70', plain,
% 21.45/21.66      (![X33 : $i, X34 : $i, X35 : $i]:
% 21.45/21.66         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 21.45/21.66          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 21.45/21.66          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 21.45/21.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 21.45/21.66  thf('71', plain,
% 21.45/21.66      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 21.45/21.66        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 21.45/21.66      inference('sup-', [status(thm)], ['69', '70'])).
% 21.45/21.66  thf('72', plain,
% 21.45/21.66      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 21.45/21.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.45/21.66  thf('73', plain,
% 21.45/21.66      (![X24 : $i, X25 : $i, X26 : $i]:
% 21.45/21.66         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 21.45/21.66          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 21.45/21.66      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 21.45/21.66  thf('74', plain,
% 21.45/21.66      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 21.45/21.66      inference('sup-', [status(thm)], ['72', '73'])).
% 21.45/21.66  thf('75', plain,
% 21.45/21.66      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 21.45/21.66        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 21.45/21.66      inference('demod', [status(thm)], ['71', '74'])).
% 21.45/21.66  thf('76', plain, ((((sk_C_1) = (sk_D)) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 21.45/21.66      inference('sup-', [status(thm)], ['68', '75'])).
% 21.45/21.66  thf(t9_funct_1, axiom,
% 21.45/21.66    (![A:$i]:
% 21.45/21.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 21.45/21.66       ( ![B:$i]:
% 21.45/21.66         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 21.45/21.66           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 21.45/21.66               ( ![C:$i]:
% 21.45/21.66                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 21.45/21.66                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 21.45/21.66             ( ( A ) = ( B ) ) ) ) ) ))).
% 21.45/21.66  thf('77', plain,
% 21.45/21.66      (![X19 : $i, X20 : $i]:
% 21.45/21.66         (~ (v1_relat_1 @ X19)
% 21.45/21.66          | ~ (v1_funct_1 @ X19)
% 21.45/21.66          | ((X20) = (X19))
% 21.45/21.66          | (r2_hidden @ (sk_C @ X19 @ X20) @ (k1_relat_1 @ X20))
% 21.45/21.66          | ((k1_relat_1 @ X20) != (k1_relat_1 @ X19))
% 21.45/21.66          | ~ (v1_funct_1 @ X20)
% 21.45/21.66          | ~ (v1_relat_1 @ X20))),
% 21.45/21.66      inference('cnf', [status(esa)], [t9_funct_1])).
% 21.45/21.66  thf('78', plain,
% 21.45/21.66      (![X0 : $i]:
% 21.45/21.66         (((sk_A) != (k1_relat_1 @ X0))
% 21.45/21.66          | ((sk_C_1) = (sk_D))
% 21.45/21.66          | ~ (v1_relat_1 @ sk_C_1)
% 21.45/21.66          | ~ (v1_funct_1 @ sk_C_1)
% 21.45/21.66          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 21.45/21.66          | ((sk_C_1) = (X0))
% 21.45/21.66          | ~ (v1_funct_1 @ X0)
% 21.45/21.66          | ~ (v1_relat_1 @ X0))),
% 21.45/21.66      inference('sup-', [status(thm)], ['76', '77'])).
% 21.45/21.66  thf('79', plain,
% 21.45/21.66      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 21.45/21.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.45/21.66  thf(cc1_relset_1, axiom,
% 21.45/21.66    (![A:$i,B:$i,C:$i]:
% 21.45/21.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.45/21.66       ( v1_relat_1 @ C ) ))).
% 21.45/21.66  thf('80', plain,
% 21.45/21.66      (![X21 : $i, X22 : $i, X23 : $i]:
% 21.45/21.66         ((v1_relat_1 @ X21)
% 21.45/21.66          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 21.45/21.66      inference('cnf', [status(esa)], [cc1_relset_1])).
% 21.45/21.66  thf('81', plain, ((v1_relat_1 @ sk_C_1)),
% 21.45/21.66      inference('sup-', [status(thm)], ['79', '80'])).
% 21.45/21.66  thf('82', plain, ((v1_funct_1 @ sk_C_1)),
% 21.45/21.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.45/21.66  thf('83', plain,
% 21.45/21.66      (![X0 : $i]:
% 21.45/21.66         (((sk_A) != (k1_relat_1 @ X0))
% 21.45/21.66          | ((sk_C_1) = (sk_D))
% 21.45/21.66          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 21.45/21.66          | ((sk_C_1) = (X0))
% 21.45/21.66          | ~ (v1_funct_1 @ X0)
% 21.45/21.66          | ~ (v1_relat_1 @ X0))),
% 21.45/21.66      inference('demod', [status(thm)], ['78', '81', '82'])).
% 21.45/21.66  thf('84', plain,
% 21.45/21.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.45/21.66         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 21.45/21.66      inference('sup+', [status(thm)], ['1', '3'])).
% 21.45/21.66  thf('85', plain,
% 21.45/21.66      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 21.45/21.66        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 21.45/21.66      inference('sup-', [status(thm)], ['65', '66'])).
% 21.45/21.66  thf('86', plain,
% 21.45/21.66      (![X0 : $i]:
% 21.45/21.66         (((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0))
% 21.45/21.66          | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A))),
% 21.45/21.66      inference('sup-', [status(thm)], ['84', '85'])).
% 21.45/21.66  thf('87', plain,
% 21.45/21.66      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 21.45/21.66        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 21.45/21.66      inference('demod', [status(thm)], ['71', '74'])).
% 21.45/21.66  thf('88', plain,
% 21.45/21.66      (![X0 : $i]:
% 21.45/21.66         (((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0))
% 21.45/21.66          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 21.45/21.66      inference('sup-', [status(thm)], ['86', '87'])).
% 21.45/21.66  thf('89', plain,
% 21.45/21.66      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_D)
% 21.45/21.66        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_D)))),
% 21.45/21.66      inference('sup-', [status(thm)], ['19', '20'])).
% 21.45/21.66  thf('90', plain,
% 21.45/21.66      ((~ (r1_tarski @ k1_xboole_0 @ sk_D)
% 21.45/21.66        | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 21.45/21.66        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_D)))),
% 21.45/21.66      inference('sup-', [status(thm)], ['88', '89'])).
% 21.45/21.66  thf('91', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 21.45/21.66      inference('sup-', [status(thm)], ['23', '24'])).
% 21.45/21.66  thf('92', plain,
% 21.45/21.66      ((((sk_A) = (k1_relat_1 @ sk_C_1))
% 21.45/21.66        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_D)))),
% 21.45/21.66      inference('demod', [status(thm)], ['90', '91'])).
% 21.45/21.66  thf('93', plain,
% 21.45/21.66      (![X0 : $i]:
% 21.45/21.66         (((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0))
% 21.45/21.66          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 21.45/21.66      inference('sup-', [status(thm)], ['86', '87'])).
% 21.45/21.66  thf('94', plain,
% 21.45/21.66      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C_1)
% 21.45/21.66        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_C_1)))),
% 21.45/21.66      inference('sup-', [status(thm)], ['30', '31'])).
% 21.45/21.66  thf('95', plain,
% 21.45/21.66      ((~ (r1_tarski @ k1_xboole_0 @ sk_C_1)
% 21.45/21.66        | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 21.45/21.66        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_C_1)))),
% 21.45/21.66      inference('sup-', [status(thm)], ['93', '94'])).
% 21.45/21.66  thf('96', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 21.45/21.66      inference('sup-', [status(thm)], ['23', '24'])).
% 21.45/21.66  thf('97', plain,
% 21.45/21.66      ((((sk_A) = (k1_relat_1 @ sk_C_1))
% 21.45/21.66        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_C_1)))),
% 21.45/21.66      inference('demod', [status(thm)], ['95', '96'])).
% 21.45/21.66  thf('98', plain,
% 21.45/21.66      (![X0 : $i, X1 : $i]:
% 21.45/21.66         (r2_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 21.45/21.66          (k2_zfmisc_1 @ X1 @ X0))),
% 21.45/21.66      inference('sup-', [status(thm)], ['39', '41'])).
% 21.45/21.66  thf('99', plain,
% 21.45/21.66      (((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 21.45/21.66        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 21.45/21.66      inference('sup+', [status(thm)], ['97', '98'])).
% 21.45/21.66  thf('100', plain,
% 21.45/21.66      (((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)
% 21.45/21.66        | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 21.45/21.66        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 21.45/21.66      inference('sup+', [status(thm)], ['92', '99'])).
% 21.45/21.66  thf('101', plain,
% 21.45/21.66      ((((sk_A) = (k1_relat_1 @ sk_C_1))
% 21.45/21.66        | (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))),
% 21.45/21.66      inference('simplify', [status(thm)], ['100'])).
% 21.45/21.66  thf('102', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)),
% 21.45/21.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.45/21.66  thf('103', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 21.45/21.66      inference('clc', [status(thm)], ['101', '102'])).
% 21.45/21.66  thf('104', plain,
% 21.45/21.66      (![X0 : $i]:
% 21.45/21.66         (((sk_A) != (k1_relat_1 @ X0))
% 21.45/21.66          | ((sk_C_1) = (sk_D))
% 21.45/21.66          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A)
% 21.45/21.66          | ((sk_C_1) = (X0))
% 21.45/21.66          | ~ (v1_funct_1 @ X0)
% 21.45/21.66          | ~ (v1_relat_1 @ X0))),
% 21.45/21.66      inference('demod', [status(thm)], ['83', '103'])).
% 21.45/21.66  thf('105', plain,
% 21.45/21.66      ((((sk_A) != (sk_A))
% 21.45/21.66        | ~ (v1_relat_1 @ sk_D)
% 21.45/21.66        | ~ (v1_funct_1 @ sk_D)
% 21.45/21.66        | ((sk_C_1) = (sk_D))
% 21.45/21.66        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A)
% 21.45/21.66        | ((sk_C_1) = (sk_D)))),
% 21.45/21.66      inference('sup-', [status(thm)], ['47', '104'])).
% 21.45/21.66  thf('106', plain,
% 21.45/21.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 21.45/21.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.45/21.66  thf('107', plain,
% 21.45/21.66      (![X21 : $i, X22 : $i, X23 : $i]:
% 21.45/21.66         ((v1_relat_1 @ X21)
% 21.45/21.66          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 21.45/21.66      inference('cnf', [status(esa)], [cc1_relset_1])).
% 21.45/21.66  thf('108', plain, ((v1_relat_1 @ sk_D)),
% 21.45/21.66      inference('sup-', [status(thm)], ['106', '107'])).
% 21.45/21.66  thf('109', plain, ((v1_funct_1 @ sk_D)),
% 21.45/21.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.45/21.66  thf('110', plain,
% 21.45/21.66      ((((sk_A) != (sk_A))
% 21.45/21.66        | ((sk_C_1) = (sk_D))
% 21.45/21.66        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A)
% 21.45/21.66        | ((sk_C_1) = (sk_D)))),
% 21.45/21.66      inference('demod', [status(thm)], ['105', '108', '109'])).
% 21.45/21.66  thf('111', plain,
% 21.45/21.66      (((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A) | ((sk_C_1) = (sk_D)))),
% 21.45/21.66      inference('simplify', [status(thm)], ['110'])).
% 21.45/21.66  thf(d2_subset_1, axiom,
% 21.45/21.66    (![A:$i,B:$i]:
% 21.45/21.66     ( ( ( v1_xboole_0 @ A ) =>
% 21.45/21.66         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 21.45/21.66       ( ( ~( v1_xboole_0 @ A ) ) =>
% 21.45/21.66         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 21.45/21.66  thf('112', plain,
% 21.45/21.66      (![X9 : $i, X10 : $i]:
% 21.45/21.66         (~ (r2_hidden @ X9 @ X10)
% 21.45/21.66          | (m1_subset_1 @ X9 @ X10)
% 21.45/21.66          | (v1_xboole_0 @ X10))),
% 21.45/21.66      inference('cnf', [status(esa)], [d2_subset_1])).
% 21.45/21.66  thf(d1_xboole_0, axiom,
% 21.45/21.66    (![A:$i]:
% 21.45/21.66     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 21.45/21.66  thf('113', plain,
% 21.45/21.66      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 21.45/21.66      inference('cnf', [status(esa)], [d1_xboole_0])).
% 21.45/21.66  thf('114', plain,
% 21.45/21.66      (![X9 : $i, X10 : $i]:
% 21.45/21.66         ((m1_subset_1 @ X9 @ X10) | ~ (r2_hidden @ X9 @ X10))),
% 21.45/21.66      inference('clc', [status(thm)], ['112', '113'])).
% 21.45/21.66  thf('115', plain,
% 21.45/21.66      ((((sk_C_1) = (sk_D)) | (m1_subset_1 @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 21.45/21.66      inference('sup-', [status(thm)], ['111', '114'])).
% 21.45/21.66  thf('116', plain,
% 21.45/21.66      (![X39 : $i]:
% 21.45/21.66         (((k1_funct_1 @ sk_C_1 @ X39) = (k1_funct_1 @ sk_D @ X39))
% 21.45/21.66          | ~ (m1_subset_1 @ X39 @ sk_A))),
% 21.45/21.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.45/21.66  thf('117', plain,
% 21.45/21.66      ((((sk_C_1) = (sk_D))
% 21.45/21.66        | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 21.45/21.66            = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))))),
% 21.45/21.66      inference('sup-', [status(thm)], ['115', '116'])).
% 21.45/21.66  thf('118', plain,
% 21.45/21.66      (((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 21.45/21.66         = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))),
% 21.45/21.66      inference('condensation', [status(thm)], ['117'])).
% 21.45/21.66  thf('119', plain,
% 21.45/21.66      (![X19 : $i, X20 : $i]:
% 21.45/21.66         (~ (v1_relat_1 @ X19)
% 21.45/21.66          | ~ (v1_funct_1 @ X19)
% 21.45/21.66          | ((X20) = (X19))
% 21.45/21.66          | ((k1_funct_1 @ X20 @ (sk_C @ X19 @ X20))
% 21.45/21.66              != (k1_funct_1 @ X19 @ (sk_C @ X19 @ X20)))
% 21.45/21.66          | ((k1_relat_1 @ X20) != (k1_relat_1 @ X19))
% 21.45/21.66          | ~ (v1_funct_1 @ X20)
% 21.45/21.66          | ~ (v1_relat_1 @ X20))),
% 21.45/21.66      inference('cnf', [status(esa)], [t9_funct_1])).
% 21.45/21.66  thf('120', plain,
% 21.45/21.66      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 21.45/21.66          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 21.45/21.66        | ~ (v1_relat_1 @ sk_C_1)
% 21.45/21.66        | ~ (v1_funct_1 @ sk_C_1)
% 21.45/21.66        | ((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_D))
% 21.45/21.66        | ((sk_C_1) = (sk_D))
% 21.45/21.66        | ~ (v1_funct_1 @ sk_D)
% 21.45/21.66        | ~ (v1_relat_1 @ sk_D))),
% 21.45/21.66      inference('sup-', [status(thm)], ['118', '119'])).
% 21.45/21.66  thf('121', plain, ((v1_relat_1 @ sk_C_1)),
% 21.45/21.66      inference('sup-', [status(thm)], ['79', '80'])).
% 21.45/21.66  thf('122', plain, ((v1_funct_1 @ sk_C_1)),
% 21.45/21.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.45/21.66  thf('123', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 21.45/21.66      inference('clc', [status(thm)], ['101', '102'])).
% 21.45/21.66  thf('124', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 21.45/21.66      inference('clc', [status(thm)], ['45', '46'])).
% 21.45/21.66  thf('125', plain, ((v1_funct_1 @ sk_D)),
% 21.45/21.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.45/21.66  thf('126', plain, ((v1_relat_1 @ sk_D)),
% 21.45/21.66      inference('sup-', [status(thm)], ['106', '107'])).
% 21.45/21.66  thf('127', plain,
% 21.45/21.66      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 21.45/21.66          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 21.45/21.66        | ((sk_A) != (sk_A))
% 21.45/21.66        | ((sk_C_1) = (sk_D)))),
% 21.45/21.66      inference('demod', [status(thm)],
% 21.45/21.66                ['120', '121', '122', '123', '124', '125', '126'])).
% 21.45/21.66  thf('128', plain, (((sk_C_1) = (sk_D))),
% 21.45/21.66      inference('simplify', [status(thm)], ['127'])).
% 21.45/21.66  thf('129', plain,
% 21.45/21.66      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 21.45/21.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.45/21.66  thf('130', plain,
% 21.45/21.66      (![X28 : $i, X29 : $i, X30 : $i]:
% 21.45/21.66         ((r2_relset_1 @ X28 @ X29 @ X30 @ X30)
% 21.45/21.66          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 21.45/21.66      inference('simplify', [status(thm)], ['40'])).
% 21.45/21.66  thf('131', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_C_1)),
% 21.45/21.66      inference('sup-', [status(thm)], ['129', '130'])).
% 21.45/21.66  thf('132', plain, ($false),
% 21.45/21.66      inference('demod', [status(thm)], ['0', '128', '131'])).
% 21.45/21.66  
% 21.45/21.66  % SZS output end Refutation
% 21.45/21.66  
% 21.45/21.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
