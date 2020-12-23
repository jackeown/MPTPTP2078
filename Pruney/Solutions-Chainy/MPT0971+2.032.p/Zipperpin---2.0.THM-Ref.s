%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HKwKC0kO9K

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:31 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 791 expanded)
%              Number of leaves         :   38 ( 244 expanded)
%              Depth                    :   17
%              Number of atoms          :  841 (10150 expanded)
%              Number of equality atoms :   75 ( 571 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(t17_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ~ ( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) )
          & ! [E: $i] :
              ~ ( ( r2_hidden @ E @ A )
                & ( ( k1_funct_1 @ D @ E )
                  = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ~ ( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) )
            & ! [E: $i] :
                ~ ( ( r2_hidden @ E @ A )
                  & ( ( k1_funct_1 @ D @ E )
                    = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C_1 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_C_1 @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ( X13
       != ( k2_relat_1 @ X11 ) )
      | ( r2_hidden @ ( sk_D_1 @ X14 @ X11 ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('6',plain,(
    ! [X11: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( r2_hidden @ X14 @ ( k2_relat_1 @ X11 ) )
      | ( r2_hidden @ ( sk_D_1 @ X14 @ X11 ) @ ( k1_relat_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    r2_hidden @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['7','8','13'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('16',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B_1 ),
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

thf('18',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('25',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('26',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('27',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('30',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r2_hidden @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['7','8','13'])).

thf('32',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) @ sk_A )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X34: $i] :
      ( ~ ( r2_hidden @ X34 @ sk_A )
      | ( ( k1_funct_1 @ sk_D_2 @ X34 )
       != sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) )
     != sk_C_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r2_hidden @ sk_C_1 @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('36',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ( X13
       != ( k2_relat_1 @ X11 ) )
      | ( X14
        = ( k1_funct_1 @ X11 @ ( sk_D_1 @ X14 @ X11 ) ) )
      | ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('37',plain,(
    ! [X11: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( r2_hidden @ X14 @ ( k2_relat_1 @ X11 ) )
      | ( X14
        = ( k1_funct_1 @ X11 @ ( sk_D_1 @ X14 @ X11 ) ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( sk_C_1
      = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['11','12'])).

thf('41',plain,
    ( sk_C_1
    = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_1 != sk_C_1 ) ),
    inference(demod,[status(thm)],['34','41'])).

thf('43',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['23','43'])).

thf('45',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('47',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('50',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('51',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49','51'])).

thf('53',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( X31 != k1_xboole_0 )
      | ( X32 = k1_xboole_0 )
      | ( X33 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X33 @ X32 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('54',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X32 @ k1_xboole_0 )
      | ( X33 = k1_xboole_0 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('56',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_2 @ X33 @ X32 @ k1_xboole_0 )
      | ( X33 = k1_xboole_0 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_D_2 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ sk_D_2 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','56'])).

thf('58',plain,
    ( ( sk_D_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','57'])).

thf('59',plain,(
    r2_hidden @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['7','8','13'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('60',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) )
      | ( X19
       != ( k1_funct_1 @ X18 @ X17 ) )
      | ( r2_hidden @ ( k4_tarski @ X17 @ X19 ) @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('61',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( r2_hidden @ ( k4_tarski @ X17 @ ( k1_funct_1 @ X18 @ X17 ) ) @ X18 )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) @ ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) ) ) @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['59','61'])).

thf('63',plain,
    ( sk_C_1
    = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('64',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['11','12'])).

thf('66',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) @ sk_C_1 ) @ sk_D_2 ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('68',plain,(
    ~ ( v1_xboole_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','68'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('70',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('71',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49','51'])).

thf('73',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('74',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X27 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('78',plain,(
    ! [X26: $i] :
      ( zip_tseitin_0 @ X26 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['76','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ sk_D_2 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','79'])).

thf('81',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','70'])).

thf('82',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['44','71','80','81'])).

thf('83',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('84',plain,(
    $false ),
    inference(demod,[status(thm)],['16','82','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HKwKC0kO9K
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:59:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.52/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.71  % Solved by: fo/fo7.sh
% 0.52/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.71  % done 193 iterations in 0.252s
% 0.52/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.71  % SZS output start Refutation
% 0.52/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.52/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.52/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.52/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.52/0.71  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.52/0.71  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.52/0.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.52/0.71  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.52/0.71  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.52/0.71  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.52/0.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.52/0.71  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.52/0.71  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.52/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.71  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.52/0.71  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.52/0.71  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.52/0.71  thf(t17_funct_2, conjecture,
% 0.52/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.71     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.52/0.71         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.71       ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.52/0.71            ( ![E:$i]:
% 0.52/0.71              ( ~( ( r2_hidden @ E @ A ) & ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ))).
% 0.52/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.71    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.71        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.52/0.71            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.71          ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.52/0.71               ( ![E:$i]:
% 0.52/0.71                 ( ~( ( r2_hidden @ E @ A ) & 
% 0.52/0.71                      ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ) )),
% 0.52/0.71    inference('cnf.neg', [status(esa)], [t17_funct_2])).
% 0.52/0.71  thf('0', plain,
% 0.52/0.71      ((r2_hidden @ sk_C_1 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_2))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('1', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf(redefinition_k2_relset_1, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i]:
% 0.52/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.71       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.52/0.71  thf('2', plain,
% 0.52/0.71      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.52/0.71         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 0.52/0.71          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.52/0.71      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.52/0.71  thf('3', plain,
% 0.52/0.71      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 0.52/0.71      inference('sup-', [status(thm)], ['1', '2'])).
% 0.52/0.71  thf('4', plain, ((r2_hidden @ sk_C_1 @ (k2_relat_1 @ sk_D_2))),
% 0.52/0.71      inference('demod', [status(thm)], ['0', '3'])).
% 0.52/0.71  thf(d5_funct_1, axiom,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.52/0.71       ( ![B:$i]:
% 0.52/0.71         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.52/0.71           ( ![C:$i]:
% 0.52/0.71             ( ( r2_hidden @ C @ B ) <=>
% 0.52/0.71               ( ?[D:$i]:
% 0.52/0.71                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.52/0.71                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.52/0.71  thf('5', plain,
% 0.52/0.71      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.52/0.71         (((X13) != (k2_relat_1 @ X11))
% 0.52/0.71          | (r2_hidden @ (sk_D_1 @ X14 @ X11) @ (k1_relat_1 @ X11))
% 0.52/0.71          | ~ (r2_hidden @ X14 @ X13)
% 0.52/0.71          | ~ (v1_funct_1 @ X11)
% 0.52/0.71          | ~ (v1_relat_1 @ X11))),
% 0.52/0.71      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.52/0.71  thf('6', plain,
% 0.52/0.71      (![X11 : $i, X14 : $i]:
% 0.52/0.71         (~ (v1_relat_1 @ X11)
% 0.52/0.71          | ~ (v1_funct_1 @ X11)
% 0.52/0.71          | ~ (r2_hidden @ X14 @ (k2_relat_1 @ X11))
% 0.52/0.71          | (r2_hidden @ (sk_D_1 @ X14 @ X11) @ (k1_relat_1 @ X11)))),
% 0.52/0.71      inference('simplify', [status(thm)], ['5'])).
% 0.52/0.71  thf('7', plain,
% 0.52/0.71      (((r2_hidden @ (sk_D_1 @ sk_C_1 @ sk_D_2) @ (k1_relat_1 @ sk_D_2))
% 0.52/0.71        | ~ (v1_funct_1 @ sk_D_2)
% 0.52/0.71        | ~ (v1_relat_1 @ sk_D_2))),
% 0.52/0.71      inference('sup-', [status(thm)], ['4', '6'])).
% 0.52/0.71  thf('8', plain, ((v1_funct_1 @ sk_D_2)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('9', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf(cc2_relat_1, axiom,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( v1_relat_1 @ A ) =>
% 0.52/0.71       ( ![B:$i]:
% 0.52/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.52/0.71  thf('10', plain,
% 0.52/0.71      (![X6 : $i, X7 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.52/0.71          | (v1_relat_1 @ X6)
% 0.52/0.71          | ~ (v1_relat_1 @ X7))),
% 0.52/0.71      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.52/0.71  thf('11', plain,
% 0.52/0.71      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D_2))),
% 0.52/0.71      inference('sup-', [status(thm)], ['9', '10'])).
% 0.52/0.71  thf(fc6_relat_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.52/0.71  thf('12', plain,
% 0.52/0.71      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.52/0.71      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.52/0.71  thf('13', plain, ((v1_relat_1 @ sk_D_2)),
% 0.52/0.71      inference('demod', [status(thm)], ['11', '12'])).
% 0.52/0.71  thf('14', plain,
% 0.52/0.71      ((r2_hidden @ (sk_D_1 @ sk_C_1 @ sk_D_2) @ (k1_relat_1 @ sk_D_2))),
% 0.52/0.71      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.52/0.71  thf(d1_xboole_0, axiom,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.52/0.71  thf('15', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.52/0.71      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.52/0.71  thf('16', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_D_2))),
% 0.52/0.71      inference('sup-', [status(thm)], ['14', '15'])).
% 0.52/0.71  thf('17', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B_1)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf(d1_funct_2, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i]:
% 0.52/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.71       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.52/0.71           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.52/0.71             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.52/0.71         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.52/0.71           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.52/0.71             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.52/0.71  thf(zf_stmt_1, axiom,
% 0.52/0.71    (![C:$i,B:$i,A:$i]:
% 0.52/0.71     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.52/0.71       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.52/0.71  thf('18', plain,
% 0.52/0.71      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.52/0.71         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 0.52/0.71          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 0.52/0.71          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.52/0.71  thf('19', plain,
% 0.52/0.71      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_B_1 @ sk_A)
% 0.52/0.71        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['17', '18'])).
% 0.52/0.71  thf('20', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf(redefinition_k1_relset_1, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i]:
% 0.52/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.71       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.52/0.71  thf('21', plain,
% 0.52/0.71      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.52/0.71         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.52/0.71          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.52/0.71      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.52/0.71  thf('22', plain,
% 0.52/0.71      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.52/0.71      inference('sup-', [status(thm)], ['20', '21'])).
% 0.52/0.71  thf('23', plain,
% 0.52/0.71      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_B_1 @ sk_A)
% 0.52/0.71        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.52/0.71      inference('demod', [status(thm)], ['19', '22'])).
% 0.52/0.71  thf(zf_stmt_2, axiom,
% 0.52/0.71    (![B:$i,A:$i]:
% 0.52/0.71     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.52/0.71       ( zip_tseitin_0 @ B @ A ) ))).
% 0.52/0.71  thf('24', plain,
% 0.52/0.71      (![X26 : $i, X27 : $i]:
% 0.52/0.71         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.52/0.71  thf('25', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.52/0.71  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.52/0.71  thf(zf_stmt_5, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i]:
% 0.52/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.71       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.52/0.71         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.52/0.71           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.52/0.71             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.52/0.71  thf('26', plain,
% 0.52/0.71      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.52/0.71         (~ (zip_tseitin_0 @ X31 @ X32)
% 0.52/0.71          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 0.52/0.71          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.52/0.71  thf('27', plain,
% 0.52/0.71      (((zip_tseitin_1 @ sk_D_2 @ sk_B_1 @ sk_A)
% 0.52/0.71        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.52/0.71      inference('sup-', [status(thm)], ['25', '26'])).
% 0.52/0.71  thf('28', plain,
% 0.52/0.71      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_2 @ sk_B_1 @ sk_A))),
% 0.52/0.71      inference('sup-', [status(thm)], ['24', '27'])).
% 0.52/0.71  thf('29', plain,
% 0.52/0.71      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_B_1 @ sk_A)
% 0.52/0.71        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.52/0.71      inference('demod', [status(thm)], ['19', '22'])).
% 0.52/0.71  thf('30', plain,
% 0.52/0.71      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['28', '29'])).
% 0.52/0.71  thf('31', plain,
% 0.52/0.71      ((r2_hidden @ (sk_D_1 @ sk_C_1 @ sk_D_2) @ (k1_relat_1 @ sk_D_2))),
% 0.52/0.71      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.52/0.71  thf('32', plain,
% 0.52/0.71      (((r2_hidden @ (sk_D_1 @ sk_C_1 @ sk_D_2) @ sk_A)
% 0.52/0.71        | ((sk_B_1) = (k1_xboole_0)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['30', '31'])).
% 0.52/0.71  thf('33', plain,
% 0.52/0.71      (![X34 : $i]:
% 0.52/0.71         (~ (r2_hidden @ X34 @ sk_A)
% 0.52/0.71          | ((k1_funct_1 @ sk_D_2 @ X34) != (sk_C_1)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('34', plain,
% 0.52/0.71      ((((sk_B_1) = (k1_xboole_0))
% 0.52/0.71        | ((k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_C_1 @ sk_D_2)) != (sk_C_1)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['32', '33'])).
% 0.52/0.71  thf('35', plain, ((r2_hidden @ sk_C_1 @ (k2_relat_1 @ sk_D_2))),
% 0.52/0.71      inference('demod', [status(thm)], ['0', '3'])).
% 0.52/0.71  thf('36', plain,
% 0.52/0.71      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.52/0.71         (((X13) != (k2_relat_1 @ X11))
% 0.52/0.71          | ((X14) = (k1_funct_1 @ X11 @ (sk_D_1 @ X14 @ X11)))
% 0.52/0.71          | ~ (r2_hidden @ X14 @ X13)
% 0.52/0.71          | ~ (v1_funct_1 @ X11)
% 0.52/0.71          | ~ (v1_relat_1 @ X11))),
% 0.52/0.71      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.52/0.71  thf('37', plain,
% 0.52/0.71      (![X11 : $i, X14 : $i]:
% 0.52/0.71         (~ (v1_relat_1 @ X11)
% 0.52/0.71          | ~ (v1_funct_1 @ X11)
% 0.52/0.71          | ~ (r2_hidden @ X14 @ (k2_relat_1 @ X11))
% 0.52/0.71          | ((X14) = (k1_funct_1 @ X11 @ (sk_D_1 @ X14 @ X11))))),
% 0.52/0.71      inference('simplify', [status(thm)], ['36'])).
% 0.52/0.71  thf('38', plain,
% 0.52/0.71      ((((sk_C_1) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_C_1 @ sk_D_2)))
% 0.52/0.71        | ~ (v1_funct_1 @ sk_D_2)
% 0.52/0.71        | ~ (v1_relat_1 @ sk_D_2))),
% 0.52/0.71      inference('sup-', [status(thm)], ['35', '37'])).
% 0.52/0.71  thf('39', plain, ((v1_funct_1 @ sk_D_2)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('40', plain, ((v1_relat_1 @ sk_D_2)),
% 0.52/0.71      inference('demod', [status(thm)], ['11', '12'])).
% 0.52/0.71  thf('41', plain,
% 0.52/0.71      (((sk_C_1) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_C_1 @ sk_D_2)))),
% 0.52/0.71      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.52/0.71  thf('42', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_C_1) != (sk_C_1)))),
% 0.52/0.71      inference('demod', [status(thm)], ['34', '41'])).
% 0.52/0.71  thf('43', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.52/0.71      inference('simplify', [status(thm)], ['42'])).
% 0.52/0.71  thf('44', plain,
% 0.52/0.71      ((~ (zip_tseitin_1 @ sk_D_2 @ k1_xboole_0 @ sk_A)
% 0.52/0.71        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.52/0.71      inference('demod', [status(thm)], ['23', '43'])).
% 0.52/0.71  thf('45', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B_1)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('46', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.52/0.71      inference('simplify', [status(thm)], ['42'])).
% 0.52/0.71  thf('47', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0)),
% 0.52/0.71      inference('demod', [status(thm)], ['45', '46'])).
% 0.52/0.71  thf('48', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('49', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.52/0.71      inference('simplify', [status(thm)], ['42'])).
% 0.52/0.71  thf(t113_zfmisc_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.52/0.71       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.52/0.71  thf('50', plain,
% 0.52/0.71      (![X4 : $i, X5 : $i]:
% 0.52/0.71         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.52/0.71  thf('51', plain,
% 0.52/0.71      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.71      inference('simplify', [status(thm)], ['50'])).
% 0.52/0.71  thf('52', plain, ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.52/0.71      inference('demod', [status(thm)], ['48', '49', '51'])).
% 0.52/0.71  thf('53', plain,
% 0.52/0.71      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.52/0.71         (((X31) != (k1_xboole_0))
% 0.52/0.71          | ((X32) = (k1_xboole_0))
% 0.52/0.71          | ((X33) = (k1_xboole_0))
% 0.52/0.71          | ~ (v1_funct_2 @ X33 @ X32 @ X31)
% 0.52/0.71          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.52/0.71  thf('54', plain,
% 0.52/0.71      (![X32 : $i, X33 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X33 @ 
% 0.52/0.71             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ k1_xboole_0)))
% 0.52/0.71          | ~ (v1_funct_2 @ X33 @ X32 @ k1_xboole_0)
% 0.52/0.71          | ((X33) = (k1_xboole_0))
% 0.52/0.71          | ((X32) = (k1_xboole_0)))),
% 0.52/0.71      inference('simplify', [status(thm)], ['53'])).
% 0.52/0.71  thf('55', plain,
% 0.52/0.71      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.71      inference('simplify', [status(thm)], ['50'])).
% 0.52/0.71  thf('56', plain,
% 0.52/0.71      (![X32 : $i, X33 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.52/0.71          | ~ (v1_funct_2 @ X33 @ X32 @ k1_xboole_0)
% 0.52/0.71          | ((X33) = (k1_xboole_0))
% 0.52/0.71          | ((X32) = (k1_xboole_0)))),
% 0.52/0.71      inference('demod', [status(thm)], ['54', '55'])).
% 0.52/0.71  thf('57', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (((X0) = (k1_xboole_0))
% 0.52/0.71          | ((sk_D_2) = (k1_xboole_0))
% 0.52/0.71          | ~ (v1_funct_2 @ sk_D_2 @ X0 @ k1_xboole_0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['52', '56'])).
% 0.52/0.71  thf('58', plain, ((((sk_D_2) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['47', '57'])).
% 0.52/0.71  thf('59', plain,
% 0.52/0.71      ((r2_hidden @ (sk_D_1 @ sk_C_1 @ sk_D_2) @ (k1_relat_1 @ sk_D_2))),
% 0.52/0.71      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.52/0.71  thf(t8_funct_1, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i]:
% 0.52/0.71     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.52/0.71       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.52/0.71         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.52/0.71           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.52/0.71  thf('60', plain,
% 0.52/0.71      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.52/0.71         (~ (r2_hidden @ X17 @ (k1_relat_1 @ X18))
% 0.52/0.71          | ((X19) != (k1_funct_1 @ X18 @ X17))
% 0.52/0.71          | (r2_hidden @ (k4_tarski @ X17 @ X19) @ X18)
% 0.52/0.71          | ~ (v1_funct_1 @ X18)
% 0.52/0.71          | ~ (v1_relat_1 @ X18))),
% 0.52/0.71      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.52/0.71  thf('61', plain,
% 0.52/0.71      (![X17 : $i, X18 : $i]:
% 0.52/0.71         (~ (v1_relat_1 @ X18)
% 0.52/0.71          | ~ (v1_funct_1 @ X18)
% 0.52/0.71          | (r2_hidden @ (k4_tarski @ X17 @ (k1_funct_1 @ X18 @ X17)) @ X18)
% 0.52/0.71          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X18)))),
% 0.52/0.71      inference('simplify', [status(thm)], ['60'])).
% 0.52/0.71  thf('62', plain,
% 0.52/0.71      (((r2_hidden @ 
% 0.52/0.71         (k4_tarski @ (sk_D_1 @ sk_C_1 @ sk_D_2) @ 
% 0.52/0.71          (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_C_1 @ sk_D_2))) @ 
% 0.52/0.71         sk_D_2)
% 0.52/0.71        | ~ (v1_funct_1 @ sk_D_2)
% 0.52/0.71        | ~ (v1_relat_1 @ sk_D_2))),
% 0.52/0.71      inference('sup-', [status(thm)], ['59', '61'])).
% 0.52/0.71  thf('63', plain,
% 0.52/0.71      (((sk_C_1) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_C_1 @ sk_D_2)))),
% 0.52/0.71      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.52/0.71  thf('64', plain, ((v1_funct_1 @ sk_D_2)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('65', plain, ((v1_relat_1 @ sk_D_2)),
% 0.52/0.71      inference('demod', [status(thm)], ['11', '12'])).
% 0.52/0.71  thf('66', plain,
% 0.52/0.71      ((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_C_1 @ sk_D_2) @ sk_C_1) @ sk_D_2)),
% 0.52/0.71      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 0.52/0.71  thf('67', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.52/0.71      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.52/0.71  thf('68', plain, (~ (v1_xboole_0 @ sk_D_2)),
% 0.52/0.71      inference('sup-', [status(thm)], ['66', '67'])).
% 0.52/0.71  thf('69', plain,
% 0.52/0.71      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['58', '68'])).
% 0.52/0.71  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.52/0.71  thf('70', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.52/0.71  thf('71', plain, (((sk_A) = (k1_xboole_0))),
% 0.52/0.71      inference('demod', [status(thm)], ['69', '70'])).
% 0.52/0.71  thf('72', plain, ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.52/0.71      inference('demod', [status(thm)], ['48', '49', '51'])).
% 0.52/0.71  thf('73', plain,
% 0.52/0.71      (![X4 : $i, X5 : $i]:
% 0.52/0.71         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.52/0.71  thf('74', plain,
% 0.52/0.71      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.52/0.71      inference('simplify', [status(thm)], ['73'])).
% 0.52/0.71  thf('75', plain,
% 0.52/0.71      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.52/0.71         (~ (zip_tseitin_0 @ X31 @ X32)
% 0.52/0.71          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 0.52/0.71          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.52/0.71  thf('76', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.52/0.71          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 0.52/0.71          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['74', '75'])).
% 0.52/0.71  thf('77', plain,
% 0.52/0.71      (![X26 : $i, X27 : $i]:
% 0.52/0.71         ((zip_tseitin_0 @ X26 @ X27) | ((X27) != (k1_xboole_0)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.52/0.71  thf('78', plain, (![X26 : $i]: (zip_tseitin_0 @ X26 @ k1_xboole_0)),
% 0.52/0.71      inference('simplify', [status(thm)], ['77'])).
% 0.52/0.71  thf('79', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.52/0.71          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 0.52/0.71      inference('demod', [status(thm)], ['76', '78'])).
% 0.52/0.71  thf('80', plain, (![X0 : $i]: (zip_tseitin_1 @ sk_D_2 @ X0 @ k1_xboole_0)),
% 0.52/0.71      inference('sup-', [status(thm)], ['72', '79'])).
% 0.52/0.71  thf('81', plain, (((sk_A) = (k1_xboole_0))),
% 0.52/0.71      inference('demod', [status(thm)], ['69', '70'])).
% 0.52/0.71  thf('82', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_D_2))),
% 0.52/0.71      inference('demod', [status(thm)], ['44', '71', '80', '81'])).
% 0.52/0.71  thf('83', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.52/0.71  thf('84', plain, ($false),
% 0.52/0.71      inference('demod', [status(thm)], ['16', '82', '83'])).
% 0.52/0.71  
% 0.52/0.71  % SZS output end Refutation
% 0.52/0.71  
% 0.52/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
