%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wZvTFKyYKy

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:44 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 249 expanded)
%              Number of leaves         :   50 (  96 expanded)
%              Depth                    :   17
%              Number of atoms          :  816 (3184 expanded)
%              Number of equality atoms :   40 ( 119 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_5_type,type,(
    sk_D_5: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t116_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
            & ! [F: $i] :
                ( ( m1_subset_1 @ F @ A )
               => ~ ( ( r2_hidden @ F @ C )
                    & ( E
                      = ( k1_funct_1 @ D @ F ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
              & ! [F: $i] :
                  ( ( m1_subset_1 @ F @ A )
                 => ~ ( ( r2_hidden @ F @ C )
                      & ( E
                        = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t116_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_5 @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X68: $i,X69: $i,X70: $i,X71: $i] :
      ( ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X69 @ X70 ) ) )
      | ( ( k7_relset_1 @ X69 @ X70 @ X68 @ X71 )
        = ( k9_relat_1 @ X68 @ X71 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_5 @ X0 )
      = ( k9_relat_1 @ sk_D_5 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_5 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d12_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_funct_1 @ A )
        & ( v1_relat_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) )
                  & ( r2_hidden @ E @ B )
                  & ( D
                    = ( k1_funct_1 @ A @ E ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( D
          = ( k1_funct_1 @ A @ E ) )
        & ( r2_hidden @ E @ B )
        & ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X35: $i,X36: $i,X38: $i,X39: $i] :
      ( ( X38
       != ( k9_relat_1 @ X36 @ X35 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X39 @ X35 @ X36 ) @ X39 @ X35 @ X36 )
      | ~ ( r2_hidden @ X39 @ X38 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X35: $i,X36: $i,X39: $i] :
      ( ~ ( v1_relat_1 @ X36 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( r2_hidden @ X39 @ ( k9_relat_1 @ X36 @ X35 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X39 @ X35 @ X36 ) @ X39 @ X35 @ X36 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C_3 @ sk_D_5 ) @ sk_E_2 @ sk_C_3 @ sk_D_5 )
    | ~ ( v1_funct_1 @ sk_D_5 )
    | ~ ( v1_relat_1 @ sk_D_5 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D_5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('10',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ( v1_relat_1 @ X56 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X58 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D_5 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C_3 @ sk_D_5 ) @ sk_E_2 @ sk_C_3 @ sk_D_5 ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('13',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ X30 @ X32 )
      | ~ ( zip_tseitin_0 @ X30 @ X31 @ X32 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('14',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C_3 @ sk_D_5 ) @ sk_C_3 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X82: $i] :
      ( ( sk_E_2
       != ( k1_funct_1 @ sk_D_5 @ X82 ) )
      | ~ ( r2_hidden @ X82 @ sk_C_3 )
      | ~ ( m1_subset_1 @ X82 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C_3 @ sk_D_5 ) @ sk_A )
    | ( sk_E_2
     != ( k1_funct_1 @ sk_D_5 @ ( sk_E_1 @ sk_E_2 @ sk_C_3 @ sk_D_5 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C_3 @ sk_D_5 ) @ sk_E_2 @ sk_C_3 @ sk_D_5 ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('18',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( X31
        = ( k1_funct_1 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_0 @ X30 @ X31 @ X32 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('19',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_5 @ ( sk_E_1 @ sk_E_2 @ sk_C_3 @ sk_D_5 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C_3 @ sk_D_5 ) @ sk_A )
    | ( sk_E_2 != sk_E_2 ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C_3 @ sk_D_5 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C_3 @ sk_D_5 ) @ sk_E_2 @ sk_C_3 @ sk_D_5 ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('23',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ X30 @ ( k1_relat_1 @ X29 ) )
      | ~ ( zip_tseitin_0 @ X30 @ X31 @ X32 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('24',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C_3 @ sk_D_5 ) @ ( k1_relat_1 @ sk_D_5 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_2 @ sk_D_5 @ sk_A @ sk_B_2 ),
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

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('26',plain,(
    ! [X74: $i,X75: $i,X76: $i] :
      ( ~ ( v1_funct_2 @ X76 @ X74 @ X75 )
      | ( X74
        = ( k1_relset_1 @ X74 @ X75 @ X76 ) )
      | ~ ( zip_tseitin_2 @ X76 @ X75 @ X74 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('27',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_5 @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_D_5 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D_5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ( ( k1_relset_1 @ X66 @ X67 @ X65 )
        = ( k1_relat_1 @ X65 ) )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X66 @ X67 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('30',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_D_5 )
    = ( k1_relat_1 @ sk_D_5 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_5 @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_5 ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D_5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_5,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_6,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_1 @ B @ A )
         => ( zip_tseitin_2 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('33',plain,(
    ! [X77: $i,X78: $i,X79: $i] :
      ( ~ ( zip_tseitin_1 @ X77 @ X78 )
      | ( zip_tseitin_2 @ X79 @ X77 @ X78 )
      | ~ ( m1_subset_1 @ X79 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X78 @ X77 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('34',plain,
    ( ( zip_tseitin_2 @ sk_D_5 @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X72: $i,X73: $i] :
      ( ( zip_tseitin_1 @ X72 @ X73 )
      | ( X72 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('36',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('37',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('38',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( r2_hidden @ X54 @ X55 )
      | ~ ( r1_tarski @ X55 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_1 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','40'])).

thf('42',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C_3 @ sk_D_5 ) @ ( k1_relat_1 @ sk_D_5 ) ),
    inference('sup-',[status(thm)],['22','23'])).

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

thf('43',plain,(
    ! [X43: $i,X45: $i,X47: $i,X48: $i] :
      ( ( X45
       != ( k2_relat_1 @ X43 ) )
      | ( r2_hidden @ X47 @ X45 )
      | ~ ( r2_hidden @ X48 @ ( k1_relat_1 @ X43 ) )
      | ( X47
       != ( k1_funct_1 @ X43 @ X48 ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('44',plain,(
    ! [X43: $i,X48: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( r2_hidden @ X48 @ ( k1_relat_1 @ X43 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X43 @ X48 ) @ ( k2_relat_1 @ X43 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_D_5 @ ( sk_E_1 @ sk_E_2 @ sk_C_3 @ sk_D_5 ) ) @ ( k2_relat_1 @ sk_D_5 ) )
    | ~ ( v1_funct_1 @ sk_D_5 )
    | ~ ( v1_relat_1 @ sk_D_5 ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_5 @ ( sk_E_1 @ sk_E_2 @ sk_C_3 @ sk_D_5 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('47',plain,(
    v1_funct_1 @ sk_D_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_relat_1 @ sk_D_5 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('49',plain,(
    r2_hidden @ sk_E_2 @ ( k2_relat_1 @ sk_D_5 ) ),
    inference(demod,[status(thm)],['45','46','47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D_5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('51',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( v5_relat_1 @ X59 @ X61 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X61 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('52',plain,(
    v5_relat_1 @ sk_D_5 @ sk_B_2 ),
    inference('sup-',[status(thm)],['50','51'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('53',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v5_relat_1 @ X21 @ X22 )
      | ( r1_tarski @ ( k2_relat_1 @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('54',plain,
    ( ~ ( v1_relat_1 @ sk_D_5 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_5 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_D_5 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('56',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_5 ) @ sk_B_2 ),
    inference(demod,[status(thm)],['54','55'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('57',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_5 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    r2_hidden @ sk_E_2 @ sk_B_2 ),
    inference('sup-',[status(thm)],['49','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('61',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ sk_B_2 @ X0 ) ),
    inference('sup-',[status(thm)],['41','61'])).

thf('63',plain,(
    zip_tseitin_2 @ sk_D_5 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['34','62'])).

thf('64',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_5 ) ),
    inference(demod,[status(thm)],['31','63'])).

thf('65',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C_3 @ sk_D_5 ) @ sk_A ),
    inference(demod,[status(thm)],['24','64'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('66',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ X16 @ X17 )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('67',plain,(
    m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C_3 @ sk_D_5 ) @ sk_A ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    $false ),
    inference(demod,[status(thm)],['21','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wZvTFKyYKy
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:34:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.33/1.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.33/1.52  % Solved by: fo/fo7.sh
% 1.33/1.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.33/1.52  % done 1316 iterations in 1.050s
% 1.33/1.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.33/1.52  % SZS output start Refutation
% 1.33/1.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.33/1.52  thf(sk_A_type, type, sk_A: $i).
% 1.33/1.52  thf(sk_B_2_type, type, sk_B_2: $i).
% 1.33/1.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.33/1.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.33/1.52  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 1.33/1.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.33/1.52  thf(sk_C_3_type, type, sk_C_3: $i).
% 1.33/1.52  thf(sk_B_type, type, sk_B: $i > $i).
% 1.33/1.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.33/1.52  thf(sk_D_5_type, type, sk_D_5: $i).
% 1.33/1.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.33/1.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.33/1.52  thf(sk_E_2_type, type, sk_E_2: $i).
% 1.33/1.52  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.33/1.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.33/1.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.33/1.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.33/1.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.33/1.52  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.33/1.52  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 1.33/1.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.33/1.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.33/1.52  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 1.33/1.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.33/1.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.33/1.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.33/1.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.33/1.52  thf(t116_funct_2, conjecture,
% 1.33/1.52    (![A:$i,B:$i,C:$i,D:$i]:
% 1.33/1.52     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.33/1.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.33/1.52       ( ![E:$i]:
% 1.33/1.52         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 1.33/1.52              ( ![F:$i]:
% 1.33/1.52                ( ( m1_subset_1 @ F @ A ) =>
% 1.33/1.52                  ( ~( ( r2_hidden @ F @ C ) & 
% 1.33/1.52                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 1.33/1.52  thf(zf_stmt_0, negated_conjecture,
% 1.33/1.52    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.33/1.52        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.33/1.52            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.33/1.52          ( ![E:$i]:
% 1.33/1.52            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 1.33/1.52                 ( ![F:$i]:
% 1.33/1.52                   ( ( m1_subset_1 @ F @ A ) =>
% 1.33/1.52                     ( ~( ( r2_hidden @ F @ C ) & 
% 1.33/1.52                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 1.33/1.52    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 1.33/1.52  thf('0', plain,
% 1.33/1.52      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_5 @ sk_C_3))),
% 1.33/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.52  thf('1', plain,
% 1.33/1.52      ((m1_subset_1 @ sk_D_5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.33/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.52  thf(redefinition_k7_relset_1, axiom,
% 1.33/1.52    (![A:$i,B:$i,C:$i,D:$i]:
% 1.33/1.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.33/1.52       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 1.33/1.52  thf('2', plain,
% 1.33/1.52      (![X68 : $i, X69 : $i, X70 : $i, X71 : $i]:
% 1.33/1.52         (~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X69 @ X70)))
% 1.33/1.52          | ((k7_relset_1 @ X69 @ X70 @ X68 @ X71) = (k9_relat_1 @ X68 @ X71)))),
% 1.33/1.52      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.33/1.52  thf('3', plain,
% 1.33/1.52      (![X0 : $i]:
% 1.33/1.52         ((k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_5 @ X0)
% 1.33/1.52           = (k9_relat_1 @ sk_D_5 @ X0))),
% 1.33/1.52      inference('sup-', [status(thm)], ['1', '2'])).
% 1.33/1.52  thf('4', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_5 @ sk_C_3))),
% 1.33/1.52      inference('demod', [status(thm)], ['0', '3'])).
% 1.33/1.52  thf(d12_funct_1, axiom,
% 1.33/1.52    (![A:$i]:
% 1.33/1.52     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 1.33/1.52       ( ![B:$i,C:$i]:
% 1.33/1.52         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 1.33/1.52           ( ![D:$i]:
% 1.33/1.52             ( ( r2_hidden @ D @ C ) <=>
% 1.33/1.52               ( ?[E:$i]:
% 1.33/1.52                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 1.33/1.52                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 1.33/1.52  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.33/1.52  thf(zf_stmt_2, axiom,
% 1.33/1.52    (![E:$i,D:$i,B:$i,A:$i]:
% 1.33/1.52     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 1.33/1.52       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 1.33/1.52         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 1.33/1.52  thf(zf_stmt_3, axiom,
% 1.33/1.52    (![A:$i]:
% 1.33/1.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.33/1.52       ( ![B:$i,C:$i]:
% 1.33/1.52         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 1.33/1.52           ( ![D:$i]:
% 1.33/1.52             ( ( r2_hidden @ D @ C ) <=>
% 1.33/1.52               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 1.33/1.52  thf('5', plain,
% 1.33/1.52      (![X35 : $i, X36 : $i, X38 : $i, X39 : $i]:
% 1.33/1.52         (((X38) != (k9_relat_1 @ X36 @ X35))
% 1.33/1.52          | (zip_tseitin_0 @ (sk_E_1 @ X39 @ X35 @ X36) @ X39 @ X35 @ X36)
% 1.33/1.52          | ~ (r2_hidden @ X39 @ X38)
% 1.33/1.52          | ~ (v1_funct_1 @ X36)
% 1.33/1.52          | ~ (v1_relat_1 @ X36))),
% 1.33/1.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.33/1.52  thf('6', plain,
% 1.33/1.52      (![X35 : $i, X36 : $i, X39 : $i]:
% 1.33/1.52         (~ (v1_relat_1 @ X36)
% 1.33/1.52          | ~ (v1_funct_1 @ X36)
% 1.33/1.52          | ~ (r2_hidden @ X39 @ (k9_relat_1 @ X36 @ X35))
% 1.33/1.52          | (zip_tseitin_0 @ (sk_E_1 @ X39 @ X35 @ X36) @ X39 @ X35 @ X36))),
% 1.33/1.52      inference('simplify', [status(thm)], ['5'])).
% 1.33/1.52  thf('7', plain,
% 1.33/1.52      (((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C_3 @ sk_D_5) @ sk_E_2 @ 
% 1.33/1.52         sk_C_3 @ sk_D_5)
% 1.33/1.52        | ~ (v1_funct_1 @ sk_D_5)
% 1.33/1.52        | ~ (v1_relat_1 @ sk_D_5))),
% 1.33/1.52      inference('sup-', [status(thm)], ['4', '6'])).
% 1.33/1.52  thf('8', plain, ((v1_funct_1 @ sk_D_5)),
% 1.33/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.52  thf('9', plain,
% 1.33/1.52      ((m1_subset_1 @ sk_D_5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.33/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.52  thf(cc1_relset_1, axiom,
% 1.33/1.52    (![A:$i,B:$i,C:$i]:
% 1.33/1.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.33/1.52       ( v1_relat_1 @ C ) ))).
% 1.33/1.52  thf('10', plain,
% 1.33/1.52      (![X56 : $i, X57 : $i, X58 : $i]:
% 1.33/1.52         ((v1_relat_1 @ X56)
% 1.33/1.52          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X58))))),
% 1.33/1.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.33/1.52  thf('11', plain, ((v1_relat_1 @ sk_D_5)),
% 1.33/1.52      inference('sup-', [status(thm)], ['9', '10'])).
% 1.33/1.52  thf('12', plain,
% 1.33/1.52      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C_3 @ sk_D_5) @ sk_E_2 @ 
% 1.33/1.52        sk_C_3 @ sk_D_5)),
% 1.33/1.52      inference('demod', [status(thm)], ['7', '8', '11'])).
% 1.33/1.52  thf('13', plain,
% 1.33/1.52      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.33/1.52         ((r2_hidden @ X30 @ X32) | ~ (zip_tseitin_0 @ X30 @ X31 @ X32 @ X29))),
% 1.33/1.52      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.33/1.52  thf('14', plain,
% 1.33/1.52      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C_3 @ sk_D_5) @ sk_C_3)),
% 1.33/1.52      inference('sup-', [status(thm)], ['12', '13'])).
% 1.33/1.52  thf('15', plain,
% 1.33/1.52      (![X82 : $i]:
% 1.33/1.52         (((sk_E_2) != (k1_funct_1 @ sk_D_5 @ X82))
% 1.33/1.52          | ~ (r2_hidden @ X82 @ sk_C_3)
% 1.33/1.52          | ~ (m1_subset_1 @ X82 @ sk_A))),
% 1.33/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.52  thf('16', plain,
% 1.33/1.52      ((~ (m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C_3 @ sk_D_5) @ sk_A)
% 1.33/1.52        | ((sk_E_2)
% 1.33/1.52            != (k1_funct_1 @ sk_D_5 @ (sk_E_1 @ sk_E_2 @ sk_C_3 @ sk_D_5))))),
% 1.33/1.52      inference('sup-', [status(thm)], ['14', '15'])).
% 1.33/1.52  thf('17', plain,
% 1.33/1.52      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C_3 @ sk_D_5) @ sk_E_2 @ 
% 1.33/1.52        sk_C_3 @ sk_D_5)),
% 1.33/1.52      inference('demod', [status(thm)], ['7', '8', '11'])).
% 1.33/1.52  thf('18', plain,
% 1.33/1.52      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.33/1.52         (((X31) = (k1_funct_1 @ X29 @ X30))
% 1.33/1.52          | ~ (zip_tseitin_0 @ X30 @ X31 @ X32 @ X29))),
% 1.33/1.52      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.33/1.52  thf('19', plain,
% 1.33/1.52      (((sk_E_2) = (k1_funct_1 @ sk_D_5 @ (sk_E_1 @ sk_E_2 @ sk_C_3 @ sk_D_5)))),
% 1.33/1.52      inference('sup-', [status(thm)], ['17', '18'])).
% 1.33/1.52  thf('20', plain,
% 1.33/1.52      ((~ (m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C_3 @ sk_D_5) @ sk_A)
% 1.33/1.52        | ((sk_E_2) != (sk_E_2)))),
% 1.33/1.52      inference('demod', [status(thm)], ['16', '19'])).
% 1.33/1.52  thf('21', plain,
% 1.33/1.52      (~ (m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C_3 @ sk_D_5) @ sk_A)),
% 1.33/1.52      inference('simplify', [status(thm)], ['20'])).
% 1.33/1.52  thf('22', plain,
% 1.33/1.52      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C_3 @ sk_D_5) @ sk_E_2 @ 
% 1.33/1.52        sk_C_3 @ sk_D_5)),
% 1.33/1.52      inference('demod', [status(thm)], ['7', '8', '11'])).
% 1.33/1.52  thf('23', plain,
% 1.33/1.52      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.33/1.52         ((r2_hidden @ X30 @ (k1_relat_1 @ X29))
% 1.33/1.52          | ~ (zip_tseitin_0 @ X30 @ X31 @ X32 @ X29))),
% 1.33/1.52      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.33/1.52  thf('24', plain,
% 1.33/1.52      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C_3 @ sk_D_5) @ (k1_relat_1 @ sk_D_5))),
% 1.33/1.52      inference('sup-', [status(thm)], ['22', '23'])).
% 1.33/1.52  thf('25', plain, ((v1_funct_2 @ sk_D_5 @ sk_A @ sk_B_2)),
% 1.33/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.52  thf(d1_funct_2, axiom,
% 1.33/1.52    (![A:$i,B:$i,C:$i]:
% 1.33/1.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.33/1.52       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.33/1.52           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.33/1.52             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.33/1.52         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.33/1.52           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.33/1.52             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.33/1.52  thf(zf_stmt_4, axiom,
% 1.33/1.52    (![C:$i,B:$i,A:$i]:
% 1.33/1.52     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 1.33/1.52       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.33/1.52  thf('26', plain,
% 1.33/1.52      (![X74 : $i, X75 : $i, X76 : $i]:
% 1.33/1.52         (~ (v1_funct_2 @ X76 @ X74 @ X75)
% 1.33/1.52          | ((X74) = (k1_relset_1 @ X74 @ X75 @ X76))
% 1.33/1.52          | ~ (zip_tseitin_2 @ X76 @ X75 @ X74))),
% 1.33/1.52      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.33/1.52  thf('27', plain,
% 1.33/1.52      ((~ (zip_tseitin_2 @ sk_D_5 @ sk_B_2 @ sk_A)
% 1.33/1.52        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_2 @ sk_D_5)))),
% 1.33/1.52      inference('sup-', [status(thm)], ['25', '26'])).
% 1.33/1.52  thf('28', plain,
% 1.33/1.52      ((m1_subset_1 @ sk_D_5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.33/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.52  thf(redefinition_k1_relset_1, axiom,
% 1.33/1.52    (![A:$i,B:$i,C:$i]:
% 1.33/1.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.33/1.52       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.33/1.52  thf('29', plain,
% 1.33/1.52      (![X65 : $i, X66 : $i, X67 : $i]:
% 1.33/1.52         (((k1_relset_1 @ X66 @ X67 @ X65) = (k1_relat_1 @ X65))
% 1.33/1.52          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X66 @ X67))))),
% 1.33/1.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.33/1.52  thf('30', plain,
% 1.33/1.52      (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_D_5) = (k1_relat_1 @ sk_D_5))),
% 1.33/1.52      inference('sup-', [status(thm)], ['28', '29'])).
% 1.33/1.52  thf('31', plain,
% 1.33/1.52      ((~ (zip_tseitin_2 @ sk_D_5 @ sk_B_2 @ sk_A)
% 1.33/1.52        | ((sk_A) = (k1_relat_1 @ sk_D_5)))),
% 1.33/1.52      inference('demod', [status(thm)], ['27', '30'])).
% 1.33/1.52  thf('32', plain,
% 1.33/1.52      ((m1_subset_1 @ sk_D_5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.33/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.52  thf(zf_stmt_5, type, zip_tseitin_2 : $i > $i > $i > $o).
% 1.33/1.52  thf(zf_stmt_6, type, zip_tseitin_1 : $i > $i > $o).
% 1.33/1.52  thf(zf_stmt_7, axiom,
% 1.33/1.52    (![B:$i,A:$i]:
% 1.33/1.52     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.33/1.52       ( zip_tseitin_1 @ B @ A ) ))).
% 1.33/1.52  thf(zf_stmt_8, axiom,
% 1.33/1.52    (![A:$i,B:$i,C:$i]:
% 1.33/1.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.33/1.52       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 1.33/1.52         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.33/1.52           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.33/1.52             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.33/1.52  thf('33', plain,
% 1.33/1.52      (![X77 : $i, X78 : $i, X79 : $i]:
% 1.33/1.52         (~ (zip_tseitin_1 @ X77 @ X78)
% 1.33/1.52          | (zip_tseitin_2 @ X79 @ X77 @ X78)
% 1.33/1.52          | ~ (m1_subset_1 @ X79 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X78 @ X77))))),
% 1.33/1.52      inference('cnf', [status(esa)], [zf_stmt_8])).
% 1.33/1.52  thf('34', plain,
% 1.33/1.52      (((zip_tseitin_2 @ sk_D_5 @ sk_B_2 @ sk_A)
% 1.33/1.52        | ~ (zip_tseitin_1 @ sk_B_2 @ sk_A))),
% 1.33/1.52      inference('sup-', [status(thm)], ['32', '33'])).
% 1.33/1.52  thf('35', plain,
% 1.33/1.52      (![X72 : $i, X73 : $i]:
% 1.33/1.52         ((zip_tseitin_1 @ X72 @ X73) | ((X72) = (k1_xboole_0)))),
% 1.33/1.52      inference('cnf', [status(esa)], [zf_stmt_7])).
% 1.33/1.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.33/1.52  thf('36', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 1.33/1.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.33/1.52  thf(d1_xboole_0, axiom,
% 1.33/1.52    (![A:$i]:
% 1.33/1.52     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.33/1.52  thf('37', plain,
% 1.33/1.52      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.33/1.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.33/1.52  thf(t7_ordinal1, axiom,
% 1.33/1.52    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.33/1.52  thf('38', plain,
% 1.33/1.52      (![X54 : $i, X55 : $i]:
% 1.33/1.52         (~ (r2_hidden @ X54 @ X55) | ~ (r1_tarski @ X55 @ X54))),
% 1.33/1.52      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.33/1.52  thf('39', plain,
% 1.33/1.52      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 1.33/1.52      inference('sup-', [status(thm)], ['37', '38'])).
% 1.33/1.52  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.33/1.52      inference('sup-', [status(thm)], ['36', '39'])).
% 1.33/1.52  thf('41', plain,
% 1.33/1.52      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_1 @ X0 @ X1))),
% 1.33/1.52      inference('sup+', [status(thm)], ['35', '40'])).
% 1.33/1.52  thf('42', plain,
% 1.33/1.52      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C_3 @ sk_D_5) @ (k1_relat_1 @ sk_D_5))),
% 1.33/1.52      inference('sup-', [status(thm)], ['22', '23'])).
% 1.33/1.52  thf(d5_funct_1, axiom,
% 1.33/1.52    (![A:$i]:
% 1.33/1.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.33/1.52       ( ![B:$i]:
% 1.33/1.52         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 1.33/1.52           ( ![C:$i]:
% 1.33/1.52             ( ( r2_hidden @ C @ B ) <=>
% 1.33/1.52               ( ?[D:$i]:
% 1.33/1.52                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 1.33/1.52                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 1.33/1.52  thf('43', plain,
% 1.33/1.52      (![X43 : $i, X45 : $i, X47 : $i, X48 : $i]:
% 1.33/1.52         (((X45) != (k2_relat_1 @ X43))
% 1.33/1.52          | (r2_hidden @ X47 @ X45)
% 1.33/1.52          | ~ (r2_hidden @ X48 @ (k1_relat_1 @ X43))
% 1.33/1.52          | ((X47) != (k1_funct_1 @ X43 @ X48))
% 1.33/1.52          | ~ (v1_funct_1 @ X43)
% 1.33/1.52          | ~ (v1_relat_1 @ X43))),
% 1.33/1.52      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.33/1.52  thf('44', plain,
% 1.33/1.52      (![X43 : $i, X48 : $i]:
% 1.33/1.52         (~ (v1_relat_1 @ X43)
% 1.33/1.52          | ~ (v1_funct_1 @ X43)
% 1.33/1.52          | ~ (r2_hidden @ X48 @ (k1_relat_1 @ X43))
% 1.33/1.52          | (r2_hidden @ (k1_funct_1 @ X43 @ X48) @ (k2_relat_1 @ X43)))),
% 1.33/1.52      inference('simplify', [status(thm)], ['43'])).
% 1.33/1.52  thf('45', plain,
% 1.33/1.52      (((r2_hidden @ 
% 1.33/1.52         (k1_funct_1 @ sk_D_5 @ (sk_E_1 @ sk_E_2 @ sk_C_3 @ sk_D_5)) @ 
% 1.33/1.52         (k2_relat_1 @ sk_D_5))
% 1.33/1.52        | ~ (v1_funct_1 @ sk_D_5)
% 1.33/1.52        | ~ (v1_relat_1 @ sk_D_5))),
% 1.33/1.52      inference('sup-', [status(thm)], ['42', '44'])).
% 1.33/1.52  thf('46', plain,
% 1.33/1.52      (((sk_E_2) = (k1_funct_1 @ sk_D_5 @ (sk_E_1 @ sk_E_2 @ sk_C_3 @ sk_D_5)))),
% 1.33/1.52      inference('sup-', [status(thm)], ['17', '18'])).
% 1.33/1.52  thf('47', plain, ((v1_funct_1 @ sk_D_5)),
% 1.33/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.52  thf('48', plain, ((v1_relat_1 @ sk_D_5)),
% 1.33/1.52      inference('sup-', [status(thm)], ['9', '10'])).
% 1.33/1.52  thf('49', plain, ((r2_hidden @ sk_E_2 @ (k2_relat_1 @ sk_D_5))),
% 1.33/1.52      inference('demod', [status(thm)], ['45', '46', '47', '48'])).
% 1.33/1.52  thf('50', plain,
% 1.33/1.52      ((m1_subset_1 @ sk_D_5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.33/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.52  thf(cc2_relset_1, axiom,
% 1.33/1.52    (![A:$i,B:$i,C:$i]:
% 1.33/1.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.33/1.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.33/1.52  thf('51', plain,
% 1.33/1.52      (![X59 : $i, X60 : $i, X61 : $i]:
% 1.33/1.52         ((v5_relat_1 @ X59 @ X61)
% 1.33/1.52          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X61))))),
% 1.33/1.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.33/1.52  thf('52', plain, ((v5_relat_1 @ sk_D_5 @ sk_B_2)),
% 1.33/1.52      inference('sup-', [status(thm)], ['50', '51'])).
% 1.33/1.52  thf(d19_relat_1, axiom,
% 1.33/1.52    (![A:$i,B:$i]:
% 1.33/1.52     ( ( v1_relat_1 @ B ) =>
% 1.33/1.52       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.33/1.52  thf('53', plain,
% 1.33/1.52      (![X21 : $i, X22 : $i]:
% 1.33/1.52         (~ (v5_relat_1 @ X21 @ X22)
% 1.33/1.52          | (r1_tarski @ (k2_relat_1 @ X21) @ X22)
% 1.33/1.52          | ~ (v1_relat_1 @ X21))),
% 1.33/1.52      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.33/1.52  thf('54', plain,
% 1.33/1.52      ((~ (v1_relat_1 @ sk_D_5) | (r1_tarski @ (k2_relat_1 @ sk_D_5) @ sk_B_2))),
% 1.33/1.52      inference('sup-', [status(thm)], ['52', '53'])).
% 1.33/1.52  thf('55', plain, ((v1_relat_1 @ sk_D_5)),
% 1.33/1.52      inference('sup-', [status(thm)], ['9', '10'])).
% 1.33/1.52  thf('56', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_5) @ sk_B_2)),
% 1.33/1.52      inference('demod', [status(thm)], ['54', '55'])).
% 1.33/1.52  thf(d3_tarski, axiom,
% 1.33/1.52    (![A:$i,B:$i]:
% 1.33/1.52     ( ( r1_tarski @ A @ B ) <=>
% 1.33/1.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.33/1.52  thf('57', plain,
% 1.33/1.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.33/1.52         (~ (r2_hidden @ X3 @ X4)
% 1.33/1.52          | (r2_hidden @ X3 @ X5)
% 1.33/1.52          | ~ (r1_tarski @ X4 @ X5))),
% 1.33/1.52      inference('cnf', [status(esa)], [d3_tarski])).
% 1.33/1.52  thf('58', plain,
% 1.33/1.52      (![X0 : $i]:
% 1.33/1.52         ((r2_hidden @ X0 @ sk_B_2)
% 1.33/1.52          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_5)))),
% 1.33/1.52      inference('sup-', [status(thm)], ['56', '57'])).
% 1.33/1.52  thf('59', plain, ((r2_hidden @ sk_E_2 @ sk_B_2)),
% 1.33/1.52      inference('sup-', [status(thm)], ['49', '58'])).
% 1.33/1.52  thf('60', plain,
% 1.33/1.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.33/1.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.33/1.52  thf('61', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 1.33/1.52      inference('sup-', [status(thm)], ['59', '60'])).
% 1.33/1.52  thf('62', plain, (![X0 : $i]: (zip_tseitin_1 @ sk_B_2 @ X0)),
% 1.33/1.52      inference('sup-', [status(thm)], ['41', '61'])).
% 1.33/1.52  thf('63', plain, ((zip_tseitin_2 @ sk_D_5 @ sk_B_2 @ sk_A)),
% 1.33/1.52      inference('demod', [status(thm)], ['34', '62'])).
% 1.33/1.52  thf('64', plain, (((sk_A) = (k1_relat_1 @ sk_D_5))),
% 1.33/1.52      inference('demod', [status(thm)], ['31', '63'])).
% 1.33/1.52  thf('65', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C_3 @ sk_D_5) @ sk_A)),
% 1.33/1.52      inference('demod', [status(thm)], ['24', '64'])).
% 1.33/1.52  thf(t1_subset, axiom,
% 1.33/1.52    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.33/1.52  thf('66', plain,
% 1.33/1.52      (![X16 : $i, X17 : $i]:
% 1.33/1.52         ((m1_subset_1 @ X16 @ X17) | ~ (r2_hidden @ X16 @ X17))),
% 1.33/1.52      inference('cnf', [status(esa)], [t1_subset])).
% 1.33/1.52  thf('67', plain,
% 1.33/1.52      ((m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C_3 @ sk_D_5) @ sk_A)),
% 1.33/1.52      inference('sup-', [status(thm)], ['65', '66'])).
% 1.33/1.52  thf('68', plain, ($false), inference('demod', [status(thm)], ['21', '67'])).
% 1.33/1.52  
% 1.33/1.52  % SZS output end Refutation
% 1.33/1.52  
% 1.33/1.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
