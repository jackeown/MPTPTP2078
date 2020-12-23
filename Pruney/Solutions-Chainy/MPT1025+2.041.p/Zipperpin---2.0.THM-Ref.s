%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2Xf8WBJNIM

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:48 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 213 expanded)
%              Number of leaves         :   46 (  84 expanded)
%              Depth                    :   14
%              Number of atoms          :  763 (2424 expanded)
%              Number of equality atoms :   33 (  82 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

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
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k7_relset_1 @ X41 @ X42 @ X40 @ X43 )
        = ( k9_relat_1 @ X40 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('5',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ ( k9_relat_1 @ X25 @ X23 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X25 @ X23 @ X24 ) @ X24 ) @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['6','11'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X29 @ X31 ) @ X30 )
      | ( X31
        = ( k1_funct_1 @ X30 @ X29 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('16',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('19',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ ( k9_relat_1 @ X25 @ X23 ) )
      | ( r2_hidden @ ( sk_D @ X25 @ X23 @ X24 ) @ X23 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('22',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X52: $i] :
      ( ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X52 ) )
      | ~ ( r2_hidden @ X52 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X52 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_A )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('26',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ ( k9_relat_1 @ X25 @ X23 ) )
      | ( r2_hidden @ ( sk_D @ X25 @ X23 @ X24 ) @ ( k1_relat_1 @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('29',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('30',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('31',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

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

thf('32',plain,(
    ! [X44: $i,X45: $i] :
      ( ( zip_tseitin_0 @ X44 @ X45 )
      | ( X44 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('33',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('36',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( zip_tseitin_0 @ X49 @ X50 )
      | ( zip_tseitin_1 @ X51 @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('37',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_2 @ X48 @ X46 @ X47 )
      | ( X46
        = ( k1_relset_1 @ X46 @ X47 @ X48 ) )
      | ~ ( zip_tseitin_1 @ X48 @ X47 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('43',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k1_relset_1 @ X38 @ X39 @ X37 )
        = ( k1_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('44',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['38','45'])).

thf('47',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['6','11'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('48',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X26 @ X27 ) @ X28 )
      | ( r2_hidden @ X27 @ ( k2_relat_1 @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ sk_E @ ( k2_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('51',plain,(
    r2_hidden @ sk_E @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('53',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v5_relat_1 @ X34 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('54',plain,(
    v5_relat_1 @ sk_D_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['52','53'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('55',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v5_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k2_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('56',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('58',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['56','57'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('59',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    r2_hidden @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['51','60'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('62',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X32 @ X33 )
      | ~ ( r1_tarski @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('63',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['46','63'])).

thf('65',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_A ),
    inference(demod,[status(thm)],['31','64'])).

thf('66',plain,(
    sk_E
 != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['24','65'])).

thf('67',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['17','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2Xf8WBJNIM
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:16:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.68/0.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.68/0.88  % Solved by: fo/fo7.sh
% 0.68/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.88  % done 544 iterations in 0.433s
% 0.68/0.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.68/0.88  % SZS output start Refutation
% 0.68/0.88  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.68/0.88  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.68/0.88  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.68/0.88  thf(sk_E_type, type, sk_E: $i).
% 0.68/0.88  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.68/0.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.88  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.68/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.88  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.68/0.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.68/0.88  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.68/0.88  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.68/0.88  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.68/0.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.88  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.68/0.88  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.68/0.88  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.68/0.88  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.68/0.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.68/0.88  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.68/0.88  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.68/0.88  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.68/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.88  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.68/0.88  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.68/0.88  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.68/0.88  thf(t116_funct_2, conjecture,
% 0.68/0.88    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.88     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.68/0.88         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.68/0.88       ( ![E:$i]:
% 0.68/0.88         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.68/0.88              ( ![F:$i]:
% 0.68/0.88                ( ( m1_subset_1 @ F @ A ) =>
% 0.68/0.88                  ( ~( ( r2_hidden @ F @ C ) & 
% 0.68/0.88                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 0.68/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.88    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.88        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.68/0.88            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.68/0.88          ( ![E:$i]:
% 0.68/0.88            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.68/0.88                 ( ![F:$i]:
% 0.68/0.88                   ( ( m1_subset_1 @ F @ A ) =>
% 0.68/0.88                     ( ~( ( r2_hidden @ F @ C ) & 
% 0.68/0.88                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.68/0.88    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 0.68/0.88  thf('0', plain,
% 0.68/0.88      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('1', plain,
% 0.68/0.88      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(redefinition_k7_relset_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.88       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.68/0.88  thf('2', plain,
% 0.68/0.88      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.68/0.88          | ((k7_relset_1 @ X41 @ X42 @ X40 @ X43) = (k9_relat_1 @ X40 @ X43)))),
% 0.68/0.88      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.68/0.88  thf('3', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.68/0.88           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['1', '2'])).
% 0.68/0.88  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 0.68/0.88      inference('demod', [status(thm)], ['0', '3'])).
% 0.68/0.88  thf(t143_relat_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( v1_relat_1 @ C ) =>
% 0.68/0.88       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.68/0.88         ( ?[D:$i]:
% 0.68/0.88           ( ( r2_hidden @ D @ B ) & 
% 0.68/0.88             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.68/0.88             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.68/0.88  thf('5', plain,
% 0.68/0.88      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.68/0.88         (~ (r2_hidden @ X24 @ (k9_relat_1 @ X25 @ X23))
% 0.68/0.88          | (r2_hidden @ (k4_tarski @ (sk_D @ X25 @ X23 @ X24) @ X24) @ X25)
% 0.68/0.88          | ~ (v1_relat_1 @ X25))),
% 0.68/0.88      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.68/0.88  thf('6', plain,
% 0.68/0.88      ((~ (v1_relat_1 @ sk_D_1)
% 0.68/0.88        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_E) @ 
% 0.68/0.88           sk_D_1))),
% 0.68/0.88      inference('sup-', [status(thm)], ['4', '5'])).
% 0.68/0.88  thf('7', plain,
% 0.68/0.88      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(cc2_relat_1, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( v1_relat_1 @ A ) =>
% 0.68/0.88       ( ![B:$i]:
% 0.68/0.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.68/0.88  thf('8', plain,
% 0.68/0.88      (![X16 : $i, X17 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.68/0.88          | (v1_relat_1 @ X16)
% 0.68/0.88          | ~ (v1_relat_1 @ X17))),
% 0.68/0.88      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.68/0.88  thf('9', plain,
% 0.68/0.88      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D_1))),
% 0.68/0.88      inference('sup-', [status(thm)], ['7', '8'])).
% 0.68/0.88  thf(fc6_relat_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.68/0.88  thf('10', plain,
% 0.68/0.88      (![X20 : $i, X21 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21))),
% 0.68/0.88      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.68/0.88  thf('11', plain, ((v1_relat_1 @ sk_D_1)),
% 0.68/0.88      inference('demod', [status(thm)], ['9', '10'])).
% 0.68/0.88  thf('12', plain,
% 0.68/0.88      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_E) @ 
% 0.68/0.88        sk_D_1)),
% 0.68/0.88      inference('demod', [status(thm)], ['6', '11'])).
% 0.68/0.88  thf(t8_funct_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.68/0.88       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.68/0.88         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.68/0.88           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.68/0.88  thf('13', plain,
% 0.68/0.88      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.68/0.88         (~ (r2_hidden @ (k4_tarski @ X29 @ X31) @ X30)
% 0.68/0.88          | ((X31) = (k1_funct_1 @ X30 @ X29))
% 0.68/0.88          | ~ (v1_funct_1 @ X30)
% 0.68/0.88          | ~ (v1_relat_1 @ X30))),
% 0.68/0.88      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.68/0.88  thf('14', plain,
% 0.68/0.88      ((~ (v1_relat_1 @ sk_D_1)
% 0.68/0.88        | ~ (v1_funct_1 @ sk_D_1)
% 0.68/0.88        | ((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['12', '13'])).
% 0.68/0.88  thf('15', plain, ((v1_relat_1 @ sk_D_1)),
% 0.68/0.88      inference('demod', [status(thm)], ['9', '10'])).
% 0.68/0.88  thf('16', plain, ((v1_funct_1 @ sk_D_1)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('17', plain,
% 0.68/0.88      (((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E)))),
% 0.68/0.88      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.68/0.88  thf('18', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 0.68/0.88      inference('demod', [status(thm)], ['0', '3'])).
% 0.68/0.88  thf('19', plain,
% 0.68/0.88      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.68/0.88         (~ (r2_hidden @ X24 @ (k9_relat_1 @ X25 @ X23))
% 0.68/0.88          | (r2_hidden @ (sk_D @ X25 @ X23 @ X24) @ X23)
% 0.68/0.88          | ~ (v1_relat_1 @ X25))),
% 0.68/0.88      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.68/0.88  thf('20', plain,
% 0.68/0.88      ((~ (v1_relat_1 @ sk_D_1)
% 0.68/0.88        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_C_1))),
% 0.68/0.88      inference('sup-', [status(thm)], ['18', '19'])).
% 0.68/0.88  thf('21', plain, ((v1_relat_1 @ sk_D_1)),
% 0.68/0.88      inference('demod', [status(thm)], ['9', '10'])).
% 0.68/0.88  thf('22', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_C_1)),
% 0.68/0.88      inference('demod', [status(thm)], ['20', '21'])).
% 0.68/0.88  thf('23', plain,
% 0.68/0.88      (![X52 : $i]:
% 0.68/0.88         (((sk_E) != (k1_funct_1 @ sk_D_1 @ X52))
% 0.68/0.88          | ~ (r2_hidden @ X52 @ sk_C_1)
% 0.68/0.88          | ~ (m1_subset_1 @ X52 @ sk_A))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('24', plain,
% 0.68/0.88      ((~ (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_A)
% 0.68/0.88        | ((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['22', '23'])).
% 0.68/0.88  thf('25', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 0.68/0.88      inference('demod', [status(thm)], ['0', '3'])).
% 0.68/0.88  thf('26', plain,
% 0.68/0.88      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.68/0.88         (~ (r2_hidden @ X24 @ (k9_relat_1 @ X25 @ X23))
% 0.68/0.88          | (r2_hidden @ (sk_D @ X25 @ X23 @ X24) @ (k1_relat_1 @ X25))
% 0.68/0.88          | ~ (v1_relat_1 @ X25))),
% 0.68/0.88      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.68/0.88  thf('27', plain,
% 0.68/0.88      ((~ (v1_relat_1 @ sk_D_1)
% 0.68/0.88        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ (k1_relat_1 @ sk_D_1)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['25', '26'])).
% 0.68/0.88  thf('28', plain, ((v1_relat_1 @ sk_D_1)),
% 0.68/0.88      inference('demod', [status(thm)], ['9', '10'])).
% 0.68/0.88  thf('29', plain,
% 0.68/0.88      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.68/0.88      inference('demod', [status(thm)], ['27', '28'])).
% 0.68/0.88  thf(t1_subset, axiom,
% 0.68/0.88    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.68/0.88  thf('30', plain,
% 0.68/0.88      (![X11 : $i, X12 : $i]:
% 0.68/0.88         ((m1_subset_1 @ X11 @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 0.68/0.88      inference('cnf', [status(esa)], [t1_subset])).
% 0.68/0.88  thf('31', plain,
% 0.68/0.88      ((m1_subset_1 @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.68/0.88      inference('sup-', [status(thm)], ['29', '30'])).
% 0.68/0.88  thf(d1_funct_2, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.88       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.68/0.88           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.68/0.88             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.68/0.88         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.68/0.88           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.68/0.88             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.68/0.88  thf(zf_stmt_1, axiom,
% 0.68/0.88    (![B:$i,A:$i]:
% 0.68/0.88     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.68/0.88       ( zip_tseitin_0 @ B @ A ) ))).
% 0.68/0.88  thf('32', plain,
% 0.68/0.88      (![X44 : $i, X45 : $i]:
% 0.68/0.88         ((zip_tseitin_0 @ X44 @ X45) | ((X44) = (k1_xboole_0)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.68/0.88  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.68/0.88  thf('33', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.68/0.88      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.68/0.88  thf('34', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.68/0.88      inference('sup+', [status(thm)], ['32', '33'])).
% 0.68/0.88  thf('35', plain,
% 0.68/0.88      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.68/0.88  thf(zf_stmt_3, axiom,
% 0.68/0.88    (![C:$i,B:$i,A:$i]:
% 0.68/0.88     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.68/0.88       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.68/0.88  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.68/0.88  thf(zf_stmt_5, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.88       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.68/0.88         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.68/0.88           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.68/0.88             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.68/0.88  thf('36', plain,
% 0.68/0.88      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.68/0.88         (~ (zip_tseitin_0 @ X49 @ X50)
% 0.68/0.88          | (zip_tseitin_1 @ X51 @ X49 @ X50)
% 0.68/0.88          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49))))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.68/0.88  thf('37', plain,
% 0.68/0.88      (((zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.68/0.88        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['35', '36'])).
% 0.68/0.88  thf('38', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((r1_tarski @ sk_B_1 @ X0) | (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['34', '37'])).
% 0.68/0.88  thf('39', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B_1)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('40', plain,
% 0.68/0.88      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.68/0.88         (~ (v1_funct_2 @ X48 @ X46 @ X47)
% 0.68/0.88          | ((X46) = (k1_relset_1 @ X46 @ X47 @ X48))
% 0.68/0.88          | ~ (zip_tseitin_1 @ X48 @ X47 @ X46))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.68/0.88  thf('41', plain,
% 0.68/0.88      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.68/0.88        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['39', '40'])).
% 0.68/0.88  thf('42', plain,
% 0.68/0.88      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(redefinition_k1_relset_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.88       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.68/0.88  thf('43', plain,
% 0.68/0.88      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.68/0.88         (((k1_relset_1 @ X38 @ X39 @ X37) = (k1_relat_1 @ X37))
% 0.68/0.88          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.68/0.88      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.68/0.88  thf('44', plain,
% 0.68/0.88      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.68/0.88      inference('sup-', [status(thm)], ['42', '43'])).
% 0.68/0.88  thf('45', plain,
% 0.68/0.88      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.68/0.88        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.68/0.88      inference('demod', [status(thm)], ['41', '44'])).
% 0.68/0.88  thf('46', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((r1_tarski @ sk_B_1 @ X0) | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['38', '45'])).
% 0.68/0.88  thf('47', plain,
% 0.68/0.88      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_E) @ 
% 0.68/0.88        sk_D_1)),
% 0.68/0.88      inference('demod', [status(thm)], ['6', '11'])).
% 0.68/0.88  thf(t20_relat_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( v1_relat_1 @ C ) =>
% 0.68/0.88       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.68/0.88         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.68/0.88           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.68/0.88  thf('48', plain,
% 0.68/0.88      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.68/0.88         (~ (r2_hidden @ (k4_tarski @ X26 @ X27) @ X28)
% 0.68/0.88          | (r2_hidden @ X27 @ (k2_relat_1 @ X28))
% 0.68/0.88          | ~ (v1_relat_1 @ X28))),
% 0.68/0.88      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.68/0.88  thf('49', plain,
% 0.68/0.88      ((~ (v1_relat_1 @ sk_D_1) | (r2_hidden @ sk_E @ (k2_relat_1 @ sk_D_1)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['47', '48'])).
% 0.68/0.88  thf('50', plain, ((v1_relat_1 @ sk_D_1)),
% 0.68/0.88      inference('demod', [status(thm)], ['9', '10'])).
% 0.68/0.88  thf('51', plain, ((r2_hidden @ sk_E @ (k2_relat_1 @ sk_D_1))),
% 0.68/0.88      inference('demod', [status(thm)], ['49', '50'])).
% 0.68/0.88  thf('52', plain,
% 0.68/0.88      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(cc2_relset_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.88       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.68/0.88  thf('53', plain,
% 0.68/0.88      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.68/0.88         ((v5_relat_1 @ X34 @ X36)
% 0.68/0.88          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.68/0.88      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.68/0.88  thf('54', plain, ((v5_relat_1 @ sk_D_1 @ sk_B_1)),
% 0.68/0.88      inference('sup-', [status(thm)], ['52', '53'])).
% 0.68/0.88  thf(d19_relat_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( v1_relat_1 @ B ) =>
% 0.68/0.88       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.68/0.88  thf('55', plain,
% 0.68/0.88      (![X18 : $i, X19 : $i]:
% 0.68/0.88         (~ (v5_relat_1 @ X18 @ X19)
% 0.68/0.88          | (r1_tarski @ (k2_relat_1 @ X18) @ X19)
% 0.68/0.88          | ~ (v1_relat_1 @ X18))),
% 0.68/0.88      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.68/0.88  thf('56', plain,
% 0.68/0.88      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_B_1))),
% 0.68/0.88      inference('sup-', [status(thm)], ['54', '55'])).
% 0.68/0.88  thf('57', plain, ((v1_relat_1 @ sk_D_1)),
% 0.68/0.88      inference('demod', [status(thm)], ['9', '10'])).
% 0.68/0.88  thf('58', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_B_1)),
% 0.68/0.88      inference('demod', [status(thm)], ['56', '57'])).
% 0.68/0.88  thf(d3_tarski, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( r1_tarski @ A @ B ) <=>
% 0.68/0.88       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.68/0.88  thf('59', plain,
% 0.68/0.88      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.68/0.88         (~ (r2_hidden @ X3 @ X4)
% 0.68/0.88          | (r2_hidden @ X3 @ X5)
% 0.68/0.88          | ~ (r1_tarski @ X4 @ X5))),
% 0.68/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.88  thf('60', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((r2_hidden @ X0 @ sk_B_1)
% 0.68/0.88          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['58', '59'])).
% 0.68/0.88  thf('61', plain, ((r2_hidden @ sk_E @ sk_B_1)),
% 0.68/0.88      inference('sup-', [status(thm)], ['51', '60'])).
% 0.68/0.88  thf(t7_ordinal1, axiom,
% 0.68/0.88    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.68/0.88  thf('62', plain,
% 0.68/0.88      (![X32 : $i, X33 : $i]:
% 0.68/0.88         (~ (r2_hidden @ X32 @ X33) | ~ (r1_tarski @ X33 @ X32))),
% 0.68/0.88      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.68/0.88  thf('63', plain, (~ (r1_tarski @ sk_B_1 @ sk_E)),
% 0.68/0.88      inference('sup-', [status(thm)], ['61', '62'])).
% 0.68/0.88  thf('64', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.68/0.88      inference('sup-', [status(thm)], ['46', '63'])).
% 0.68/0.88  thf('65', plain, ((m1_subset_1 @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_A)),
% 0.68/0.88      inference('demod', [status(thm)], ['31', '64'])).
% 0.68/0.88  thf('66', plain,
% 0.68/0.88      (((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E)))),
% 0.68/0.88      inference('demod', [status(thm)], ['24', '65'])).
% 0.68/0.88  thf('67', plain, ($false),
% 0.68/0.88      inference('simplify_reflect-', [status(thm)], ['17', '66'])).
% 0.68/0.88  
% 0.68/0.88  % SZS output end Refutation
% 0.68/0.88  
% 0.71/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
