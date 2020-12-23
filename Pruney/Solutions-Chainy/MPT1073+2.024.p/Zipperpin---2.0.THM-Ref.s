%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JDWN64OkEY

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:17 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  138 (1307 expanded)
%              Number of leaves         :   40 ( 396 expanded)
%              Depth                    :   22
%              Number of atoms          : 1006 (17336 expanded)
%              Number of equality atoms :   76 ( 808 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t190_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ B @ C )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
     => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
          & ! [E: $i] :
              ( ( m1_subset_1 @ E @ B )
             => ( A
               != ( k1_funct_1 @ D @ E ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ B @ C )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
       => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
            & ! [E: $i] :
                ( ( m1_subset_1 @ E @ B )
               => ( A
                 != ( k1_funct_1 @ D @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t190_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k2_relset_1 @ X37 @ X38 @ X36 )
        = ( k2_relat_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X23: $i] :
      ( ( ( k9_relat_1 @ X23 @ ( k1_relat_1 @ X23 ) )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k9_relat_1 @ X22 @ X20 ) )
      | ( r2_hidden @ ( sk_D @ X22 @ X20 @ X21 ) @ ( k1_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_relat_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C_1 ),
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

thf('17',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ( X41
        = ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ~ ( zip_tseitin_1 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('20',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k1_relset_1 @ X34 @ X35 @ X33 )
        = ( k1_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('21',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('23',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('24',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
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

thf('25',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X44 @ X45 )
      | ( zip_tseitin_1 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('26',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ sk_B_1 )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('29',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('31',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('32',plain,(
    ! [X23: $i] :
      ( ( ( k9_relat_1 @ X23 @ ( k1_relat_1 @ X23 ) )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('33',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k9_relat_1 @ X22 @ X20 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X22 @ X20 @ X21 ) @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ sk_A ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['31','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('38',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ sk_A ) @ sk_D_1 ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ X22 )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X22 ) )
      | ( r2_hidden @ X21 @ ( k9_relat_1 @ X22 @ X20 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ sk_A @ ( k9_relat_1 @ sk_D_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('42',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k9_relat_1 @ sk_D_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    r2_hidden @ sk_A @ ( k9_relat_1 @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['30','43'])).

thf('45',plain,
    ( ( r2_hidden @ sk_A @ ( k9_relat_1 @ sk_D_1 @ sk_B_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','44'])).

thf('46',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k9_relat_1 @ X22 @ X20 ) )
      | ( r2_hidden @ ( sk_D @ X22 @ X20 @ X21 ) @ X20 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('47',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('49',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('50',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('51',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X47: $i] :
      ( ( sk_A
       != ( k1_funct_1 @ sk_D_1 @ X47 ) )
      | ~ ( m1_subset_1 @ X47 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_A
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('55',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ sk_A ) @ sk_D_1 ),
    inference(demod,[status(thm)],['36','37'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('56',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X27 @ X29 ) @ X28 )
      | ( X29
        = ( k1_funct_1 @ X28 @ X27 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('57',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_A
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('59',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( sk_A
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_A ) ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','60'])).

thf('62',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['53','61'])).

thf('63',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['22','62'])).

thf('64',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['53','61'])).

thf('66',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['53','61'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('69',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('70',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68','70'])).

thf('72',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( X44 != k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X46 @ X45 @ X44 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('73',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X45 @ k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('75',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_2 @ X46 @ X45 @ k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_D_1 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ sk_D_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','75'])).

thf('77',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','76'])).

thf('78',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ sk_A ) @ sk_D_1 ),
    inference(demod,[status(thm)],['36','37'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('80',plain,(
    ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('82',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('83',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68','70'])).

thf('85',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('86',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X44 @ X45 )
      | ( zip_tseitin_1 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X40 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('90',plain,(
    ! [X39: $i] :
      ( zip_tseitin_0 @ X39 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['88','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ sk_D_1 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','91'])).

thf('93',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['81','82'])).

thf('94',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['63','83','92','93'])).

thf('95',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['15','94','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JDWN64OkEY
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:11:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.58/0.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.79  % Solved by: fo/fo7.sh
% 0.58/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.79  % done 407 iterations in 0.336s
% 0.58/0.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.79  % SZS output start Refutation
% 0.58/0.79  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.58/0.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.79  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.58/0.79  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.58/0.79  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.58/0.79  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.58/0.79  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.58/0.79  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.58/0.79  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.58/0.79  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.58/0.79  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.58/0.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.79  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.58/0.79  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.79  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.58/0.79  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.58/0.79  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.58/0.79  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.58/0.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.79  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.58/0.79  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.58/0.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.79  thf(t190_funct_2, conjecture,
% 0.58/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.79     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.58/0.79         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.58/0.79       ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.58/0.79            ( ![E:$i]:
% 0.58/0.79              ( ( m1_subset_1 @ E @ B ) => ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ))).
% 0.58/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.79    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.79        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.58/0.79            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.58/0.79          ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.58/0.79               ( ![E:$i]:
% 0.58/0.79                 ( ( m1_subset_1 @ E @ B ) =>
% 0.58/0.79                   ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )),
% 0.58/0.79    inference('cnf.neg', [status(esa)], [t190_funct_2])).
% 0.58/0.79  thf('0', plain,
% 0.58/0.79      ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_1))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('1', plain,
% 0.58/0.79      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf(redefinition_k2_relset_1, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.79       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.58/0.79  thf('2', plain,
% 0.58/0.79      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.58/0.79         (((k2_relset_1 @ X37 @ X38 @ X36) = (k2_relat_1 @ X36))
% 0.58/0.79          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.58/0.79      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.58/0.79  thf('3', plain,
% 0.58/0.79      (((k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.58/0.79      inference('sup-', [status(thm)], ['1', '2'])).
% 0.58/0.79  thf('4', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_1))),
% 0.58/0.79      inference('demod', [status(thm)], ['0', '3'])).
% 0.58/0.79  thf(t146_relat_1, axiom,
% 0.58/0.79    (![A:$i]:
% 0.58/0.79     ( ( v1_relat_1 @ A ) =>
% 0.58/0.79       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.58/0.79  thf('5', plain,
% 0.58/0.79      (![X23 : $i]:
% 0.58/0.79         (((k9_relat_1 @ X23 @ (k1_relat_1 @ X23)) = (k2_relat_1 @ X23))
% 0.58/0.79          | ~ (v1_relat_1 @ X23))),
% 0.58/0.79      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.58/0.79  thf(t143_relat_1, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ( v1_relat_1 @ C ) =>
% 0.58/0.79       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.58/0.79         ( ?[D:$i]:
% 0.58/0.79           ( ( r2_hidden @ D @ B ) & 
% 0.58/0.79             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.58/0.79             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.58/0.79  thf('6', plain,
% 0.58/0.79      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.58/0.79         (~ (r2_hidden @ X21 @ (k9_relat_1 @ X22 @ X20))
% 0.58/0.79          | (r2_hidden @ (sk_D @ X22 @ X20 @ X21) @ (k1_relat_1 @ X22))
% 0.58/0.79          | ~ (v1_relat_1 @ X22))),
% 0.58/0.79      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.58/0.79  thf('7', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.58/0.79          | ~ (v1_relat_1 @ X0)
% 0.58/0.79          | ~ (v1_relat_1 @ X0)
% 0.58/0.79          | (r2_hidden @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ 
% 0.58/0.79             (k1_relat_1 @ X0)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.58/0.79  thf('8', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         ((r2_hidden @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ (k1_relat_1 @ X0))
% 0.58/0.79          | ~ (v1_relat_1 @ X0)
% 0.58/0.79          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.58/0.79      inference('simplify', [status(thm)], ['7'])).
% 0.58/0.79  thf('9', plain,
% 0.58/0.79      ((~ (v1_relat_1 @ sk_D_1)
% 0.58/0.79        | (r2_hidden @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ 
% 0.58/0.79           (k1_relat_1 @ sk_D_1)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['4', '8'])).
% 0.58/0.79  thf('10', plain,
% 0.58/0.79      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf(cc1_relset_1, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.79       ( v1_relat_1 @ C ) ))).
% 0.58/0.79  thf('11', plain,
% 0.58/0.79      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.58/0.79         ((v1_relat_1 @ X30)
% 0.58/0.79          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.58/0.79      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.58/0.79  thf('12', plain, ((v1_relat_1 @ sk_D_1)),
% 0.58/0.79      inference('sup-', [status(thm)], ['10', '11'])).
% 0.58/0.79  thf('13', plain,
% 0.58/0.79      ((r2_hidden @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ 
% 0.58/0.79        (k1_relat_1 @ sk_D_1))),
% 0.58/0.79      inference('demod', [status(thm)], ['9', '12'])).
% 0.58/0.79  thf(d1_xboole_0, axiom,
% 0.58/0.79    (![A:$i]:
% 0.58/0.79     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.58/0.79  thf('14', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.58/0.79      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.58/0.79  thf('15', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_D_1))),
% 0.58/0.79      inference('sup-', [status(thm)], ['13', '14'])).
% 0.58/0.79  thf('16', plain, ((v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C_1)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf(d1_funct_2, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.79       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.58/0.79           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.58/0.79             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.58/0.79         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.58/0.79           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.58/0.79             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.58/0.79  thf(zf_stmt_1, axiom,
% 0.58/0.79    (![C:$i,B:$i,A:$i]:
% 0.58/0.79     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.58/0.79       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.58/0.79  thf('17', plain,
% 0.58/0.79      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.58/0.79         (~ (v1_funct_2 @ X43 @ X41 @ X42)
% 0.58/0.79          | ((X41) = (k1_relset_1 @ X41 @ X42 @ X43))
% 0.58/0.79          | ~ (zip_tseitin_1 @ X43 @ X42 @ X41))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.58/0.79  thf('18', plain,
% 0.58/0.79      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ sk_B_1)
% 0.58/0.79        | ((sk_B_1) = (k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_1)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['16', '17'])).
% 0.58/0.79  thf('19', plain,
% 0.58/0.79      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf(redefinition_k1_relset_1, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.79       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.58/0.79  thf('20', plain,
% 0.58/0.79      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.58/0.79         (((k1_relset_1 @ X34 @ X35 @ X33) = (k1_relat_1 @ X33))
% 0.58/0.79          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.58/0.79      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.58/0.79  thf('21', plain,
% 0.58/0.79      (((k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.58/0.79      inference('sup-', [status(thm)], ['19', '20'])).
% 0.58/0.79  thf('22', plain,
% 0.58/0.79      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ sk_B_1)
% 0.58/0.79        | ((sk_B_1) = (k1_relat_1 @ sk_D_1)))),
% 0.58/0.79      inference('demod', [status(thm)], ['18', '21'])).
% 0.58/0.79  thf(zf_stmt_2, axiom,
% 0.58/0.79    (![B:$i,A:$i]:
% 0.58/0.79     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.58/0.79       ( zip_tseitin_0 @ B @ A ) ))).
% 0.58/0.79  thf('23', plain,
% 0.58/0.79      (![X39 : $i, X40 : $i]:
% 0.58/0.79         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.58/0.79  thf('24', plain,
% 0.58/0.79      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.58/0.79  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.58/0.79  thf(zf_stmt_5, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.79       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.58/0.79         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.58/0.79           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.58/0.79             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.58/0.79  thf('25', plain,
% 0.58/0.79      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.58/0.79         (~ (zip_tseitin_0 @ X44 @ X45)
% 0.58/0.79          | (zip_tseitin_1 @ X46 @ X44 @ X45)
% 0.58/0.79          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.58/0.79  thf('26', plain,
% 0.58/0.79      (((zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ sk_B_1)
% 0.58/0.79        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_B_1))),
% 0.58/0.79      inference('sup-', [status(thm)], ['24', '25'])).
% 0.58/0.79  thf('27', plain,
% 0.58/0.79      ((((sk_C_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ sk_B_1))),
% 0.58/0.79      inference('sup-', [status(thm)], ['23', '26'])).
% 0.58/0.79  thf('28', plain,
% 0.58/0.79      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ sk_B_1)
% 0.58/0.79        | ((sk_B_1) = (k1_relat_1 @ sk_D_1)))),
% 0.58/0.79      inference('demod', [status(thm)], ['18', '21'])).
% 0.58/0.79  thf('29', plain,
% 0.58/0.79      ((((sk_C_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_relat_1 @ sk_D_1)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['27', '28'])).
% 0.58/0.79  thf('30', plain,
% 0.58/0.79      ((r2_hidden @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ 
% 0.58/0.79        (k1_relat_1 @ sk_D_1))),
% 0.58/0.79      inference('demod', [status(thm)], ['9', '12'])).
% 0.58/0.79  thf('31', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_1))),
% 0.58/0.79      inference('demod', [status(thm)], ['0', '3'])).
% 0.58/0.79  thf('32', plain,
% 0.58/0.79      (![X23 : $i]:
% 0.58/0.79         (((k9_relat_1 @ X23 @ (k1_relat_1 @ X23)) = (k2_relat_1 @ X23))
% 0.58/0.79          | ~ (v1_relat_1 @ X23))),
% 0.58/0.79      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.58/0.79  thf('33', plain,
% 0.58/0.79      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.58/0.79         (~ (r2_hidden @ X21 @ (k9_relat_1 @ X22 @ X20))
% 0.58/0.79          | (r2_hidden @ (k4_tarski @ (sk_D @ X22 @ X20 @ X21) @ X21) @ X22)
% 0.58/0.79          | ~ (v1_relat_1 @ X22))),
% 0.58/0.79      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.58/0.79  thf('34', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.58/0.79          | ~ (v1_relat_1 @ X0)
% 0.58/0.79          | ~ (v1_relat_1 @ X0)
% 0.58/0.79          | (r2_hidden @ 
% 0.58/0.79             (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0))),
% 0.58/0.79      inference('sup-', [status(thm)], ['32', '33'])).
% 0.58/0.79  thf('35', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         ((r2_hidden @ 
% 0.58/0.79           (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0)
% 0.58/0.79          | ~ (v1_relat_1 @ X0)
% 0.58/0.79          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.58/0.79      inference('simplify', [status(thm)], ['34'])).
% 0.58/0.79  thf('36', plain,
% 0.58/0.79      ((~ (v1_relat_1 @ sk_D_1)
% 0.58/0.79        | (r2_hidden @ 
% 0.58/0.79           (k4_tarski @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ sk_A) @ 
% 0.58/0.79           sk_D_1))),
% 0.58/0.79      inference('sup-', [status(thm)], ['31', '35'])).
% 0.58/0.79  thf('37', plain, ((v1_relat_1 @ sk_D_1)),
% 0.58/0.79      inference('sup-', [status(thm)], ['10', '11'])).
% 0.58/0.79  thf('38', plain,
% 0.58/0.79      ((r2_hidden @ 
% 0.58/0.79        (k4_tarski @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ sk_A) @ 
% 0.58/0.79        sk_D_1)),
% 0.58/0.79      inference('demod', [status(thm)], ['36', '37'])).
% 0.58/0.79  thf('39', plain,
% 0.58/0.79      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.58/0.79         (~ (r2_hidden @ X19 @ X20)
% 0.58/0.79          | ~ (r2_hidden @ (k4_tarski @ X19 @ X21) @ X22)
% 0.58/0.79          | ~ (r2_hidden @ X19 @ (k1_relat_1 @ X22))
% 0.58/0.79          | (r2_hidden @ X21 @ (k9_relat_1 @ X22 @ X20))
% 0.58/0.79          | ~ (v1_relat_1 @ X22))),
% 0.58/0.79      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.58/0.79  thf('40', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         (~ (v1_relat_1 @ sk_D_1)
% 0.58/0.79          | (r2_hidden @ sk_A @ (k9_relat_1 @ sk_D_1 @ X0))
% 0.58/0.79          | ~ (r2_hidden @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ 
% 0.58/0.79               (k1_relat_1 @ sk_D_1))
% 0.58/0.79          | ~ (r2_hidden @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ X0))),
% 0.58/0.79      inference('sup-', [status(thm)], ['38', '39'])).
% 0.58/0.79  thf('41', plain, ((v1_relat_1 @ sk_D_1)),
% 0.58/0.79      inference('sup-', [status(thm)], ['10', '11'])).
% 0.58/0.79  thf('42', plain,
% 0.58/0.79      ((r2_hidden @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ 
% 0.58/0.79        (k1_relat_1 @ sk_D_1))),
% 0.58/0.79      inference('demod', [status(thm)], ['9', '12'])).
% 0.58/0.79  thf('43', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         ((r2_hidden @ sk_A @ (k9_relat_1 @ sk_D_1 @ X0))
% 0.58/0.79          | ~ (r2_hidden @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ X0))),
% 0.58/0.79      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.58/0.79  thf('44', plain,
% 0.58/0.79      ((r2_hidden @ sk_A @ (k9_relat_1 @ sk_D_1 @ (k1_relat_1 @ sk_D_1)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['30', '43'])).
% 0.58/0.79  thf('45', plain,
% 0.58/0.79      (((r2_hidden @ sk_A @ (k9_relat_1 @ sk_D_1 @ sk_B_1))
% 0.58/0.79        | ((sk_C_1) = (k1_xboole_0)))),
% 0.58/0.79      inference('sup+', [status(thm)], ['29', '44'])).
% 0.58/0.79  thf('46', plain,
% 0.58/0.79      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.58/0.79         (~ (r2_hidden @ X21 @ (k9_relat_1 @ X22 @ X20))
% 0.58/0.79          | (r2_hidden @ (sk_D @ X22 @ X20 @ X21) @ X20)
% 0.58/0.79          | ~ (v1_relat_1 @ X22))),
% 0.58/0.79      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.58/0.79  thf('47', plain,
% 0.58/0.79      ((((sk_C_1) = (k1_xboole_0))
% 0.58/0.79        | ~ (v1_relat_1 @ sk_D_1)
% 0.58/0.79        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_A) @ sk_B_1))),
% 0.58/0.79      inference('sup-', [status(thm)], ['45', '46'])).
% 0.58/0.79  thf('48', plain, ((v1_relat_1 @ sk_D_1)),
% 0.58/0.79      inference('sup-', [status(thm)], ['10', '11'])).
% 0.58/0.79  thf('49', plain,
% 0.58/0.79      ((((sk_C_1) = (k1_xboole_0))
% 0.58/0.79        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_A) @ sk_B_1))),
% 0.58/0.79      inference('demod', [status(thm)], ['47', '48'])).
% 0.58/0.79  thf(t1_subset, axiom,
% 0.58/0.79    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.58/0.79  thf('50', plain,
% 0.58/0.79      (![X10 : $i, X11 : $i]:
% 0.58/0.79         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.58/0.79      inference('cnf', [status(esa)], [t1_subset])).
% 0.58/0.79  thf('51', plain,
% 0.58/0.79      ((((sk_C_1) = (k1_xboole_0))
% 0.58/0.79        | (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_A) @ sk_B_1))),
% 0.58/0.79      inference('sup-', [status(thm)], ['49', '50'])).
% 0.58/0.79  thf('52', plain,
% 0.58/0.79      (![X47 : $i]:
% 0.58/0.79         (((sk_A) != (k1_funct_1 @ sk_D_1 @ X47))
% 0.58/0.79          | ~ (m1_subset_1 @ X47 @ sk_B_1))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('53', plain,
% 0.58/0.79      ((((sk_C_1) = (k1_xboole_0))
% 0.58/0.79        | ((sk_A) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_A))))),
% 0.58/0.79      inference('sup-', [status(thm)], ['51', '52'])).
% 0.58/0.79  thf('54', plain,
% 0.58/0.79      ((((sk_C_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_relat_1 @ sk_D_1)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['27', '28'])).
% 0.58/0.79  thf('55', plain,
% 0.58/0.79      ((r2_hidden @ 
% 0.58/0.79        (k4_tarski @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ sk_A) @ 
% 0.58/0.79        sk_D_1)),
% 0.58/0.79      inference('demod', [status(thm)], ['36', '37'])).
% 0.58/0.79  thf(t8_funct_1, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.58/0.79       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.58/0.79         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.58/0.79           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.58/0.79  thf('56', plain,
% 0.58/0.79      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.58/0.79         (~ (r2_hidden @ (k4_tarski @ X27 @ X29) @ X28)
% 0.58/0.79          | ((X29) = (k1_funct_1 @ X28 @ X27))
% 0.58/0.79          | ~ (v1_funct_1 @ X28)
% 0.58/0.79          | ~ (v1_relat_1 @ X28))),
% 0.58/0.79      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.58/0.79  thf('57', plain,
% 0.58/0.79      ((~ (v1_relat_1 @ sk_D_1)
% 0.58/0.79        | ~ (v1_funct_1 @ sk_D_1)
% 0.58/0.79        | ((sk_A)
% 0.58/0.79            = (k1_funct_1 @ sk_D_1 @ 
% 0.58/0.79               (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A))))),
% 0.58/0.79      inference('sup-', [status(thm)], ['55', '56'])).
% 0.58/0.79  thf('58', plain, ((v1_relat_1 @ sk_D_1)),
% 0.58/0.79      inference('sup-', [status(thm)], ['10', '11'])).
% 0.58/0.79  thf('59', plain, ((v1_funct_1 @ sk_D_1)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('60', plain,
% 0.58/0.79      (((sk_A)
% 0.58/0.79         = (k1_funct_1 @ sk_D_1 @ 
% 0.58/0.79            (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A)))),
% 0.58/0.79      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.58/0.79  thf('61', plain,
% 0.58/0.79      ((((sk_A) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_A)))
% 0.58/0.79        | ((sk_C_1) = (k1_xboole_0)))),
% 0.58/0.79      inference('sup+', [status(thm)], ['54', '60'])).
% 0.58/0.79  thf('62', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.58/0.79      inference('clc', [status(thm)], ['53', '61'])).
% 0.58/0.79  thf('63', plain,
% 0.58/0.79      ((~ (zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ sk_B_1)
% 0.58/0.79        | ((sk_B_1) = (k1_relat_1 @ sk_D_1)))),
% 0.58/0.79      inference('demod', [status(thm)], ['22', '62'])).
% 0.58/0.79  thf('64', plain, ((v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C_1)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('65', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.58/0.79      inference('clc', [status(thm)], ['53', '61'])).
% 0.58/0.79  thf('66', plain, ((v1_funct_2 @ sk_D_1 @ sk_B_1 @ k1_xboole_0)),
% 0.58/0.79      inference('demod', [status(thm)], ['64', '65'])).
% 0.58/0.79  thf('67', plain,
% 0.58/0.79      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('68', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.58/0.79      inference('clc', [status(thm)], ['53', '61'])).
% 0.58/0.79  thf(t113_zfmisc_1, axiom,
% 0.58/0.79    (![A:$i,B:$i]:
% 0.58/0.79     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.58/0.79       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.58/0.79  thf('69', plain,
% 0.58/0.79      (![X8 : $i, X9 : $i]:
% 0.58/0.79         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 0.58/0.79      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.58/0.79  thf('70', plain,
% 0.58/0.79      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.79      inference('simplify', [status(thm)], ['69'])).
% 0.58/0.79  thf('71', plain, ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.58/0.79      inference('demod', [status(thm)], ['67', '68', '70'])).
% 0.58/0.79  thf('72', plain,
% 0.58/0.79      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.58/0.79         (((X44) != (k1_xboole_0))
% 0.58/0.79          | ((X45) = (k1_xboole_0))
% 0.58/0.79          | ((X46) = (k1_xboole_0))
% 0.58/0.79          | ~ (v1_funct_2 @ X46 @ X45 @ X44)
% 0.58/0.79          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.58/0.79  thf('73', plain,
% 0.58/0.79      (![X45 : $i, X46 : $i]:
% 0.58/0.79         (~ (m1_subset_1 @ X46 @ 
% 0.58/0.79             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ k1_xboole_0)))
% 0.58/0.79          | ~ (v1_funct_2 @ X46 @ X45 @ k1_xboole_0)
% 0.58/0.79          | ((X46) = (k1_xboole_0))
% 0.58/0.79          | ((X45) = (k1_xboole_0)))),
% 0.58/0.79      inference('simplify', [status(thm)], ['72'])).
% 0.58/0.79  thf('74', plain,
% 0.58/0.79      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.79      inference('simplify', [status(thm)], ['69'])).
% 0.58/0.79  thf('75', plain,
% 0.58/0.79      (![X45 : $i, X46 : $i]:
% 0.58/0.79         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.58/0.79          | ~ (v1_funct_2 @ X46 @ X45 @ k1_xboole_0)
% 0.58/0.79          | ((X46) = (k1_xboole_0))
% 0.58/0.79          | ((X45) = (k1_xboole_0)))),
% 0.58/0.79      inference('demod', [status(thm)], ['73', '74'])).
% 0.58/0.79  thf('76', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         (((X0) = (k1_xboole_0))
% 0.58/0.79          | ((sk_D_1) = (k1_xboole_0))
% 0.58/0.79          | ~ (v1_funct_2 @ sk_D_1 @ X0 @ k1_xboole_0))),
% 0.58/0.79      inference('sup-', [status(thm)], ['71', '75'])).
% 0.58/0.79  thf('77', plain, ((((sk_D_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['66', '76'])).
% 0.58/0.79  thf('78', plain,
% 0.58/0.79      ((r2_hidden @ 
% 0.58/0.79        (k4_tarski @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ sk_A) @ 
% 0.58/0.79        sk_D_1)),
% 0.58/0.79      inference('demod', [status(thm)], ['36', '37'])).
% 0.58/0.79  thf('79', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.58/0.79      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.58/0.79  thf('80', plain, (~ (v1_xboole_0 @ sk_D_1)),
% 0.58/0.79      inference('sup-', [status(thm)], ['78', '79'])).
% 0.58/0.79  thf('81', plain,
% 0.58/0.79      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_B_1) = (k1_xboole_0)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['77', '80'])).
% 0.58/0.79  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.58/0.79  thf('82', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.79      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.58/0.79  thf('83', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.58/0.79      inference('demod', [status(thm)], ['81', '82'])).
% 0.58/0.79  thf('84', plain, ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.58/0.79      inference('demod', [status(thm)], ['67', '68', '70'])).
% 0.58/0.79  thf('85', plain,
% 0.58/0.79      (![X8 : $i, X9 : $i]:
% 0.58/0.79         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 0.58/0.79      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.58/0.79  thf('86', plain,
% 0.58/0.79      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 0.58/0.79      inference('simplify', [status(thm)], ['85'])).
% 0.58/0.79  thf('87', plain,
% 0.58/0.79      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.58/0.79         (~ (zip_tseitin_0 @ X44 @ X45)
% 0.58/0.79          | (zip_tseitin_1 @ X46 @ X44 @ X45)
% 0.58/0.79          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.58/0.79  thf('88', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.58/0.79          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 0.58/0.79          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 0.58/0.79      inference('sup-', [status(thm)], ['86', '87'])).
% 0.58/0.79  thf('89', plain,
% 0.58/0.79      (![X39 : $i, X40 : $i]:
% 0.58/0.79         ((zip_tseitin_0 @ X39 @ X40) | ((X40) != (k1_xboole_0)))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.58/0.79  thf('90', plain, (![X39 : $i]: (zip_tseitin_0 @ X39 @ k1_xboole_0)),
% 0.58/0.79      inference('simplify', [status(thm)], ['89'])).
% 0.58/0.79  thf('91', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.58/0.79          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 0.58/0.79      inference('demod', [status(thm)], ['88', '90'])).
% 0.58/0.79  thf('92', plain, (![X0 : $i]: (zip_tseitin_1 @ sk_D_1 @ X0 @ k1_xboole_0)),
% 0.58/0.79      inference('sup-', [status(thm)], ['84', '91'])).
% 0.58/0.79  thf('93', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.58/0.79      inference('demod', [status(thm)], ['81', '82'])).
% 0.58/0.79  thf('94', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_D_1))),
% 0.58/0.79      inference('demod', [status(thm)], ['63', '83', '92', '93'])).
% 0.58/0.79  thf('95', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.79      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.58/0.79  thf('96', plain, ($false),
% 0.58/0.79      inference('demod', [status(thm)], ['15', '94', '95'])).
% 0.58/0.79  
% 0.58/0.79  % SZS output end Refutation
% 0.58/0.79  
% 0.58/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
