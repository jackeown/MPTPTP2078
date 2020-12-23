%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Vx8GKMqZWY

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:15 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.10s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 231 expanded)
%              Number of leaves         :   41 (  83 expanded)
%              Depth                    :   16
%              Number of atoms          :  762 (2398 expanded)
%              Number of equality atoms :   83 ( 247 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_4_type,type,(
    sk_C_4: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t11_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t11_funct_2])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_C_4 @ ( k1_funct_2 @ sk_A @ sk_B_2 ) ) ),
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
    ! [X68: $i,X69: $i] :
      ( ( zip_tseitin_0 @ X68 @ X69 )
      | ( X68 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    m1_subset_1 @ sk_C_4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
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

thf('3',plain,(
    ! [X73: $i,X74: $i,X75: $i] :
      ( ~ ( zip_tseitin_0 @ X73 @ X74 )
      | ( zip_tseitin_1 @ X75 @ X73 @ X74 )
      | ~ ( m1_subset_1 @ X75 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X74 @ X73 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('4',plain,
    ( ( zip_tseitin_1 @ sk_C_4 @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_4 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_C_4 @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X70: $i,X71: $i,X72: $i] :
      ( ~ ( v1_funct_2 @ X72 @ X70 @ X71 )
      | ( X70
        = ( k1_relset_1 @ X70 @ X71 @ X72 ) )
      | ~ ( zip_tseitin_1 @ X72 @ X71 @ X70 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('8',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_4 @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_4 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C_4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('10',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ( ( k1_relset_1 @ X56 @ X57 @ X55 )
        = ( k1_relat_1 @ X55 ) )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('11',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_4 )
    = ( k1_relat_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_4 @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_4 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_4 ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('15',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X52 @ X53 @ X54 ) @ ( k1_zfmisc_1 @ X53 ) )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('16',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B_2 @ sk_C_4 ) @ ( k1_zfmisc_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C_4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('18',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( ( k2_relset_1 @ X59 @ X60 @ X58 )
        = ( k2_relat_1 @ X58 ) )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X60 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('19',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_2 @ sk_C_4 )
    = ( k2_relat_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_4 ) @ ( k1_zfmisc_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['16','19'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_4 ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['20','21'])).

thf(d2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k1_funct_2 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( ( v1_relat_1 @ E )
              & ( v1_funct_1 @ E )
              & ( D = E )
              & ( ( k1_relat_1 @ E )
                = A )
              & ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) )).

thf(zf_stmt_6,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ E @ D @ B @ A )
    <=> ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B )
        & ( ( k1_relat_1 @ E )
          = A )
        & ( D = E )
        & ( v1_funct_1 @ E )
        & ( v1_relat_1 @ E ) ) ) )).

thf('23',plain,(
    ! [X76: $i,X77: $i,X78: $i,X80: $i] :
      ( ( zip_tseitin_2 @ X76 @ X78 @ X77 @ X80 )
      | ~ ( v1_relat_1 @ X76 )
      | ~ ( v1_funct_1 @ X76 )
      | ( X78 != X76 )
      | ( ( k1_relat_1 @ X76 )
       != X80 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X76 ) @ X77 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('24',plain,(
    ! [X76: $i,X77: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X76 ) @ X77 )
      | ~ ( v1_funct_1 @ X76 )
      | ~ ( v1_relat_1 @ X76 )
      | ( zip_tseitin_2 @ X76 @ X76 @ X77 @ ( k1_relat_1 @ X76 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( zip_tseitin_2 @ sk_C_4 @ sk_C_4 @ sk_B_2 @ ( k1_relat_1 @ sk_C_4 ) )
    | ~ ( v1_relat_1 @ sk_C_4 )
    | ~ ( v1_funct_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C_4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('27',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( v1_relat_1 @ X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('28',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    zip_tseitin_2 @ sk_C_4 @ sk_C_4 @ sk_B_2 @ ( k1_relat_1 @ sk_C_4 ) ),
    inference(demod,[status(thm)],['25','28','29'])).

thf(zf_stmt_7,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k1_funct_2 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( zip_tseitin_2 @ E @ D @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X81: $i,X82: $i,X83: $i,X84: $i,X85: $i] :
      ( ~ ( zip_tseitin_2 @ X81 @ X82 @ X83 @ X84 )
      | ( r2_hidden @ X82 @ X85 )
      | ( X85
       != ( k1_funct_2 @ X84 @ X83 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('32',plain,(
    ! [X81: $i,X82: $i,X83: $i,X84: $i] :
      ( ( r2_hidden @ X82 @ ( k1_funct_2 @ X84 @ X83 ) )
      | ~ ( zip_tseitin_2 @ X81 @ X82 @ X83 @ X84 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    r2_hidden @ sk_C_4 @ ( k1_funct_2 @ ( k1_relat_1 @ sk_C_4 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,
    ( ( r2_hidden @ sk_C_4 @ ( k1_funct_2 @ sk_A @ sk_B_2 ) )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','33'])).

thf('35',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( sk_B_2 != k1_xboole_0 )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('38',plain,(
    ~ ( r2_hidden @ sk_C_4 @ ( k1_funct_2 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( r2_hidden @ sk_C_4 @ ( k1_funct_2 @ k1_xboole_0 @ sk_B_2 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('40',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_zfmisc_1 @ X14 @ X15 )
        = k1_xboole_0 )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('41',plain,(
    ! [X15: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X15 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('43',plain,(
    m1_subset_1 @ sk_C_4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( m1_subset_1 @ sk_C_4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_2 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( m1_subset_1 @ sk_C_4 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,
    ( ( r1_tarski @ sk_C_4 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('48',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X2 )
        = X1 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('49',plain,
    ( ( ( k3_xboole_0 @ sk_C_4 @ k1_xboole_0 )
      = sk_C_4 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('50',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('51',plain,
    ( ( k1_xboole_0 = sk_C_4 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( r2_hidden @ k1_xboole_0 @ ( k1_funct_2 @ k1_xboole_0 @ sk_B_2 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','51'])).

thf('53',plain,
    ( ( k1_xboole_0 = sk_C_4 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('54',plain,(
    zip_tseitin_2 @ sk_C_4 @ sk_C_4 @ sk_B_2 @ ( k1_relat_1 @ sk_C_4 ) ),
    inference(demod,[status(thm)],['25','28','29'])).

thf('55',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ sk_C_4 @ sk_B_2 @ ( k1_relat_1 @ sk_C_4 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k1_xboole_0 = sk_C_4 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('57',plain,
    ( ( k1_xboole_0 = sk_C_4 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('58',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('59',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_B_2 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('60',plain,(
    ! [X81: $i,X82: $i,X83: $i,X84: $i] :
      ( ( r2_hidden @ X82 @ ( k1_funct_2 @ X84 @ X83 ) )
      | ~ ( zip_tseitin_2 @ X81 @ X82 @ X83 @ X84 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('61',plain,
    ( ( r2_hidden @ k1_xboole_0 @ ( k1_funct_2 @ k1_xboole_0 @ sk_B_2 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['52','61'])).

thf('63',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('64',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['62','63'])).

thf('65',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['36','64'])).

thf('66',plain,(
    r2_hidden @ sk_C_4 @ ( k1_funct_2 @ sk_A @ sk_B_2 ) ),
    inference('simplify_reflect-',[status(thm)],['34','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['0','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Vx8GKMqZWY
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:14:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.06/1.26  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.06/1.26  % Solved by: fo/fo7.sh
% 1.06/1.26  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.26  % done 951 iterations in 0.806s
% 1.06/1.26  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.06/1.26  % SZS output start Refutation
% 1.06/1.26  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.06/1.26  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.06/1.26  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.06/1.26  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.06/1.26  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.06/1.26  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.06/1.26  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.06/1.26  thf(sk_C_4_type, type, sk_C_4: $i).
% 1.06/1.26  thf(sk_B_2_type, type, sk_B_2: $i).
% 1.06/1.26  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.06/1.26  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 1.06/1.26  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.06/1.26  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.06/1.26  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.26  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.06/1.26  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.06/1.26  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.06/1.26  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.06/1.26  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.06/1.26  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 1.06/1.26  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.06/1.26  thf(t11_funct_2, conjecture,
% 1.06/1.26    (![A:$i,B:$i,C:$i]:
% 1.06/1.26     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.06/1.26         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.06/1.26       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.06/1.26         ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) ) ))).
% 1.06/1.26  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.26    (~( ![A:$i,B:$i,C:$i]:
% 1.06/1.26        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.06/1.26            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.06/1.26          ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.06/1.26            ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) ) ) )),
% 1.06/1.26    inference('cnf.neg', [status(esa)], [t11_funct_2])).
% 1.06/1.26  thf('0', plain, (~ (r2_hidden @ sk_C_4 @ (k1_funct_2 @ sk_A @ sk_B_2))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf(d1_funct_2, axiom,
% 1.06/1.26    (![A:$i,B:$i,C:$i]:
% 1.06/1.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.06/1.26       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.06/1.26           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.06/1.26             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.06/1.26         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.06/1.26           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.06/1.26             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.06/1.26  thf(zf_stmt_1, axiom,
% 1.06/1.26    (![B:$i,A:$i]:
% 1.06/1.26     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.06/1.26       ( zip_tseitin_0 @ B @ A ) ))).
% 1.06/1.26  thf('1', plain,
% 1.06/1.26      (![X68 : $i, X69 : $i]:
% 1.06/1.26         ((zip_tseitin_0 @ X68 @ X69) | ((X68) = (k1_xboole_0)))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.06/1.26  thf('2', plain,
% 1.06/1.26      ((m1_subset_1 @ sk_C_4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.06/1.26  thf(zf_stmt_3, axiom,
% 1.06/1.26    (![C:$i,B:$i,A:$i]:
% 1.06/1.26     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.06/1.26       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.06/1.26  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.06/1.26  thf(zf_stmt_5, axiom,
% 1.06/1.26    (![A:$i,B:$i,C:$i]:
% 1.06/1.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.06/1.26       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.06/1.26         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.06/1.26           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.06/1.26             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.06/1.26  thf('3', plain,
% 1.06/1.26      (![X73 : $i, X74 : $i, X75 : $i]:
% 1.06/1.26         (~ (zip_tseitin_0 @ X73 @ X74)
% 1.06/1.26          | (zip_tseitin_1 @ X75 @ X73 @ X74)
% 1.06/1.26          | ~ (m1_subset_1 @ X75 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X74 @ X73))))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.06/1.26  thf('4', plain,
% 1.06/1.26      (((zip_tseitin_1 @ sk_C_4 @ sk_B_2 @ sk_A)
% 1.10/1.26        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 1.10/1.26      inference('sup-', [status(thm)], ['2', '3'])).
% 1.10/1.26  thf('5', plain,
% 1.10/1.26      ((((sk_B_2) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_4 @ sk_B_2 @ sk_A))),
% 1.10/1.26      inference('sup-', [status(thm)], ['1', '4'])).
% 1.10/1.26  thf('6', plain, ((v1_funct_2 @ sk_C_4 @ sk_A @ sk_B_2)),
% 1.10/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.26  thf('7', plain,
% 1.10/1.26      (![X70 : $i, X71 : $i, X72 : $i]:
% 1.10/1.26         (~ (v1_funct_2 @ X72 @ X70 @ X71)
% 1.10/1.26          | ((X70) = (k1_relset_1 @ X70 @ X71 @ X72))
% 1.10/1.26          | ~ (zip_tseitin_1 @ X72 @ X71 @ X70))),
% 1.10/1.26      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.10/1.26  thf('8', plain,
% 1.10/1.26      ((~ (zip_tseitin_1 @ sk_C_4 @ sk_B_2 @ sk_A)
% 1.10/1.26        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_4)))),
% 1.10/1.26      inference('sup-', [status(thm)], ['6', '7'])).
% 1.10/1.26  thf('9', plain,
% 1.10/1.26      ((m1_subset_1 @ sk_C_4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.10/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.26  thf(redefinition_k1_relset_1, axiom,
% 1.10/1.26    (![A:$i,B:$i,C:$i]:
% 1.10/1.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.10/1.26       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.10/1.26  thf('10', plain,
% 1.10/1.26      (![X55 : $i, X56 : $i, X57 : $i]:
% 1.10/1.26         (((k1_relset_1 @ X56 @ X57 @ X55) = (k1_relat_1 @ X55))
% 1.10/1.26          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57))))),
% 1.10/1.26      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.10/1.26  thf('11', plain,
% 1.10/1.26      (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_4) = (k1_relat_1 @ sk_C_4))),
% 1.10/1.26      inference('sup-', [status(thm)], ['9', '10'])).
% 1.10/1.26  thf('12', plain,
% 1.10/1.26      ((~ (zip_tseitin_1 @ sk_C_4 @ sk_B_2 @ sk_A)
% 1.10/1.26        | ((sk_A) = (k1_relat_1 @ sk_C_4)))),
% 1.10/1.26      inference('demod', [status(thm)], ['8', '11'])).
% 1.10/1.26  thf('13', plain,
% 1.10/1.26      ((((sk_B_2) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_4)))),
% 1.10/1.26      inference('sup-', [status(thm)], ['5', '12'])).
% 1.10/1.26  thf('14', plain,
% 1.10/1.26      ((m1_subset_1 @ sk_C_4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.10/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.26  thf(dt_k2_relset_1, axiom,
% 1.10/1.26    (![A:$i,B:$i,C:$i]:
% 1.10/1.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.10/1.26       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.10/1.26  thf('15', plain,
% 1.10/1.26      (![X52 : $i, X53 : $i, X54 : $i]:
% 1.10/1.26         ((m1_subset_1 @ (k2_relset_1 @ X52 @ X53 @ X54) @ (k1_zfmisc_1 @ X53))
% 1.10/1.26          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53))))),
% 1.10/1.26      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 1.10/1.26  thf('16', plain,
% 1.10/1.26      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B_2 @ sk_C_4) @ 
% 1.10/1.26        (k1_zfmisc_1 @ sk_B_2))),
% 1.10/1.26      inference('sup-', [status(thm)], ['14', '15'])).
% 1.10/1.26  thf('17', plain,
% 1.10/1.26      ((m1_subset_1 @ sk_C_4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.10/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.26  thf(redefinition_k2_relset_1, axiom,
% 1.10/1.26    (![A:$i,B:$i,C:$i]:
% 1.10/1.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.10/1.26       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.10/1.26  thf('18', plain,
% 1.10/1.26      (![X58 : $i, X59 : $i, X60 : $i]:
% 1.10/1.26         (((k2_relset_1 @ X59 @ X60 @ X58) = (k2_relat_1 @ X58))
% 1.10/1.26          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X60))))),
% 1.10/1.26      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.10/1.26  thf('19', plain,
% 1.10/1.26      (((k2_relset_1 @ sk_A @ sk_B_2 @ sk_C_4) = (k2_relat_1 @ sk_C_4))),
% 1.10/1.26      inference('sup-', [status(thm)], ['17', '18'])).
% 1.10/1.26  thf('20', plain,
% 1.10/1.26      ((m1_subset_1 @ (k2_relat_1 @ sk_C_4) @ (k1_zfmisc_1 @ sk_B_2))),
% 1.10/1.26      inference('demod', [status(thm)], ['16', '19'])).
% 1.10/1.26  thf(t3_subset, axiom,
% 1.10/1.26    (![A:$i,B:$i]:
% 1.10/1.26     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.10/1.26  thf('21', plain,
% 1.10/1.26      (![X20 : $i, X21 : $i]:
% 1.10/1.26         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 1.10/1.26      inference('cnf', [status(esa)], [t3_subset])).
% 1.10/1.26  thf('22', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_4) @ sk_B_2)),
% 1.10/1.26      inference('sup-', [status(thm)], ['20', '21'])).
% 1.10/1.26  thf(d2_funct_2, axiom,
% 1.10/1.26    (![A:$i,B:$i,C:$i]:
% 1.10/1.26     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 1.10/1.26       ( ![D:$i]:
% 1.10/1.26         ( ( r2_hidden @ D @ C ) <=>
% 1.10/1.26           ( ?[E:$i]:
% 1.10/1.26             ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) & ( ( D ) = ( E ) ) & 
% 1.10/1.26               ( ( k1_relat_1 @ E ) = ( A ) ) & 
% 1.10/1.26               ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) ) ))).
% 1.10/1.26  thf(zf_stmt_6, axiom,
% 1.10/1.26    (![E:$i,D:$i,B:$i,A:$i]:
% 1.10/1.26     ( ( zip_tseitin_2 @ E @ D @ B @ A ) <=>
% 1.10/1.26       ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) & 
% 1.10/1.26         ( ( k1_relat_1 @ E ) = ( A ) ) & ( ( D ) = ( E ) ) & 
% 1.10/1.26         ( v1_funct_1 @ E ) & ( v1_relat_1 @ E ) ) ))).
% 1.10/1.26  thf('23', plain,
% 1.10/1.26      (![X76 : $i, X77 : $i, X78 : $i, X80 : $i]:
% 1.10/1.26         ((zip_tseitin_2 @ X76 @ X78 @ X77 @ X80)
% 1.10/1.26          | ~ (v1_relat_1 @ X76)
% 1.10/1.26          | ~ (v1_funct_1 @ X76)
% 1.10/1.26          | ((X78) != (X76))
% 1.10/1.26          | ((k1_relat_1 @ X76) != (X80))
% 1.10/1.26          | ~ (r1_tarski @ (k2_relat_1 @ X76) @ X77))),
% 1.10/1.26      inference('cnf', [status(esa)], [zf_stmt_6])).
% 1.10/1.26  thf('24', plain,
% 1.10/1.26      (![X76 : $i, X77 : $i]:
% 1.10/1.26         (~ (r1_tarski @ (k2_relat_1 @ X76) @ X77)
% 1.10/1.26          | ~ (v1_funct_1 @ X76)
% 1.10/1.26          | ~ (v1_relat_1 @ X76)
% 1.10/1.26          | (zip_tseitin_2 @ X76 @ X76 @ X77 @ (k1_relat_1 @ X76)))),
% 1.10/1.26      inference('simplify', [status(thm)], ['23'])).
% 1.10/1.26  thf('25', plain,
% 1.10/1.26      (((zip_tseitin_2 @ sk_C_4 @ sk_C_4 @ sk_B_2 @ (k1_relat_1 @ sk_C_4))
% 1.10/1.26        | ~ (v1_relat_1 @ sk_C_4)
% 1.10/1.26        | ~ (v1_funct_1 @ sk_C_4))),
% 1.10/1.26      inference('sup-', [status(thm)], ['22', '24'])).
% 1.10/1.26  thf('26', plain,
% 1.10/1.26      ((m1_subset_1 @ sk_C_4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.10/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.26  thf(cc1_relset_1, axiom,
% 1.10/1.26    (![A:$i,B:$i,C:$i]:
% 1.10/1.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.10/1.26       ( v1_relat_1 @ C ) ))).
% 1.10/1.26  thf('27', plain,
% 1.10/1.26      (![X43 : $i, X44 : $i, X45 : $i]:
% 1.10/1.26         ((v1_relat_1 @ X43)
% 1.10/1.26          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45))))),
% 1.10/1.26      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.10/1.26  thf('28', plain, ((v1_relat_1 @ sk_C_4)),
% 1.10/1.26      inference('sup-', [status(thm)], ['26', '27'])).
% 1.10/1.26  thf('29', plain, ((v1_funct_1 @ sk_C_4)),
% 1.10/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.26  thf('30', plain,
% 1.10/1.26      ((zip_tseitin_2 @ sk_C_4 @ sk_C_4 @ sk_B_2 @ (k1_relat_1 @ sk_C_4))),
% 1.10/1.26      inference('demod', [status(thm)], ['25', '28', '29'])).
% 1.10/1.26  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 1.10/1.26  thf(zf_stmt_8, axiom,
% 1.10/1.26    (![A:$i,B:$i,C:$i]:
% 1.10/1.26     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 1.10/1.26       ( ![D:$i]:
% 1.10/1.26         ( ( r2_hidden @ D @ C ) <=>
% 1.10/1.26           ( ?[E:$i]: ( zip_tseitin_2 @ E @ D @ B @ A ) ) ) ) ))).
% 1.10/1.26  thf('31', plain,
% 1.10/1.26      (![X81 : $i, X82 : $i, X83 : $i, X84 : $i, X85 : $i]:
% 1.10/1.26         (~ (zip_tseitin_2 @ X81 @ X82 @ X83 @ X84)
% 1.10/1.26          | (r2_hidden @ X82 @ X85)
% 1.10/1.26          | ((X85) != (k1_funct_2 @ X84 @ X83)))),
% 1.10/1.26      inference('cnf', [status(esa)], [zf_stmt_8])).
% 1.10/1.26  thf('32', plain,
% 1.10/1.26      (![X81 : $i, X82 : $i, X83 : $i, X84 : $i]:
% 1.10/1.26         ((r2_hidden @ X82 @ (k1_funct_2 @ X84 @ X83))
% 1.10/1.26          | ~ (zip_tseitin_2 @ X81 @ X82 @ X83 @ X84))),
% 1.10/1.26      inference('simplify', [status(thm)], ['31'])).
% 1.10/1.26  thf('33', plain,
% 1.10/1.26      ((r2_hidden @ sk_C_4 @ (k1_funct_2 @ (k1_relat_1 @ sk_C_4) @ sk_B_2))),
% 1.10/1.26      inference('sup-', [status(thm)], ['30', '32'])).
% 1.10/1.26  thf('34', plain,
% 1.10/1.26      (((r2_hidden @ sk_C_4 @ (k1_funct_2 @ sk_A @ sk_B_2))
% 1.10/1.26        | ((sk_B_2) = (k1_xboole_0)))),
% 1.10/1.26      inference('sup+', [status(thm)], ['13', '33'])).
% 1.10/1.26  thf('35', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B_2) != (k1_xboole_0)))),
% 1.10/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.26  thf('36', plain,
% 1.10/1.26      ((((sk_B_2) != (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_xboole_0))))),
% 1.10/1.26      inference('split', [status(esa)], ['35'])).
% 1.10/1.26  thf('37', plain,
% 1.10/1.26      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.10/1.26      inference('split', [status(esa)], ['35'])).
% 1.10/1.26  thf('38', plain, (~ (r2_hidden @ sk_C_4 @ (k1_funct_2 @ sk_A @ sk_B_2))),
% 1.10/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.26  thf('39', plain,
% 1.10/1.26      ((~ (r2_hidden @ sk_C_4 @ (k1_funct_2 @ k1_xboole_0 @ sk_B_2)))
% 1.10/1.26         <= ((((sk_A) = (k1_xboole_0))))),
% 1.10/1.26      inference('sup-', [status(thm)], ['37', '38'])).
% 1.10/1.26  thf(t113_zfmisc_1, axiom,
% 1.10/1.26    (![A:$i,B:$i]:
% 1.10/1.26     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.10/1.26       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.10/1.26  thf('40', plain,
% 1.10/1.26      (![X14 : $i, X15 : $i]:
% 1.10/1.26         (((k2_zfmisc_1 @ X14 @ X15) = (k1_xboole_0))
% 1.10/1.26          | ((X14) != (k1_xboole_0)))),
% 1.10/1.26      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.10/1.26  thf('41', plain,
% 1.10/1.26      (![X15 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X15) = (k1_xboole_0))),
% 1.10/1.26      inference('simplify', [status(thm)], ['40'])).
% 1.10/1.26  thf('42', plain,
% 1.10/1.26      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.10/1.26      inference('split', [status(esa)], ['35'])).
% 1.10/1.26  thf('43', plain,
% 1.10/1.26      ((m1_subset_1 @ sk_C_4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.10/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.26  thf('44', plain,
% 1.10/1.26      (((m1_subset_1 @ sk_C_4 @ 
% 1.10/1.26         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_2))))
% 1.10/1.26         <= ((((sk_A) = (k1_xboole_0))))),
% 1.10/1.26      inference('sup+', [status(thm)], ['42', '43'])).
% 1.10/1.26  thf('45', plain,
% 1.10/1.26      (((m1_subset_1 @ sk_C_4 @ (k1_zfmisc_1 @ k1_xboole_0)))
% 1.10/1.26         <= ((((sk_A) = (k1_xboole_0))))),
% 1.10/1.26      inference('sup+', [status(thm)], ['41', '44'])).
% 1.10/1.26  thf('46', plain,
% 1.10/1.26      (![X20 : $i, X21 : $i]:
% 1.10/1.26         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 1.10/1.26      inference('cnf', [status(esa)], [t3_subset])).
% 1.10/1.26  thf('47', plain,
% 1.10/1.26      (((r1_tarski @ sk_C_4 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 1.10/1.26      inference('sup-', [status(thm)], ['45', '46'])).
% 1.10/1.26  thf(t28_xboole_1, axiom,
% 1.10/1.26    (![A:$i,B:$i]:
% 1.10/1.26     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.10/1.26  thf('48', plain,
% 1.10/1.26      (![X1 : $i, X2 : $i]:
% 1.10/1.26         (((k3_xboole_0 @ X1 @ X2) = (X1)) | ~ (r1_tarski @ X1 @ X2))),
% 1.10/1.26      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.10/1.26  thf('49', plain,
% 1.10/1.26      ((((k3_xboole_0 @ sk_C_4 @ k1_xboole_0) = (sk_C_4)))
% 1.10/1.26         <= ((((sk_A) = (k1_xboole_0))))),
% 1.10/1.26      inference('sup-', [status(thm)], ['47', '48'])).
% 1.10/1.26  thf(t2_boole, axiom,
% 1.10/1.26    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.10/1.26  thf('50', plain,
% 1.10/1.26      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 1.10/1.26      inference('cnf', [status(esa)], [t2_boole])).
% 1.10/1.26  thf('51', plain,
% 1.10/1.26      ((((k1_xboole_0) = (sk_C_4))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.10/1.26      inference('demod', [status(thm)], ['49', '50'])).
% 1.10/1.26  thf('52', plain,
% 1.10/1.26      ((~ (r2_hidden @ k1_xboole_0 @ (k1_funct_2 @ k1_xboole_0 @ sk_B_2)))
% 1.10/1.26         <= ((((sk_A) = (k1_xboole_0))))),
% 1.10/1.26      inference('demod', [status(thm)], ['39', '51'])).
% 1.10/1.26  thf('53', plain,
% 1.10/1.26      ((((k1_xboole_0) = (sk_C_4))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.10/1.26      inference('demod', [status(thm)], ['49', '50'])).
% 1.10/1.26  thf('54', plain,
% 1.10/1.26      ((zip_tseitin_2 @ sk_C_4 @ sk_C_4 @ sk_B_2 @ (k1_relat_1 @ sk_C_4))),
% 1.10/1.26      inference('demod', [status(thm)], ['25', '28', '29'])).
% 1.10/1.26  thf('55', plain,
% 1.10/1.26      (((zip_tseitin_2 @ k1_xboole_0 @ sk_C_4 @ sk_B_2 @ (k1_relat_1 @ sk_C_4)))
% 1.10/1.26         <= ((((sk_A) = (k1_xboole_0))))),
% 1.10/1.26      inference('sup+', [status(thm)], ['53', '54'])).
% 1.10/1.26  thf('56', plain,
% 1.10/1.26      ((((k1_xboole_0) = (sk_C_4))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.10/1.26      inference('demod', [status(thm)], ['49', '50'])).
% 1.10/1.26  thf('57', plain,
% 1.10/1.26      ((((k1_xboole_0) = (sk_C_4))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.10/1.26      inference('demod', [status(thm)], ['49', '50'])).
% 1.10/1.26  thf(t60_relat_1, axiom,
% 1.10/1.26    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.10/1.26     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.10/1.26  thf('58', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.10/1.26      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.10/1.26  thf('59', plain,
% 1.10/1.26      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_B_2 @ k1_xboole_0))
% 1.10/1.26         <= ((((sk_A) = (k1_xboole_0))))),
% 1.10/1.26      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 1.10/1.26  thf('60', plain,
% 1.10/1.26      (![X81 : $i, X82 : $i, X83 : $i, X84 : $i]:
% 1.10/1.26         ((r2_hidden @ X82 @ (k1_funct_2 @ X84 @ X83))
% 1.10/1.26          | ~ (zip_tseitin_2 @ X81 @ X82 @ X83 @ X84))),
% 1.10/1.26      inference('simplify', [status(thm)], ['31'])).
% 1.10/1.26  thf('61', plain,
% 1.10/1.26      (((r2_hidden @ k1_xboole_0 @ (k1_funct_2 @ k1_xboole_0 @ sk_B_2)))
% 1.10/1.26         <= ((((sk_A) = (k1_xboole_0))))),
% 1.10/1.26      inference('sup-', [status(thm)], ['59', '60'])).
% 1.10/1.26  thf('62', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 1.10/1.26      inference('demod', [status(thm)], ['52', '61'])).
% 1.10/1.26  thf('63', plain,
% 1.10/1.26      (~ (((sk_B_2) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 1.10/1.26      inference('split', [status(esa)], ['35'])).
% 1.10/1.26  thf('64', plain, (~ (((sk_B_2) = (k1_xboole_0)))),
% 1.10/1.26      inference('sat_resolution*', [status(thm)], ['62', '63'])).
% 1.10/1.26  thf('65', plain, (((sk_B_2) != (k1_xboole_0))),
% 1.10/1.26      inference('simpl_trail', [status(thm)], ['36', '64'])).
% 1.10/1.26  thf('66', plain, ((r2_hidden @ sk_C_4 @ (k1_funct_2 @ sk_A @ sk_B_2))),
% 1.10/1.26      inference('simplify_reflect-', [status(thm)], ['34', '65'])).
% 1.10/1.26  thf('67', plain, ($false), inference('demod', [status(thm)], ['0', '66'])).
% 1.10/1.26  
% 1.10/1.26  % SZS output end Refutation
% 1.10/1.26  
% 1.10/1.27  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
