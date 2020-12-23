%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.C8LwNUIQAw

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:17 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 289 expanded)
%              Number of leaves         :   42 ( 104 expanded)
%              Depth                    :   18
%              Number of atoms          :  710 (3325 expanded)
%              Number of equality atoms :   38 ( 150 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

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
    r2_hidden @ sk_A @ ( k2_relset_1 @ sk_B_2 @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k2_relset_1 @ X38 @ X39 @ X37 )
        = ( k2_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B_2 @ sk_C @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B_2 @ sk_C ),
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

thf('6',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ( X42
        = ( k1_relset_1 @ X42 @ X43 @ X44 ) )
      | ~ ( zip_tseitin_1 @ X44 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_2 )
    | ( sk_B_2
      = ( k1_relset_1 @ sk_B_2 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k1_relset_1 @ X35 @ X36 @ X34 )
        = ( k1_relat_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('10',plain,
    ( ( k1_relset_1 @ sk_B_2 @ sk_C @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_2 )
    | ( sk_B_2
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( zip_tseitin_0 @ X45 @ X46 )
      | ( zip_tseitin_1 @ X47 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('14',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_2 )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_0 @ X40 @ X41 )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('16',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('21',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('22',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X31 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('23',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_B_2 @ sk_C @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k2_relset_1 @ sk_B_2 @ sk_C @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('25',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('26',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['20','27'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('29',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ~ ( r1_tarski @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('30',plain,(
    ~ ( r1_tarski @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference('sup-',[status(thm)],['19','30'])).

thf('32',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_2 ),
    inference(demod,[status(thm)],['14','31'])).

thf('33',plain,
    ( sk_B_2
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['11','32'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('34',plain,(
    ! [X22: $i] :
      ( ( ( k9_relat_1 @ X22 @ ( k1_relat_1 @ X22 ) )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('35',plain,
    ( ( ( k9_relat_1 @ sk_D_1 @ sk_B_2 )
      = ( k2_relat_1 @ sk_D_1 ) )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('37',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('38',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k9_relat_1 @ sk_D_1 @ sk_B_2 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['35','38'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('40',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k9_relat_1 @ X21 @ X19 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X21 @ X19 @ X20 ) @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_B_2 @ X0 ) @ X0 ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_B_2 @ X0 ) @ X0 ) @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_B_2 @ sk_A ) @ sk_A ) @ sk_D_1 ),
    inference('sup-',[status(thm)],['4','43'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('45',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X23 @ X25 ) @ X24 )
      | ( X25
        = ( k1_funct_1 @ X24 @ X23 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_A
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('48',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('51',plain,
    ( ( k9_relat_1 @ sk_D_1 @ sk_B_2 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('52',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k9_relat_1 @ X21 @ X19 ) )
      | ( r2_hidden @ ( sk_D @ X21 @ X19 @ X20 ) @ ( k1_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B_2 @ X0 ) @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('55',plain,
    ( sk_B_2
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['11','32'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B_2 @ X0 ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_B_2 @ sk_A ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['50','56'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('58',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('59',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B_2 @ sk_A ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X48: $i] :
      ( ( sk_A
       != ( k1_funct_1 @ sk_D_1 @ X48 ) )
      | ~ ( m1_subset_1 @ X48 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    sk_A
 != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['49','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.C8LwNUIQAw
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:20:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.75/0.98  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.75/0.98  % Solved by: fo/fo7.sh
% 0.75/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.98  % done 651 iterations in 0.525s
% 0.75/0.98  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.75/0.98  % SZS output start Refutation
% 0.75/0.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.75/0.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.98  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.75/0.98  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.75/0.98  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.75/0.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.98  thf(sk_C_type, type, sk_C: $i).
% 0.75/0.98  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.75/0.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/0.98  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.75/0.98  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.75/0.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.75/0.98  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.75/0.98  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.75/0.98  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.75/0.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.75/0.98  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.75/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.98  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.75/0.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.98  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.75/0.98  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.75/0.98  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.75/0.98  thf(t190_funct_2, conjecture,
% 0.75/0.98    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.98     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.75/0.98         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.75/0.98       ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.75/0.98            ( ![E:$i]:
% 0.75/0.98              ( ( m1_subset_1 @ E @ B ) => ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ))).
% 0.75/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.98    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.98        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.75/0.98            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.75/0.98          ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.75/0.98               ( ![E:$i]:
% 0.75/0.98                 ( ( m1_subset_1 @ E @ B ) =>
% 0.75/0.98                   ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )),
% 0.75/0.98    inference('cnf.neg', [status(esa)], [t190_funct_2])).
% 0.75/0.98  thf('0', plain,
% 0.75/0.98      ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B_2 @ sk_C @ sk_D_1))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('1', plain,
% 0.75/0.98      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_C)))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(redefinition_k2_relset_1, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i]:
% 0.75/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.98       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.75/0.98  thf('2', plain,
% 0.75/0.98      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.75/0.98         (((k2_relset_1 @ X38 @ X39 @ X37) = (k2_relat_1 @ X37))
% 0.75/0.98          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.75/0.98      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.75/0.98  thf('3', plain,
% 0.75/0.98      (((k2_relset_1 @ sk_B_2 @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.75/0.98      inference('sup-', [status(thm)], ['1', '2'])).
% 0.75/0.98  thf('4', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_1))),
% 0.75/0.98      inference('demod', [status(thm)], ['0', '3'])).
% 0.75/0.98  thf('5', plain, ((v1_funct_2 @ sk_D_1 @ sk_B_2 @ sk_C)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(d1_funct_2, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i]:
% 0.75/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.98       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.75/0.98           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.75/0.98             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.75/0.98         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.75/0.98           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.75/0.98             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.75/0.98  thf(zf_stmt_1, axiom,
% 0.75/0.98    (![C:$i,B:$i,A:$i]:
% 0.75/0.98     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.75/0.98       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.75/0.98  thf('6', plain,
% 0.75/0.98      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.75/0.98         (~ (v1_funct_2 @ X44 @ X42 @ X43)
% 0.75/0.98          | ((X42) = (k1_relset_1 @ X42 @ X43 @ X44))
% 0.75/0.98          | ~ (zip_tseitin_1 @ X44 @ X43 @ X42))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.98  thf('7', plain,
% 0.75/0.98      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_2)
% 0.75/0.98        | ((sk_B_2) = (k1_relset_1 @ sk_B_2 @ sk_C @ sk_D_1)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['5', '6'])).
% 0.75/0.98  thf('8', plain,
% 0.75/0.98      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_C)))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(redefinition_k1_relset_1, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i]:
% 0.75/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.98       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.75/0.98  thf('9', plain,
% 0.75/0.98      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.75/0.98         (((k1_relset_1 @ X35 @ X36 @ X34) = (k1_relat_1 @ X34))
% 0.75/0.98          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.75/0.98      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.75/0.98  thf('10', plain,
% 0.75/0.98      (((k1_relset_1 @ sk_B_2 @ sk_C @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.75/0.98      inference('sup-', [status(thm)], ['8', '9'])).
% 0.75/0.98  thf('11', plain,
% 0.75/0.98      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_2)
% 0.75/0.98        | ((sk_B_2) = (k1_relat_1 @ sk_D_1)))),
% 0.75/0.98      inference('demod', [status(thm)], ['7', '10'])).
% 0.75/0.98  thf('12', plain,
% 0.75/0.98      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_C)))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.75/0.98  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.75/0.98  thf(zf_stmt_4, axiom,
% 0.75/0.98    (![B:$i,A:$i]:
% 0.75/0.98     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.75/0.98       ( zip_tseitin_0 @ B @ A ) ))).
% 0.75/0.98  thf(zf_stmt_5, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i]:
% 0.75/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.98       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.75/0.98         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.75/0.98           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.75/0.98             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.75/0.98  thf('13', plain,
% 0.75/0.98      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.75/0.98         (~ (zip_tseitin_0 @ X45 @ X46)
% 0.75/0.98          | (zip_tseitin_1 @ X47 @ X45 @ X46)
% 0.75/0.98          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45))))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.75/0.98  thf('14', plain,
% 0.75/0.98      (((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_2)
% 0.75/0.98        | ~ (zip_tseitin_0 @ sk_C @ sk_B_2))),
% 0.75/0.98      inference('sup-', [status(thm)], ['12', '13'])).
% 0.75/0.98  thf('15', plain,
% 0.75/0.98      (![X40 : $i, X41 : $i]:
% 0.75/0.98         ((zip_tseitin_0 @ X40 @ X41) | ((X40) = (k1_xboole_0)))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.75/0.98  thf(t4_subset_1, axiom,
% 0.75/0.98    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.75/0.98  thf('16', plain,
% 0.75/0.98      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.75/0.98      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.75/0.98  thf(t3_subset, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.75/0.98  thf('17', plain,
% 0.75/0.98      (![X12 : $i, X13 : $i]:
% 0.75/0.98         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.75/0.98      inference('cnf', [status(esa)], [t3_subset])).
% 0.75/0.98  thf('18', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.75/0.98      inference('sup-', [status(thm)], ['16', '17'])).
% 0.75/0.98  thf('19', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.98         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.75/0.98      inference('sup+', [status(thm)], ['15', '18'])).
% 0.75/0.98  thf('20', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_1))),
% 0.75/0.98      inference('demod', [status(thm)], ['0', '3'])).
% 0.75/0.98  thf('21', plain,
% 0.75/0.98      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_C)))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(dt_k2_relset_1, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i]:
% 0.75/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.98       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.75/0.98  thf('22', plain,
% 0.75/0.98      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.75/0.98         ((m1_subset_1 @ (k2_relset_1 @ X31 @ X32 @ X33) @ (k1_zfmisc_1 @ X32))
% 0.75/0.98          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.75/0.98      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.75/0.98  thf('23', plain,
% 0.75/0.98      ((m1_subset_1 @ (k2_relset_1 @ sk_B_2 @ sk_C @ sk_D_1) @ 
% 0.75/0.98        (k1_zfmisc_1 @ sk_C))),
% 0.75/0.98      inference('sup-', [status(thm)], ['21', '22'])).
% 0.75/0.98  thf('24', plain,
% 0.75/0.98      (((k2_relset_1 @ sk_B_2 @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.75/0.98      inference('sup-', [status(thm)], ['1', '2'])).
% 0.75/0.98  thf('25', plain,
% 0.75/0.98      ((m1_subset_1 @ (k2_relat_1 @ sk_D_1) @ (k1_zfmisc_1 @ sk_C))),
% 0.75/0.98      inference('demod', [status(thm)], ['23', '24'])).
% 0.75/0.98  thf(l3_subset_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/0.98       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.75/0.98  thf('26', plain,
% 0.75/0.98      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.75/0.98         (~ (r2_hidden @ X4 @ X5)
% 0.75/0.98          | (r2_hidden @ X4 @ X6)
% 0.75/0.98          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.75/0.98      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.75/0.98  thf('27', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         ((r2_hidden @ X0 @ sk_C) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['25', '26'])).
% 0.75/0.98  thf('28', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.75/0.98      inference('sup-', [status(thm)], ['20', '27'])).
% 0.75/0.98  thf(t7_ordinal1, axiom,
% 0.75/0.98    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.75/0.98  thf('29', plain,
% 0.75/0.98      (![X26 : $i, X27 : $i]:
% 0.75/0.98         (~ (r2_hidden @ X26 @ X27) | ~ (r1_tarski @ X27 @ X26))),
% 0.75/0.98      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.75/0.98  thf('30', plain, (~ (r1_tarski @ sk_C @ sk_A)),
% 0.75/0.98      inference('sup-', [status(thm)], ['28', '29'])).
% 0.75/0.98  thf('31', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 0.75/0.98      inference('sup-', [status(thm)], ['19', '30'])).
% 0.75/0.98  thf('32', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_2)),
% 0.75/0.98      inference('demod', [status(thm)], ['14', '31'])).
% 0.75/0.98  thf('33', plain, (((sk_B_2) = (k1_relat_1 @ sk_D_1))),
% 0.75/0.98      inference('demod', [status(thm)], ['11', '32'])).
% 0.75/0.98  thf(t146_relat_1, axiom,
% 0.75/0.98    (![A:$i]:
% 0.75/0.98     ( ( v1_relat_1 @ A ) =>
% 0.75/0.98       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.75/0.98  thf('34', plain,
% 0.75/0.98      (![X22 : $i]:
% 0.75/0.98         (((k9_relat_1 @ X22 @ (k1_relat_1 @ X22)) = (k2_relat_1 @ X22))
% 0.75/0.98          | ~ (v1_relat_1 @ X22))),
% 0.75/0.98      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.75/0.98  thf('35', plain,
% 0.75/0.98      ((((k9_relat_1 @ sk_D_1 @ sk_B_2) = (k2_relat_1 @ sk_D_1))
% 0.75/0.98        | ~ (v1_relat_1 @ sk_D_1))),
% 0.75/0.98      inference('sup+', [status(thm)], ['33', '34'])).
% 0.75/0.98  thf('36', plain,
% 0.75/0.98      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_C)))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(cc1_relset_1, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i]:
% 0.75/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.98       ( v1_relat_1 @ C ) ))).
% 0.75/0.98  thf('37', plain,
% 0.75/0.98      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.75/0.98         ((v1_relat_1 @ X28)
% 0.75/0.98          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.75/0.98      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.75/0.98  thf('38', plain, ((v1_relat_1 @ sk_D_1)),
% 0.75/0.98      inference('sup-', [status(thm)], ['36', '37'])).
% 0.75/0.98  thf('39', plain, (((k9_relat_1 @ sk_D_1 @ sk_B_2) = (k2_relat_1 @ sk_D_1))),
% 0.75/0.98      inference('demod', [status(thm)], ['35', '38'])).
% 0.75/0.98  thf(t143_relat_1, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i]:
% 0.75/0.98     ( ( v1_relat_1 @ C ) =>
% 0.75/0.98       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.75/0.98         ( ?[D:$i]:
% 0.75/0.98           ( ( r2_hidden @ D @ B ) & 
% 0.75/0.98             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.75/0.98             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.75/0.98  thf('40', plain,
% 0.75/0.98      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.75/0.98         (~ (r2_hidden @ X20 @ (k9_relat_1 @ X21 @ X19))
% 0.75/0.98          | (r2_hidden @ (k4_tarski @ (sk_D @ X21 @ X19 @ X20) @ X20) @ X21)
% 0.75/0.98          | ~ (v1_relat_1 @ X21))),
% 0.75/0.98      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.75/0.98  thf('41', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1))
% 0.75/0.98          | ~ (v1_relat_1 @ sk_D_1)
% 0.75/0.98          | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_B_2 @ X0) @ X0) @ 
% 0.75/0.98             sk_D_1))),
% 0.75/0.98      inference('sup-', [status(thm)], ['39', '40'])).
% 0.75/0.98  thf('42', plain, ((v1_relat_1 @ sk_D_1)),
% 0.75/0.98      inference('sup-', [status(thm)], ['36', '37'])).
% 0.75/0.98  thf('43', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1))
% 0.75/0.98          | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_B_2 @ X0) @ X0) @ 
% 0.75/0.98             sk_D_1))),
% 0.75/0.98      inference('demod', [status(thm)], ['41', '42'])).
% 0.75/0.98  thf('44', plain,
% 0.75/0.98      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_B_2 @ sk_A) @ sk_A) @ 
% 0.75/0.98        sk_D_1)),
% 0.75/0.98      inference('sup-', [status(thm)], ['4', '43'])).
% 0.75/0.98  thf(t8_funct_1, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i]:
% 0.75/0.98     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.75/0.98       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.75/0.98         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.75/0.98           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.75/0.98  thf('45', plain,
% 0.75/0.98      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.75/0.98         (~ (r2_hidden @ (k4_tarski @ X23 @ X25) @ X24)
% 0.75/0.98          | ((X25) = (k1_funct_1 @ X24 @ X23))
% 0.75/0.98          | ~ (v1_funct_1 @ X24)
% 0.75/0.98          | ~ (v1_relat_1 @ X24))),
% 0.75/0.98      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.75/0.98  thf('46', plain,
% 0.75/0.98      ((~ (v1_relat_1 @ sk_D_1)
% 0.75/0.98        | ~ (v1_funct_1 @ sk_D_1)
% 0.75/0.98        | ((sk_A) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B_2 @ sk_A))))),
% 0.75/0.98      inference('sup-', [status(thm)], ['44', '45'])).
% 0.75/0.98  thf('47', plain, ((v1_relat_1 @ sk_D_1)),
% 0.75/0.98      inference('sup-', [status(thm)], ['36', '37'])).
% 0.75/0.98  thf('48', plain, ((v1_funct_1 @ sk_D_1)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('49', plain,
% 0.75/0.98      (((sk_A) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B_2 @ sk_A)))),
% 0.75/0.98      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.75/0.98  thf('50', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_1))),
% 0.75/0.98      inference('demod', [status(thm)], ['0', '3'])).
% 0.75/0.98  thf('51', plain, (((k9_relat_1 @ sk_D_1 @ sk_B_2) = (k2_relat_1 @ sk_D_1))),
% 0.75/0.98      inference('demod', [status(thm)], ['35', '38'])).
% 0.75/0.98  thf('52', plain,
% 0.75/0.98      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.75/0.98         (~ (r2_hidden @ X20 @ (k9_relat_1 @ X21 @ X19))
% 0.75/0.98          | (r2_hidden @ (sk_D @ X21 @ X19 @ X20) @ (k1_relat_1 @ X21))
% 0.75/0.98          | ~ (v1_relat_1 @ X21))),
% 0.75/0.98      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.75/0.98  thf('53', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1))
% 0.75/0.98          | ~ (v1_relat_1 @ sk_D_1)
% 0.75/0.98          | (r2_hidden @ (sk_D @ sk_D_1 @ sk_B_2 @ X0) @ (k1_relat_1 @ sk_D_1)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['51', '52'])).
% 0.75/0.98  thf('54', plain, ((v1_relat_1 @ sk_D_1)),
% 0.75/0.98      inference('sup-', [status(thm)], ['36', '37'])).
% 0.75/0.98  thf('55', plain, (((sk_B_2) = (k1_relat_1 @ sk_D_1))),
% 0.75/0.98      inference('demod', [status(thm)], ['11', '32'])).
% 0.75/0.98  thf('56', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1))
% 0.75/0.98          | (r2_hidden @ (sk_D @ sk_D_1 @ sk_B_2 @ X0) @ sk_B_2))),
% 0.75/0.98      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.75/0.98  thf('57', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_B_2 @ sk_A) @ sk_B_2)),
% 0.75/0.98      inference('sup-', [status(thm)], ['50', '56'])).
% 0.75/0.98  thf(t1_subset, axiom,
% 0.75/0.98    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.75/0.98  thf('58', plain,
% 0.75/0.98      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.75/0.98      inference('cnf', [status(esa)], [t1_subset])).
% 0.75/0.98  thf('59', plain, ((m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B_2 @ sk_A) @ sk_B_2)),
% 0.75/0.98      inference('sup-', [status(thm)], ['57', '58'])).
% 0.75/0.98  thf('60', plain,
% 0.75/0.98      (![X48 : $i]:
% 0.75/0.98         (((sk_A) != (k1_funct_1 @ sk_D_1 @ X48))
% 0.75/0.98          | ~ (m1_subset_1 @ X48 @ sk_B_2))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('61', plain,
% 0.75/0.98      (((sk_A) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B_2 @ sk_A)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['59', '60'])).
% 0.75/0.98  thf('62', plain, ($false),
% 0.75/0.98      inference('simplify_reflect-', [status(thm)], ['49', '61'])).
% 0.75/0.98  
% 0.75/0.98  % SZS output end Refutation
% 0.75/0.98  
% 0.75/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
