%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pX7fs75Sh1

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:06 EST 2020

% Result     : Theorem 1.04s
% Output     : Refutation 1.04s
% Verified   : 
% Statistics : Number of formulae       :  249 (2107 expanded)
%              Number of leaves         :   51 ( 632 expanded)
%              Depth                    :   31
%              Number of atoms          : 1701 (22399 expanded)
%              Number of equality atoms :  184 (2037 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(t8_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ C )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_funct_2])).

thf('0',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k2_relset_1 @ X34 @ X35 @ X33 )
        = ( k2_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C_1 ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t14_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X36 ) @ X37 )
      | ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

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

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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

thf('9',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( zip_tseitin_0 @ X45 @ X46 )
      | ( zip_tseitin_1 @ X47 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('13',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_0 @ X40 @ X41 )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( zip_tseitin_0 @ X45 @ X46 )
      | ( zip_tseitin_1 @ X47 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('17',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ( X42
        = ( k1_relset_1 @ X42 @ X43 @ X44 ) )
      | ~ ( zip_tseitin_1 @ X44 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('24',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['29','31'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('33',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X9 ) @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('34',plain,(
    ! [X8: $i] :
      ( ( k2_subset_1 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('35',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('37',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( zip_tseitin_0 @ X45 @ X46 )
      | ( zip_tseitin_1 @ X47 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_0 @ X40 @ X41 )
      | ( X41 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('41',plain,(
    ! [X40: $i] :
      ( zip_tseitin_0 @ X40 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('44',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['27'])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('48',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('51',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('52',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_D @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','52'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('54',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('55',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('57',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('59',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v4_relat_1 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('62',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X21
        = ( k7_relat_1 @ X21 @ X22 ) )
      | ~ ( v4_relat_1 @ X21 @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('65',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('66',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('67',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','68'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('70',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) )
        = ( k9_relat_1 @ X17 @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','67'])).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('73',plain,(
    ! [X16: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X16 ) )
      | ~ ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('74',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('76',plain,(
    ! [X23: $i] :
      ( ( ( k1_relat_1 @ X23 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X23 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','78'])).

thf('80',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('81',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','67'])).

thf('83',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['71','81','82'])).

thf('84',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_D @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','52'])).

thf(t152_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf('85',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X20 )
      | ~ ( r1_tarski @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( ( k9_relat_1 @ X20 @ X19 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t152_relat_1])).

thf('86',plain,
    ( ! [X0: $i] :
        ( ( ( k9_relat_1 @ X0 @ sk_D )
         != k1_xboole_0 )
        | ~ ( v1_relat_1 @ X0 )
        | ( sk_D = k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','67'])).

thf('89',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','90'])).

thf('92',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('93',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
        = ( k1_relat_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['79','80'])).

thf('95',plain,(
    ! [X23: $i] :
      ( ( ( k2_relat_1 @ X23 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X23 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('96',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','67'])).

thf('98',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['93','99'])).

thf('101',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( X42
       != ( k1_relset_1 @ X42 @ X43 @ X44 ) )
      | ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ~ ( zip_tseitin_1 @ X44 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('102',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X1 != k1_xboole_0 )
        | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
        | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ! [X0: $i] :
        ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
        | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','103'])).

thf('105',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['89'])).

thf('106',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['27'])).

thf('107',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['30'])).

thf('108',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['105','108'])).

thf('110',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['104','109'])).

thf('111',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('112',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['27'])).

thf('115',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['30'])).

thf('116',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1 ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['113','116'])).

thf('118',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('119',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('120',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('122',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['117','120','121'])).

thf('123',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['30'])).

thf('124',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['27'])).

thf('125',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['32','110','122','123','124'])).

thf('126',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['28','125'])).

thf('127',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['26','126'])).

thf('128',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['13','127'])).

thf('129',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( X42
       != ( k1_relset_1 @ X42 @ X43 @ X44 ) )
      | ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ~ ( zip_tseitin_1 @ X44 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('130',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['30'])).

thf('133',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('134',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['30'])).

thf('135',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['30'])).

thf('137',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['32','135','136'])).

thf('138',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['132','137'])).

thf('139',plain,(
    ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['131','138'])).

thf('140',plain,(
    ~ ( zip_tseitin_0 @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['10','139'])).

thf('141',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_0 @ X40 @ X41 )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('142',plain,(
    ~ ( zip_tseitin_0 @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['10','139'])).

thf('143',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ~ ( zip_tseitin_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['140','143'])).

thf('145',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('146',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('150',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X20 )
      | ~ ( r1_tarski @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( ( k9_relat_1 @ X20 @ X19 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t152_relat_1])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ( ( k9_relat_1 @ sk_D @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('154',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ( ( k9_relat_1 @ sk_D @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['151','154'])).

thf('156',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['28','125'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k9_relat_1 @ sk_D @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['155','156'])).

thf('158',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k9_relat_1 @ sk_D @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['148','157'])).

thf('159',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v4_relat_1 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('161',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X21
        = ( k7_relat_1 @ X21 @ X22 ) )
      | ~ ( v4_relat_1 @ X21 @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('163',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_A ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['152','153'])).

thf('165',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) )
        = ( k9_relat_1 @ X17 @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('167',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k9_relat_1 @ sk_D @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['165','166'])).

thf('168',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['152','153'])).

thf('169',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k9_relat_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_D )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['158','169'])).

thf('171',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('172',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('173',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('175',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['98'])).

thf('176',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X20 )
      | ~ ( r1_tarski @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( ( k9_relat_1 @ X20 @ X19 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t152_relat_1])).

thf('177',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','67'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['71','81','82'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( k1_xboole_0 != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['174','182'])).

thf('184',plain,
    ( ( sk_D = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['173','183'])).

thf('185',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['141','142'])).

thf('186',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('187',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('188',plain,(
    sk_D = k1_xboole_0 ),
    inference(demod,[status(thm)],['184','185','186','187'])).

thf('189',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['79','80'])).

thf('190',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['170','188','189'])).

thf('191',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_0 @ X40 @ X41 )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('193',plain,(
    ! [X40: $i] :
      ( zip_tseitin_0 @ X40 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('194',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['194'])).

thf('196',plain,(
    $false ),
    inference(demod,[status(thm)],['144','191','195'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pX7fs75Sh1
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:52:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.04/1.24  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.04/1.24  % Solved by: fo/fo7.sh
% 1.04/1.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.04/1.24  % done 1294 iterations in 0.789s
% 1.04/1.24  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.04/1.24  % SZS output start Refutation
% 1.04/1.24  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.04/1.24  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.04/1.24  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.04/1.24  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.04/1.24  thf(sk_A_type, type, sk_A: $i).
% 1.04/1.24  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.04/1.24  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.04/1.24  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.04/1.24  thf(sk_D_type, type, sk_D: $i).
% 1.04/1.24  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.04/1.24  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.04/1.24  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.04/1.24  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.04/1.24  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.04/1.24  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.04/1.24  thf(sk_B_type, type, sk_B: $i).
% 1.04/1.24  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.04/1.24  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.04/1.24  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.04/1.24  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.04/1.24  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.04/1.24  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.04/1.24  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.04/1.24  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.04/1.24  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.04/1.24  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.04/1.24  thf(t8_funct_2, conjecture,
% 1.04/1.24    (![A:$i,B:$i,C:$i,D:$i]:
% 1.04/1.24     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.04/1.24         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.04/1.24       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 1.04/1.24         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.04/1.24           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 1.04/1.24             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 1.04/1.24  thf(zf_stmt_0, negated_conjecture,
% 1.04/1.24    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.04/1.24        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.04/1.24            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.04/1.24          ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 1.04/1.24            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.04/1.24              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 1.04/1.24                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 1.04/1.24    inference('cnf.neg', [status(esa)], [t8_funct_2])).
% 1.04/1.24  thf('0', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ sk_C_1)),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf('1', plain,
% 1.04/1.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf(redefinition_k2_relset_1, axiom,
% 1.04/1.24    (![A:$i,B:$i,C:$i]:
% 1.04/1.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.04/1.24       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.04/1.24  thf('2', plain,
% 1.04/1.24      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.04/1.24         (((k2_relset_1 @ X34 @ X35 @ X33) = (k2_relat_1 @ X33))
% 1.04/1.24          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 1.04/1.24      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.04/1.24  thf('3', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.04/1.24      inference('sup-', [status(thm)], ['1', '2'])).
% 1.04/1.24  thf('4', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C_1)),
% 1.04/1.24      inference('demod', [status(thm)], ['0', '3'])).
% 1.04/1.24  thf('5', plain,
% 1.04/1.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf(t14_relset_1, axiom,
% 1.04/1.24    (![A:$i,B:$i,C:$i,D:$i]:
% 1.04/1.24     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 1.04/1.24       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 1.04/1.24         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 1.04/1.24  thf('6', plain,
% 1.04/1.24      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 1.04/1.24         (~ (r1_tarski @ (k2_relat_1 @ X36) @ X37)
% 1.04/1.24          | (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 1.04/1.24          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 1.04/1.24      inference('cnf', [status(esa)], [t14_relset_1])).
% 1.04/1.24  thf('7', plain,
% 1.04/1.24      (![X0 : $i]:
% 1.04/1.24         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.04/1.24          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 1.04/1.24      inference('sup-', [status(thm)], ['5', '6'])).
% 1.04/1.24  thf('8', plain,
% 1.04/1.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['4', '7'])).
% 1.04/1.24  thf(d1_funct_2, axiom,
% 1.04/1.24    (![A:$i,B:$i,C:$i]:
% 1.04/1.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.04/1.24       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.04/1.24           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.04/1.24             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.04/1.24         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.04/1.24           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.04/1.24             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.04/1.24  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.04/1.24  thf(zf_stmt_2, axiom,
% 1.04/1.24    (![C:$i,B:$i,A:$i]:
% 1.04/1.24     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.04/1.24       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.04/1.24  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.04/1.24  thf(zf_stmt_4, axiom,
% 1.04/1.24    (![B:$i,A:$i]:
% 1.04/1.24     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.04/1.24       ( zip_tseitin_0 @ B @ A ) ))).
% 1.04/1.24  thf(zf_stmt_5, axiom,
% 1.04/1.24    (![A:$i,B:$i,C:$i]:
% 1.04/1.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.04/1.24       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.04/1.24         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.04/1.24           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.04/1.24             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.04/1.24  thf('9', plain,
% 1.04/1.24      (![X45 : $i, X46 : $i, X47 : $i]:
% 1.04/1.24         (~ (zip_tseitin_0 @ X45 @ X46)
% 1.04/1.24          | (zip_tseitin_1 @ X47 @ X45 @ X46)
% 1.04/1.24          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45))))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.04/1.24  thf('10', plain,
% 1.04/1.24      (((zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)
% 1.04/1.24        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_A))),
% 1.04/1.24      inference('sup-', [status(thm)], ['8', '9'])).
% 1.04/1.24  thf('11', plain,
% 1.04/1.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['4', '7'])).
% 1.04/1.24  thf(redefinition_k1_relset_1, axiom,
% 1.04/1.24    (![A:$i,B:$i,C:$i]:
% 1.04/1.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.04/1.24       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.04/1.24  thf('12', plain,
% 1.04/1.24      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.04/1.24         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 1.04/1.24          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 1.04/1.24      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.04/1.24  thf('13', plain,
% 1.04/1.24      (((k1_relset_1 @ sk_A @ sk_C_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.04/1.24      inference('sup-', [status(thm)], ['11', '12'])).
% 1.04/1.24  thf('14', plain,
% 1.04/1.24      (![X40 : $i, X41 : $i]:
% 1.04/1.24         ((zip_tseitin_0 @ X40 @ X41) | ((X40) = (k1_xboole_0)))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.04/1.24  thf('15', plain,
% 1.04/1.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf('16', plain,
% 1.04/1.24      (![X45 : $i, X46 : $i, X47 : $i]:
% 1.04/1.24         (~ (zip_tseitin_0 @ X45 @ X46)
% 1.04/1.24          | (zip_tseitin_1 @ X47 @ X45 @ X46)
% 1.04/1.24          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45))))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.04/1.24  thf('17', plain,
% 1.04/1.24      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.04/1.24      inference('sup-', [status(thm)], ['15', '16'])).
% 1.04/1.24  thf('18', plain,
% 1.04/1.24      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 1.04/1.24      inference('sup-', [status(thm)], ['14', '17'])).
% 1.04/1.24  thf('19', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf('20', plain,
% 1.04/1.24      (![X42 : $i, X43 : $i, X44 : $i]:
% 1.04/1.24         (~ (v1_funct_2 @ X44 @ X42 @ X43)
% 1.04/1.24          | ((X42) = (k1_relset_1 @ X42 @ X43 @ X44))
% 1.04/1.24          | ~ (zip_tseitin_1 @ X44 @ X43 @ X42))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.04/1.24  thf('21', plain,
% 1.04/1.24      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 1.04/1.24        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['19', '20'])).
% 1.04/1.24  thf('22', plain,
% 1.04/1.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf('23', plain,
% 1.04/1.24      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.04/1.24         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 1.04/1.24          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 1.04/1.24      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.04/1.24  thf('24', plain,
% 1.04/1.24      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.04/1.24      inference('sup-', [status(thm)], ['22', '23'])).
% 1.04/1.24  thf('25', plain,
% 1.04/1.24      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.04/1.24      inference('demod', [status(thm)], ['21', '24'])).
% 1.04/1.24  thf('26', plain,
% 1.04/1.24      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['18', '25'])).
% 1.04/1.24  thf('27', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf('28', plain,
% 1.04/1.24      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.04/1.24      inference('split', [status(esa)], ['27'])).
% 1.04/1.24  thf('29', plain, ((v1_funct_1 @ sk_D)),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf('30', plain,
% 1.04/1.24      ((~ (v1_funct_1 @ sk_D)
% 1.04/1.24        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)
% 1.04/1.24        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf('31', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 1.04/1.24      inference('split', [status(esa)], ['30'])).
% 1.04/1.24  thf('32', plain, (((v1_funct_1 @ sk_D))),
% 1.04/1.24      inference('sup-', [status(thm)], ['29', '31'])).
% 1.04/1.24  thf(dt_k2_subset_1, axiom,
% 1.04/1.24    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.04/1.24  thf('33', plain,
% 1.04/1.24      (![X9 : $i]: (m1_subset_1 @ (k2_subset_1 @ X9) @ (k1_zfmisc_1 @ X9))),
% 1.04/1.24      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 1.04/1.24  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.04/1.24  thf('34', plain, (![X8 : $i]: ((k2_subset_1 @ X8) = (X8))),
% 1.04/1.24      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.04/1.24  thf('35', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 1.04/1.24      inference('demod', [status(thm)], ['33', '34'])).
% 1.04/1.24  thf(t113_zfmisc_1, axiom,
% 1.04/1.24    (![A:$i,B:$i]:
% 1.04/1.24     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.04/1.24       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.04/1.24  thf('36', plain,
% 1.04/1.24      (![X6 : $i, X7 : $i]:
% 1.04/1.24         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 1.04/1.24      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.04/1.24  thf('37', plain,
% 1.04/1.24      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 1.04/1.24      inference('simplify', [status(thm)], ['36'])).
% 1.04/1.24  thf('38', plain,
% 1.04/1.24      (![X45 : $i, X46 : $i, X47 : $i]:
% 1.04/1.24         (~ (zip_tseitin_0 @ X45 @ X46)
% 1.04/1.24          | (zip_tseitin_1 @ X47 @ X45 @ X46)
% 1.04/1.24          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45))))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.04/1.24  thf('39', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]:
% 1.04/1.24         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.04/1.24          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 1.04/1.24          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 1.04/1.24      inference('sup-', [status(thm)], ['37', '38'])).
% 1.04/1.24  thf('40', plain,
% 1.04/1.24      (![X40 : $i, X41 : $i]:
% 1.04/1.24         ((zip_tseitin_0 @ X40 @ X41) | ((X41) != (k1_xboole_0)))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.04/1.24  thf('41', plain, (![X40 : $i]: (zip_tseitin_0 @ X40 @ k1_xboole_0)),
% 1.04/1.24      inference('simplify', [status(thm)], ['40'])).
% 1.04/1.24  thf('42', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]:
% 1.04/1.24         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.04/1.24          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 1.04/1.24      inference('demod', [status(thm)], ['39', '41'])).
% 1.04/1.24  thf('43', plain,
% 1.04/1.24      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.04/1.24      inference('sup-', [status(thm)], ['35', '42'])).
% 1.04/1.24  thf(d3_tarski, axiom,
% 1.04/1.24    (![A:$i,B:$i]:
% 1.04/1.24     ( ( r1_tarski @ A @ B ) <=>
% 1.04/1.24       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.04/1.24  thf('44', plain,
% 1.04/1.24      (![X1 : $i, X3 : $i]:
% 1.04/1.24         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.04/1.24      inference('cnf', [status(esa)], [d3_tarski])).
% 1.04/1.24  thf('45', plain,
% 1.04/1.24      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.04/1.24      inference('split', [status(esa)], ['27'])).
% 1.04/1.24  thf('46', plain,
% 1.04/1.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf('47', plain,
% 1.04/1.24      (((m1_subset_1 @ sk_D @ 
% 1.04/1.24         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 1.04/1.24         <= ((((sk_A) = (k1_xboole_0))))),
% 1.04/1.24      inference('sup+', [status(thm)], ['45', '46'])).
% 1.04/1.24  thf(t5_subset, axiom,
% 1.04/1.24    (![A:$i,B:$i,C:$i]:
% 1.04/1.24     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.04/1.24          ( v1_xboole_0 @ C ) ) ))).
% 1.04/1.24  thf('48', plain,
% 1.04/1.24      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.04/1.24         (~ (r2_hidden @ X13 @ X14)
% 1.04/1.24          | ~ (v1_xboole_0 @ X15)
% 1.04/1.24          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 1.04/1.24      inference('cnf', [status(esa)], [t5_subset])).
% 1.04/1.24  thf('49', plain,
% 1.04/1.24      ((![X0 : $i]:
% 1.04/1.24          (~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))
% 1.04/1.24           | ~ (r2_hidden @ X0 @ sk_D)))
% 1.04/1.24         <= ((((sk_A) = (k1_xboole_0))))),
% 1.04/1.24      inference('sup-', [status(thm)], ['47', '48'])).
% 1.04/1.24  thf('50', plain,
% 1.04/1.24      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 1.04/1.24      inference('simplify', [status(thm)], ['36'])).
% 1.04/1.24  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.04/1.24  thf('51', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.04/1.24      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.04/1.24  thf('52', plain,
% 1.04/1.24      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D)) <= ((((sk_A) = (k1_xboole_0))))),
% 1.04/1.24      inference('demod', [status(thm)], ['49', '50', '51'])).
% 1.04/1.24  thf('53', plain,
% 1.04/1.24      ((![X0 : $i]: (r1_tarski @ sk_D @ X0)) <= ((((sk_A) = (k1_xboole_0))))),
% 1.04/1.24      inference('sup-', [status(thm)], ['44', '52'])).
% 1.04/1.24  thf(t3_subset, axiom,
% 1.04/1.24    (![A:$i,B:$i]:
% 1.04/1.24     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.04/1.24  thf('54', plain,
% 1.04/1.24      (![X10 : $i, X12 : $i]:
% 1.04/1.24         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 1.04/1.24      inference('cnf', [status(esa)], [t3_subset])).
% 1.04/1.24  thf('55', plain,
% 1.04/1.24      ((![X0 : $i]: (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0)))
% 1.04/1.24         <= ((((sk_A) = (k1_xboole_0))))),
% 1.04/1.24      inference('sup-', [status(thm)], ['53', '54'])).
% 1.04/1.24  thf('56', plain,
% 1.04/1.24      (![X6 : $i, X7 : $i]:
% 1.04/1.24         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 1.04/1.24      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.04/1.24  thf('57', plain,
% 1.04/1.24      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 1.04/1.24      inference('simplify', [status(thm)], ['56'])).
% 1.04/1.24  thf('58', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 1.04/1.24      inference('demod', [status(thm)], ['33', '34'])).
% 1.04/1.24  thf(cc2_relset_1, axiom,
% 1.04/1.24    (![A:$i,B:$i,C:$i]:
% 1.04/1.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.04/1.24       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.04/1.24  thf('59', plain,
% 1.04/1.24      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.04/1.24         ((v4_relat_1 @ X27 @ X28)
% 1.04/1.24          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 1.04/1.24      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.04/1.24  thf('60', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]: (v4_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X1)),
% 1.04/1.24      inference('sup-', [status(thm)], ['58', '59'])).
% 1.04/1.24  thf('61', plain, (![X0 : $i]: (v4_relat_1 @ k1_xboole_0 @ X0)),
% 1.04/1.24      inference('sup+', [status(thm)], ['57', '60'])).
% 1.04/1.24  thf(t209_relat_1, axiom,
% 1.04/1.24    (![A:$i,B:$i]:
% 1.04/1.24     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.04/1.24       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 1.04/1.24  thf('62', plain,
% 1.04/1.24      (![X21 : $i, X22 : $i]:
% 1.04/1.24         (((X21) = (k7_relat_1 @ X21 @ X22))
% 1.04/1.24          | ~ (v4_relat_1 @ X21 @ X22)
% 1.04/1.24          | ~ (v1_relat_1 @ X21))),
% 1.04/1.24      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.04/1.24  thf('63', plain,
% 1.04/1.24      (![X0 : $i]:
% 1.04/1.24         (~ (v1_relat_1 @ k1_xboole_0)
% 1.04/1.24          | ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['61', '62'])).
% 1.04/1.24  thf('64', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 1.04/1.24      inference('demod', [status(thm)], ['33', '34'])).
% 1.04/1.24  thf('65', plain,
% 1.04/1.24      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 1.04/1.24      inference('simplify', [status(thm)], ['56'])).
% 1.04/1.24  thf(cc1_relset_1, axiom,
% 1.04/1.24    (![A:$i,B:$i,C:$i]:
% 1.04/1.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.04/1.24       ( v1_relat_1 @ C ) ))).
% 1.04/1.24  thf('66', plain,
% 1.04/1.24      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.04/1.24         ((v1_relat_1 @ X24)
% 1.04/1.24          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 1.04/1.24      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.04/1.24  thf('67', plain,
% 1.04/1.24      (![X1 : $i]:
% 1.04/1.24         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.04/1.24          | (v1_relat_1 @ X1))),
% 1.04/1.24      inference('sup-', [status(thm)], ['65', '66'])).
% 1.04/1.24  thf('68', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.04/1.24      inference('sup-', [status(thm)], ['64', '67'])).
% 1.04/1.24  thf('69', plain,
% 1.04/1.24      (![X0 : $i]: ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0))),
% 1.04/1.24      inference('demod', [status(thm)], ['63', '68'])).
% 1.04/1.24  thf(t148_relat_1, axiom,
% 1.04/1.24    (![A:$i,B:$i]:
% 1.04/1.24     ( ( v1_relat_1 @ B ) =>
% 1.04/1.24       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 1.04/1.24  thf('70', plain,
% 1.04/1.24      (![X17 : $i, X18 : $i]:
% 1.04/1.24         (((k2_relat_1 @ (k7_relat_1 @ X17 @ X18)) = (k9_relat_1 @ X17 @ X18))
% 1.04/1.24          | ~ (v1_relat_1 @ X17))),
% 1.04/1.24      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.04/1.24  thf('71', plain,
% 1.04/1.24      (![X0 : $i]:
% 1.04/1.24         (((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))
% 1.04/1.24          | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.04/1.24      inference('sup+', [status(thm)], ['69', '70'])).
% 1.04/1.24  thf('72', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.04/1.24      inference('sup-', [status(thm)], ['64', '67'])).
% 1.04/1.24  thf(fc10_relat_1, axiom,
% 1.04/1.24    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 1.04/1.24  thf('73', plain,
% 1.04/1.24      (![X16 : $i]:
% 1.04/1.24         ((v1_xboole_0 @ (k1_relat_1 @ X16)) | ~ (v1_xboole_0 @ X16))),
% 1.04/1.24      inference('cnf', [status(esa)], [fc10_relat_1])).
% 1.04/1.24  thf(l13_xboole_0, axiom,
% 1.04/1.24    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.04/1.24  thf('74', plain,
% 1.04/1.24      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 1.04/1.24      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.04/1.24  thf('75', plain,
% 1.04/1.24      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['73', '74'])).
% 1.04/1.24  thf(t65_relat_1, axiom,
% 1.04/1.24    (![A:$i]:
% 1.04/1.24     ( ( v1_relat_1 @ A ) =>
% 1.04/1.24       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 1.04/1.24         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 1.04/1.24  thf('76', plain,
% 1.04/1.24      (![X23 : $i]:
% 1.04/1.24         (((k1_relat_1 @ X23) != (k1_xboole_0))
% 1.04/1.24          | ((k2_relat_1 @ X23) = (k1_xboole_0))
% 1.04/1.24          | ~ (v1_relat_1 @ X23))),
% 1.04/1.24      inference('cnf', [status(esa)], [t65_relat_1])).
% 1.04/1.24  thf('77', plain,
% 1.04/1.24      (![X0 : $i]:
% 1.04/1.24         (((k1_xboole_0) != (k1_xboole_0))
% 1.04/1.24          | ~ (v1_xboole_0 @ X0)
% 1.04/1.24          | ~ (v1_relat_1 @ X0)
% 1.04/1.24          | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['75', '76'])).
% 1.04/1.24  thf('78', plain,
% 1.04/1.24      (![X0 : $i]:
% 1.04/1.24         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.04/1.24          | ~ (v1_relat_1 @ X0)
% 1.04/1.24          | ~ (v1_xboole_0 @ X0))),
% 1.04/1.24      inference('simplify', [status(thm)], ['77'])).
% 1.04/1.24  thf('79', plain,
% 1.04/1.24      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.04/1.24        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['72', '78'])).
% 1.04/1.24  thf('80', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.04/1.24      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.04/1.24  thf('81', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.04/1.24      inference('demod', [status(thm)], ['79', '80'])).
% 1.04/1.24  thf('82', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.04/1.24      inference('sup-', [status(thm)], ['64', '67'])).
% 1.04/1.24  thf('83', plain,
% 1.04/1.24      (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))),
% 1.04/1.24      inference('demod', [status(thm)], ['71', '81', '82'])).
% 1.04/1.24  thf('84', plain,
% 1.04/1.24      ((![X0 : $i]: (r1_tarski @ sk_D @ X0)) <= ((((sk_A) = (k1_xboole_0))))),
% 1.04/1.24      inference('sup-', [status(thm)], ['44', '52'])).
% 1.04/1.24  thf(t152_relat_1, axiom,
% 1.04/1.24    (![A:$i,B:$i]:
% 1.04/1.24     ( ( v1_relat_1 @ B ) =>
% 1.04/1.24       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.04/1.24            ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 1.04/1.24            ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 1.04/1.24  thf('85', plain,
% 1.04/1.24      (![X19 : $i, X20 : $i]:
% 1.04/1.24         (((X19) = (k1_xboole_0))
% 1.04/1.24          | ~ (v1_relat_1 @ X20)
% 1.04/1.24          | ~ (r1_tarski @ X19 @ (k1_relat_1 @ X20))
% 1.04/1.24          | ((k9_relat_1 @ X20 @ X19) != (k1_xboole_0)))),
% 1.04/1.24      inference('cnf', [status(esa)], [t152_relat_1])).
% 1.04/1.24  thf('86', plain,
% 1.04/1.24      ((![X0 : $i]:
% 1.04/1.24          (((k9_relat_1 @ X0 @ sk_D) != (k1_xboole_0))
% 1.04/1.24           | ~ (v1_relat_1 @ X0)
% 1.04/1.24           | ((sk_D) = (k1_xboole_0))))
% 1.04/1.24         <= ((((sk_A) = (k1_xboole_0))))),
% 1.04/1.24      inference('sup-', [status(thm)], ['84', '85'])).
% 1.04/1.24  thf('87', plain,
% 1.04/1.24      (((((k1_xboole_0) != (k1_xboole_0))
% 1.04/1.24         | ((sk_D) = (k1_xboole_0))
% 1.04/1.24         | ~ (v1_relat_1 @ k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.04/1.24      inference('sup-', [status(thm)], ['83', '86'])).
% 1.04/1.24  thf('88', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.04/1.24      inference('sup-', [status(thm)], ['64', '67'])).
% 1.04/1.24  thf('89', plain,
% 1.04/1.24      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_D) = (k1_xboole_0))))
% 1.04/1.24         <= ((((sk_A) = (k1_xboole_0))))),
% 1.04/1.24      inference('demod', [status(thm)], ['87', '88'])).
% 1.04/1.24  thf('90', plain,
% 1.04/1.24      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.04/1.24      inference('simplify', [status(thm)], ['89'])).
% 1.04/1.24  thf('91', plain,
% 1.04/1.24      ((![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))
% 1.04/1.24         <= ((((sk_A) = (k1_xboole_0))))),
% 1.04/1.24      inference('demod', [status(thm)], ['55', '90'])).
% 1.04/1.24  thf('92', plain,
% 1.04/1.24      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.04/1.24         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 1.04/1.24          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 1.04/1.24      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.04/1.24  thf('93', plain,
% 1.04/1.24      ((![X0 : $i, X1 : $i]:
% 1.04/1.24          ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))
% 1.04/1.24         <= ((((sk_A) = (k1_xboole_0))))),
% 1.04/1.24      inference('sup-', [status(thm)], ['91', '92'])).
% 1.04/1.24  thf('94', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.04/1.24      inference('demod', [status(thm)], ['79', '80'])).
% 1.04/1.24  thf('95', plain,
% 1.04/1.24      (![X23 : $i]:
% 1.04/1.24         (((k2_relat_1 @ X23) != (k1_xboole_0))
% 1.04/1.24          | ((k1_relat_1 @ X23) = (k1_xboole_0))
% 1.04/1.24          | ~ (v1_relat_1 @ X23))),
% 1.04/1.24      inference('cnf', [status(esa)], [t65_relat_1])).
% 1.04/1.24  thf('96', plain,
% 1.04/1.24      ((((k1_xboole_0) != (k1_xboole_0))
% 1.04/1.24        | ~ (v1_relat_1 @ k1_xboole_0)
% 1.04/1.24        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['94', '95'])).
% 1.04/1.24  thf('97', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.04/1.24      inference('sup-', [status(thm)], ['64', '67'])).
% 1.04/1.24  thf('98', plain,
% 1.04/1.24      ((((k1_xboole_0) != (k1_xboole_0))
% 1.04/1.24        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 1.04/1.24      inference('demod', [status(thm)], ['96', '97'])).
% 1.04/1.24  thf('99', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.04/1.24      inference('simplify', [status(thm)], ['98'])).
% 1.04/1.24  thf('100', plain,
% 1.04/1.24      ((![X0 : $i, X1 : $i]:
% 1.04/1.24          ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))
% 1.04/1.24         <= ((((sk_A) = (k1_xboole_0))))),
% 1.04/1.24      inference('demod', [status(thm)], ['93', '99'])).
% 1.04/1.24  thf('101', plain,
% 1.04/1.24      (![X42 : $i, X43 : $i, X44 : $i]:
% 1.04/1.24         (((X42) != (k1_relset_1 @ X42 @ X43 @ X44))
% 1.04/1.24          | (v1_funct_2 @ X44 @ X42 @ X43)
% 1.04/1.24          | ~ (zip_tseitin_1 @ X44 @ X43 @ X42))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.04/1.24  thf('102', plain,
% 1.04/1.24      ((![X0 : $i, X1 : $i]:
% 1.04/1.24          (((X1) != (k1_xboole_0))
% 1.04/1.24           | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 1.04/1.24           | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0)))
% 1.04/1.24         <= ((((sk_A) = (k1_xboole_0))))),
% 1.04/1.24      inference('sup-', [status(thm)], ['100', '101'])).
% 1.04/1.24  thf('103', plain,
% 1.04/1.24      ((![X0 : $i]:
% 1.04/1.24          ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.04/1.24           | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)))
% 1.04/1.24         <= ((((sk_A) = (k1_xboole_0))))),
% 1.04/1.24      inference('simplify', [status(thm)], ['102'])).
% 1.04/1.24  thf('104', plain,
% 1.04/1.24      ((![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0))
% 1.04/1.24         <= ((((sk_A) = (k1_xboole_0))))),
% 1.04/1.24      inference('sup-', [status(thm)], ['43', '103'])).
% 1.04/1.24  thf('105', plain,
% 1.04/1.24      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.04/1.24      inference('simplify', [status(thm)], ['89'])).
% 1.04/1.24  thf('106', plain,
% 1.04/1.24      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.04/1.24      inference('split', [status(esa)], ['27'])).
% 1.04/1.24  thf('107', plain,
% 1.04/1.24      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 1.04/1.24         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 1.04/1.24      inference('split', [status(esa)], ['30'])).
% 1.04/1.24  thf('108', plain,
% 1.04/1.24      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1))
% 1.04/1.24         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 1.04/1.24             (((sk_A) = (k1_xboole_0))))),
% 1.04/1.24      inference('sup-', [status(thm)], ['106', '107'])).
% 1.04/1.24  thf('109', plain,
% 1.04/1.24      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1))
% 1.04/1.24         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 1.04/1.24             (((sk_A) = (k1_xboole_0))))),
% 1.04/1.24      inference('sup-', [status(thm)], ['105', '108'])).
% 1.04/1.24  thf('110', plain,
% 1.04/1.24      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | ~ (((sk_A) = (k1_xboole_0)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['104', '109'])).
% 1.04/1.24  thf('111', plain,
% 1.04/1.24      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 1.04/1.24      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.04/1.24  thf('112', plain,
% 1.04/1.24      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 1.04/1.24      inference('simplify', [status(thm)], ['36'])).
% 1.04/1.24  thf('113', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]:
% 1.04/1.24         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.04/1.24      inference('sup+', [status(thm)], ['111', '112'])).
% 1.04/1.24  thf('114', plain,
% 1.04/1.24      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.04/1.24      inference('split', [status(esa)], ['27'])).
% 1.04/1.24  thf('115', plain,
% 1.04/1.24      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 1.04/1.24         <= (~
% 1.04/1.24             ((m1_subset_1 @ sk_D @ 
% 1.04/1.24               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))))),
% 1.04/1.24      inference('split', [status(esa)], ['30'])).
% 1.04/1.24  thf('116', plain,
% 1.04/1.24      ((~ (m1_subset_1 @ sk_D @ 
% 1.04/1.24           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1))))
% 1.04/1.24         <= (~
% 1.04/1.24             ((m1_subset_1 @ sk_D @ 
% 1.04/1.24               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) & 
% 1.04/1.24             (((sk_A) = (k1_xboole_0))))),
% 1.04/1.24      inference('sup-', [status(thm)], ['114', '115'])).
% 1.04/1.24  thf('117', plain,
% 1.04/1.24      (((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.04/1.24         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 1.04/1.24         <= (~
% 1.04/1.24             ((m1_subset_1 @ sk_D @ 
% 1.04/1.24               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) & 
% 1.04/1.24             (((sk_A) = (k1_xboole_0))))),
% 1.04/1.24      inference('sup-', [status(thm)], ['113', '116'])).
% 1.04/1.24  thf('118', plain,
% 1.04/1.24      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 1.04/1.24      inference('simplify', [status(thm)], ['36'])).
% 1.04/1.24  thf('119', plain,
% 1.04/1.24      (((m1_subset_1 @ sk_D @ 
% 1.04/1.24         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 1.04/1.24         <= ((((sk_A) = (k1_xboole_0))))),
% 1.04/1.24      inference('sup+', [status(thm)], ['45', '46'])).
% 1.04/1.24  thf('120', plain,
% 1.04/1.24      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 1.04/1.24         <= ((((sk_A) = (k1_xboole_0))))),
% 1.04/1.24      inference('sup+', [status(thm)], ['118', '119'])).
% 1.04/1.24  thf('121', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.04/1.24      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.04/1.24  thf('122', plain,
% 1.04/1.24      (~ (((sk_A) = (k1_xboole_0))) | 
% 1.04/1.24       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 1.04/1.24      inference('demod', [status(thm)], ['117', '120', '121'])).
% 1.04/1.24  thf('123', plain,
% 1.04/1.24      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) | 
% 1.04/1.24       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | ~ ((v1_funct_1 @ sk_D))),
% 1.04/1.24      inference('split', [status(esa)], ['30'])).
% 1.04/1.24  thf('124', plain,
% 1.04/1.24      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 1.04/1.24      inference('split', [status(esa)], ['27'])).
% 1.04/1.24  thf('125', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 1.04/1.24      inference('sat_resolution*', [status(thm)],
% 1.04/1.24                ['32', '110', '122', '123', '124'])).
% 1.04/1.24  thf('126', plain, (((sk_B) != (k1_xboole_0))),
% 1.04/1.24      inference('simpl_trail', [status(thm)], ['28', '125'])).
% 1.04/1.24  thf('127', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 1.04/1.24      inference('simplify_reflect-', [status(thm)], ['26', '126'])).
% 1.04/1.24  thf('128', plain, (((k1_relset_1 @ sk_A @ sk_C_1 @ sk_D) = (sk_A))),
% 1.04/1.24      inference('demod', [status(thm)], ['13', '127'])).
% 1.04/1.24  thf('129', plain,
% 1.04/1.24      (![X42 : $i, X43 : $i, X44 : $i]:
% 1.04/1.24         (((X42) != (k1_relset_1 @ X42 @ X43 @ X44))
% 1.04/1.24          | (v1_funct_2 @ X44 @ X42 @ X43)
% 1.04/1.24          | ~ (zip_tseitin_1 @ X44 @ X43 @ X42))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.04/1.24  thf('130', plain,
% 1.04/1.24      ((((sk_A) != (sk_A))
% 1.04/1.24        | ~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)
% 1.04/1.24        | (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 1.04/1.24      inference('sup-', [status(thm)], ['128', '129'])).
% 1.04/1.24  thf('131', plain,
% 1.04/1.24      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)
% 1.04/1.24        | ~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A))),
% 1.04/1.24      inference('simplify', [status(thm)], ['130'])).
% 1.04/1.24  thf('132', plain,
% 1.04/1.24      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 1.04/1.24         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 1.04/1.24      inference('split', [status(esa)], ['30'])).
% 1.04/1.24  thf('133', plain,
% 1.04/1.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['4', '7'])).
% 1.04/1.24  thf('134', plain,
% 1.04/1.24      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 1.04/1.24         <= (~
% 1.04/1.24             ((m1_subset_1 @ sk_D @ 
% 1.04/1.24               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))))),
% 1.04/1.24      inference('split', [status(esa)], ['30'])).
% 1.04/1.24  thf('135', plain,
% 1.04/1.24      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 1.04/1.24      inference('sup-', [status(thm)], ['133', '134'])).
% 1.04/1.24  thf('136', plain,
% 1.04/1.24      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | 
% 1.04/1.24       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) | 
% 1.04/1.24       ~ ((v1_funct_1 @ sk_D))),
% 1.04/1.24      inference('split', [status(esa)], ['30'])).
% 1.04/1.24  thf('137', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 1.04/1.24      inference('sat_resolution*', [status(thm)], ['32', '135', '136'])).
% 1.04/1.24  thf('138', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)),
% 1.04/1.24      inference('simpl_trail', [status(thm)], ['132', '137'])).
% 1.04/1.24  thf('139', plain, (~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)),
% 1.04/1.24      inference('clc', [status(thm)], ['131', '138'])).
% 1.04/1.24  thf('140', plain, (~ (zip_tseitin_0 @ sk_C_1 @ sk_A)),
% 1.04/1.24      inference('clc', [status(thm)], ['10', '139'])).
% 1.04/1.24  thf('141', plain,
% 1.04/1.24      (![X40 : $i, X41 : $i]:
% 1.04/1.24         ((zip_tseitin_0 @ X40 @ X41) | ((X40) = (k1_xboole_0)))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.04/1.24  thf('142', plain, (~ (zip_tseitin_0 @ sk_C_1 @ sk_A)),
% 1.04/1.24      inference('clc', [status(thm)], ['10', '139'])).
% 1.04/1.24  thf('143', plain, (((sk_C_1) = (k1_xboole_0))),
% 1.04/1.24      inference('sup-', [status(thm)], ['141', '142'])).
% 1.04/1.24  thf('144', plain, (~ (zip_tseitin_0 @ k1_xboole_0 @ sk_A)),
% 1.04/1.24      inference('demod', [status(thm)], ['140', '143'])).
% 1.04/1.24  thf('145', plain,
% 1.04/1.24      (![X1 : $i, X3 : $i]:
% 1.04/1.24         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.04/1.24      inference('cnf', [status(esa)], [d3_tarski])).
% 1.04/1.24  thf('146', plain,
% 1.04/1.24      (![X1 : $i, X3 : $i]:
% 1.04/1.24         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.04/1.24      inference('cnf', [status(esa)], [d3_tarski])).
% 1.04/1.24  thf('147', plain,
% 1.04/1.24      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 1.04/1.24      inference('sup-', [status(thm)], ['145', '146'])).
% 1.04/1.24  thf('148', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.04/1.24      inference('simplify', [status(thm)], ['147'])).
% 1.04/1.24  thf('149', plain,
% 1.04/1.24      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['18', '25'])).
% 1.04/1.24  thf('150', plain,
% 1.04/1.24      (![X19 : $i, X20 : $i]:
% 1.04/1.24         (((X19) = (k1_xboole_0))
% 1.04/1.24          | ~ (v1_relat_1 @ X20)
% 1.04/1.24          | ~ (r1_tarski @ X19 @ (k1_relat_1 @ X20))
% 1.04/1.24          | ((k9_relat_1 @ X20 @ X19) != (k1_xboole_0)))),
% 1.04/1.24      inference('cnf', [status(esa)], [t152_relat_1])).
% 1.04/1.24  thf('151', plain,
% 1.04/1.24      (![X0 : $i]:
% 1.04/1.24         (~ (r1_tarski @ X0 @ sk_A)
% 1.04/1.24          | ((sk_B) = (k1_xboole_0))
% 1.04/1.24          | ((k9_relat_1 @ sk_D @ X0) != (k1_xboole_0))
% 1.04/1.24          | ~ (v1_relat_1 @ sk_D)
% 1.04/1.24          | ((X0) = (k1_xboole_0)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['149', '150'])).
% 1.04/1.24  thf('152', plain,
% 1.04/1.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf('153', plain,
% 1.04/1.24      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.04/1.24         ((v1_relat_1 @ X24)
% 1.04/1.24          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 1.04/1.24      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.04/1.24  thf('154', plain, ((v1_relat_1 @ sk_D)),
% 1.04/1.24      inference('sup-', [status(thm)], ['152', '153'])).
% 1.04/1.24  thf('155', plain,
% 1.04/1.24      (![X0 : $i]:
% 1.04/1.24         (~ (r1_tarski @ X0 @ sk_A)
% 1.04/1.24          | ((sk_B) = (k1_xboole_0))
% 1.04/1.24          | ((k9_relat_1 @ sk_D @ X0) != (k1_xboole_0))
% 1.04/1.24          | ((X0) = (k1_xboole_0)))),
% 1.04/1.24      inference('demod', [status(thm)], ['151', '154'])).
% 1.04/1.24  thf('156', plain, (((sk_B) != (k1_xboole_0))),
% 1.04/1.24      inference('simpl_trail', [status(thm)], ['28', '125'])).
% 1.04/1.24  thf('157', plain,
% 1.04/1.24      (![X0 : $i]:
% 1.04/1.24         (~ (r1_tarski @ X0 @ sk_A)
% 1.04/1.24          | ((k9_relat_1 @ sk_D @ X0) != (k1_xboole_0))
% 1.04/1.24          | ((X0) = (k1_xboole_0)))),
% 1.04/1.24      inference('simplify_reflect-', [status(thm)], ['155', '156'])).
% 1.04/1.24  thf('158', plain,
% 1.04/1.24      ((((sk_A) = (k1_xboole_0))
% 1.04/1.24        | ((k9_relat_1 @ sk_D @ sk_A) != (k1_xboole_0)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['148', '157'])).
% 1.04/1.24  thf('159', plain,
% 1.04/1.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf('160', plain,
% 1.04/1.24      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.04/1.24         ((v4_relat_1 @ X27 @ X28)
% 1.04/1.24          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 1.04/1.24      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.04/1.24  thf('161', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 1.04/1.24      inference('sup-', [status(thm)], ['159', '160'])).
% 1.04/1.24  thf('162', plain,
% 1.04/1.24      (![X21 : $i, X22 : $i]:
% 1.04/1.24         (((X21) = (k7_relat_1 @ X21 @ X22))
% 1.04/1.24          | ~ (v4_relat_1 @ X21 @ X22)
% 1.04/1.24          | ~ (v1_relat_1 @ X21))),
% 1.04/1.24      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.04/1.24  thf('163', plain,
% 1.04/1.24      ((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_A)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['161', '162'])).
% 1.04/1.24  thf('164', plain, ((v1_relat_1 @ sk_D)),
% 1.04/1.24      inference('sup-', [status(thm)], ['152', '153'])).
% 1.04/1.24  thf('165', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_A))),
% 1.04/1.24      inference('demod', [status(thm)], ['163', '164'])).
% 1.04/1.24  thf('166', plain,
% 1.04/1.24      (![X17 : $i, X18 : $i]:
% 1.04/1.24         (((k2_relat_1 @ (k7_relat_1 @ X17 @ X18)) = (k9_relat_1 @ X17 @ X18))
% 1.04/1.24          | ~ (v1_relat_1 @ X17))),
% 1.04/1.24      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.04/1.24  thf('167', plain,
% 1.04/1.24      ((((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ sk_A))
% 1.04/1.24        | ~ (v1_relat_1 @ sk_D))),
% 1.04/1.24      inference('sup+', [status(thm)], ['165', '166'])).
% 1.04/1.24  thf('168', plain, ((v1_relat_1 @ sk_D)),
% 1.04/1.24      inference('sup-', [status(thm)], ['152', '153'])).
% 1.04/1.24  thf('169', plain, (((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ sk_A))),
% 1.04/1.24      inference('demod', [status(thm)], ['167', '168'])).
% 1.04/1.24  thf('170', plain,
% 1.04/1.24      ((((sk_A) = (k1_xboole_0)) | ((k2_relat_1 @ sk_D) != (k1_xboole_0)))),
% 1.04/1.24      inference('demod', [status(thm)], ['158', '169'])).
% 1.04/1.24  thf('171', plain,
% 1.04/1.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['4', '7'])).
% 1.04/1.24  thf('172', plain,
% 1.04/1.24      (![X10 : $i, X11 : $i]:
% 1.04/1.24         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 1.04/1.24      inference('cnf', [status(esa)], [t3_subset])).
% 1.04/1.24  thf('173', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_C_1))),
% 1.04/1.24      inference('sup-', [status(thm)], ['171', '172'])).
% 1.04/1.24  thf('174', plain,
% 1.04/1.24      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 1.04/1.24      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.04/1.24  thf('175', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.04/1.24      inference('simplify', [status(thm)], ['98'])).
% 1.04/1.24  thf('176', plain,
% 1.04/1.24      (![X19 : $i, X20 : $i]:
% 1.04/1.24         (((X19) = (k1_xboole_0))
% 1.04/1.24          | ~ (v1_relat_1 @ X20)
% 1.04/1.24          | ~ (r1_tarski @ X19 @ (k1_relat_1 @ X20))
% 1.04/1.24          | ((k9_relat_1 @ X20 @ X19) != (k1_xboole_0)))),
% 1.04/1.24      inference('cnf', [status(esa)], [t152_relat_1])).
% 1.04/1.24  thf('177', plain,
% 1.04/1.24      (![X0 : $i]:
% 1.04/1.24         (~ (r1_tarski @ X0 @ k1_xboole_0)
% 1.04/1.24          | ((k9_relat_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 1.04/1.24          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.04/1.24          | ((X0) = (k1_xboole_0)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['175', '176'])).
% 1.04/1.24  thf('178', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.04/1.24      inference('sup-', [status(thm)], ['64', '67'])).
% 1.04/1.24  thf('179', plain,
% 1.04/1.24      (![X0 : $i]:
% 1.04/1.24         (~ (r1_tarski @ X0 @ k1_xboole_0)
% 1.04/1.24          | ((k9_relat_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 1.04/1.25          | ((X0) = (k1_xboole_0)))),
% 1.04/1.25      inference('demod', [status(thm)], ['177', '178'])).
% 1.04/1.25  thf('180', plain,
% 1.04/1.25      (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))),
% 1.04/1.25      inference('demod', [status(thm)], ['71', '81', '82'])).
% 1.04/1.25  thf('181', plain,
% 1.04/1.25      (![X0 : $i]:
% 1.04/1.25         (~ (r1_tarski @ X0 @ k1_xboole_0)
% 1.04/1.25          | ((k1_xboole_0) != (k1_xboole_0))
% 1.04/1.25          | ((X0) = (k1_xboole_0)))),
% 1.04/1.25      inference('demod', [status(thm)], ['179', '180'])).
% 1.04/1.25  thf('182', plain,
% 1.04/1.25      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 1.04/1.25      inference('simplify', [status(thm)], ['181'])).
% 1.04/1.25  thf('183', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i]:
% 1.04/1.25         (~ (r1_tarski @ X1 @ X0)
% 1.04/1.25          | ~ (v1_xboole_0 @ X0)
% 1.04/1.25          | ((X1) = (k1_xboole_0)))),
% 1.04/1.25      inference('sup-', [status(thm)], ['174', '182'])).
% 1.04/1.25  thf('184', plain,
% 1.04/1.25      ((((sk_D) = (k1_xboole_0))
% 1.04/1.25        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 1.04/1.25      inference('sup-', [status(thm)], ['173', '183'])).
% 1.04/1.25  thf('185', plain, (((sk_C_1) = (k1_xboole_0))),
% 1.04/1.25      inference('sup-', [status(thm)], ['141', '142'])).
% 1.04/1.25  thf('186', plain,
% 1.04/1.25      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 1.04/1.25      inference('simplify', [status(thm)], ['56'])).
% 1.04/1.25  thf('187', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.04/1.25      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.04/1.25  thf('188', plain, (((sk_D) = (k1_xboole_0))),
% 1.04/1.25      inference('demod', [status(thm)], ['184', '185', '186', '187'])).
% 1.04/1.25  thf('189', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.04/1.25      inference('demod', [status(thm)], ['79', '80'])).
% 1.04/1.25  thf('190', plain,
% 1.04/1.25      ((((sk_A) = (k1_xboole_0)) | ((k1_xboole_0) != (k1_xboole_0)))),
% 1.04/1.25      inference('demod', [status(thm)], ['170', '188', '189'])).
% 1.04/1.25  thf('191', plain, (((sk_A) = (k1_xboole_0))),
% 1.04/1.25      inference('simplify', [status(thm)], ['190'])).
% 1.04/1.25  thf('192', plain,
% 1.04/1.25      (![X40 : $i, X41 : $i]:
% 1.04/1.25         ((zip_tseitin_0 @ X40 @ X41) | ((X40) = (k1_xboole_0)))),
% 1.04/1.25      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.04/1.25  thf('193', plain, (![X40 : $i]: (zip_tseitin_0 @ X40 @ k1_xboole_0)),
% 1.04/1.25      inference('simplify', [status(thm)], ['40'])).
% 1.04/1.25  thf('194', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.25         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 1.04/1.25      inference('sup+', [status(thm)], ['192', '193'])).
% 1.04/1.25  thf('195', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 1.04/1.25      inference('eq_fact', [status(thm)], ['194'])).
% 1.04/1.25  thf('196', plain, ($false),
% 1.04/1.25      inference('demod', [status(thm)], ['144', '191', '195'])).
% 1.04/1.25  
% 1.04/1.25  % SZS output end Refutation
% 1.04/1.25  
% 1.04/1.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
