%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TslZdLCU2J

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:10 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :  228 ( 903 expanded)
%              Number of leaves         :   42 ( 285 expanded)
%              Depth                    :   20
%              Number of atoms          : 1526 (10308 expanded)
%              Number of equality atoms :  125 ( 756 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t9_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ B @ C )
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
       => ( ( r1_tarski @ B @ C )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ C )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t9_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_D_1 )
   <= ~ ( v1_funct_1 @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v5_relat_1 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('7',plain,(
    v5_relat_1 @ sk_D_1 @ sk_B ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t218_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v5_relat_1 @ C @ A ) )
         => ( v5_relat_1 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v5_relat_1 @ X19 @ X20 )
      | ( v5_relat_1 @ X19 @ X21 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t218_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ X0 @ sk_C )
      | ~ ( v5_relat_1 @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( v5_relat_1 @ sk_D_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('16',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    v5_relat_1 @ sk_D_1 @ sk_C ),
    inference(demod,[status(thm)],['11','16'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v5_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('21',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('24',plain,(
    v4_relat_1 @ sk_D_1 @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('25',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v4_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('28',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ),
    inference(demod,[status(thm)],['26','27'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('29',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X31 ) @ X32 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X31 ) @ X33 )
      | ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','32'])).

thf('34',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,(
    ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['4','35','36'])).

thf('38',plain,(
    ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','32'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('40',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('41',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B ),
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

thf('43',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ( X41
        = ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ~ ( zip_tseitin_1 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('44',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('47',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['44','47'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('49',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('50',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('51',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X44 @ X45 )
      | ( zip_tseitin_1 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('52',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['54'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('56',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('57',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X31 ) @ X32 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X31 ) @ X33 )
      | ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('59',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('60',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('61',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('63',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('65',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['58','59','63','64','65'])).

thf('67',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( X41
       != ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ~ ( zip_tseitin_1 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X40 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('75',plain,(
    ! [X39: $i] :
      ( zip_tseitin_0 @ X39 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['58','59','63','64','65'])).

thf('77',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X44 @ X45 )
      | ( zip_tseitin_1 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['73','79'])).

thf('81',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['54'])).

thf('82',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('84',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v1_xboole_0 @ X8 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('85',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) )
      | ( v1_xboole_0 @ sk_D_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('87',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('88',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('89',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('90',plain,
    ( ( sk_D_1 = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['54'])).

thf('92',plain,
    ( ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('93',plain,
    ( ~ ( v1_funct_2 @ sk_D_1 @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,
    ( ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','94'])).

thf('96',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('97',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['54'])).

thf('100',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('101',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('104',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('105',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('107',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['102','105','106'])).

thf('108',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C )
    | ~ ( v1_funct_1 @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('109',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['54'])).

thf('110',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['4','95','107','108','109'])).

thf('111',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['55','110'])).

thf('112',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['53','111'])).

thf('113',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['48','112'])).

thf('114',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D_1 )
    = sk_A ),
    inference(demod,[status(thm)],['41','113'])).

thf('115',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( X41
       != ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ~ ( zip_tseitin_1 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('116',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_A )
    | ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C )
    | ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','32'])).

thf('119',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X44 @ X45 )
      | ( zip_tseitin_1 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('120',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('122',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('125',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('128',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('129',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('131',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( ( k2_relat_1 @ sk_D_1 )
      = sk_C )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['127','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X0 )
      | ( ( k2_relat_1 @ sk_D_1 )
        = sk_C ) ) ),
    inference('sup-',[status(thm)],['126','133'])).

thf('135',plain,(
    v5_relat_1 @ sk_D_1 @ sk_B ),
    inference('sup-',[status(thm)],['5','6'])).

thf('136',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v5_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('137',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('139',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_B ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('141',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D_1 ) )
    | ( sk_B
      = ( k2_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ sk_C )
      | ( zip_tseitin_0 @ sk_C @ X0 )
      | ( sk_B
        = ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['134','141'])).

thf('143',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X0 )
      | ( sk_B
        = ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_D_1 )
      | ( zip_tseitin_0 @ sk_C @ X0 ) ) ),
    inference('sup+',[status(thm)],['123','144'])).

thf('146',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['55','110'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_D_1 )
      | ( zip_tseitin_0 @ sk_C @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('150',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('152',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('153',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['151','154'])).

thf('156',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['150','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['149','156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( zip_tseitin_1 @ k1_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['55','110'])).

thf('161',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ sk_C @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('163',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( X44 != k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ( v1_funct_2 @ X46 @ X45 @ X44 )
      | ( X46 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('164',plain,(
    ! [X45: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X45 @ k1_xboole_0 )
      | ( X45 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('166',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['165'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['58','59','63','64','65'])).

thf('169',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X45: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X45 @ k1_xboole_0 )
      | ( X45 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['164','166','169'])).

thf('171',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ( X41
        = ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ~ ( zip_tseitin_1 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0
        = ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['162','175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['161','176'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['148','177'])).

thf('179',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ sk_C @ X1 ) ) ),
    inference('sup+',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference(clc,[status(thm)],['147','180'])).

thf('182',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['120','181'])).

thf('183',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_C ),
    inference(demod,[status(thm)],['117','182'])).

thf('184',plain,(
    $false ),
    inference(demod,[status(thm)],['38','183'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TslZdLCU2J
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:40:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.61/1.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.61/1.80  % Solved by: fo/fo7.sh
% 1.61/1.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.61/1.80  % done 1466 iterations in 1.347s
% 1.61/1.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.61/1.80  % SZS output start Refutation
% 1.61/1.80  thf(sk_A_type, type, sk_A: $i).
% 1.61/1.80  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.61/1.80  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.61/1.80  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.61/1.80  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.61/1.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.61/1.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.61/1.80  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.61/1.80  thf(sk_B_type, type, sk_B: $i).
% 1.61/1.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.61/1.80  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.61/1.80  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.61/1.80  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.61/1.80  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.61/1.80  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.61/1.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.61/1.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.61/1.80  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.61/1.80  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.61/1.80  thf(sk_C_type, type, sk_C: $i).
% 1.61/1.80  thf(t9_funct_2, conjecture,
% 1.61/1.80    (![A:$i,B:$i,C:$i,D:$i]:
% 1.61/1.80     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.61/1.80         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.61/1.80       ( ( r1_tarski @ B @ C ) =>
% 1.61/1.80         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.61/1.80           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 1.61/1.80             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 1.61/1.80  thf(zf_stmt_0, negated_conjecture,
% 1.61/1.80    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.61/1.80        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.61/1.80            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.61/1.80          ( ( r1_tarski @ B @ C ) =>
% 1.61/1.80            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.61/1.80              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 1.61/1.80                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 1.61/1.80    inference('cnf.neg', [status(esa)], [t9_funct_2])).
% 1.61/1.80  thf('0', plain,
% 1.61/1.80      ((~ (v1_funct_1 @ sk_D_1)
% 1.61/1.80        | ~ (v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)
% 1.61/1.80        | ~ (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf('1', plain,
% 1.61/1.80      ((~ (v1_funct_2 @ sk_D_1 @ sk_A @ sk_C))
% 1.61/1.80         <= (~ ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)))),
% 1.61/1.80      inference('split', [status(esa)], ['0'])).
% 1.61/1.80  thf('2', plain, ((v1_funct_1 @ sk_D_1)),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf('3', plain, ((~ (v1_funct_1 @ sk_D_1)) <= (~ ((v1_funct_1 @ sk_D_1)))),
% 1.61/1.80      inference('split', [status(esa)], ['0'])).
% 1.61/1.80  thf('4', plain, (((v1_funct_1 @ sk_D_1))),
% 1.61/1.80      inference('sup-', [status(thm)], ['2', '3'])).
% 1.61/1.80  thf('5', plain,
% 1.61/1.80      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf(cc2_relset_1, axiom,
% 1.61/1.80    (![A:$i,B:$i,C:$i]:
% 1.61/1.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.61/1.80       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.61/1.80  thf('6', plain,
% 1.61/1.80      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.61/1.80         ((v5_relat_1 @ X25 @ X27)
% 1.61/1.80          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.61/1.80      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.61/1.80  thf('7', plain, ((v5_relat_1 @ sk_D_1 @ sk_B)),
% 1.61/1.80      inference('sup-', [status(thm)], ['5', '6'])).
% 1.61/1.80  thf('8', plain, ((r1_tarski @ sk_B @ sk_C)),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf(t218_relat_1, axiom,
% 1.61/1.80    (![A:$i,B:$i]:
% 1.61/1.80     ( ( r1_tarski @ A @ B ) =>
% 1.61/1.80       ( ![C:$i]:
% 1.61/1.80         ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) ) =>
% 1.61/1.80           ( v5_relat_1 @ C @ B ) ) ) ))).
% 1.61/1.80  thf('9', plain,
% 1.61/1.80      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.61/1.80         (~ (v1_relat_1 @ X19)
% 1.61/1.80          | ~ (v5_relat_1 @ X19 @ X20)
% 1.61/1.80          | (v5_relat_1 @ X19 @ X21)
% 1.61/1.80          | ~ (r1_tarski @ X20 @ X21))),
% 1.61/1.80      inference('cnf', [status(esa)], [t218_relat_1])).
% 1.61/1.80  thf('10', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         ((v5_relat_1 @ X0 @ sk_C)
% 1.61/1.80          | ~ (v5_relat_1 @ X0 @ sk_B)
% 1.61/1.80          | ~ (v1_relat_1 @ X0))),
% 1.61/1.80      inference('sup-', [status(thm)], ['8', '9'])).
% 1.61/1.80  thf('11', plain, ((~ (v1_relat_1 @ sk_D_1) | (v5_relat_1 @ sk_D_1 @ sk_C))),
% 1.61/1.80      inference('sup-', [status(thm)], ['7', '10'])).
% 1.61/1.80  thf('12', plain,
% 1.61/1.80      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf(cc2_relat_1, axiom,
% 1.61/1.80    (![A:$i]:
% 1.61/1.80     ( ( v1_relat_1 @ A ) =>
% 1.61/1.80       ( ![B:$i]:
% 1.61/1.80         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.61/1.80  thf('13', plain,
% 1.61/1.80      (![X11 : $i, X12 : $i]:
% 1.61/1.80         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 1.61/1.80          | (v1_relat_1 @ X11)
% 1.61/1.80          | ~ (v1_relat_1 @ X12))),
% 1.61/1.80      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.61/1.80  thf('14', plain,
% 1.61/1.80      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_1))),
% 1.61/1.80      inference('sup-', [status(thm)], ['12', '13'])).
% 1.61/1.80  thf(fc6_relat_1, axiom,
% 1.61/1.80    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.61/1.80  thf('15', plain,
% 1.61/1.80      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 1.61/1.80      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.61/1.80  thf('16', plain, ((v1_relat_1 @ sk_D_1)),
% 1.61/1.80      inference('demod', [status(thm)], ['14', '15'])).
% 1.61/1.80  thf('17', plain, ((v5_relat_1 @ sk_D_1 @ sk_C)),
% 1.61/1.80      inference('demod', [status(thm)], ['11', '16'])).
% 1.61/1.80  thf(d19_relat_1, axiom,
% 1.61/1.80    (![A:$i,B:$i]:
% 1.61/1.80     ( ( v1_relat_1 @ B ) =>
% 1.61/1.80       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.61/1.80  thf('18', plain,
% 1.61/1.80      (![X15 : $i, X16 : $i]:
% 1.61/1.80         (~ (v5_relat_1 @ X15 @ X16)
% 1.61/1.80          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 1.61/1.80          | ~ (v1_relat_1 @ X15))),
% 1.61/1.80      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.61/1.80  thf('19', plain,
% 1.61/1.80      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_C))),
% 1.61/1.80      inference('sup-', [status(thm)], ['17', '18'])).
% 1.61/1.80  thf('20', plain, ((v1_relat_1 @ sk_D_1)),
% 1.61/1.80      inference('demod', [status(thm)], ['14', '15'])).
% 1.61/1.80  thf('21', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_C)),
% 1.61/1.80      inference('demod', [status(thm)], ['19', '20'])).
% 1.61/1.80  thf('22', plain,
% 1.61/1.80      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf('23', plain,
% 1.61/1.80      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.61/1.80         ((v4_relat_1 @ X25 @ X26)
% 1.61/1.80          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.61/1.80      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.61/1.80  thf('24', plain, ((v4_relat_1 @ sk_D_1 @ sk_A)),
% 1.61/1.80      inference('sup-', [status(thm)], ['22', '23'])).
% 1.61/1.80  thf(d18_relat_1, axiom,
% 1.61/1.80    (![A:$i,B:$i]:
% 1.61/1.80     ( ( v1_relat_1 @ B ) =>
% 1.61/1.80       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.61/1.80  thf('25', plain,
% 1.61/1.80      (![X13 : $i, X14 : $i]:
% 1.61/1.80         (~ (v4_relat_1 @ X13 @ X14)
% 1.61/1.80          | (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 1.61/1.80          | ~ (v1_relat_1 @ X13))),
% 1.61/1.80      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.61/1.80  thf('26', plain,
% 1.61/1.80      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_A))),
% 1.61/1.80      inference('sup-', [status(thm)], ['24', '25'])).
% 1.61/1.80  thf('27', plain, ((v1_relat_1 @ sk_D_1)),
% 1.61/1.80      inference('demod', [status(thm)], ['14', '15'])).
% 1.61/1.80  thf('28', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_A)),
% 1.61/1.80      inference('demod', [status(thm)], ['26', '27'])).
% 1.61/1.80  thf(t11_relset_1, axiom,
% 1.61/1.80    (![A:$i,B:$i,C:$i]:
% 1.61/1.80     ( ( v1_relat_1 @ C ) =>
% 1.61/1.80       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 1.61/1.80           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 1.61/1.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.61/1.80  thf('29', plain,
% 1.61/1.80      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.61/1.80         (~ (r1_tarski @ (k1_relat_1 @ X31) @ X32)
% 1.61/1.80          | ~ (r1_tarski @ (k2_relat_1 @ X31) @ X33)
% 1.61/1.80          | (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.61/1.80          | ~ (v1_relat_1 @ X31))),
% 1.61/1.80      inference('cnf', [status(esa)], [t11_relset_1])).
% 1.61/1.80  thf('30', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (~ (v1_relat_1 @ sk_D_1)
% 1.61/1.80          | (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.61/1.80          | ~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ X0))),
% 1.61/1.80      inference('sup-', [status(thm)], ['28', '29'])).
% 1.61/1.80  thf('31', plain, ((v1_relat_1 @ sk_D_1)),
% 1.61/1.80      inference('demod', [status(thm)], ['14', '15'])).
% 1.61/1.80  thf('32', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.61/1.80          | ~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ X0))),
% 1.61/1.80      inference('demod', [status(thm)], ['30', '31'])).
% 1.61/1.80  thf('33', plain,
% 1.61/1.80      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.61/1.80      inference('sup-', [status(thm)], ['21', '32'])).
% 1.61/1.80  thf('34', plain,
% 1.61/1.80      ((~ (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 1.61/1.80         <= (~
% 1.61/1.80             ((m1_subset_1 @ sk_D_1 @ 
% 1.61/1.80               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 1.61/1.80      inference('split', [status(esa)], ['0'])).
% 1.61/1.80  thf('35', plain,
% 1.61/1.80      (((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 1.61/1.80      inference('sup-', [status(thm)], ['33', '34'])).
% 1.61/1.80  thf('36', plain,
% 1.61/1.80      (~ ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)) | 
% 1.61/1.80       ~ ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 1.61/1.80       ~ ((v1_funct_1 @ sk_D_1))),
% 1.61/1.80      inference('split', [status(esa)], ['0'])).
% 1.61/1.80  thf('37', plain, (~ ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C))),
% 1.61/1.80      inference('sat_resolution*', [status(thm)], ['4', '35', '36'])).
% 1.61/1.80  thf('38', plain, (~ (v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)),
% 1.61/1.80      inference('simpl_trail', [status(thm)], ['1', '37'])).
% 1.61/1.80  thf('39', plain,
% 1.61/1.80      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.61/1.80      inference('sup-', [status(thm)], ['21', '32'])).
% 1.61/1.80  thf(redefinition_k1_relset_1, axiom,
% 1.61/1.80    (![A:$i,B:$i,C:$i]:
% 1.61/1.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.61/1.80       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.61/1.80  thf('40', plain,
% 1.61/1.80      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.61/1.80         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 1.61/1.80          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.61/1.80      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.61/1.80  thf('41', plain,
% 1.61/1.80      (((k1_relset_1 @ sk_A @ sk_C @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 1.61/1.80      inference('sup-', [status(thm)], ['39', '40'])).
% 1.61/1.80  thf('42', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf(d1_funct_2, axiom,
% 1.61/1.80    (![A:$i,B:$i,C:$i]:
% 1.61/1.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.61/1.80       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.61/1.80           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.61/1.80             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.61/1.80         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.61/1.80           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.61/1.80             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.61/1.80  thf(zf_stmt_1, axiom,
% 1.61/1.80    (![C:$i,B:$i,A:$i]:
% 1.61/1.80     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.61/1.80       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.61/1.80  thf('43', plain,
% 1.61/1.80      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.61/1.80         (~ (v1_funct_2 @ X43 @ X41 @ X42)
% 1.61/1.80          | ((X41) = (k1_relset_1 @ X41 @ X42 @ X43))
% 1.61/1.80          | ~ (zip_tseitin_1 @ X43 @ X42 @ X41))),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.61/1.80  thf('44', plain,
% 1.61/1.80      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 1.61/1.80        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_1)))),
% 1.61/1.80      inference('sup-', [status(thm)], ['42', '43'])).
% 1.61/1.80  thf('45', plain,
% 1.61/1.80      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf('46', plain,
% 1.61/1.80      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.61/1.80         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 1.61/1.80          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.61/1.80      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.61/1.80  thf('47', plain,
% 1.61/1.80      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 1.61/1.80      inference('sup-', [status(thm)], ['45', '46'])).
% 1.61/1.80  thf('48', plain,
% 1.61/1.80      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 1.61/1.80        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 1.61/1.80      inference('demod', [status(thm)], ['44', '47'])).
% 1.61/1.80  thf(zf_stmt_2, axiom,
% 1.61/1.80    (![B:$i,A:$i]:
% 1.61/1.80     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.61/1.80       ( zip_tseitin_0 @ B @ A ) ))).
% 1.61/1.80  thf('49', plain,
% 1.61/1.80      (![X39 : $i, X40 : $i]:
% 1.61/1.80         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.61/1.80  thf('50', plain,
% 1.61/1.80      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.61/1.80  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.61/1.80  thf(zf_stmt_5, axiom,
% 1.61/1.80    (![A:$i,B:$i,C:$i]:
% 1.61/1.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.61/1.80       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.61/1.80         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.61/1.80           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.61/1.80             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.61/1.80  thf('51', plain,
% 1.61/1.80      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.61/1.80         (~ (zip_tseitin_0 @ X44 @ X45)
% 1.61/1.80          | (zip_tseitin_1 @ X46 @ X44 @ X45)
% 1.61/1.80          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.61/1.80  thf('52', plain,
% 1.61/1.80      (((zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 1.61/1.80        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.61/1.80      inference('sup-', [status(thm)], ['50', '51'])).
% 1.61/1.80  thf('53', plain,
% 1.61/1.80      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A))),
% 1.61/1.80      inference('sup-', [status(thm)], ['49', '52'])).
% 1.61/1.80  thf('54', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf('55', plain,
% 1.61/1.80      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.61/1.80      inference('split', [status(esa)], ['54'])).
% 1.61/1.80  thf(t60_relat_1, axiom,
% 1.61/1.80    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.61/1.80     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.61/1.80  thf('56', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.61/1.80      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.61/1.80  thf('57', plain,
% 1.61/1.80      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.61/1.80         (~ (r1_tarski @ (k1_relat_1 @ X31) @ X32)
% 1.61/1.80          | ~ (r1_tarski @ (k2_relat_1 @ X31) @ X33)
% 1.61/1.80          | (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.61/1.80          | ~ (v1_relat_1 @ X31))),
% 1.61/1.80      inference('cnf', [status(esa)], [t11_relset_1])).
% 1.61/1.80  thf('58', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i]:
% 1.61/1.80         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 1.61/1.80          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.61/1.80          | (m1_subset_1 @ k1_xboole_0 @ 
% 1.61/1.80             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 1.61/1.80          | ~ (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X1))),
% 1.61/1.80      inference('sup-', [status(thm)], ['56', '57'])).
% 1.61/1.80  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.61/1.80  thf('59', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 1.61/1.80      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.61/1.80  thf(t113_zfmisc_1, axiom,
% 1.61/1.80    (![A:$i,B:$i]:
% 1.61/1.80     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.61/1.80       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.61/1.80  thf('60', plain,
% 1.61/1.80      (![X6 : $i, X7 : $i]:
% 1.61/1.80         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 1.61/1.80      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.61/1.80  thf('61', plain,
% 1.61/1.80      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 1.61/1.80      inference('simplify', [status(thm)], ['60'])).
% 1.61/1.80  thf('62', plain,
% 1.61/1.80      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 1.61/1.80      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.61/1.80  thf('63', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.61/1.80      inference('sup+', [status(thm)], ['61', '62'])).
% 1.61/1.80  thf('64', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.61/1.80      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.61/1.80  thf('65', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 1.61/1.80      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.61/1.80  thf('66', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i]:
% 1.61/1.80         (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))),
% 1.61/1.80      inference('demod', [status(thm)], ['58', '59', '63', '64', '65'])).
% 1.61/1.80  thf('67', plain,
% 1.61/1.80      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.61/1.80         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 1.61/1.80          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.61/1.80      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.61/1.80  thf('68', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i]:
% 1.61/1.80         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 1.61/1.80      inference('sup-', [status(thm)], ['66', '67'])).
% 1.61/1.80  thf('69', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.61/1.80      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.61/1.80  thf('70', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i]:
% 1.61/1.80         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.61/1.80      inference('demod', [status(thm)], ['68', '69'])).
% 1.61/1.80  thf('71', plain,
% 1.61/1.80      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.61/1.80         (((X41) != (k1_relset_1 @ X41 @ X42 @ X43))
% 1.61/1.80          | (v1_funct_2 @ X43 @ X41 @ X42)
% 1.61/1.80          | ~ (zip_tseitin_1 @ X43 @ X42 @ X41))),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.61/1.80  thf('72', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i]:
% 1.61/1.80         (((X1) != (k1_xboole_0))
% 1.61/1.80          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 1.61/1.80          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 1.61/1.80      inference('sup-', [status(thm)], ['70', '71'])).
% 1.61/1.80  thf('73', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.61/1.80          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.61/1.80      inference('simplify', [status(thm)], ['72'])).
% 1.61/1.80  thf('74', plain,
% 1.61/1.80      (![X39 : $i, X40 : $i]:
% 1.61/1.80         ((zip_tseitin_0 @ X39 @ X40) | ((X40) != (k1_xboole_0)))),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.61/1.80  thf('75', plain, (![X39 : $i]: (zip_tseitin_0 @ X39 @ k1_xboole_0)),
% 1.61/1.80      inference('simplify', [status(thm)], ['74'])).
% 1.61/1.80  thf('76', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i]:
% 1.61/1.80         (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))),
% 1.61/1.80      inference('demod', [status(thm)], ['58', '59', '63', '64', '65'])).
% 1.61/1.80  thf('77', plain,
% 1.61/1.80      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.61/1.80         (~ (zip_tseitin_0 @ X44 @ X45)
% 1.61/1.80          | (zip_tseitin_1 @ X46 @ X44 @ X45)
% 1.61/1.80          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.61/1.80  thf('78', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i]:
% 1.61/1.80         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 1.61/1.80      inference('sup-', [status(thm)], ['76', '77'])).
% 1.61/1.80  thf('79', plain,
% 1.61/1.80      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.61/1.80      inference('sup-', [status(thm)], ['75', '78'])).
% 1.61/1.80  thf('80', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.61/1.80      inference('demod', [status(thm)], ['73', '79'])).
% 1.61/1.80  thf('81', plain,
% 1.61/1.80      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.61/1.80      inference('split', [status(esa)], ['54'])).
% 1.61/1.80  thf('82', plain,
% 1.61/1.80      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf('83', plain,
% 1.61/1.80      (((m1_subset_1 @ sk_D_1 @ 
% 1.61/1.80         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 1.61/1.80         <= ((((sk_A) = (k1_xboole_0))))),
% 1.61/1.80      inference('sup+', [status(thm)], ['81', '82'])).
% 1.61/1.80  thf(cc1_subset_1, axiom,
% 1.61/1.80    (![A:$i]:
% 1.61/1.80     ( ( v1_xboole_0 @ A ) =>
% 1.61/1.80       ( ![B:$i]:
% 1.61/1.80         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 1.61/1.81  thf('84', plain,
% 1.61/1.81      (![X8 : $i, X9 : $i]:
% 1.61/1.81         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 1.61/1.81          | (v1_xboole_0 @ X8)
% 1.61/1.81          | ~ (v1_xboole_0 @ X9))),
% 1.61/1.81      inference('cnf', [status(esa)], [cc1_subset_1])).
% 1.61/1.81  thf('85', plain,
% 1.61/1.81      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))
% 1.61/1.81         | (v1_xboole_0 @ sk_D_1))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.61/1.81      inference('sup-', [status(thm)], ['83', '84'])).
% 1.61/1.81  thf('86', plain,
% 1.61/1.81      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 1.61/1.81      inference('simplify', [status(thm)], ['60'])).
% 1.61/1.81  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.61/1.81  thf('87', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.61/1.81      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.61/1.81  thf('88', plain, (((v1_xboole_0 @ sk_D_1)) <= ((((sk_A) = (k1_xboole_0))))),
% 1.61/1.81      inference('demod', [status(thm)], ['85', '86', '87'])).
% 1.61/1.81  thf(t6_boole, axiom,
% 1.61/1.81    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.61/1.81  thf('89', plain,
% 1.61/1.81      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 1.61/1.81      inference('cnf', [status(esa)], [t6_boole])).
% 1.61/1.81  thf('90', plain,
% 1.61/1.81      ((((sk_D_1) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.61/1.81      inference('sup-', [status(thm)], ['88', '89'])).
% 1.61/1.81  thf('91', plain,
% 1.61/1.81      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.61/1.81      inference('split', [status(esa)], ['54'])).
% 1.61/1.81  thf('92', plain,
% 1.61/1.81      ((~ (v1_funct_2 @ sk_D_1 @ sk_A @ sk_C))
% 1.61/1.81         <= (~ ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)))),
% 1.61/1.81      inference('split', [status(esa)], ['0'])).
% 1.61/1.81  thf('93', plain,
% 1.61/1.81      ((~ (v1_funct_2 @ sk_D_1 @ k1_xboole_0 @ sk_C))
% 1.61/1.81         <= (~ ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)) & 
% 1.61/1.81             (((sk_A) = (k1_xboole_0))))),
% 1.61/1.81      inference('sup-', [status(thm)], ['91', '92'])).
% 1.61/1.81  thf('94', plain,
% 1.61/1.81      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C))
% 1.61/1.81         <= (~ ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)) & 
% 1.61/1.81             (((sk_A) = (k1_xboole_0))))),
% 1.61/1.81      inference('sup-', [status(thm)], ['90', '93'])).
% 1.61/1.81  thf('95', plain,
% 1.61/1.81      (((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)) | ~ (((sk_A) = (k1_xboole_0)))),
% 1.61/1.81      inference('sup-', [status(thm)], ['80', '94'])).
% 1.61/1.81  thf('96', plain,
% 1.61/1.81      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 1.61/1.81      inference('cnf', [status(esa)], [t6_boole])).
% 1.61/1.81  thf('97', plain,
% 1.61/1.81      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 1.61/1.81      inference('simplify', [status(thm)], ['60'])).
% 1.61/1.81  thf('98', plain,
% 1.61/1.81      (![X0 : $i, X1 : $i]:
% 1.61/1.81         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.61/1.81      inference('sup+', [status(thm)], ['96', '97'])).
% 1.61/1.81  thf('99', plain,
% 1.61/1.81      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.61/1.81      inference('split', [status(esa)], ['54'])).
% 1.61/1.81  thf('100', plain,
% 1.61/1.81      ((~ (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 1.61/1.81         <= (~
% 1.61/1.81             ((m1_subset_1 @ sk_D_1 @ 
% 1.61/1.81               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 1.61/1.81      inference('split', [status(esa)], ['0'])).
% 1.61/1.81  thf('101', plain,
% 1.61/1.81      ((~ (m1_subset_1 @ sk_D_1 @ 
% 1.61/1.81           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 1.61/1.81         <= (~
% 1.61/1.81             ((m1_subset_1 @ sk_D_1 @ 
% 1.61/1.81               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 1.61/1.81             (((sk_A) = (k1_xboole_0))))),
% 1.61/1.81      inference('sup-', [status(thm)], ['99', '100'])).
% 1.61/1.81  thf('102', plain,
% 1.61/1.81      (((~ (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.61/1.81         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 1.61/1.81         <= (~
% 1.61/1.81             ((m1_subset_1 @ sk_D_1 @ 
% 1.61/1.81               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 1.61/1.81             (((sk_A) = (k1_xboole_0))))),
% 1.61/1.81      inference('sup-', [status(thm)], ['98', '101'])).
% 1.61/1.81  thf('103', plain,
% 1.61/1.81      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 1.61/1.81      inference('simplify', [status(thm)], ['60'])).
% 1.61/1.81  thf('104', plain,
% 1.61/1.81      (((m1_subset_1 @ sk_D_1 @ 
% 1.61/1.81         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 1.61/1.81         <= ((((sk_A) = (k1_xboole_0))))),
% 1.61/1.81      inference('sup+', [status(thm)], ['81', '82'])).
% 1.61/1.81  thf('105', plain,
% 1.61/1.81      (((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ k1_xboole_0)))
% 1.61/1.81         <= ((((sk_A) = (k1_xboole_0))))),
% 1.61/1.81      inference('sup+', [status(thm)], ['103', '104'])).
% 1.61/1.81  thf('106', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.61/1.81      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.61/1.81  thf('107', plain,
% 1.61/1.81      (~ (((sk_A) = (k1_xboole_0))) | 
% 1.61/1.81       ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 1.61/1.81      inference('demod', [status(thm)], ['102', '105', '106'])).
% 1.61/1.81  thf('108', plain,
% 1.61/1.81      (~ ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 1.61/1.81       ~ ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)) | ~ ((v1_funct_1 @ sk_D_1))),
% 1.61/1.81      inference('split', [status(esa)], ['0'])).
% 1.61/1.81  thf('109', plain,
% 1.61/1.81      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 1.61/1.81      inference('split', [status(esa)], ['54'])).
% 1.61/1.81  thf('110', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 1.61/1.81      inference('sat_resolution*', [status(thm)],
% 1.61/1.81                ['4', '95', '107', '108', '109'])).
% 1.61/1.81  thf('111', plain, (((sk_B) != (k1_xboole_0))),
% 1.61/1.81      inference('simpl_trail', [status(thm)], ['55', '110'])).
% 1.61/1.81  thf('112', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)),
% 1.61/1.81      inference('simplify_reflect-', [status(thm)], ['53', '111'])).
% 1.61/1.81  thf('113', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 1.61/1.81      inference('demod', [status(thm)], ['48', '112'])).
% 1.61/1.81  thf('114', plain, (((k1_relset_1 @ sk_A @ sk_C @ sk_D_1) = (sk_A))),
% 1.61/1.81      inference('demod', [status(thm)], ['41', '113'])).
% 1.61/1.81  thf('115', plain,
% 1.61/1.81      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.61/1.81         (((X41) != (k1_relset_1 @ X41 @ X42 @ X43))
% 1.61/1.81          | (v1_funct_2 @ X43 @ X41 @ X42)
% 1.61/1.81          | ~ (zip_tseitin_1 @ X43 @ X42 @ X41))),
% 1.61/1.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.61/1.81  thf('116', plain,
% 1.61/1.81      ((((sk_A) != (sk_A))
% 1.61/1.81        | ~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_A)
% 1.61/1.81        | (v1_funct_2 @ sk_D_1 @ sk_A @ sk_C))),
% 1.61/1.81      inference('sup-', [status(thm)], ['114', '115'])).
% 1.61/1.81  thf('117', plain,
% 1.61/1.81      (((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)
% 1.61/1.81        | ~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_A))),
% 1.61/1.81      inference('simplify', [status(thm)], ['116'])).
% 1.61/1.81  thf('118', plain,
% 1.61/1.81      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.61/1.81      inference('sup-', [status(thm)], ['21', '32'])).
% 1.61/1.81  thf('119', plain,
% 1.61/1.81      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.61/1.81         (~ (zip_tseitin_0 @ X44 @ X45)
% 1.61/1.81          | (zip_tseitin_1 @ X46 @ X44 @ X45)
% 1.61/1.81          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 1.61/1.81      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.61/1.81  thf('120', plain,
% 1.61/1.81      (((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_A)
% 1.61/1.81        | ~ (zip_tseitin_0 @ sk_C @ sk_A))),
% 1.61/1.81      inference('sup-', [status(thm)], ['118', '119'])).
% 1.61/1.81  thf('121', plain,
% 1.61/1.81      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 1.61/1.81      inference('cnf', [status(esa)], [t6_boole])).
% 1.61/1.81  thf('122', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.61/1.81      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.61/1.81  thf('123', plain,
% 1.61/1.81      (![X0 : $i]: (((k2_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.61/1.81      inference('sup+', [status(thm)], ['121', '122'])).
% 1.61/1.81  thf('124', plain,
% 1.61/1.81      (![X39 : $i, X40 : $i]:
% 1.61/1.81         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 1.61/1.81      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.61/1.81  thf('125', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.61/1.81      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.61/1.81  thf('126', plain,
% 1.61/1.81      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.61/1.81      inference('sup+', [status(thm)], ['124', '125'])).
% 1.61/1.81  thf('127', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_C)),
% 1.61/1.81      inference('demod', [status(thm)], ['19', '20'])).
% 1.61/1.81  thf('128', plain,
% 1.61/1.81      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 1.61/1.81      inference('cnf', [status(esa)], [t6_boole])).
% 1.61/1.81  thf('129', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 1.61/1.81      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.61/1.81  thf('130', plain,
% 1.61/1.81      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.61/1.81      inference('sup+', [status(thm)], ['128', '129'])).
% 1.61/1.81  thf(d10_xboole_0, axiom,
% 1.61/1.81    (![A:$i,B:$i]:
% 1.61/1.81     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.61/1.81  thf('131', plain,
% 1.61/1.81      (![X0 : $i, X2 : $i]:
% 1.61/1.81         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.61/1.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.61/1.81  thf('132', plain,
% 1.61/1.81      (![X0 : $i, X1 : $i]:
% 1.61/1.81         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 1.61/1.81      inference('sup-', [status(thm)], ['130', '131'])).
% 1.61/1.81  thf('133', plain,
% 1.61/1.81      ((((k2_relat_1 @ sk_D_1) = (sk_C)) | ~ (v1_xboole_0 @ sk_C))),
% 1.61/1.81      inference('sup-', [status(thm)], ['127', '132'])).
% 1.61/1.81  thf('134', plain,
% 1.61/1.81      (![X0 : $i]:
% 1.61/1.81         ((zip_tseitin_0 @ sk_C @ X0) | ((k2_relat_1 @ sk_D_1) = (sk_C)))),
% 1.61/1.81      inference('sup-', [status(thm)], ['126', '133'])).
% 1.61/1.81  thf('135', plain, ((v5_relat_1 @ sk_D_1 @ sk_B)),
% 1.61/1.81      inference('sup-', [status(thm)], ['5', '6'])).
% 1.61/1.81  thf('136', plain,
% 1.61/1.81      (![X15 : $i, X16 : $i]:
% 1.61/1.81         (~ (v5_relat_1 @ X15 @ X16)
% 1.61/1.81          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 1.61/1.81          | ~ (v1_relat_1 @ X15))),
% 1.61/1.81      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.61/1.81  thf('137', plain,
% 1.61/1.81      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_B))),
% 1.61/1.81      inference('sup-', [status(thm)], ['135', '136'])).
% 1.61/1.81  thf('138', plain, ((v1_relat_1 @ sk_D_1)),
% 1.61/1.81      inference('demod', [status(thm)], ['14', '15'])).
% 1.61/1.81  thf('139', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_B)),
% 1.61/1.81      inference('demod', [status(thm)], ['137', '138'])).
% 1.61/1.81  thf('140', plain,
% 1.61/1.81      (![X0 : $i, X2 : $i]:
% 1.61/1.81         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.61/1.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.61/1.81  thf('141', plain,
% 1.61/1.81      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D_1))
% 1.61/1.81        | ((sk_B) = (k2_relat_1 @ sk_D_1)))),
% 1.61/1.81      inference('sup-', [status(thm)], ['139', '140'])).
% 1.61/1.81  thf('142', plain,
% 1.61/1.81      (![X0 : $i]:
% 1.61/1.81         (~ (r1_tarski @ sk_B @ sk_C)
% 1.61/1.81          | (zip_tseitin_0 @ sk_C @ X0)
% 1.61/1.81          | ((sk_B) = (k2_relat_1 @ sk_D_1)))),
% 1.61/1.81      inference('sup-', [status(thm)], ['134', '141'])).
% 1.61/1.81  thf('143', plain, ((r1_tarski @ sk_B @ sk_C)),
% 1.61/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.81  thf('144', plain,
% 1.61/1.81      (![X0 : $i]:
% 1.61/1.81         ((zip_tseitin_0 @ sk_C @ X0) | ((sk_B) = (k2_relat_1 @ sk_D_1)))),
% 1.61/1.81      inference('demod', [status(thm)], ['142', '143'])).
% 1.61/1.81  thf('145', plain,
% 1.61/1.81      (![X0 : $i]:
% 1.61/1.81         (((sk_B) = (k1_xboole_0))
% 1.61/1.81          | ~ (v1_xboole_0 @ sk_D_1)
% 1.61/1.81          | (zip_tseitin_0 @ sk_C @ X0))),
% 1.61/1.81      inference('sup+', [status(thm)], ['123', '144'])).
% 1.61/1.81  thf('146', plain, (((sk_B) != (k1_xboole_0))),
% 1.61/1.81      inference('simpl_trail', [status(thm)], ['55', '110'])).
% 1.61/1.81  thf('147', plain,
% 1.61/1.81      (![X0 : $i]: (~ (v1_xboole_0 @ sk_D_1) | (zip_tseitin_0 @ sk_C @ X0))),
% 1.61/1.81      inference('simplify_reflect-', [status(thm)], ['145', '146'])).
% 1.61/1.81  thf('148', plain,
% 1.61/1.81      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.61/1.81      inference('sup+', [status(thm)], ['124', '125'])).
% 1.61/1.81  thf('149', plain,
% 1.61/1.81      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.61/1.81      inference('sup+', [status(thm)], ['124', '125'])).
% 1.61/1.81  thf('150', plain, ((r1_tarski @ sk_B @ sk_C)),
% 1.61/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.81  thf('151', plain,
% 1.61/1.81      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 1.61/1.81      inference('cnf', [status(esa)], [t6_boole])).
% 1.61/1.81  thf('152', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 1.61/1.81      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.61/1.81  thf('153', plain,
% 1.61/1.81      (![X0 : $i, X2 : $i]:
% 1.61/1.81         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.61/1.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.61/1.81  thf('154', plain,
% 1.61/1.81      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.61/1.81      inference('sup-', [status(thm)], ['152', '153'])).
% 1.61/1.81  thf('155', plain,
% 1.61/1.81      (![X0 : $i, X1 : $i]:
% 1.61/1.81         (~ (r1_tarski @ X1 @ X0)
% 1.61/1.81          | ~ (v1_xboole_0 @ X0)
% 1.61/1.81          | ((X1) = (k1_xboole_0)))),
% 1.61/1.81      inference('sup-', [status(thm)], ['151', '154'])).
% 1.61/1.81  thf('156', plain, ((((sk_B) = (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_C))),
% 1.61/1.81      inference('sup-', [status(thm)], ['150', '155'])).
% 1.61/1.81  thf('157', plain,
% 1.61/1.81      (![X0 : $i]: ((zip_tseitin_0 @ sk_C @ X0) | ((sk_B) = (k1_xboole_0)))),
% 1.61/1.81      inference('sup-', [status(thm)], ['149', '156'])).
% 1.61/1.81  thf('158', plain,
% 1.61/1.81      (![X0 : $i, X1 : $i]:
% 1.61/1.81         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 1.61/1.81      inference('sup-', [status(thm)], ['76', '77'])).
% 1.61/1.81  thf('159', plain,
% 1.61/1.81      (![X0 : $i]:
% 1.61/1.81         (((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ k1_xboole_0 @ sk_C @ X0))),
% 1.61/1.81      inference('sup-', [status(thm)], ['157', '158'])).
% 1.61/1.81  thf('160', plain, (((sk_B) != (k1_xboole_0))),
% 1.61/1.81      inference('simpl_trail', [status(thm)], ['55', '110'])).
% 1.61/1.81  thf('161', plain, (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ sk_C @ X0)),
% 1.61/1.81      inference('simplify_reflect-', [status(thm)], ['159', '160'])).
% 1.61/1.81  thf('162', plain,
% 1.61/1.81      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 1.61/1.81      inference('cnf', [status(esa)], [t6_boole])).
% 1.61/1.81  thf('163', plain,
% 1.61/1.81      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.61/1.81         (((X44) != (k1_xboole_0))
% 1.61/1.81          | ((X45) = (k1_xboole_0))
% 1.61/1.81          | (v1_funct_2 @ X46 @ X45 @ X44)
% 1.61/1.81          | ((X46) != (k1_xboole_0))
% 1.61/1.81          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 1.61/1.81      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.61/1.81  thf('164', plain,
% 1.61/1.81      (![X45 : $i]:
% 1.61/1.81         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 1.61/1.81             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ k1_xboole_0)))
% 1.61/1.81          | (v1_funct_2 @ k1_xboole_0 @ X45 @ k1_xboole_0)
% 1.61/1.81          | ((X45) = (k1_xboole_0)))),
% 1.61/1.81      inference('simplify', [status(thm)], ['163'])).
% 1.61/1.81  thf('165', plain,
% 1.61/1.81      (![X6 : $i, X7 : $i]:
% 1.61/1.81         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 1.61/1.81      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.61/1.81  thf('166', plain,
% 1.61/1.81      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 1.61/1.81      inference('simplify', [status(thm)], ['165'])).
% 1.61/1.81  thf('167', plain,
% 1.61/1.81      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 1.61/1.81      inference('simplify', [status(thm)], ['165'])).
% 1.61/1.81  thf('168', plain,
% 1.61/1.81      (![X0 : $i, X1 : $i]:
% 1.61/1.81         (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))),
% 1.61/1.81      inference('demod', [status(thm)], ['58', '59', '63', '64', '65'])).
% 1.61/1.81  thf('169', plain,
% 1.61/1.81      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 1.61/1.81      inference('sup+', [status(thm)], ['167', '168'])).
% 1.61/1.81  thf('170', plain,
% 1.61/1.81      (![X45 : $i]:
% 1.61/1.81         ((v1_funct_2 @ k1_xboole_0 @ X45 @ k1_xboole_0)
% 1.61/1.81          | ((X45) = (k1_xboole_0)))),
% 1.61/1.81      inference('demod', [status(thm)], ['164', '166', '169'])).
% 1.61/1.81  thf('171', plain,
% 1.61/1.81      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.61/1.81         (~ (v1_funct_2 @ X43 @ X41 @ X42)
% 1.61/1.81          | ((X41) = (k1_relset_1 @ X41 @ X42 @ X43))
% 1.61/1.81          | ~ (zip_tseitin_1 @ X43 @ X42 @ X41))),
% 1.61/1.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.61/1.81  thf('172', plain,
% 1.61/1.81      (![X0 : $i]:
% 1.61/1.81         (((X0) = (k1_xboole_0))
% 1.61/1.81          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.61/1.81          | ((X0) = (k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)))),
% 1.61/1.81      inference('sup-', [status(thm)], ['170', '171'])).
% 1.61/1.81  thf('173', plain,
% 1.61/1.81      (![X0 : $i, X1 : $i]:
% 1.61/1.81         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.61/1.81      inference('demod', [status(thm)], ['68', '69'])).
% 1.61/1.81  thf('174', plain,
% 1.61/1.81      (![X0 : $i]:
% 1.61/1.81         (((X0) = (k1_xboole_0))
% 1.61/1.81          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.61/1.81          | ((X0) = (k1_xboole_0)))),
% 1.61/1.81      inference('demod', [status(thm)], ['172', '173'])).
% 1.61/1.81  thf('175', plain,
% 1.61/1.81      (![X0 : $i]:
% 1.61/1.81         (~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.61/1.81          | ((X0) = (k1_xboole_0)))),
% 1.61/1.81      inference('simplify', [status(thm)], ['174'])).
% 1.61/1.81  thf('176', plain,
% 1.61/1.81      (![X0 : $i, X1 : $i]:
% 1.61/1.81         (~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 1.61/1.81          | ~ (v1_xboole_0 @ X0)
% 1.61/1.81          | ((X1) = (k1_xboole_0)))),
% 1.61/1.81      inference('sup-', [status(thm)], ['162', '175'])).
% 1.61/1.81  thf('177', plain,
% 1.61/1.81      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_C))),
% 1.61/1.81      inference('sup-', [status(thm)], ['161', '176'])).
% 1.61/1.81  thf('178', plain,
% 1.61/1.81      (![X0 : $i, X1 : $i]:
% 1.61/1.81         ((zip_tseitin_0 @ sk_C @ X1) | ((X0) = (k1_xboole_0)))),
% 1.61/1.81      inference('sup-', [status(thm)], ['148', '177'])).
% 1.61/1.81  thf('179', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.61/1.81      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.61/1.81  thf('180', plain,
% 1.61/1.81      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ sk_C @ X1))),
% 1.61/1.81      inference('sup+', [status(thm)], ['178', '179'])).
% 1.61/1.81  thf('181', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 1.61/1.81      inference('clc', [status(thm)], ['147', '180'])).
% 1.61/1.81  thf('182', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_A)),
% 1.61/1.81      inference('demod', [status(thm)], ['120', '181'])).
% 1.61/1.81  thf('183', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)),
% 1.61/1.81      inference('demod', [status(thm)], ['117', '182'])).
% 1.61/1.81  thf('184', plain, ($false), inference('demod', [status(thm)], ['38', '183'])).
% 1.61/1.81  
% 1.61/1.81  % SZS output end Refutation
% 1.61/1.81  
% 1.61/1.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
