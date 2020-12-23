%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Al3kDMcfTZ

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:35 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  207 ( 916 expanded)
%              Number of leaves         :   40 ( 267 expanded)
%              Depth                    :   23
%              Number of atoms          : 1754 (18406 expanded)
%              Number of equality atoms :  121 ( 957 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t38_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ C @ A )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) )
            & ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B )
            & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ D @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ C @ A )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) )
              & ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B )
              & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ D @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ( ( k2_partfun1 @ X33 @ X34 @ X32 @ X35 )
        = ( k7_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['1','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X29 @ X30 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,(
    v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('20',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('22',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ k1_xboole_0 ) @ sk_C @ sk_B )
   <= ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('28',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('29',plain,
    ( ( v4_relat_1 @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7
        = ( k7_relat_1 @ X7 @ X8 ) )
      | ~ ( v4_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('31',plain,
    ( ( ~ ( v1_relat_1 @ sk_D )
      | ( sk_D
        = ( k7_relat_1 @ sk_D @ k1_xboole_0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('33',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('35',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('36',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_D
      = ( k7_relat_1 @ sk_D @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','36'])).

thf('38',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('39',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('40',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ( sk_A != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','37','38','41'])).

thf('43',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('44',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X29 @ X30 @ X28 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
        | ~ ( v1_funct_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('49',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
   <= ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('52',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('53',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['47','53'])).

thf('55',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('56',plain,(
    r1_tarski @ sk_C @ sk_A ),
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

thf('57',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('58',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('59',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('60',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('64',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('66',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('67',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['61','68'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('70',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X9 @ ( k1_relat_1 @ X10 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X9 ) )
        = X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['34','35'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
      = sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X29 @ X30 @ X28 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('82',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('85',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('89',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['87','88'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('90',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X36 ) @ X37 )
      | ( v1_funct_2 @ X36 @ ( k1_relat_1 @ X36 ) @ X37 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('94',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('97',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['91','94','97'])).

thf('99',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['74','98'])).

thf('100',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('101',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('103',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( sk_B != k1_xboole_0 )
      & ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('106',plain,(
    ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['14','42','54','55','104','105'])).

thf('107',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['7','106'])).

thf('108',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['61','68'])).

thf('110',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('111',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('113',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('115',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['34','35'])).

thf('117',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['117','120'])).

thf('122',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['115','116'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ sk_B )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('125',plain,
    ( ( r1_tarski @ k1_xboole_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('127',plain,
    ( ( r1_tarski @ k1_xboole_0 @ sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ sk_B )
      | ( zip_tseitin_0 @ X0 @ X1 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['110','127'])).

thf('129',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['115','116'])).

thf('130',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X36 ) @ X37 )
      | ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X36 ) @ X37 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('131',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['34','35'])).

thf('133',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('135',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('136',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_D ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( r1_tarski @ sk_B @ sk_B )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['128','136'])).

thf('138',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['109','137'])).

thf('139',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('140',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['14','42','54','105','55'])).

thf('141',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['138','141'])).

thf('143',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('144',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( r1_tarski @ sk_B @ sk_B ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_B = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['139','140'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['146','147'])).

thf('149',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('150',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('152',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X9 @ ( k1_relat_1 @ X10 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X9 ) )
        = X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['34','35'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['108','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('159',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X36 ) @ X37 )
      | ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X36 ) @ X37 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('162',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('163',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['160','161','162'])).

thf('164',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['157','163'])).

thf('165',plain,(
    $false ),
    inference(demod,[status(thm)],['107','164'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Al3kDMcfTZ
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:38:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.76/0.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.95  % Solved by: fo/fo7.sh
% 0.76/0.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.95  % done 814 iterations in 0.493s
% 0.76/0.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.95  % SZS output start Refutation
% 0.76/0.95  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.76/0.95  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.76/0.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.95  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.76/0.95  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.95  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.76/0.95  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.76/0.95  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.95  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.76/0.95  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.76/0.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.95  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.76/0.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.95  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/0.95  thf(sk_C_type, type, sk_C: $i).
% 0.76/0.95  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.76/0.95  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.76/0.95  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.76/0.95  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.76/0.95  thf(sk_D_type, type, sk_D: $i).
% 0.76/0.95  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.95  thf(t38_funct_2, conjecture,
% 0.76/0.95    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.95     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.76/0.95         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.95       ( ( r1_tarski @ C @ A ) =>
% 0.76/0.95         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.76/0.95           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 0.76/0.95             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 0.76/0.95             ( m1_subset_1 @
% 0.76/0.95               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 0.76/0.95               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 0.76/0.95  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.95    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.95        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.76/0.95            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.95          ( ( r1_tarski @ C @ A ) =>
% 0.76/0.95            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.76/0.95              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 0.76/0.95                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 0.76/0.95                ( m1_subset_1 @
% 0.76/0.95                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 0.76/0.95                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 0.76/0.95    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 0.76/0.95  thf('0', plain,
% 0.76/0.95      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 0.76/0.95        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 0.76/0.95             sk_B)
% 0.76/0.95        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.76/0.95             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('1', plain,
% 0.76/0.95      ((~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.76/0.95           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))
% 0.76/0.95         <= (~
% 0.76/0.95             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.76/0.95               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 0.76/0.95      inference('split', [status(esa)], ['0'])).
% 0.76/0.95  thf('2', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf(redefinition_k2_partfun1, axiom,
% 0.76/0.95    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.95     ( ( ( v1_funct_1 @ C ) & 
% 0.76/0.95         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.95       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.76/0.95  thf('3', plain,
% 0.76/0.95      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.76/0.95         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.76/0.95          | ~ (v1_funct_1 @ X32)
% 0.76/0.95          | ((k2_partfun1 @ X33 @ X34 @ X32 @ X35) = (k7_relat_1 @ X32 @ X35)))),
% 0.76/0.95      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.76/0.95  thf('4', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 0.76/0.95          | ~ (v1_funct_1 @ sk_D))),
% 0.76/0.95      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.95  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('6', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.76/0.95      inference('demod', [status(thm)], ['4', '5'])).
% 0.76/0.95  thf('7', plain,
% 0.76/0.95      ((~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 0.76/0.95           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))
% 0.76/0.95         <= (~
% 0.76/0.95             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.76/0.95               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 0.76/0.95      inference('demod', [status(thm)], ['1', '6'])).
% 0.76/0.95  thf('8', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf(dt_k2_partfun1, axiom,
% 0.76/0.95    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.95     ( ( ( v1_funct_1 @ C ) & 
% 0.76/0.95         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.95       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 0.76/0.95         ( m1_subset_1 @
% 0.76/0.95           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 0.76/0.95           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.76/0.95  thf('9', plain,
% 0.76/0.95      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.76/0.95         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.76/0.95          | ~ (v1_funct_1 @ X28)
% 0.76/0.95          | (v1_funct_1 @ (k2_partfun1 @ X29 @ X30 @ X28 @ X31)))),
% 0.76/0.95      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 0.76/0.95  thf('10', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 0.76/0.95          | ~ (v1_funct_1 @ sk_D))),
% 0.76/0.95      inference('sup-', [status(thm)], ['8', '9'])).
% 0.76/0.95  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('12', plain,
% 0.76/0.95      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 0.76/0.95      inference('demod', [status(thm)], ['10', '11'])).
% 0.76/0.95  thf('13', plain,
% 0.76/0.95      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C)))
% 0.76/0.95         <= (~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))))),
% 0.76/0.95      inference('split', [status(esa)], ['0'])).
% 0.76/0.95  thf('14', plain,
% 0.76/0.95      (((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['12', '13'])).
% 0.76/0.95  thf('15', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('16', plain,
% 0.76/0.95      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('split', [status(esa)], ['15'])).
% 0.76/0.95  thf('17', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('18', plain,
% 0.76/0.95      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup+', [status(thm)], ['16', '17'])).
% 0.76/0.95  thf(t3_xboole_1, axiom,
% 0.76/0.95    (![A:$i]:
% 0.76/0.95     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.76/0.95  thf('19', plain,
% 0.76/0.95      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.76/0.95      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.76/0.95  thf('20', plain,
% 0.76/0.95      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['18', '19'])).
% 0.76/0.95  thf('21', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.76/0.95      inference('demod', [status(thm)], ['4', '5'])).
% 0.76/0.95  thf('22', plain,
% 0.76/0.95      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B))
% 0.76/0.95         <= (~
% 0.76/0.95             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 0.76/0.95               sk_B)))),
% 0.76/0.95      inference('split', [status(esa)], ['0'])).
% 0.76/0.95  thf('23', plain,
% 0.76/0.95      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B))
% 0.76/0.95         <= (~
% 0.76/0.95             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 0.76/0.95               sk_B)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['21', '22'])).
% 0.76/0.95  thf('24', plain,
% 0.76/0.95      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ k1_xboole_0) @ sk_C @ sk_B))
% 0.76/0.95         <= (~
% 0.76/0.95             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 0.76/0.95               sk_B)) & 
% 0.76/0.95             (((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['20', '23'])).
% 0.76/0.95  thf('25', plain,
% 0.76/0.95      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('split', [status(esa)], ['15'])).
% 0.76/0.95  thf('26', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('27', plain,
% 0.76/0.95      (((m1_subset_1 @ sk_D @ 
% 0.76/0.95         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.76/0.95         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup+', [status(thm)], ['25', '26'])).
% 0.76/0.95  thf(cc2_relset_1, axiom,
% 0.76/0.95    (![A:$i,B:$i,C:$i]:
% 0.76/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.95       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.76/0.95  thf('28', plain,
% 0.76/0.95      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.76/0.95         ((v4_relat_1 @ X14 @ X15)
% 0.76/0.95          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.76/0.95      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.76/0.95  thf('29', plain,
% 0.76/0.95      (((v4_relat_1 @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['27', '28'])).
% 0.76/0.95  thf(t209_relat_1, axiom,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.76/0.95       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.76/0.95  thf('30', plain,
% 0.76/0.95      (![X7 : $i, X8 : $i]:
% 0.76/0.95         (((X7) = (k7_relat_1 @ X7 @ X8))
% 0.76/0.95          | ~ (v4_relat_1 @ X7 @ X8)
% 0.76/0.95          | ~ (v1_relat_1 @ X7))),
% 0.76/0.95      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.76/0.95  thf('31', plain,
% 0.76/0.95      (((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ k1_xboole_0))))
% 0.76/0.95         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['29', '30'])).
% 0.76/0.95  thf('32', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf(cc2_relat_1, axiom,
% 0.76/0.95    (![A:$i]:
% 0.76/0.95     ( ( v1_relat_1 @ A ) =>
% 0.76/0.95       ( ![B:$i]:
% 0.76/0.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.76/0.95  thf('33', plain,
% 0.76/0.95      (![X1 : $i, X2 : $i]:
% 0.76/0.95         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.76/0.95          | (v1_relat_1 @ X1)
% 0.76/0.95          | ~ (v1_relat_1 @ X2))),
% 0.76/0.95      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.76/0.95  thf('34', plain,
% 0.76/0.95      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.76/0.95      inference('sup-', [status(thm)], ['32', '33'])).
% 0.76/0.95  thf(fc6_relat_1, axiom,
% 0.76/0.95    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.76/0.95  thf('35', plain,
% 0.76/0.95      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.76/0.95      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.76/0.95  thf('36', plain, ((v1_relat_1 @ sk_D)),
% 0.76/0.95      inference('demod', [status(thm)], ['34', '35'])).
% 0.76/0.95  thf('37', plain,
% 0.76/0.95      ((((sk_D) = (k7_relat_1 @ sk_D @ k1_xboole_0)))
% 0.76/0.95         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('demod', [status(thm)], ['31', '36'])).
% 0.76/0.95  thf('38', plain,
% 0.76/0.95      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['18', '19'])).
% 0.76/0.95  thf('39', plain,
% 0.76/0.95      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('split', [status(esa)], ['15'])).
% 0.76/0.95  thf('40', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('41', plain,
% 0.76/0.95      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 0.76/0.95         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup+', [status(thm)], ['39', '40'])).
% 0.76/0.95  thf('42', plain,
% 0.76/0.95      (((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)) | 
% 0.76/0.95       ~ (((sk_A) = (k1_xboole_0)))),
% 0.76/0.95      inference('demod', [status(thm)], ['24', '37', '38', '41'])).
% 0.76/0.95  thf('43', plain,
% 0.76/0.95      (((m1_subset_1 @ sk_D @ 
% 0.76/0.95         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.76/0.95         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup+', [status(thm)], ['25', '26'])).
% 0.76/0.95  thf('44', plain,
% 0.76/0.95      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.76/0.95         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.76/0.95          | ~ (v1_funct_1 @ X28)
% 0.76/0.95          | (m1_subset_1 @ (k2_partfun1 @ X29 @ X30 @ X28 @ X31) @ 
% 0.76/0.95             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.76/0.95      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 0.76/0.95  thf('45', plain,
% 0.76/0.95      ((![X0 : $i]:
% 0.76/0.95          ((m1_subset_1 @ (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ X0) @ 
% 0.76/0.95            (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B)))
% 0.76/0.95           | ~ (v1_funct_1 @ sk_D)))
% 0.76/0.95         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['43', '44'])).
% 0.76/0.95  thf('46', plain, ((v1_funct_1 @ sk_D)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('47', plain,
% 0.76/0.95      ((![X0 : $i]:
% 0.76/0.95          (m1_subset_1 @ (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ X0) @ 
% 0.76/0.95           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.76/0.95         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('demod', [status(thm)], ['45', '46'])).
% 0.76/0.95  thf('48', plain,
% 0.76/0.95      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('split', [status(esa)], ['15'])).
% 0.76/0.95  thf('49', plain,
% 0.76/0.95      ((~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.76/0.95           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))
% 0.76/0.95         <= (~
% 0.76/0.95             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.76/0.95               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 0.76/0.95      inference('split', [status(esa)], ['0'])).
% 0.76/0.95  thf('50', plain,
% 0.76/0.95      ((~ (m1_subset_1 @ (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C) @ 
% 0.76/0.95           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))
% 0.76/0.95         <= (~
% 0.76/0.95             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.76/0.95               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))) & 
% 0.76/0.95             (((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['48', '49'])).
% 0.76/0.95  thf('51', plain,
% 0.76/0.95      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['18', '19'])).
% 0.76/0.95  thf('52', plain,
% 0.76/0.95      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['18', '19'])).
% 0.76/0.95  thf('53', plain,
% 0.76/0.95      ((~ (m1_subset_1 @ 
% 0.76/0.95           (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ k1_xboole_0) @ 
% 0.76/0.95           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.76/0.95         <= (~
% 0.76/0.95             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.76/0.95               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))) & 
% 0.76/0.95             (((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.76/0.95  thf('54', plain,
% 0.76/0.95      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.76/0.95       ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.76/0.95         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['47', '53'])).
% 0.76/0.95  thf('55', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.76/0.95      inference('split', [status(esa)], ['15'])).
% 0.76/0.95  thf('56', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf(d1_funct_2, axiom,
% 0.76/0.95    (![A:$i,B:$i,C:$i]:
% 0.76/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.95       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.76/0.95           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.76/0.95             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.76/0.95         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.76/0.95           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.76/0.95             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.76/0.95  thf(zf_stmt_1, axiom,
% 0.76/0.95    (![B:$i,A:$i]:
% 0.76/0.95     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.76/0.95       ( zip_tseitin_0 @ B @ A ) ))).
% 0.76/0.95  thf('57', plain,
% 0.76/0.95      (![X20 : $i, X21 : $i]:
% 0.76/0.95         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.76/0.95  thf('58', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.76/0.95  thf(zf_stmt_3, axiom,
% 0.76/0.95    (![C:$i,B:$i,A:$i]:
% 0.76/0.95     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.76/0.95       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.76/0.95  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.76/0.95  thf(zf_stmt_5, axiom,
% 0.76/0.95    (![A:$i,B:$i,C:$i]:
% 0.76/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.95       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.76/0.95         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.76/0.95           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.76/0.95             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.76/0.95  thf('59', plain,
% 0.76/0.95      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.76/0.95         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.76/0.95          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.76/0.95          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.76/0.95  thf('60', plain,
% 0.76/0.95      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.76/0.95      inference('sup-', [status(thm)], ['58', '59'])).
% 0.76/0.95  thf('61', plain,
% 0.76/0.95      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.76/0.95      inference('sup-', [status(thm)], ['57', '60'])).
% 0.76/0.95  thf('62', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('63', plain,
% 0.76/0.95      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.76/0.95         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.76/0.95          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 0.76/0.95          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.76/0.95  thf('64', plain,
% 0.76/0.95      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.76/0.95        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['62', '63'])).
% 0.76/0.95  thf('65', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf(redefinition_k1_relset_1, axiom,
% 0.76/0.95    (![A:$i,B:$i,C:$i]:
% 0.76/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.95       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.76/0.95  thf('66', plain,
% 0.76/0.95      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.76/0.95         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.76/0.95          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.76/0.95      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.76/0.95  thf('67', plain,
% 0.76/0.95      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.76/0.95      inference('sup-', [status(thm)], ['65', '66'])).
% 0.76/0.95  thf('68', plain,
% 0.76/0.95      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.76/0.95      inference('demod', [status(thm)], ['64', '67'])).
% 0.76/0.95  thf('69', plain,
% 0.76/0.95      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['61', '68'])).
% 0.76/0.95  thf(t91_relat_1, axiom,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( v1_relat_1 @ B ) =>
% 0.76/0.95       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.76/0.95         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.76/0.95  thf('70', plain,
% 0.76/0.95      (![X9 : $i, X10 : $i]:
% 0.76/0.95         (~ (r1_tarski @ X9 @ (k1_relat_1 @ X10))
% 0.76/0.95          | ((k1_relat_1 @ (k7_relat_1 @ X10 @ X9)) = (X9))
% 0.76/0.95          | ~ (v1_relat_1 @ X10))),
% 0.76/0.95      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.76/0.95  thf('71', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         (~ (r1_tarski @ X0 @ sk_A)
% 0.76/0.95          | ((sk_B) = (k1_xboole_0))
% 0.76/0.95          | ~ (v1_relat_1 @ sk_D)
% 0.76/0.95          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['69', '70'])).
% 0.76/0.95  thf('72', plain, ((v1_relat_1 @ sk_D)),
% 0.76/0.95      inference('demod', [status(thm)], ['34', '35'])).
% 0.76/0.95  thf('73', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         (~ (r1_tarski @ X0 @ sk_A)
% 0.76/0.95          | ((sk_B) = (k1_xboole_0))
% 0.76/0.95          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 0.76/0.95      inference('demod', [status(thm)], ['71', '72'])).
% 0.76/0.95  thf('74', plain,
% 0.76/0.95      ((((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))
% 0.76/0.95        | ((sk_B) = (k1_xboole_0)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['56', '73'])).
% 0.76/0.95  thf('75', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('76', plain,
% 0.76/0.95      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.76/0.95         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.76/0.95          | ~ (v1_funct_1 @ X28)
% 0.76/0.95          | (m1_subset_1 @ (k2_partfun1 @ X29 @ X30 @ X28 @ X31) @ 
% 0.76/0.95             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.76/0.95      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 0.76/0.95  thf('77', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 0.76/0.95           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.76/0.95          | ~ (v1_funct_1 @ sk_D))),
% 0.76/0.95      inference('sup-', [status(thm)], ['75', '76'])).
% 0.76/0.95  thf('78', plain, ((v1_funct_1 @ sk_D)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('79', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 0.76/0.95          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.95      inference('demod', [status(thm)], ['77', '78'])).
% 0.76/0.95  thf('80', plain,
% 0.76/0.95      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.76/0.95         ((v5_relat_1 @ X14 @ X16)
% 0.76/0.95          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.76/0.95      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.76/0.95  thf('81', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         (v5_relat_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ sk_B)),
% 0.76/0.95      inference('sup-', [status(thm)], ['79', '80'])).
% 0.76/0.95  thf(d19_relat_1, axiom,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( v1_relat_1 @ B ) =>
% 0.76/0.95       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.76/0.95  thf('82', plain,
% 0.76/0.95      (![X3 : $i, X4 : $i]:
% 0.76/0.95         (~ (v5_relat_1 @ X3 @ X4)
% 0.76/0.95          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 0.76/0.95          | ~ (v1_relat_1 @ X3))),
% 0.76/0.95      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.76/0.95  thf('83', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         (~ (v1_relat_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 0.76/0.95          | (r1_tarski @ 
% 0.76/0.95             (k2_relat_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0)) @ sk_B))),
% 0.76/0.95      inference('sup-', [status(thm)], ['81', '82'])).
% 0.76/0.95  thf('84', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 0.76/0.95          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.95      inference('demod', [status(thm)], ['77', '78'])).
% 0.76/0.95  thf(cc1_relset_1, axiom,
% 0.76/0.95    (![A:$i,B:$i,C:$i]:
% 0.76/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.95       ( v1_relat_1 @ C ) ))).
% 0.76/0.95  thf('85', plain,
% 0.76/0.95      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.76/0.95         ((v1_relat_1 @ X11)
% 0.76/0.95          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.76/0.95      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.76/0.95  thf('86', plain,
% 0.76/0.95      (![X0 : $i]: (v1_relat_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 0.76/0.95      inference('sup-', [status(thm)], ['84', '85'])).
% 0.76/0.95  thf('87', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         (r1_tarski @ (k2_relat_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0)) @ 
% 0.76/0.95          sk_B)),
% 0.76/0.95      inference('demod', [status(thm)], ['83', '86'])).
% 0.76/0.95  thf('88', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.76/0.95      inference('demod', [status(thm)], ['4', '5'])).
% 0.76/0.95  thf('89', plain,
% 0.76/0.95      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 0.76/0.95      inference('demod', [status(thm)], ['87', '88'])).
% 0.76/0.95  thf(t4_funct_2, axiom,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.76/0.95       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.76/0.95         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.76/0.95           ( m1_subset_1 @
% 0.76/0.95             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.76/0.95  thf('90', plain,
% 0.76/0.95      (![X36 : $i, X37 : $i]:
% 0.76/0.95         (~ (r1_tarski @ (k2_relat_1 @ X36) @ X37)
% 0.76/0.95          | (v1_funct_2 @ X36 @ (k1_relat_1 @ X36) @ X37)
% 0.76/0.95          | ~ (v1_funct_1 @ X36)
% 0.76/0.95          | ~ (v1_relat_1 @ X36))),
% 0.76/0.95      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.76/0.95  thf('91', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 0.76/0.95          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 0.76/0.95          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.76/0.95             (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 0.76/0.95      inference('sup-', [status(thm)], ['89', '90'])).
% 0.76/0.95  thf('92', plain,
% 0.76/0.95      (![X0 : $i]: (v1_relat_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 0.76/0.95      inference('sup-', [status(thm)], ['84', '85'])).
% 0.76/0.95  thf('93', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.76/0.95      inference('demod', [status(thm)], ['4', '5'])).
% 0.76/0.95  thf('94', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 0.76/0.95      inference('demod', [status(thm)], ['92', '93'])).
% 0.76/0.95  thf('95', plain,
% 0.76/0.95      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 0.76/0.95      inference('demod', [status(thm)], ['10', '11'])).
% 0.76/0.95  thf('96', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.76/0.95      inference('demod', [status(thm)], ['4', '5'])).
% 0.76/0.95  thf('97', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 0.76/0.95      inference('demod', [status(thm)], ['95', '96'])).
% 0.76/0.95  thf('98', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.76/0.95          (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 0.76/0.95      inference('demod', [status(thm)], ['91', '94', '97'])).
% 0.76/0.95  thf('99', plain,
% 0.76/0.95      (((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 0.76/0.95        | ((sk_B) = (k1_xboole_0)))),
% 0.76/0.95      inference('sup+', [status(thm)], ['74', '98'])).
% 0.76/0.95  thf('100', plain,
% 0.76/0.95      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B))
% 0.76/0.95         <= (~
% 0.76/0.95             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 0.76/0.95               sk_B)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['21', '22'])).
% 0.76/0.95  thf('101', plain,
% 0.76/0.95      ((((sk_B) = (k1_xboole_0)))
% 0.76/0.95         <= (~
% 0.76/0.95             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 0.76/0.95               sk_B)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['99', '100'])).
% 0.76/0.95  thf('102', plain,
% 0.76/0.95      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.76/0.95      inference('split', [status(esa)], ['15'])).
% 0.76/0.95  thf('103', plain,
% 0.76/0.95      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.76/0.95         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.76/0.95             ~
% 0.76/0.95             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 0.76/0.95               sk_B)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['101', '102'])).
% 0.76/0.95  thf('104', plain,
% 0.76/0.95      (((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)) | 
% 0.76/0.95       (((sk_B) = (k1_xboole_0)))),
% 0.76/0.95      inference('simplify', [status(thm)], ['103'])).
% 0.76/0.95  thf('105', plain,
% 0.76/0.95      (~
% 0.76/0.95       ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.76/0.95         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))) | 
% 0.76/0.95       ~
% 0.76/0.95       ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)) | 
% 0.76/0.95       ~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C)))),
% 0.76/0.95      inference('split', [status(esa)], ['0'])).
% 0.76/0.95  thf('106', plain,
% 0.76/0.95      (~
% 0.76/0.95       ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.76/0.95         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 0.76/0.95      inference('sat_resolution*', [status(thm)],
% 0.76/0.95                ['14', '42', '54', '55', '104', '105'])).
% 0.76/0.95  thf('107', plain,
% 0.76/0.95      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 0.76/0.95          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.76/0.95      inference('simpl_trail', [status(thm)], ['7', '106'])).
% 0.76/0.95  thf('108', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('109', plain,
% 0.76/0.95      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['61', '68'])).
% 0.76/0.95  thf('110', plain,
% 0.76/0.95      (![X20 : $i, X21 : $i]:
% 0.76/0.95         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.76/0.95  thf('111', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('112', plain,
% 0.76/0.95      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.76/0.95         ((v5_relat_1 @ X14 @ X16)
% 0.76/0.95          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.76/0.95      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.76/0.95  thf('113', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 0.76/0.95      inference('sup-', [status(thm)], ['111', '112'])).
% 0.76/0.95  thf('114', plain,
% 0.76/0.95      (![X3 : $i, X4 : $i]:
% 0.76/0.95         (~ (v5_relat_1 @ X3 @ X4)
% 0.76/0.95          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 0.76/0.95          | ~ (v1_relat_1 @ X3))),
% 0.76/0.95      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.76/0.95  thf('115', plain,
% 0.76/0.95      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 0.76/0.95      inference('sup-', [status(thm)], ['113', '114'])).
% 0.76/0.95  thf('116', plain, ((v1_relat_1 @ sk_D)),
% 0.76/0.95      inference('demod', [status(thm)], ['34', '35'])).
% 0.76/0.95  thf('117', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 0.76/0.95      inference('demod', [status(thm)], ['115', '116'])).
% 0.76/0.95  thf('118', plain,
% 0.76/0.95      (![X20 : $i, X21 : $i]:
% 0.76/0.95         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.76/0.95  thf('119', plain,
% 0.76/0.95      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.76/0.95      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.76/0.95  thf('120', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.95         (~ (r1_tarski @ X1 @ X0)
% 0.76/0.95          | (zip_tseitin_0 @ X0 @ X2)
% 0.76/0.95          | ((X1) = (k1_xboole_0)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['118', '119'])).
% 0.76/0.95  thf('121', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         (((k2_relat_1 @ sk_D) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_B @ X0))),
% 0.76/0.95      inference('sup-', [status(thm)], ['117', '120'])).
% 0.76/0.95  thf('122', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 0.76/0.95      inference('demod', [status(thm)], ['115', '116'])).
% 0.76/0.95  thf('123', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((r1_tarski @ k1_xboole_0 @ sk_B) | (zip_tseitin_0 @ sk_B @ X0))),
% 0.76/0.95      inference('sup+', [status(thm)], ['121', '122'])).
% 0.76/0.95  thf('124', plain,
% 0.76/0.95      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.76/0.95      inference('sup-', [status(thm)], ['58', '59'])).
% 0.76/0.95  thf('125', plain,
% 0.76/0.95      (((r1_tarski @ k1_xboole_0 @ sk_B) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.76/0.95      inference('sup-', [status(thm)], ['123', '124'])).
% 0.76/0.95  thf('126', plain,
% 0.76/0.95      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.76/0.95      inference('demod', [status(thm)], ['64', '67'])).
% 0.76/0.95  thf('127', plain,
% 0.76/0.95      (((r1_tarski @ k1_xboole_0 @ sk_B) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['125', '126'])).
% 0.76/0.95  thf('128', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((r1_tarski @ X0 @ sk_B)
% 0.76/0.95          | (zip_tseitin_0 @ X0 @ X1)
% 0.76/0.95          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.76/0.95      inference('sup+', [status(thm)], ['110', '127'])).
% 0.76/0.95  thf('129', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 0.76/0.95      inference('demod', [status(thm)], ['115', '116'])).
% 0.76/0.95  thf('130', plain,
% 0.76/0.95      (![X36 : $i, X37 : $i]:
% 0.76/0.95         (~ (r1_tarski @ (k2_relat_1 @ X36) @ X37)
% 0.76/0.95          | (m1_subset_1 @ X36 @ 
% 0.76/0.95             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X36) @ X37)))
% 0.76/0.95          | ~ (v1_funct_1 @ X36)
% 0.76/0.95          | ~ (v1_relat_1 @ X36))),
% 0.76/0.95      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.76/0.95  thf('131', plain,
% 0.76/0.95      ((~ (v1_relat_1 @ sk_D)
% 0.76/0.95        | ~ (v1_funct_1 @ sk_D)
% 0.76/0.95        | (m1_subset_1 @ sk_D @ 
% 0.76/0.95           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['129', '130'])).
% 0.76/0.95  thf('132', plain, ((v1_relat_1 @ sk_D)),
% 0.76/0.95      inference('demod', [status(thm)], ['34', '35'])).
% 0.76/0.95  thf('133', plain, ((v1_funct_1 @ sk_D)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('134', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_D @ 
% 0.76/0.95        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.76/0.95      inference('demod', [status(thm)], ['131', '132', '133'])).
% 0.76/0.95  thf('135', plain,
% 0.76/0.95      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.76/0.95         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.76/0.95          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.76/0.95          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.76/0.95  thf('136', plain,
% 0.76/0.95      (((zip_tseitin_1 @ sk_D @ sk_B @ (k1_relat_1 @ sk_D))
% 0.76/0.95        | ~ (zip_tseitin_0 @ sk_B @ (k1_relat_1 @ sk_D)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['134', '135'])).
% 0.76/0.95  thf('137', plain,
% 0.76/0.95      ((((sk_A) = (k1_relat_1 @ sk_D))
% 0.76/0.95        | (r1_tarski @ sk_B @ sk_B)
% 0.76/0.95        | (zip_tseitin_1 @ sk_D @ sk_B @ (k1_relat_1 @ sk_D)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['128', '136'])).
% 0.76/0.95  thf('138', plain,
% 0.76/0.95      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.76/0.95        | ((sk_B) = (k1_xboole_0))
% 0.76/0.95        | (r1_tarski @ sk_B @ sk_B)
% 0.76/0.95        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.76/0.95      inference('sup+', [status(thm)], ['109', '137'])).
% 0.76/0.95  thf('139', plain,
% 0.76/0.95      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.76/0.95      inference('split', [status(esa)], ['15'])).
% 0.76/0.95  thf('140', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.76/0.95      inference('sat_resolution*', [status(thm)],
% 0.76/0.95                ['14', '42', '54', '105', '55'])).
% 0.76/0.95  thf('141', plain, (((sk_B) != (k1_xboole_0))),
% 0.76/0.95      inference('simpl_trail', [status(thm)], ['139', '140'])).
% 0.76/0.95  thf('142', plain,
% 0.76/0.95      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.76/0.95        | (r1_tarski @ sk_B @ sk_B)
% 0.76/0.95        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.76/0.95      inference('simplify_reflect-', [status(thm)], ['138', '141'])).
% 0.76/0.95  thf('143', plain,
% 0.76/0.95      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.76/0.95      inference('demod', [status(thm)], ['64', '67'])).
% 0.76/0.95  thf('144', plain,
% 0.76/0.95      ((((sk_A) = (k1_relat_1 @ sk_D)) | (r1_tarski @ sk_B @ sk_B))),
% 0.76/0.95      inference('clc', [status(thm)], ['142', '143'])).
% 0.76/0.95  thf('145', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.95         (~ (r1_tarski @ X1 @ X0)
% 0.76/0.95          | (zip_tseitin_0 @ X0 @ X2)
% 0.76/0.95          | ((X1) = (k1_xboole_0)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['118', '119'])).
% 0.76/0.95  thf('146', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         (((sk_A) = (k1_relat_1 @ sk_D))
% 0.76/0.95          | ((sk_B) = (k1_xboole_0))
% 0.76/0.95          | (zip_tseitin_0 @ sk_B @ X0))),
% 0.76/0.95      inference('sup-', [status(thm)], ['144', '145'])).
% 0.76/0.95  thf('147', plain, (((sk_B) != (k1_xboole_0))),
% 0.76/0.95      inference('simpl_trail', [status(thm)], ['139', '140'])).
% 0.76/0.95  thf('148', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         (((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_0 @ sk_B @ X0))),
% 0.76/0.95      inference('simplify_reflect-', [status(thm)], ['146', '147'])).
% 0.76/0.95  thf('149', plain,
% 0.76/0.95      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.76/0.95      inference('sup-', [status(thm)], ['58', '59'])).
% 0.76/0.95  thf('150', plain,
% 0.76/0.95      ((((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.76/0.95      inference('sup-', [status(thm)], ['148', '149'])).
% 0.76/0.95  thf('151', plain,
% 0.76/0.95      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.76/0.95      inference('demod', [status(thm)], ['64', '67'])).
% 0.76/0.95  thf('152', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.76/0.95      inference('clc', [status(thm)], ['150', '151'])).
% 0.76/0.95  thf('153', plain,
% 0.76/0.95      (![X9 : $i, X10 : $i]:
% 0.76/0.95         (~ (r1_tarski @ X9 @ (k1_relat_1 @ X10))
% 0.76/0.95          | ((k1_relat_1 @ (k7_relat_1 @ X10 @ X9)) = (X9))
% 0.76/0.95          | ~ (v1_relat_1 @ X10))),
% 0.76/0.95      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.76/0.95  thf('154', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         (~ (r1_tarski @ X0 @ sk_A)
% 0.76/0.95          | ~ (v1_relat_1 @ sk_D)
% 0.76/0.95          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['152', '153'])).
% 0.76/0.95  thf('155', plain, ((v1_relat_1 @ sk_D)),
% 0.76/0.95      inference('demod', [status(thm)], ['34', '35'])).
% 0.76/0.95  thf('156', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         (~ (r1_tarski @ X0 @ sk_A)
% 0.76/0.95          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 0.76/0.95      inference('demod', [status(thm)], ['154', '155'])).
% 0.76/0.95  thf('157', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 0.76/0.95      inference('sup-', [status(thm)], ['108', '156'])).
% 0.76/0.95  thf('158', plain,
% 0.76/0.95      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 0.76/0.95      inference('demod', [status(thm)], ['87', '88'])).
% 0.76/0.95  thf('159', plain,
% 0.76/0.95      (![X36 : $i, X37 : $i]:
% 0.76/0.95         (~ (r1_tarski @ (k2_relat_1 @ X36) @ X37)
% 0.76/0.95          | (m1_subset_1 @ X36 @ 
% 0.76/0.95             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X36) @ X37)))
% 0.76/0.95          | ~ (v1_funct_1 @ X36)
% 0.76/0.95          | ~ (v1_relat_1 @ X36))),
% 0.76/0.95      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.76/0.95  thf('160', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 0.76/0.95          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 0.76/0.95          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.76/0.95             (k1_zfmisc_1 @ 
% 0.76/0.95              (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['158', '159'])).
% 0.76/0.95  thf('161', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 0.76/0.95      inference('demod', [status(thm)], ['92', '93'])).
% 0.76/0.95  thf('162', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 0.76/0.95      inference('demod', [status(thm)], ['95', '96'])).
% 0.76/0.95  thf('163', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.76/0.95          (k1_zfmisc_1 @ 
% 0.76/0.95           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)))),
% 0.76/0.95      inference('demod', [status(thm)], ['160', '161', '162'])).
% 0.76/0.95  thf('164', plain,
% 0.76/0.95      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 0.76/0.95        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.76/0.95      inference('sup+', [status(thm)], ['157', '163'])).
% 0.76/0.95  thf('165', plain, ($false), inference('demod', [status(thm)], ['107', '164'])).
% 0.76/0.95  
% 0.76/0.95  % SZS output end Refutation
% 0.76/0.95  
% 0.76/0.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
