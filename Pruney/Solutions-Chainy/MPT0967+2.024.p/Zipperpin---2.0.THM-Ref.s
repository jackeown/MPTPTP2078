%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pEacZCaMcj

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:14 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 500 expanded)
%              Number of leaves         :   38 ( 154 expanded)
%              Depth                    :   21
%              Number of atoms          : 1111 (6300 expanded)
%              Number of equality atoms :   80 ( 413 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf('0',plain,(
    r1_tarski @ sk_B @ sk_C ),
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
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v5_relat_1 @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v5_relat_1 @ X22 @ X23 )
      | ( r1_tarski @ ( k2_relat_1 @ X22 ) @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X24: $i,X25: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['10','15'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['5','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('22',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('23',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v4_relat_1 @ X20 @ X21 )
      | ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('26',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['24','25'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('27',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X32 ) @ X33 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X32 ) @ X34 )
      | ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','30'])).

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

thf('32',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('33',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','30'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('35',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('36',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ( X37
        = ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('42',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('47',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['52'])).

thf('54',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['51','53'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('55',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('56',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('59',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('60',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v4_relat_1 @ X20 @ X21 )
      | ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('63',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('64',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X24: $i,X25: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('66',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['62','66'])).

thf('68',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('69',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','69'])).

thf('71',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( X37
       != ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

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
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X36 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('75',plain,(
    ! [X35: $i] :
      ( zip_tseitin_0 @ X35 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('77',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
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

thf('81',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('82',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('83',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['81','84'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('86',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('87',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('89',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('91',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['52'])).

thf('92',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','93'])).

thf('95',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['81','84'])).

thf('96',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('97',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('98',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['52'])).

thf('99',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('101',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['95','100'])).

thf('102',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['52'])).

thf('103',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('104',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['54','94','101','102','103'])).

thf('105',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['50','104'])).

thf('106',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['48','105'])).

thf('107',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['43','106'])).

thf('108',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['36','107'])).

thf('109',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( X37
       != ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('110',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['52'])).

thf('113',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','30'])).

thf('114',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['52'])).

thf('115',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['52'])).

thf('117',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['54','115','116'])).

thf('118',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['112','117'])).

thf('119',plain,(
    ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['111','118'])).

thf('120',plain,(
    ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['33','119'])).

thf('121',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','120'])).

thf('122',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['50','104'])).

thf('123',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['121','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pEacZCaMcj
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:34:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 441 iterations in 0.209s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.66  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.46/0.66  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.66  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.46/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.66  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.66  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.66  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.46/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.66  thf(t9_funct_2, conjecture,
% 0.46/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.66     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.66         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.66       ( ( r1_tarski @ B @ C ) =>
% 0.46/0.66         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.46/0.66           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.46/0.66             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.66    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.66        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.66            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.66          ( ( r1_tarski @ B @ C ) =>
% 0.46/0.66            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.46/0.66              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.46/0.66                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t9_funct_2])).
% 0.46/0.66  thf('0', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(d1_funct_2, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.66       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.66           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.46/0.66             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.46/0.66         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.66           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.46/0.66             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_1, axiom,
% 0.46/0.66    (![B:$i,A:$i]:
% 0.46/0.66     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.66       ( zip_tseitin_0 @ B @ A ) ))).
% 0.46/0.66  thf('1', plain,
% 0.46/0.66      (![X35 : $i, X36 : $i]:
% 0.46/0.66         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.66  thf(t3_xboole_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.66  thf('2', plain,
% 0.46/0.66      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ k1_xboole_0))),
% 0.46/0.66      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.46/0.66  thf('3', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         (~ (r1_tarski @ X1 @ X0)
% 0.46/0.66          | (zip_tseitin_0 @ X0 @ X2)
% 0.46/0.66          | ((X1) = (k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.66  thf('4', plain,
% 0.46/0.66      (![X0 : $i]: (((sk_B) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_C @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['0', '3'])).
% 0.46/0.66  thf('5', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('6', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(cc2_relset_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.66       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.66  thf('7', plain,
% 0.46/0.66      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.66         ((v5_relat_1 @ X26 @ X28)
% 0.46/0.66          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.46/0.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.66  thf('8', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 0.46/0.66      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.66  thf(d19_relat_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( v1_relat_1 @ B ) =>
% 0.46/0.66       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.46/0.66  thf('9', plain,
% 0.46/0.66      (![X22 : $i, X23 : $i]:
% 0.46/0.66         (~ (v5_relat_1 @ X22 @ X23)
% 0.46/0.66          | (r1_tarski @ (k2_relat_1 @ X22) @ X23)
% 0.46/0.66          | ~ (v1_relat_1 @ X22))),
% 0.46/0.66      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.46/0.66  thf('10', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 0.46/0.66      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.66  thf('11', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(cc2_relat_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( v1_relat_1 @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.46/0.66  thf('12', plain,
% 0.46/0.66      (![X18 : $i, X19 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.46/0.66          | (v1_relat_1 @ X18)
% 0.46/0.66          | ~ (v1_relat_1 @ X19))),
% 0.46/0.66      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.46/0.66  thf('13', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.46/0.66      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.66  thf(fc6_relat_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.46/0.66  thf('14', plain,
% 0.46/0.66      (![X24 : $i, X25 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X24 @ X25))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.66  thf('15', plain, ((v1_relat_1 @ sk_D)),
% 0.46/0.66      inference('demod', [status(thm)], ['13', '14'])).
% 0.46/0.66  thf('16', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 0.46/0.66      inference('demod', [status(thm)], ['10', '15'])).
% 0.46/0.66  thf(t1_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.46/0.66       ( r1_tarski @ A @ C ) ))).
% 0.46/0.66  thf('17', plain,
% 0.46/0.66      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.66         (~ (r1_tarski @ X3 @ X4)
% 0.46/0.66          | ~ (r1_tarski @ X4 @ X5)
% 0.46/0.66          | (r1_tarski @ X3 @ X5))),
% 0.46/0.66      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.46/0.66  thf('18', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r1_tarski @ (k2_relat_1 @ sk_D) @ X0) | ~ (r1_tarski @ sk_B @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.66  thf('19', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.46/0.66      inference('sup-', [status(thm)], ['5', '18'])).
% 0.46/0.66  thf('20', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('21', plain,
% 0.46/0.66      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.66         ((v4_relat_1 @ X26 @ X27)
% 0.46/0.66          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.46/0.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.66  thf('22', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 0.46/0.66      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.66  thf(d18_relat_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( v1_relat_1 @ B ) =>
% 0.46/0.66       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.46/0.66  thf('23', plain,
% 0.46/0.66      (![X20 : $i, X21 : $i]:
% 0.46/0.66         (~ (v4_relat_1 @ X20 @ X21)
% 0.46/0.66          | (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.46/0.66          | ~ (v1_relat_1 @ X20))),
% 0.46/0.66      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.46/0.66  thf('24', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.66  thf('25', plain, ((v1_relat_1 @ sk_D)),
% 0.46/0.66      inference('demod', [status(thm)], ['13', '14'])).
% 0.46/0.66  thf('26', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A)),
% 0.46/0.66      inference('demod', [status(thm)], ['24', '25'])).
% 0.46/0.66  thf(t11_relset_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( v1_relat_1 @ C ) =>
% 0.46/0.66       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.46/0.66           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.46/0.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.46/0.66  thf('27', plain,
% 0.46/0.66      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.46/0.66         (~ (r1_tarski @ (k1_relat_1 @ X32) @ X33)
% 0.46/0.66          | ~ (r1_tarski @ (k2_relat_1 @ X32) @ X34)
% 0.46/0.66          | (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.46/0.66          | ~ (v1_relat_1 @ X32))),
% 0.46/0.66      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.46/0.66  thf('28', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ sk_D)
% 0.46/0.66          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.46/0.66          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.66  thf('29', plain, ((v1_relat_1 @ sk_D)),
% 0.46/0.66      inference('demod', [status(thm)], ['13', '14'])).
% 0.46/0.66  thf('30', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.46/0.66          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.46/0.66      inference('demod', [status(thm)], ['28', '29'])).
% 0.46/0.66  thf('31', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['19', '30'])).
% 0.46/0.66  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.46/0.66  thf(zf_stmt_3, axiom,
% 0.46/0.66    (![C:$i,B:$i,A:$i]:
% 0.46/0.66     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.46/0.66       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.46/0.66  thf(zf_stmt_5, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.66       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.46/0.66         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.66           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.46/0.66             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.46/0.66  thf('32', plain,
% 0.46/0.66      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.46/0.66         (~ (zip_tseitin_0 @ X40 @ X41)
% 0.46/0.66          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 0.46/0.66          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.66  thf('33', plain,
% 0.46/0.66      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_A) | ~ (zip_tseitin_0 @ sk_C @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['31', '32'])).
% 0.46/0.66  thf('34', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['19', '30'])).
% 0.46/0.66  thf(redefinition_k1_relset_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.66       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.46/0.66  thf('35', plain,
% 0.46/0.66      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.66         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 0.46/0.66          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.46/0.66      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.66  thf('36', plain,
% 0.46/0.66      (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.46/0.66      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.66  thf('37', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('38', plain,
% 0.46/0.66      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.46/0.66         (~ (v1_funct_2 @ X39 @ X37 @ X38)
% 0.46/0.66          | ((X37) = (k1_relset_1 @ X37 @ X38 @ X39))
% 0.46/0.66          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.66  thf('39', plain,
% 0.46/0.66      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.46/0.66        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.66  thf('40', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('41', plain,
% 0.46/0.66      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.66         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 0.46/0.66          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.46/0.66      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.66  thf('42', plain,
% 0.46/0.66      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.46/0.66      inference('sup-', [status(thm)], ['40', '41'])).
% 0.46/0.66  thf('43', plain,
% 0.46/0.66      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.46/0.66      inference('demod', [status(thm)], ['39', '42'])).
% 0.46/0.66  thf('44', plain,
% 0.46/0.66      (![X35 : $i, X36 : $i]:
% 0.46/0.66         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.66  thf('45', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('46', plain,
% 0.46/0.66      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.46/0.66         (~ (zip_tseitin_0 @ X40 @ X41)
% 0.46/0.66          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 0.46/0.66          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.66  thf('47', plain,
% 0.46/0.66      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['45', '46'])).
% 0.46/0.66  thf('48', plain,
% 0.46/0.66      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['44', '47'])).
% 0.46/0.66  thf('49', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('50', plain,
% 0.46/0.66      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.46/0.66      inference('split', [status(esa)], ['49'])).
% 0.46/0.66  thf('51', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('52', plain,
% 0.46/0.66      ((~ (v1_funct_1 @ sk_D)
% 0.46/0.66        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.46/0.66        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('53', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.46/0.66      inference('split', [status(esa)], ['52'])).
% 0.46/0.66  thf('54', plain, (((v1_funct_1 @ sk_D))),
% 0.46/0.66      inference('sup-', [status(thm)], ['51', '53'])).
% 0.46/0.66  thf(t4_subset_1, axiom,
% 0.46/0.66    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.46/0.66  thf('55', plain,
% 0.46/0.66      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.46/0.66      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.66  thf('56', plain,
% 0.46/0.66      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.66         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 0.46/0.66          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.46/0.66      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.66  thf('57', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['55', '56'])).
% 0.46/0.66  thf('58', plain,
% 0.46/0.66      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.46/0.66      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.66  thf('59', plain,
% 0.46/0.66      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.66         ((v4_relat_1 @ X26 @ X27)
% 0.46/0.66          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.46/0.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.66  thf('60', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 0.46/0.66      inference('sup-', [status(thm)], ['58', '59'])).
% 0.46/0.66  thf('61', plain,
% 0.46/0.66      (![X20 : $i, X21 : $i]:
% 0.46/0.66         (~ (v4_relat_1 @ X20 @ X21)
% 0.46/0.66          | (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.46/0.66          | ~ (v1_relat_1 @ X20))),
% 0.46/0.66      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.46/0.66  thf('62', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ k1_xboole_0)
% 0.46/0.66          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['60', '61'])).
% 0.46/0.66  thf(t113_zfmisc_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.46/0.66       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.46/0.66  thf('63', plain,
% 0.46/0.66      (![X9 : $i, X10 : $i]:
% 0.46/0.66         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.46/0.66  thf('64', plain,
% 0.46/0.66      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['63'])).
% 0.46/0.66  thf('65', plain,
% 0.46/0.66      (![X24 : $i, X25 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X24 @ X25))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.66  thf('66', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.46/0.66      inference('sup+', [status(thm)], ['64', '65'])).
% 0.46/0.66  thf('67', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.46/0.66      inference('demod', [status(thm)], ['62', '66'])).
% 0.46/0.66  thf('68', plain,
% 0.46/0.66      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ k1_xboole_0))),
% 0.46/0.66      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.46/0.66  thf('69', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['67', '68'])).
% 0.46/0.66  thf('70', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['57', '69'])).
% 0.46/0.66  thf('71', plain,
% 0.46/0.66      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.46/0.66         (((X37) != (k1_relset_1 @ X37 @ X38 @ X39))
% 0.46/0.66          | (v1_funct_2 @ X39 @ X37 @ X38)
% 0.46/0.66          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.66  thf('72', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((X1) != (k1_xboole_0))
% 0.46/0.66          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 0.46/0.66          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['70', '71'])).
% 0.46/0.66  thf('73', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.66          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['72'])).
% 0.46/0.66  thf('74', plain,
% 0.46/0.66      (![X35 : $i, X36 : $i]:
% 0.46/0.66         ((zip_tseitin_0 @ X35 @ X36) | ((X36) != (k1_xboole_0)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.66  thf('75', plain, (![X35 : $i]: (zip_tseitin_0 @ X35 @ k1_xboole_0)),
% 0.46/0.66      inference('simplify', [status(thm)], ['74'])).
% 0.46/0.66  thf('76', plain,
% 0.46/0.66      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.46/0.66      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.66  thf('77', plain,
% 0.46/0.66      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.46/0.66         (~ (zip_tseitin_0 @ X40 @ X41)
% 0.46/0.66          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 0.46/0.66          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.66  thf('78', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['76', '77'])).
% 0.46/0.66  thf('79', plain,
% 0.46/0.66      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.46/0.66      inference('sup-', [status(thm)], ['75', '78'])).
% 0.46/0.66  thf('80', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.46/0.66      inference('demod', [status(thm)], ['73', '79'])).
% 0.46/0.66  thf('81', plain,
% 0.46/0.66      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['63'])).
% 0.46/0.66  thf('82', plain,
% 0.46/0.66      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.66      inference('split', [status(esa)], ['49'])).
% 0.46/0.66  thf('83', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('84', plain,
% 0.46/0.66      (((m1_subset_1 @ sk_D @ 
% 0.46/0.66         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.46/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.66      inference('sup+', [status(thm)], ['82', '83'])).
% 0.46/0.66  thf('85', plain,
% 0.46/0.66      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.46/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.66      inference('sup+', [status(thm)], ['81', '84'])).
% 0.46/0.66  thf(t3_subset, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.66  thf('86', plain,
% 0.46/0.66      (![X12 : $i, X13 : $i]:
% 0.46/0.66         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.66  thf('87', plain,
% 0.46/0.66      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['85', '86'])).
% 0.46/0.66  thf('88', plain,
% 0.46/0.66      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ k1_xboole_0))),
% 0.46/0.66      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.46/0.66  thf('89', plain,
% 0.46/0.66      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['87', '88'])).
% 0.46/0.66  thf('90', plain,
% 0.46/0.66      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.66      inference('split', [status(esa)], ['49'])).
% 0.46/0.66  thf('91', plain,
% 0.46/0.66      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.46/0.66         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.46/0.66      inference('split', [status(esa)], ['52'])).
% 0.46/0.66  thf('92', plain,
% 0.46/0.66      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.46/0.66         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['90', '91'])).
% 0.46/0.66  thf('93', plain,
% 0.46/0.66      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C))
% 0.46/0.66         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['89', '92'])).
% 0.46/0.66  thf('94', plain,
% 0.46/0.66      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['80', '93'])).
% 0.46/0.66  thf('95', plain,
% 0.46/0.66      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.46/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.66      inference('sup+', [status(thm)], ['81', '84'])).
% 0.46/0.66  thf('96', plain,
% 0.46/0.66      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['63'])).
% 0.46/0.66  thf('97', plain,
% 0.46/0.66      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.66      inference('split', [status(esa)], ['49'])).
% 0.46/0.66  thf('98', plain,
% 0.46/0.66      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.46/0.66         <= (~
% 0.46/0.66             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.46/0.66      inference('split', [status(esa)], ['52'])).
% 0.46/0.66  thf('99', plain,
% 0.46/0.66      ((~ (m1_subset_1 @ sk_D @ 
% 0.46/0.66           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.46/0.66         <= (~
% 0.46/0.66             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 0.46/0.66             (((sk_A) = (k1_xboole_0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['97', '98'])).
% 0.46/0.66  thf('100', plain,
% 0.46/0.66      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.46/0.66         <= (~
% 0.46/0.66             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 0.46/0.66             (((sk_A) = (k1_xboole_0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['96', '99'])).
% 0.46/0.66  thf('101', plain,
% 0.46/0.66      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.46/0.66       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['95', '100'])).
% 0.46/0.66  thf('102', plain,
% 0.46/0.66      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.46/0.66       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ ((v1_funct_1 @ sk_D))),
% 0.46/0.66      inference('split', [status(esa)], ['52'])).
% 0.46/0.66  thf('103', plain,
% 0.46/0.66      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.46/0.66      inference('split', [status(esa)], ['49'])).
% 0.46/0.66  thf('104', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.46/0.66      inference('sat_resolution*', [status(thm)],
% 0.46/0.66                ['54', '94', '101', '102', '103'])).
% 0.46/0.66  thf('105', plain, (((sk_B) != (k1_xboole_0))),
% 0.46/0.66      inference('simpl_trail', [status(thm)], ['50', '104'])).
% 0.46/0.66  thf('106', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['48', '105'])).
% 0.46/0.66  thf('107', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.46/0.66      inference('demod', [status(thm)], ['43', '106'])).
% 0.46/0.66  thf('108', plain, (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['36', '107'])).
% 0.46/0.66  thf('109', plain,
% 0.46/0.66      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.46/0.66         (((X37) != (k1_relset_1 @ X37 @ X38 @ X39))
% 0.46/0.66          | (v1_funct_2 @ X39 @ X37 @ X38)
% 0.46/0.66          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.66  thf('110', plain,
% 0.46/0.66      ((((sk_A) != (sk_A))
% 0.46/0.66        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)
% 0.46/0.66        | (v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.46/0.66      inference('sup-', [status(thm)], ['108', '109'])).
% 0.46/0.66  thf('111', plain,
% 0.46/0.66      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.46/0.66        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A))),
% 0.46/0.66      inference('simplify', [status(thm)], ['110'])).
% 0.46/0.66  thf('112', plain,
% 0.46/0.66      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.46/0.66         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.46/0.66      inference('split', [status(esa)], ['52'])).
% 0.46/0.66  thf('113', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['19', '30'])).
% 0.46/0.66  thf('114', plain,
% 0.46/0.66      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.46/0.66         <= (~
% 0.46/0.66             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.46/0.66      inference('split', [status(esa)], ['52'])).
% 0.46/0.66  thf('115', plain,
% 0.46/0.66      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['113', '114'])).
% 0.46/0.66  thf('116', plain,
% 0.46/0.66      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | 
% 0.46/0.66       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.46/0.66       ~ ((v1_funct_1 @ sk_D))),
% 0.46/0.66      inference('split', [status(esa)], ['52'])).
% 0.46/0.66  thf('117', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.46/0.66      inference('sat_resolution*', [status(thm)], ['54', '115', '116'])).
% 0.46/0.66  thf('118', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.46/0.66      inference('simpl_trail', [status(thm)], ['112', '117'])).
% 0.46/0.66  thf('119', plain, (~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)),
% 0.46/0.66      inference('clc', [status(thm)], ['111', '118'])).
% 0.46/0.66  thf('120', plain, (~ (zip_tseitin_0 @ sk_C @ sk_A)),
% 0.46/0.66      inference('clc', [status(thm)], ['33', '119'])).
% 0.46/0.66  thf('121', plain, (((sk_B) = (k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['4', '120'])).
% 0.46/0.66  thf('122', plain, (((sk_B) != (k1_xboole_0))),
% 0.46/0.66      inference('simpl_trail', [status(thm)], ['50', '104'])).
% 0.46/0.66  thf('123', plain, ($false),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['121', '122'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.46/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
