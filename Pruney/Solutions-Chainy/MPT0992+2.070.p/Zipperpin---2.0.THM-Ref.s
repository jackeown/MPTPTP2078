%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YgwzIGNziz

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:44 EST 2020

% Result     : Theorem 4.85s
% Output     : Refutation 4.85s
% Verified   : 
% Statistics : Number of formulae       :  214 (4405 expanded)
%              Number of leaves         :   41 (1374 expanded)
%              Depth                    :   25
%              Number of atoms          : 1595 (42108 expanded)
%              Number of equality atoms :  119 (3476 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X32 @ X33 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('8',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ( ( k2_partfun1 @ X36 @ X37 @ X35 @ X38 )
        = ( k7_relat_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('13',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','11','12'])).

thf('14',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
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

thf('16',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('17',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('19',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('20',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('24',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('25',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('28',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('31',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('32',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['30','31'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('33',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v5_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('38',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('39',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['34','39'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X39 ) @ X40 )
      | ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X39 ) @ X40 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['37','38'])).

thf('44',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('47',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_D ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['29','47'])).

thf('49',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('52',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('53',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('55',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('57',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('60',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('61',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('62',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('63',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('64',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('66',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('67',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13
        = ( k7_relat_1 @ X13 @ X14 ) )
      | ~ ( v4_relat_1 @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('70',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('71',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('74',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','75'])).

thf('77',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['69','70'])).

thf('78',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ k1_xboole_0 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['69','70'])).

thf('82',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('83',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['76','77'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(demod,[status(thm)],['80','81','82','83'])).

thf('85',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','84'])).

thf('86',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('87',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(demod,[status(thm)],['80','81','82','83'])).

thf('90',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','84'])).

thf('92',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('95',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ( ( k2_partfun1 @ X36 @ X37 @ X35 @ X38 )
        = ( k7_relat_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = ( k7_relat_1 @ k1_xboole_0 @ X2 ) )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['93','98'])).

thf('100',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('101',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('102',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('103',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('104',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','84'])).

thf('105',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('106',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['93','98'])).

thf('107',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('108',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('109',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['76','77'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X25
       != ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X24 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('117',plain,(
    ! [X23: $i] :
      ( zip_tseitin_0 @ X23 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('119',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['117','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['115','121'])).

thf('123',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['53','85','90','99','100','101','102','103','104','105','106','107','122'])).

thf('124',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('125',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['123','124'])).

thf('126',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['50','125'])).

thf('127',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['48','126'])).

thf('128',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','127'])).

thf('129',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['50','125'])).

thf('130',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['128','129'])).

thf('131',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['21','130'])).

thf('132',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['37','38'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['14','135'])).

thf('137',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X32 @ X33 @ X31 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('143',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('145',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v5_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('149',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('152',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['147','152'])).

thf('154',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X39 ) @ X40 )
      | ( v1_funct_2 @ X39 @ ( k1_relat_1 @ X39 ) @ X40 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('157',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('159',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['155','156','159'])).

thf('161',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference('sup+',[status(thm)],['136','160'])).

thf('162',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','161'])).

thf('163',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['14','135'])).

thf('164',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['147','152'])).

thf('165',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X39 ) @ X40 )
      | ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X39 ) @ X40 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('168',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('169',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['166','167','168'])).

thf('170',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['163','169'])).

thf('171',plain,(
    $false ),
    inference(demod,[status(thm)],['162','170'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YgwzIGNziz
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:23:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 4.85/5.06  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.85/5.06  % Solved by: fo/fo7.sh
% 4.85/5.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.85/5.06  % done 5256 iterations in 4.611s
% 4.85/5.06  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.85/5.06  % SZS output start Refutation
% 4.85/5.06  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.85/5.06  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.85/5.06  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 4.85/5.06  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 4.85/5.06  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.85/5.06  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 4.85/5.06  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.85/5.06  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.85/5.06  thf(sk_B_type, type, sk_B: $i).
% 4.85/5.06  thf(sk_A_type, type, sk_A: $i).
% 4.85/5.06  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 4.85/5.06  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.85/5.06  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 4.85/5.06  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.85/5.06  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.85/5.06  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 4.85/5.06  thf(sk_D_type, type, sk_D: $i).
% 4.85/5.06  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.85/5.06  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 4.85/5.06  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.85/5.06  thf(sk_C_type, type, sk_C: $i).
% 4.85/5.06  thf(t38_funct_2, conjecture,
% 4.85/5.06    (![A:$i,B:$i,C:$i,D:$i]:
% 4.85/5.06     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.85/5.06         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.85/5.06       ( ( r1_tarski @ C @ A ) =>
% 4.85/5.06         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 4.85/5.06           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 4.85/5.06             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 4.85/5.06             ( m1_subset_1 @
% 4.85/5.06               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 4.85/5.06               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 4.85/5.06  thf(zf_stmt_0, negated_conjecture,
% 4.85/5.06    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 4.85/5.06        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.85/5.06            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.85/5.06          ( ( r1_tarski @ C @ A ) =>
% 4.85/5.06            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 4.85/5.06              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 4.85/5.06                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 4.85/5.06                ( m1_subset_1 @
% 4.85/5.06                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 4.85/5.06                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 4.85/5.06    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 4.85/5.06  thf('0', plain,
% 4.85/5.06      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 4.85/5.06        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 4.85/5.06             sk_B)
% 4.85/5.06        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 4.85/5.06             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('1', plain,
% 4.85/5.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf(dt_k2_partfun1, axiom,
% 4.85/5.06    (![A:$i,B:$i,C:$i,D:$i]:
% 4.85/5.06     ( ( ( v1_funct_1 @ C ) & 
% 4.85/5.06         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.85/5.06       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 4.85/5.06         ( m1_subset_1 @
% 4.85/5.06           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 4.85/5.06           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 4.85/5.06  thf('2', plain,
% 4.85/5.06      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 4.85/5.06         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 4.85/5.06          | ~ (v1_funct_1 @ X31)
% 4.85/5.06          | (v1_funct_1 @ (k2_partfun1 @ X32 @ X33 @ X31 @ X34)))),
% 4.85/5.06      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 4.85/5.06  thf('3', plain,
% 4.85/5.06      (![X0 : $i]:
% 4.85/5.06         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 4.85/5.06          | ~ (v1_funct_1 @ sk_D))),
% 4.85/5.06      inference('sup-', [status(thm)], ['1', '2'])).
% 4.85/5.06  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('5', plain,
% 4.85/5.06      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 4.85/5.06      inference('demod', [status(thm)], ['3', '4'])).
% 4.85/5.06  thf('6', plain,
% 4.85/5.06      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 4.85/5.06        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 4.85/5.06             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 4.85/5.06      inference('demod', [status(thm)], ['0', '5'])).
% 4.85/5.06  thf('7', plain,
% 4.85/5.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf(redefinition_k2_partfun1, axiom,
% 4.85/5.06    (![A:$i,B:$i,C:$i,D:$i]:
% 4.85/5.06     ( ( ( v1_funct_1 @ C ) & 
% 4.85/5.06         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.85/5.06       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 4.85/5.06  thf('8', plain,
% 4.85/5.06      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 4.85/5.06         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 4.85/5.06          | ~ (v1_funct_1 @ X35)
% 4.85/5.06          | ((k2_partfun1 @ X36 @ X37 @ X35 @ X38) = (k7_relat_1 @ X35 @ X38)))),
% 4.85/5.06      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 4.85/5.06  thf('9', plain,
% 4.85/5.06      (![X0 : $i]:
% 4.85/5.06         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 4.85/5.06          | ~ (v1_funct_1 @ sk_D))),
% 4.85/5.06      inference('sup-', [status(thm)], ['7', '8'])).
% 4.85/5.06  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('11', plain,
% 4.85/5.06      (![X0 : $i]:
% 4.85/5.06         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 4.85/5.06      inference('demod', [status(thm)], ['9', '10'])).
% 4.85/5.06  thf('12', plain,
% 4.85/5.06      (![X0 : $i]:
% 4.85/5.06         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 4.85/5.06      inference('demod', [status(thm)], ['9', '10'])).
% 4.85/5.06  thf('13', plain,
% 4.85/5.06      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 4.85/5.06        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 4.85/5.06             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 4.85/5.06      inference('demod', [status(thm)], ['6', '11', '12'])).
% 4.85/5.06  thf('14', plain, ((r1_tarski @ sk_C @ sk_A)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('15', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf(d1_funct_2, axiom,
% 4.85/5.06    (![A:$i,B:$i,C:$i]:
% 4.85/5.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.85/5.06       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.85/5.06           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 4.85/5.06             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 4.85/5.06         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.85/5.06           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 4.85/5.06             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 4.85/5.06  thf(zf_stmt_1, axiom,
% 4.85/5.06    (![C:$i,B:$i,A:$i]:
% 4.85/5.06     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 4.85/5.06       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.85/5.06  thf('16', plain,
% 4.85/5.06      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.85/5.06         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 4.85/5.06          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 4.85/5.06          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.85/5.06  thf('17', plain,
% 4.85/5.06      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 4.85/5.06        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 4.85/5.06      inference('sup-', [status(thm)], ['15', '16'])).
% 4.85/5.06  thf('18', plain,
% 4.85/5.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf(redefinition_k1_relset_1, axiom,
% 4.85/5.06    (![A:$i,B:$i,C:$i]:
% 4.85/5.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.85/5.06       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 4.85/5.06  thf('19', plain,
% 4.85/5.06      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.85/5.06         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 4.85/5.06          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 4.85/5.06      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.85/5.06  thf('20', plain,
% 4.85/5.06      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 4.85/5.06      inference('sup-', [status(thm)], ['18', '19'])).
% 4.85/5.06  thf('21', plain,
% 4.85/5.06      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.85/5.06      inference('demod', [status(thm)], ['17', '20'])).
% 4.85/5.06  thf(zf_stmt_2, axiom,
% 4.85/5.06    (![B:$i,A:$i]:
% 4.85/5.06     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.85/5.06       ( zip_tseitin_0 @ B @ A ) ))).
% 4.85/5.06  thf('22', plain,
% 4.85/5.06      (![X23 : $i, X24 : $i]:
% 4.85/5.06         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.85/5.06  thf('23', plain,
% 4.85/5.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 4.85/5.06  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 4.85/5.06  thf(zf_stmt_5, axiom,
% 4.85/5.06    (![A:$i,B:$i,C:$i]:
% 4.85/5.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.85/5.06       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 4.85/5.06         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.85/5.06           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 4.85/5.06             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 4.85/5.06  thf('24', plain,
% 4.85/5.06      (![X28 : $i, X29 : $i, X30 : $i]:
% 4.85/5.06         (~ (zip_tseitin_0 @ X28 @ X29)
% 4.85/5.06          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 4.85/5.06          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.85/5.06  thf('25', plain,
% 4.85/5.06      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 4.85/5.06      inference('sup-', [status(thm)], ['23', '24'])).
% 4.85/5.06  thf('26', plain,
% 4.85/5.06      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 4.85/5.06      inference('sup-', [status(thm)], ['22', '25'])).
% 4.85/5.06  thf('27', plain,
% 4.85/5.06      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.85/5.06      inference('demod', [status(thm)], ['17', '20'])).
% 4.85/5.06  thf('28', plain,
% 4.85/5.06      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.85/5.06      inference('sup-', [status(thm)], ['26', '27'])).
% 4.85/5.06  thf('29', plain,
% 4.85/5.06      (![X23 : $i, X24 : $i]:
% 4.85/5.06         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.85/5.06  thf('30', plain,
% 4.85/5.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf(cc2_relset_1, axiom,
% 4.85/5.06    (![A:$i,B:$i,C:$i]:
% 4.85/5.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.85/5.06       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 4.85/5.06  thf('31', plain,
% 4.85/5.06      (![X17 : $i, X18 : $i, X19 : $i]:
% 4.85/5.06         ((v5_relat_1 @ X17 @ X19)
% 4.85/5.06          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 4.85/5.06      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.85/5.06  thf('32', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 4.85/5.06      inference('sup-', [status(thm)], ['30', '31'])).
% 4.85/5.06  thf(d19_relat_1, axiom,
% 4.85/5.06    (![A:$i,B:$i]:
% 4.85/5.06     ( ( v1_relat_1 @ B ) =>
% 4.85/5.06       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 4.85/5.06  thf('33', plain,
% 4.85/5.06      (![X9 : $i, X10 : $i]:
% 4.85/5.06         (~ (v5_relat_1 @ X9 @ X10)
% 4.85/5.06          | (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 4.85/5.06          | ~ (v1_relat_1 @ X9))),
% 4.85/5.06      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.85/5.06  thf('34', plain,
% 4.85/5.06      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 4.85/5.06      inference('sup-', [status(thm)], ['32', '33'])).
% 4.85/5.06  thf('35', plain,
% 4.85/5.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf(cc2_relat_1, axiom,
% 4.85/5.06    (![A:$i]:
% 4.85/5.06     ( ( v1_relat_1 @ A ) =>
% 4.85/5.06       ( ![B:$i]:
% 4.85/5.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 4.85/5.06  thf('36', plain,
% 4.85/5.06      (![X7 : $i, X8 : $i]:
% 4.85/5.06         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 4.85/5.06          | (v1_relat_1 @ X7)
% 4.85/5.06          | ~ (v1_relat_1 @ X8))),
% 4.85/5.06      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.85/5.06  thf('37', plain,
% 4.85/5.06      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 4.85/5.06      inference('sup-', [status(thm)], ['35', '36'])).
% 4.85/5.06  thf(fc6_relat_1, axiom,
% 4.85/5.06    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 4.85/5.06  thf('38', plain,
% 4.85/5.06      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 4.85/5.06      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.85/5.06  thf('39', plain, ((v1_relat_1 @ sk_D)),
% 4.85/5.06      inference('demod', [status(thm)], ['37', '38'])).
% 4.85/5.06  thf('40', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 4.85/5.06      inference('demod', [status(thm)], ['34', '39'])).
% 4.85/5.06  thf(t4_funct_2, axiom,
% 4.85/5.06    (![A:$i,B:$i]:
% 4.85/5.06     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.85/5.06       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 4.85/5.06         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 4.85/5.06           ( m1_subset_1 @
% 4.85/5.06             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 4.85/5.06  thf('41', plain,
% 4.85/5.06      (![X39 : $i, X40 : $i]:
% 4.85/5.06         (~ (r1_tarski @ (k2_relat_1 @ X39) @ X40)
% 4.85/5.06          | (m1_subset_1 @ X39 @ 
% 4.85/5.06             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X39) @ X40)))
% 4.85/5.06          | ~ (v1_funct_1 @ X39)
% 4.85/5.06          | ~ (v1_relat_1 @ X39))),
% 4.85/5.06      inference('cnf', [status(esa)], [t4_funct_2])).
% 4.85/5.06  thf('42', plain,
% 4.85/5.06      ((~ (v1_relat_1 @ sk_D)
% 4.85/5.06        | ~ (v1_funct_1 @ sk_D)
% 4.85/5.06        | (m1_subset_1 @ sk_D @ 
% 4.85/5.06           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B))))),
% 4.85/5.06      inference('sup-', [status(thm)], ['40', '41'])).
% 4.85/5.06  thf('43', plain, ((v1_relat_1 @ sk_D)),
% 4.85/5.06      inference('demod', [status(thm)], ['37', '38'])).
% 4.85/5.06  thf('44', plain, ((v1_funct_1 @ sk_D)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('45', plain,
% 4.85/5.06      ((m1_subset_1 @ sk_D @ 
% 4.85/5.06        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 4.85/5.06      inference('demod', [status(thm)], ['42', '43', '44'])).
% 4.85/5.06  thf('46', plain,
% 4.85/5.06      (![X28 : $i, X29 : $i, X30 : $i]:
% 4.85/5.06         (~ (zip_tseitin_0 @ X28 @ X29)
% 4.85/5.06          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 4.85/5.06          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.85/5.06  thf('47', plain,
% 4.85/5.06      (((zip_tseitin_1 @ sk_D @ sk_B @ (k1_relat_1 @ sk_D))
% 4.85/5.06        | ~ (zip_tseitin_0 @ sk_B @ (k1_relat_1 @ sk_D)))),
% 4.85/5.06      inference('sup-', [status(thm)], ['45', '46'])).
% 4.85/5.06  thf('48', plain,
% 4.85/5.06      ((((sk_B) = (k1_xboole_0))
% 4.85/5.06        | (zip_tseitin_1 @ sk_D @ sk_B @ (k1_relat_1 @ sk_D)))),
% 4.85/5.06      inference('sup-', [status(thm)], ['29', '47'])).
% 4.85/5.06  thf('49', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('50', plain,
% 4.85/5.06      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 4.85/5.06      inference('split', [status(esa)], ['49'])).
% 4.85/5.06  thf('51', plain,
% 4.85/5.06      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.85/5.06      inference('split', [status(esa)], ['49'])).
% 4.85/5.06  thf('52', plain,
% 4.85/5.06      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 4.85/5.06        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 4.85/5.06             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 4.85/5.06      inference('demod', [status(thm)], ['0', '5'])).
% 4.85/5.06  thf('53', plain,
% 4.85/5.06      (((~ (m1_subset_1 @ (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C) @ 
% 4.85/5.06            (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 4.85/5.06         | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 4.85/5.06              sk_B)))
% 4.85/5.06         <= ((((sk_A) = (k1_xboole_0))))),
% 4.85/5.06      inference('sup-', [status(thm)], ['51', '52'])).
% 4.85/5.06  thf(t113_zfmisc_1, axiom,
% 4.85/5.06    (![A:$i,B:$i]:
% 4.85/5.06     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 4.85/5.06       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 4.85/5.06  thf('54', plain,
% 4.85/5.06      (![X2 : $i, X3 : $i]:
% 4.85/5.06         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 4.85/5.06      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.85/5.06  thf('55', plain,
% 4.85/5.06      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 4.85/5.06      inference('simplify', [status(thm)], ['54'])).
% 4.85/5.06  thf('56', plain,
% 4.85/5.06      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.85/5.06      inference('split', [status(esa)], ['49'])).
% 4.85/5.06  thf('57', plain,
% 4.85/5.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('58', plain,
% 4.85/5.06      (((m1_subset_1 @ sk_D @ 
% 4.85/5.06         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 4.85/5.06         <= ((((sk_A) = (k1_xboole_0))))),
% 4.85/5.06      inference('sup+', [status(thm)], ['56', '57'])).
% 4.85/5.06  thf('59', plain,
% 4.85/5.06      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 4.85/5.06         <= ((((sk_A) = (k1_xboole_0))))),
% 4.85/5.06      inference('sup+', [status(thm)], ['55', '58'])).
% 4.85/5.06  thf(t3_subset, axiom,
% 4.85/5.06    (![A:$i,B:$i]:
% 4.85/5.06     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.85/5.06  thf('60', plain,
% 4.85/5.06      (![X4 : $i, X5 : $i]:
% 4.85/5.06         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 4.85/5.06      inference('cnf', [status(esa)], [t3_subset])).
% 4.85/5.06  thf('61', plain,
% 4.85/5.06      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 4.85/5.06      inference('sup-', [status(thm)], ['59', '60'])).
% 4.85/5.06  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 4.85/5.06  thf('62', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 4.85/5.06      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.85/5.06  thf('63', plain,
% 4.85/5.06      (![X4 : $i, X6 : $i]:
% 4.85/5.06         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 4.85/5.06      inference('cnf', [status(esa)], [t3_subset])).
% 4.85/5.06  thf('64', plain,
% 4.85/5.06      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 4.85/5.06      inference('sup-', [status(thm)], ['62', '63'])).
% 4.85/5.06  thf('65', plain,
% 4.85/5.06      (![X17 : $i, X18 : $i, X19 : $i]:
% 4.85/5.06         ((v4_relat_1 @ X17 @ X18)
% 4.85/5.06          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 4.85/5.06      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.85/5.06  thf('66', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 4.85/5.06      inference('sup-', [status(thm)], ['64', '65'])).
% 4.85/5.06  thf(t209_relat_1, axiom,
% 4.85/5.06    (![A:$i,B:$i]:
% 4.85/5.06     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 4.85/5.06       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 4.85/5.06  thf('67', plain,
% 4.85/5.06      (![X13 : $i, X14 : $i]:
% 4.85/5.06         (((X13) = (k7_relat_1 @ X13 @ X14))
% 4.85/5.06          | ~ (v4_relat_1 @ X13 @ X14)
% 4.85/5.06          | ~ (v1_relat_1 @ X13))),
% 4.85/5.06      inference('cnf', [status(esa)], [t209_relat_1])).
% 4.85/5.06  thf('68', plain,
% 4.85/5.06      (![X0 : $i]:
% 4.85/5.06         (~ (v1_relat_1 @ k1_xboole_0)
% 4.85/5.06          | ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0)))),
% 4.85/5.06      inference('sup-', [status(thm)], ['66', '67'])).
% 4.85/5.06  thf('69', plain,
% 4.85/5.06      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 4.85/5.06      inference('simplify', [status(thm)], ['54'])).
% 4.85/5.06  thf('70', plain,
% 4.85/5.06      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 4.85/5.06      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.85/5.06  thf('71', plain, ((v1_relat_1 @ k1_xboole_0)),
% 4.85/5.06      inference('sup+', [status(thm)], ['69', '70'])).
% 4.85/5.06  thf('72', plain,
% 4.85/5.06      (![X0 : $i]: ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0))),
% 4.85/5.06      inference('demod', [status(thm)], ['68', '71'])).
% 4.85/5.06  thf('73', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 4.85/5.06      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.85/5.06  thf(t91_relat_1, axiom,
% 4.85/5.06    (![A:$i,B:$i]:
% 4.85/5.06     ( ( v1_relat_1 @ B ) =>
% 4.85/5.06       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 4.85/5.06         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 4.85/5.06  thf('74', plain,
% 4.85/5.06      (![X15 : $i, X16 : $i]:
% 4.85/5.06         (~ (r1_tarski @ X15 @ (k1_relat_1 @ X16))
% 4.85/5.06          | ((k1_relat_1 @ (k7_relat_1 @ X16 @ X15)) = (X15))
% 4.85/5.06          | ~ (v1_relat_1 @ X16))),
% 4.85/5.06      inference('cnf', [status(esa)], [t91_relat_1])).
% 4.85/5.06  thf('75', plain,
% 4.85/5.06      (![X0 : $i]:
% 4.85/5.06         (~ (v1_relat_1 @ X0)
% 4.85/5.06          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 4.85/5.06      inference('sup-', [status(thm)], ['73', '74'])).
% 4.85/5.06  thf('76', plain,
% 4.85/5.06      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 4.85/5.06        | ~ (v1_relat_1 @ k1_xboole_0))),
% 4.85/5.06      inference('sup+', [status(thm)], ['72', '75'])).
% 4.85/5.06  thf('77', plain, ((v1_relat_1 @ k1_xboole_0)),
% 4.85/5.06      inference('sup+', [status(thm)], ['69', '70'])).
% 4.85/5.06  thf('78', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.85/5.06      inference('demod', [status(thm)], ['76', '77'])).
% 4.85/5.06  thf('79', plain,
% 4.85/5.06      (![X15 : $i, X16 : $i]:
% 4.85/5.06         (~ (r1_tarski @ X15 @ (k1_relat_1 @ X16))
% 4.85/5.06          | ((k1_relat_1 @ (k7_relat_1 @ X16 @ X15)) = (X15))
% 4.85/5.06          | ~ (v1_relat_1 @ X16))),
% 4.85/5.06      inference('cnf', [status(esa)], [t91_relat_1])).
% 4.85/5.06  thf('80', plain,
% 4.85/5.06      (![X0 : $i]:
% 4.85/5.06         (~ (r1_tarski @ X0 @ k1_xboole_0)
% 4.85/5.06          | ~ (v1_relat_1 @ k1_xboole_0)
% 4.85/5.06          | ((k1_relat_1 @ (k7_relat_1 @ k1_xboole_0 @ X0)) = (X0)))),
% 4.85/5.06      inference('sup-', [status(thm)], ['78', '79'])).
% 4.85/5.06  thf('81', plain, ((v1_relat_1 @ k1_xboole_0)),
% 4.85/5.06      inference('sup+', [status(thm)], ['69', '70'])).
% 4.85/5.06  thf('82', plain,
% 4.85/5.06      (![X0 : $i]: ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0))),
% 4.85/5.06      inference('demod', [status(thm)], ['68', '71'])).
% 4.85/5.06  thf('83', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.85/5.07      inference('demod', [status(thm)], ['76', '77'])).
% 4.85/5.07  thf('84', plain,
% 4.85/5.07      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((k1_xboole_0) = (X0)))),
% 4.85/5.07      inference('demod', [status(thm)], ['80', '81', '82', '83'])).
% 4.85/5.07  thf('85', plain,
% 4.85/5.07      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.85/5.07      inference('sup-', [status(thm)], ['61', '84'])).
% 4.85/5.07  thf('86', plain,
% 4.85/5.07      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.85/5.07      inference('split', [status(esa)], ['49'])).
% 4.85/5.07  thf('87', plain, ((r1_tarski @ sk_C @ sk_A)),
% 4.85/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.07  thf('88', plain,
% 4.85/5.07      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 4.85/5.07      inference('sup+', [status(thm)], ['86', '87'])).
% 4.85/5.07  thf('89', plain,
% 4.85/5.07      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((k1_xboole_0) = (X0)))),
% 4.85/5.07      inference('demod', [status(thm)], ['80', '81', '82', '83'])).
% 4.85/5.07  thf('90', plain,
% 4.85/5.07      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.85/5.07      inference('sup-', [status(thm)], ['88', '89'])).
% 4.85/5.07  thf('91', plain,
% 4.85/5.07      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.85/5.07      inference('sup-', [status(thm)], ['61', '84'])).
% 4.85/5.07  thf('92', plain, ((v1_funct_1 @ sk_D)),
% 4.85/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.07  thf('93', plain,
% 4.85/5.07      (((v1_funct_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 4.85/5.07      inference('sup+', [status(thm)], ['91', '92'])).
% 4.85/5.07  thf('94', plain,
% 4.85/5.07      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 4.85/5.07      inference('sup-', [status(thm)], ['62', '63'])).
% 4.85/5.07  thf('95', plain,
% 4.85/5.07      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 4.85/5.07         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 4.85/5.07          | ~ (v1_funct_1 @ X35)
% 4.85/5.07          | ((k2_partfun1 @ X36 @ X37 @ X35 @ X38) = (k7_relat_1 @ X35 @ X38)))),
% 4.85/5.07      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 4.85/5.07  thf('96', plain,
% 4.85/5.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.85/5.07         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 4.85/5.07            = (k7_relat_1 @ k1_xboole_0 @ X2))
% 4.85/5.07          | ~ (v1_funct_1 @ k1_xboole_0))),
% 4.85/5.07      inference('sup-', [status(thm)], ['94', '95'])).
% 4.85/5.07  thf('97', plain,
% 4.85/5.07      (![X0 : $i]: ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0))),
% 4.85/5.07      inference('demod', [status(thm)], ['68', '71'])).
% 4.85/5.07  thf('98', plain,
% 4.85/5.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.85/5.07         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))
% 4.85/5.07          | ~ (v1_funct_1 @ k1_xboole_0))),
% 4.85/5.07      inference('demod', [status(thm)], ['96', '97'])).
% 4.85/5.07  thf('99', plain,
% 4.85/5.07      ((![X0 : $i, X1 : $i, X2 : $i]:
% 4.85/5.07          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 4.85/5.07         <= ((((sk_A) = (k1_xboole_0))))),
% 4.85/5.07      inference('sup-', [status(thm)], ['93', '98'])).
% 4.85/5.07  thf('100', plain,
% 4.85/5.07      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.85/5.07      inference('sup-', [status(thm)], ['88', '89'])).
% 4.85/5.07  thf('101', plain,
% 4.85/5.07      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 4.85/5.07      inference('simplify', [status(thm)], ['54'])).
% 4.85/5.07  thf('102', plain,
% 4.85/5.07      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 4.85/5.07      inference('sup-', [status(thm)], ['62', '63'])).
% 4.85/5.07  thf('103', plain,
% 4.85/5.07      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.85/5.07      inference('split', [status(esa)], ['49'])).
% 4.85/5.07  thf('104', plain,
% 4.85/5.07      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.85/5.07      inference('sup-', [status(thm)], ['61', '84'])).
% 4.85/5.07  thf('105', plain,
% 4.85/5.07      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.85/5.07      inference('sup-', [status(thm)], ['88', '89'])).
% 4.85/5.07  thf('106', plain,
% 4.85/5.07      ((![X0 : $i, X1 : $i, X2 : $i]:
% 4.85/5.07          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 4.85/5.07         <= ((((sk_A) = (k1_xboole_0))))),
% 4.85/5.07      inference('sup-', [status(thm)], ['93', '98'])).
% 4.85/5.07  thf('107', plain,
% 4.85/5.07      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.85/5.07      inference('sup-', [status(thm)], ['88', '89'])).
% 4.85/5.07  thf('108', plain,
% 4.85/5.07      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 4.85/5.07      inference('sup-', [status(thm)], ['62', '63'])).
% 4.85/5.07  thf('109', plain,
% 4.85/5.07      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.85/5.07         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 4.85/5.07          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 4.85/5.07      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.85/5.07  thf('110', plain,
% 4.85/5.07      (![X0 : $i, X1 : $i]:
% 4.85/5.07         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 4.85/5.07      inference('sup-', [status(thm)], ['108', '109'])).
% 4.85/5.07  thf('111', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.85/5.07      inference('demod', [status(thm)], ['76', '77'])).
% 4.85/5.07  thf('112', plain,
% 4.85/5.07      (![X0 : $i, X1 : $i]:
% 4.85/5.07         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 4.85/5.07      inference('demod', [status(thm)], ['110', '111'])).
% 4.85/5.07  thf('113', plain,
% 4.85/5.07      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.85/5.07         (((X25) != (k1_relset_1 @ X25 @ X26 @ X27))
% 4.85/5.07          | (v1_funct_2 @ X27 @ X25 @ X26)
% 4.85/5.07          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 4.85/5.07      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.85/5.07  thf('114', plain,
% 4.85/5.07      (![X0 : $i, X1 : $i]:
% 4.85/5.07         (((X1) != (k1_xboole_0))
% 4.85/5.07          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 4.85/5.07          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 4.85/5.07      inference('sup-', [status(thm)], ['112', '113'])).
% 4.85/5.07  thf('115', plain,
% 4.85/5.07      (![X0 : $i]:
% 4.85/5.07         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 4.85/5.07          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 4.85/5.07      inference('simplify', [status(thm)], ['114'])).
% 4.85/5.07  thf('116', plain,
% 4.85/5.07      (![X23 : $i, X24 : $i]:
% 4.85/5.07         ((zip_tseitin_0 @ X23 @ X24) | ((X24) != (k1_xboole_0)))),
% 4.85/5.07      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.85/5.07  thf('117', plain, (![X23 : $i]: (zip_tseitin_0 @ X23 @ k1_xboole_0)),
% 4.85/5.07      inference('simplify', [status(thm)], ['116'])).
% 4.85/5.07  thf('118', plain,
% 4.85/5.07      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 4.85/5.07      inference('sup-', [status(thm)], ['62', '63'])).
% 4.85/5.07  thf('119', plain,
% 4.85/5.07      (![X28 : $i, X29 : $i, X30 : $i]:
% 4.85/5.07         (~ (zip_tseitin_0 @ X28 @ X29)
% 4.85/5.07          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 4.85/5.07          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 4.85/5.07      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.85/5.07  thf('120', plain,
% 4.85/5.07      (![X0 : $i, X1 : $i]:
% 4.85/5.07         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 4.85/5.07      inference('sup-', [status(thm)], ['118', '119'])).
% 4.85/5.07  thf('121', plain,
% 4.85/5.07      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 4.85/5.07      inference('sup-', [status(thm)], ['117', '120'])).
% 4.85/5.07  thf('122', plain,
% 4.85/5.07      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 4.85/5.07      inference('demod', [status(thm)], ['115', '121'])).
% 4.85/5.07  thf('123', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 4.85/5.07      inference('demod', [status(thm)],
% 4.85/5.07                ['53', '85', '90', '99', '100', '101', '102', '103', '104', 
% 4.85/5.07                 '105', '106', '107', '122'])).
% 4.85/5.07  thf('124', plain,
% 4.85/5.07      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 4.85/5.07      inference('split', [status(esa)], ['49'])).
% 4.85/5.07  thf('125', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 4.85/5.07      inference('sat_resolution*', [status(thm)], ['123', '124'])).
% 4.85/5.07  thf('126', plain, (((sk_B) != (k1_xboole_0))),
% 4.85/5.07      inference('simpl_trail', [status(thm)], ['50', '125'])).
% 4.85/5.07  thf('127', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ (k1_relat_1 @ sk_D))),
% 4.85/5.07      inference('simplify_reflect-', [status(thm)], ['48', '126'])).
% 4.85/5.07  thf('128', plain,
% 4.85/5.07      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_B) = (k1_xboole_0)))),
% 4.85/5.07      inference('sup+', [status(thm)], ['28', '127'])).
% 4.85/5.07  thf('129', plain, (((sk_B) != (k1_xboole_0))),
% 4.85/5.07      inference('simpl_trail', [status(thm)], ['50', '125'])).
% 4.85/5.07  thf('130', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 4.85/5.07      inference('simplify_reflect-', [status(thm)], ['128', '129'])).
% 4.85/5.07  thf('131', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 4.85/5.07      inference('demod', [status(thm)], ['21', '130'])).
% 4.85/5.07  thf('132', plain,
% 4.85/5.07      (![X15 : $i, X16 : $i]:
% 4.85/5.07         (~ (r1_tarski @ X15 @ (k1_relat_1 @ X16))
% 4.85/5.07          | ((k1_relat_1 @ (k7_relat_1 @ X16 @ X15)) = (X15))
% 4.85/5.07          | ~ (v1_relat_1 @ X16))),
% 4.85/5.07      inference('cnf', [status(esa)], [t91_relat_1])).
% 4.85/5.07  thf('133', plain,
% 4.85/5.07      (![X0 : $i]:
% 4.85/5.07         (~ (r1_tarski @ X0 @ sk_A)
% 4.85/5.07          | ~ (v1_relat_1 @ sk_D)
% 4.85/5.07          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 4.85/5.07      inference('sup-', [status(thm)], ['131', '132'])).
% 4.85/5.07  thf('134', plain, ((v1_relat_1 @ sk_D)),
% 4.85/5.07      inference('demod', [status(thm)], ['37', '38'])).
% 4.85/5.07  thf('135', plain,
% 4.85/5.07      (![X0 : $i]:
% 4.85/5.07         (~ (r1_tarski @ X0 @ sk_A)
% 4.85/5.07          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 4.85/5.07      inference('demod', [status(thm)], ['133', '134'])).
% 4.85/5.07  thf('136', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 4.85/5.07      inference('sup-', [status(thm)], ['14', '135'])).
% 4.85/5.07  thf('137', plain,
% 4.85/5.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.85/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.07  thf('138', plain,
% 4.85/5.07      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 4.85/5.07         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 4.85/5.07          | ~ (v1_funct_1 @ X31)
% 4.85/5.07          | (m1_subset_1 @ (k2_partfun1 @ X32 @ X33 @ X31 @ X34) @ 
% 4.85/5.07             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 4.85/5.07      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 4.85/5.07  thf('139', plain,
% 4.85/5.07      (![X0 : $i]:
% 4.85/5.07         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 4.85/5.07           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 4.85/5.07          | ~ (v1_funct_1 @ sk_D))),
% 4.85/5.07      inference('sup-', [status(thm)], ['137', '138'])).
% 4.85/5.07  thf('140', plain, ((v1_funct_1 @ sk_D)),
% 4.85/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.07  thf('141', plain,
% 4.85/5.07      (![X0 : $i]:
% 4.85/5.07         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 4.85/5.07          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.85/5.07      inference('demod', [status(thm)], ['139', '140'])).
% 4.85/5.07  thf('142', plain,
% 4.85/5.07      (![X0 : $i]:
% 4.85/5.07         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 4.85/5.07      inference('demod', [status(thm)], ['9', '10'])).
% 4.85/5.07  thf('143', plain,
% 4.85/5.07      (![X0 : $i]:
% 4.85/5.07         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 4.85/5.07          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.85/5.07      inference('demod', [status(thm)], ['141', '142'])).
% 4.85/5.07  thf('144', plain,
% 4.85/5.07      (![X17 : $i, X18 : $i, X19 : $i]:
% 4.85/5.07         ((v5_relat_1 @ X17 @ X19)
% 4.85/5.07          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 4.85/5.07      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.85/5.07  thf('145', plain,
% 4.85/5.07      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B)),
% 4.85/5.07      inference('sup-', [status(thm)], ['143', '144'])).
% 4.85/5.07  thf('146', plain,
% 4.85/5.07      (![X9 : $i, X10 : $i]:
% 4.85/5.07         (~ (v5_relat_1 @ X9 @ X10)
% 4.85/5.07          | (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 4.85/5.07          | ~ (v1_relat_1 @ X9))),
% 4.85/5.07      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.85/5.07  thf('147', plain,
% 4.85/5.07      (![X0 : $i]:
% 4.85/5.07         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 4.85/5.07          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 4.85/5.07      inference('sup-', [status(thm)], ['145', '146'])).
% 4.85/5.07  thf('148', plain,
% 4.85/5.07      (![X0 : $i]:
% 4.85/5.07         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 4.85/5.07          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.85/5.07      inference('demod', [status(thm)], ['141', '142'])).
% 4.85/5.07  thf('149', plain,
% 4.85/5.07      (![X7 : $i, X8 : $i]:
% 4.85/5.07         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 4.85/5.07          | (v1_relat_1 @ X7)
% 4.85/5.07          | ~ (v1_relat_1 @ X8))),
% 4.85/5.07      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.85/5.07  thf('150', plain,
% 4.85/5.07      (![X0 : $i]:
% 4.85/5.07         (~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 4.85/5.07          | (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 4.85/5.07      inference('sup-', [status(thm)], ['148', '149'])).
% 4.85/5.07  thf('151', plain,
% 4.85/5.07      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 4.85/5.07      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.85/5.07  thf('152', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 4.85/5.07      inference('demod', [status(thm)], ['150', '151'])).
% 4.85/5.07  thf('153', plain,
% 4.85/5.07      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 4.85/5.07      inference('demod', [status(thm)], ['147', '152'])).
% 4.85/5.07  thf('154', plain,
% 4.85/5.07      (![X39 : $i, X40 : $i]:
% 4.85/5.07         (~ (r1_tarski @ (k2_relat_1 @ X39) @ X40)
% 4.85/5.07          | (v1_funct_2 @ X39 @ (k1_relat_1 @ X39) @ X40)
% 4.85/5.07          | ~ (v1_funct_1 @ X39)
% 4.85/5.07          | ~ (v1_relat_1 @ X39))),
% 4.85/5.07      inference('cnf', [status(esa)], [t4_funct_2])).
% 4.85/5.07  thf('155', plain,
% 4.85/5.07      (![X0 : $i]:
% 4.85/5.07         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 4.85/5.07          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 4.85/5.07          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 4.85/5.07             (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 4.85/5.07      inference('sup-', [status(thm)], ['153', '154'])).
% 4.85/5.07  thf('156', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 4.85/5.07      inference('demod', [status(thm)], ['150', '151'])).
% 4.85/5.07  thf('157', plain,
% 4.85/5.07      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 4.85/5.07      inference('demod', [status(thm)], ['3', '4'])).
% 4.85/5.07  thf('158', plain,
% 4.85/5.07      (![X0 : $i]:
% 4.85/5.07         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 4.85/5.07      inference('demod', [status(thm)], ['9', '10'])).
% 4.85/5.07  thf('159', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 4.85/5.07      inference('demod', [status(thm)], ['157', '158'])).
% 4.85/5.07  thf('160', plain,
% 4.85/5.07      (![X0 : $i]:
% 4.85/5.07         (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 4.85/5.07          (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 4.85/5.07      inference('demod', [status(thm)], ['155', '156', '159'])).
% 4.85/5.07  thf('161', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 4.85/5.07      inference('sup+', [status(thm)], ['136', '160'])).
% 4.85/5.07  thf('162', plain,
% 4.85/5.07      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 4.85/5.07          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 4.85/5.07      inference('demod', [status(thm)], ['13', '161'])).
% 4.85/5.07  thf('163', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 4.85/5.07      inference('sup-', [status(thm)], ['14', '135'])).
% 4.85/5.07  thf('164', plain,
% 4.85/5.07      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 4.85/5.07      inference('demod', [status(thm)], ['147', '152'])).
% 4.85/5.07  thf('165', plain,
% 4.85/5.07      (![X39 : $i, X40 : $i]:
% 4.85/5.07         (~ (r1_tarski @ (k2_relat_1 @ X39) @ X40)
% 4.85/5.07          | (m1_subset_1 @ X39 @ 
% 4.85/5.07             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X39) @ X40)))
% 4.85/5.07          | ~ (v1_funct_1 @ X39)
% 4.85/5.07          | ~ (v1_relat_1 @ X39))),
% 4.85/5.07      inference('cnf', [status(esa)], [t4_funct_2])).
% 4.85/5.07  thf('166', plain,
% 4.85/5.07      (![X0 : $i]:
% 4.85/5.07         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 4.85/5.07          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 4.85/5.07          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 4.85/5.07             (k1_zfmisc_1 @ 
% 4.85/5.07              (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))))),
% 4.85/5.07      inference('sup-', [status(thm)], ['164', '165'])).
% 4.85/5.07  thf('167', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 4.85/5.07      inference('demod', [status(thm)], ['150', '151'])).
% 4.85/5.07  thf('168', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 4.85/5.07      inference('demod', [status(thm)], ['157', '158'])).
% 4.85/5.07  thf('169', plain,
% 4.85/5.07      (![X0 : $i]:
% 4.85/5.07         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 4.85/5.07          (k1_zfmisc_1 @ 
% 4.85/5.07           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)))),
% 4.85/5.07      inference('demod', [status(thm)], ['166', '167', '168'])).
% 4.85/5.07  thf('170', plain,
% 4.85/5.07      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 4.85/5.07        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 4.85/5.07      inference('sup+', [status(thm)], ['163', '169'])).
% 4.85/5.07  thf('171', plain, ($false), inference('demod', [status(thm)], ['162', '170'])).
% 4.85/5.07  
% 4.85/5.07  % SZS output end Refutation
% 4.85/5.07  
% 4.85/5.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
