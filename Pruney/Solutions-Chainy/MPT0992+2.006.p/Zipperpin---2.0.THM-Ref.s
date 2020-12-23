%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PXxv4QoqsA

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:35 EST 2020

% Result     : Theorem 4.57s
% Output     : Refutation 4.57s
% Verified   : 
% Statistics : Number of formulae       :  220 (1291 expanded)
%              Number of leaves         :   41 ( 380 expanded)
%              Depth                    :   25
%              Number of atoms          : 1966 (25409 expanded)
%              Number of equality atoms :  127 (1149 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ( ( k2_partfun1 @ X35 @ X36 @ X34 @ X37 )
        = ( k7_relat_1 @ X34 @ X37 ) ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X31 @ X32 @ X30 @ X33 ) ) ) ),
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

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X8 @ ( k1_relat_1 @ X9 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X9 @ X8 ) )
        = X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X31 @ X32 @ X30 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','26'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('28',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( k1_relset_1 @ k1_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_D @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

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

thf('30',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( X24
       != ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0
         != ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) )
        | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ k1_xboole_0 )
        | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ k1_xboole_0 @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','26'])).

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

thf('33',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ k1_xboole_0 )
        | ~ ( zip_tseitin_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X23 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('36',plain,(
    ! [X22: $i] :
      ( zip_tseitin_0 @ X22 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','36'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0
         != ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) )
        | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ k1_xboole_0 @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','37'])).

thf('39',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ k1_xboole_0 ) @ k1_xboole_0 @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('43',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('44',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ k1_xboole_0 ) @ k1_xboole_0 @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','44'])).

thf('46',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ k1_xboole_0 ) @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('48',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('50',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('51',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('53',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ k1_xboole_0 ) @ sk_C @ sk_B )
   <= ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('57',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ k1_xboole_0 ) @ k1_xboole_0 @ sk_B )
   <= ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('60',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('63',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('64',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v5_relat_1 @ X4 @ X5 )
      | ( r1_tarski @ ( k2_relat_1 @ X4 ) @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('67',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('70',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['65','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('73',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X19 ) @ X20 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X21 )
      | ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ k1_xboole_0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ k1_xboole_0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ k1_xboole_0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ k1_xboole_0 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('79',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('80',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('83',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('84',plain,
    ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
   <= ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('87',plain,
    ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['80','87'])).

thf('89',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('90',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('92',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('94',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('98',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('101',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['98','101'])).

thf('103',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['95','102'])).

thf('104',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X8 @ ( k1_relat_1 @ X9 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X9 @ X8 ) )
        = X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
      = sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['65','70'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('110',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X38 ) @ X39 )
      | ( v1_funct_2 @ X38 @ ( k1_relat_1 @ X38 ) @ X39 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('113',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('115',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['111','112','115'])).

thf('117',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['108','116'])).

thf('118',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('119',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('121',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( sk_B != k1_xboole_0 )
      & ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('124',plain,(
    ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['14','58','88','89','122','123'])).

thf('125',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['7','124'])).

thf('126',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('128',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['98','101'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X8 @ ( k1_relat_1 @ X9 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X9 @ X8 ) )
        = X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ sk_B ) )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('138',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['111','112','115'])).

thf('139',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ k1_xboole_0 ) @ k1_xboole_0 @ sk_B )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('141',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ k1_xboole_0 ) @ k1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('143',plain,
    ( ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ k1_xboole_0 ) @ sk_B @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_D @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X22: $i] :
      ( zip_tseitin_0 @ X22 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('145',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('146',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ k1_xboole_0 ) @ sk_B @ X0 )
      | ~ ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ k1_xboole_0 ) @ sk_B @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['144','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('150',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ X0 @ sk_B @ ( k7_relat_1 @ sk_D @ k1_xboole_0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['143','148','151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['136','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = sk_B )
      | ~ ( v1_relat_1 @ sk_D )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['135','153'])).

thf('155',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = sk_B )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('158',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['14','58','88','123','89'])).

thf('159',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['156','159'])).

thf('161',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('162',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['98','101'])).

thf('164',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X8 @ ( k1_relat_1 @ X9 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X9 @ X8 ) )
        = X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['126','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['65','70'])).

thf('171',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X38 ) @ X39 )
      | ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X38 ) @ X39 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('174',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('175',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['172','173','174'])).

thf('176',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['169','175'])).

thf('177',plain,(
    $false ),
    inference(demod,[status(thm)],['125','176'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PXxv4QoqsA
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:20:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.57/4.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.57/4.75  % Solved by: fo/fo7.sh
% 4.57/4.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.57/4.75  % done 1751 iterations in 4.286s
% 4.57/4.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.57/4.75  % SZS output start Refutation
% 4.57/4.75  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 4.57/4.75  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.57/4.75  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.57/4.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.57/4.75  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 4.57/4.75  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.57/4.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.57/4.75  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 4.57/4.75  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 4.57/4.75  thf(sk_A_type, type, sk_A: $i).
% 4.57/4.75  thf(sk_D_type, type, sk_D: $i).
% 4.57/4.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.57/4.75  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 4.57/4.75  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 4.57/4.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.57/4.75  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.57/4.75  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 4.57/4.75  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.57/4.75  thf(sk_C_type, type, sk_C: $i).
% 4.57/4.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.57/4.75  thf(sk_B_type, type, sk_B: $i).
% 4.57/4.75  thf(t38_funct_2, conjecture,
% 4.57/4.75    (![A:$i,B:$i,C:$i,D:$i]:
% 4.57/4.75     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.57/4.75         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.57/4.75       ( ( r1_tarski @ C @ A ) =>
% 4.57/4.75         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 4.57/4.75           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 4.57/4.75             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 4.57/4.75             ( m1_subset_1 @
% 4.57/4.75               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 4.57/4.75               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 4.57/4.75  thf(zf_stmt_0, negated_conjecture,
% 4.57/4.75    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 4.57/4.75        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.57/4.75            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.57/4.75          ( ( r1_tarski @ C @ A ) =>
% 4.57/4.75            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 4.57/4.75              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 4.57/4.75                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 4.57/4.75                ( m1_subset_1 @
% 4.57/4.75                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 4.57/4.75                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 4.57/4.75    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 4.57/4.75  thf('0', plain,
% 4.57/4.75      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 4.57/4.75        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 4.57/4.75             sk_B)
% 4.57/4.75        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 4.57/4.75             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 4.57/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.75  thf('1', plain,
% 4.57/4.75      ((~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 4.57/4.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))
% 4.57/4.75         <= (~
% 4.57/4.75             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 4.57/4.75               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 4.57/4.75      inference('split', [status(esa)], ['0'])).
% 4.57/4.75  thf('2', plain,
% 4.57/4.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.57/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.75  thf(redefinition_k2_partfun1, axiom,
% 4.57/4.75    (![A:$i,B:$i,C:$i,D:$i]:
% 4.57/4.75     ( ( ( v1_funct_1 @ C ) & 
% 4.57/4.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.57/4.75       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 4.57/4.75  thf('3', plain,
% 4.57/4.75      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 4.57/4.75         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 4.57/4.75          | ~ (v1_funct_1 @ X34)
% 4.57/4.75          | ((k2_partfun1 @ X35 @ X36 @ X34 @ X37) = (k7_relat_1 @ X34 @ X37)))),
% 4.57/4.75      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 4.57/4.75  thf('4', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 4.57/4.75          | ~ (v1_funct_1 @ sk_D))),
% 4.57/4.75      inference('sup-', [status(thm)], ['2', '3'])).
% 4.57/4.75  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 4.57/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.75  thf('6', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 4.57/4.75      inference('demod', [status(thm)], ['4', '5'])).
% 4.57/4.75  thf('7', plain,
% 4.57/4.75      ((~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 4.57/4.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))
% 4.57/4.75         <= (~
% 4.57/4.75             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 4.57/4.75               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 4.57/4.75      inference('demod', [status(thm)], ['1', '6'])).
% 4.57/4.75  thf('8', plain,
% 4.57/4.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.57/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.75  thf(dt_k2_partfun1, axiom,
% 4.57/4.75    (![A:$i,B:$i,C:$i,D:$i]:
% 4.57/4.75     ( ( ( v1_funct_1 @ C ) & 
% 4.57/4.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.57/4.75       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 4.57/4.75         ( m1_subset_1 @
% 4.57/4.75           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 4.57/4.75           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 4.57/4.75  thf('9', plain,
% 4.57/4.75      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 4.57/4.75         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 4.57/4.75          | ~ (v1_funct_1 @ X30)
% 4.57/4.75          | (v1_funct_1 @ (k2_partfun1 @ X31 @ X32 @ X30 @ X33)))),
% 4.57/4.75      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 4.57/4.75  thf('10', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 4.57/4.75          | ~ (v1_funct_1 @ sk_D))),
% 4.57/4.75      inference('sup-', [status(thm)], ['8', '9'])).
% 4.57/4.75  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 4.57/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.75  thf('12', plain,
% 4.57/4.75      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 4.57/4.75      inference('demod', [status(thm)], ['10', '11'])).
% 4.57/4.75  thf('13', plain,
% 4.57/4.75      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C)))
% 4.57/4.75         <= (~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))))),
% 4.57/4.75      inference('split', [status(esa)], ['0'])).
% 4.57/4.75  thf('14', plain,
% 4.57/4.75      (((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C)))),
% 4.57/4.75      inference('sup-', [status(thm)], ['12', '13'])).
% 4.57/4.75  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 4.57/4.75  thf('15', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 4.57/4.75      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.57/4.75  thf(t91_relat_1, axiom,
% 4.57/4.75    (![A:$i,B:$i]:
% 4.57/4.75     ( ( v1_relat_1 @ B ) =>
% 4.57/4.75       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 4.57/4.75         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 4.57/4.75  thf('16', plain,
% 4.57/4.75      (![X8 : $i, X9 : $i]:
% 4.57/4.75         (~ (r1_tarski @ X8 @ (k1_relat_1 @ X9))
% 4.57/4.75          | ((k1_relat_1 @ (k7_relat_1 @ X9 @ X8)) = (X8))
% 4.57/4.75          | ~ (v1_relat_1 @ X9))),
% 4.57/4.75      inference('cnf', [status(esa)], [t91_relat_1])).
% 4.57/4.75  thf('17', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         (~ (v1_relat_1 @ X0)
% 4.57/4.75          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 4.57/4.75      inference('sup-', [status(thm)], ['15', '16'])).
% 4.57/4.75  thf('18', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 4.57/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.75  thf('19', plain,
% 4.57/4.75      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.57/4.75      inference('split', [status(esa)], ['18'])).
% 4.57/4.75  thf('20', plain,
% 4.57/4.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.57/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.75  thf('21', plain,
% 4.57/4.75      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 4.57/4.75         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 4.57/4.75          | ~ (v1_funct_1 @ X30)
% 4.57/4.75          | (m1_subset_1 @ (k2_partfun1 @ X31 @ X32 @ X30 @ X33) @ 
% 4.57/4.75             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 4.57/4.75      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 4.57/4.75  thf('22', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 4.57/4.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 4.57/4.75          | ~ (v1_funct_1 @ sk_D))),
% 4.57/4.75      inference('sup-', [status(thm)], ['20', '21'])).
% 4.57/4.75  thf('23', plain, ((v1_funct_1 @ sk_D)),
% 4.57/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.75  thf('24', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 4.57/4.75          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.57/4.75      inference('demod', [status(thm)], ['22', '23'])).
% 4.57/4.75  thf('25', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 4.57/4.75      inference('demod', [status(thm)], ['4', '5'])).
% 4.57/4.75  thf('26', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 4.57/4.75          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.57/4.75      inference('demod', [status(thm)], ['24', '25'])).
% 4.57/4.75  thf('27', plain,
% 4.57/4.75      ((![X0 : $i]:
% 4.57/4.75          (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 4.57/4.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 4.57/4.75         <= ((((sk_A) = (k1_xboole_0))))),
% 4.57/4.75      inference('sup+', [status(thm)], ['19', '26'])).
% 4.57/4.75  thf(redefinition_k1_relset_1, axiom,
% 4.57/4.75    (![A:$i,B:$i,C:$i]:
% 4.57/4.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.57/4.75       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 4.57/4.75  thf('28', plain,
% 4.57/4.75      (![X16 : $i, X17 : $i, X18 : $i]:
% 4.57/4.75         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 4.57/4.75          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 4.57/4.75      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.57/4.75  thf('29', plain,
% 4.57/4.75      ((![X0 : $i]:
% 4.57/4.75          ((k1_relset_1 @ k1_xboole_0 @ sk_B @ (k7_relat_1 @ sk_D @ X0))
% 4.57/4.75            = (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0))))
% 4.57/4.75         <= ((((sk_A) = (k1_xboole_0))))),
% 4.57/4.75      inference('sup-', [status(thm)], ['27', '28'])).
% 4.57/4.75  thf(d1_funct_2, axiom,
% 4.57/4.75    (![A:$i,B:$i,C:$i]:
% 4.57/4.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.57/4.75       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.57/4.75           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 4.57/4.75             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 4.57/4.75         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.57/4.75           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 4.57/4.75             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 4.57/4.75  thf(zf_stmt_1, axiom,
% 4.57/4.75    (![C:$i,B:$i,A:$i]:
% 4.57/4.75     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 4.57/4.75       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.57/4.75  thf('30', plain,
% 4.57/4.75      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.57/4.75         (((X24) != (k1_relset_1 @ X24 @ X25 @ X26))
% 4.57/4.75          | (v1_funct_2 @ X26 @ X24 @ X25)
% 4.57/4.75          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 4.57/4.75      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.57/4.75  thf('31', plain,
% 4.57/4.75      ((![X0 : $i]:
% 4.57/4.75          (((k1_xboole_0) != (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))
% 4.57/4.75           | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ k1_xboole_0)
% 4.57/4.75           | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ k1_xboole_0 @ sk_B)))
% 4.57/4.75         <= ((((sk_A) = (k1_xboole_0))))),
% 4.57/4.75      inference('sup-', [status(thm)], ['29', '30'])).
% 4.57/4.75  thf('32', plain,
% 4.57/4.75      ((![X0 : $i]:
% 4.57/4.75          (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 4.57/4.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 4.57/4.75         <= ((((sk_A) = (k1_xboole_0))))),
% 4.57/4.75      inference('sup+', [status(thm)], ['19', '26'])).
% 4.57/4.75  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 4.57/4.75  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 4.57/4.75  thf(zf_stmt_4, axiom,
% 4.57/4.75    (![B:$i,A:$i]:
% 4.57/4.75     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.57/4.75       ( zip_tseitin_0 @ B @ A ) ))).
% 4.57/4.75  thf(zf_stmt_5, axiom,
% 4.57/4.75    (![A:$i,B:$i,C:$i]:
% 4.57/4.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.57/4.75       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 4.57/4.75         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.57/4.75           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 4.57/4.75             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 4.57/4.75  thf('33', plain,
% 4.57/4.75      (![X27 : $i, X28 : $i, X29 : $i]:
% 4.57/4.75         (~ (zip_tseitin_0 @ X27 @ X28)
% 4.57/4.75          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 4.57/4.75          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 4.57/4.75      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.57/4.75  thf('34', plain,
% 4.57/4.75      ((![X0 : $i]:
% 4.57/4.75          ((zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ k1_xboole_0)
% 4.57/4.75           | ~ (zip_tseitin_0 @ sk_B @ k1_xboole_0)))
% 4.57/4.75         <= ((((sk_A) = (k1_xboole_0))))),
% 4.57/4.75      inference('sup-', [status(thm)], ['32', '33'])).
% 4.57/4.75  thf('35', plain,
% 4.57/4.75      (![X22 : $i, X23 : $i]:
% 4.57/4.75         ((zip_tseitin_0 @ X22 @ X23) | ((X23) != (k1_xboole_0)))),
% 4.57/4.75      inference('cnf', [status(esa)], [zf_stmt_4])).
% 4.57/4.75  thf('36', plain, (![X22 : $i]: (zip_tseitin_0 @ X22 @ k1_xboole_0)),
% 4.57/4.75      inference('simplify', [status(thm)], ['35'])).
% 4.57/4.75  thf('37', plain,
% 4.57/4.75      ((![X0 : $i]:
% 4.57/4.75          (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ k1_xboole_0))
% 4.57/4.75         <= ((((sk_A) = (k1_xboole_0))))),
% 4.57/4.75      inference('demod', [status(thm)], ['34', '36'])).
% 4.57/4.75  thf('38', plain,
% 4.57/4.75      ((![X0 : $i]:
% 4.57/4.75          (((k1_xboole_0) != (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))
% 4.57/4.75           | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ k1_xboole_0 @ sk_B)))
% 4.57/4.75         <= ((((sk_A) = (k1_xboole_0))))),
% 4.57/4.75      inference('demod', [status(thm)], ['31', '37'])).
% 4.57/4.75  thf('39', plain,
% 4.57/4.75      (((((k1_xboole_0) != (k1_xboole_0))
% 4.57/4.75         | ~ (v1_relat_1 @ sk_D)
% 4.57/4.75         | (v1_funct_2 @ (k7_relat_1 @ sk_D @ k1_xboole_0) @ k1_xboole_0 @ sk_B)))
% 4.57/4.75         <= ((((sk_A) = (k1_xboole_0))))),
% 4.57/4.75      inference('sup-', [status(thm)], ['17', '38'])).
% 4.57/4.75  thf('40', plain,
% 4.57/4.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.57/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.75  thf(cc2_relat_1, axiom,
% 4.57/4.75    (![A:$i]:
% 4.57/4.75     ( ( v1_relat_1 @ A ) =>
% 4.57/4.75       ( ![B:$i]:
% 4.57/4.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 4.57/4.75  thf('41', plain,
% 4.57/4.75      (![X2 : $i, X3 : $i]:
% 4.57/4.75         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 4.57/4.75          | (v1_relat_1 @ X2)
% 4.57/4.75          | ~ (v1_relat_1 @ X3))),
% 4.57/4.75      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.57/4.75  thf('42', plain,
% 4.57/4.75      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 4.57/4.75      inference('sup-', [status(thm)], ['40', '41'])).
% 4.57/4.75  thf(fc6_relat_1, axiom,
% 4.57/4.75    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 4.57/4.75  thf('43', plain,
% 4.57/4.75      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 4.57/4.75      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.57/4.75  thf('44', plain, ((v1_relat_1 @ sk_D)),
% 4.57/4.75      inference('demod', [status(thm)], ['42', '43'])).
% 4.57/4.75  thf('45', plain,
% 4.57/4.75      (((((k1_xboole_0) != (k1_xboole_0))
% 4.57/4.75         | (v1_funct_2 @ (k7_relat_1 @ sk_D @ k1_xboole_0) @ k1_xboole_0 @ sk_B)))
% 4.57/4.75         <= ((((sk_A) = (k1_xboole_0))))),
% 4.57/4.75      inference('demod', [status(thm)], ['39', '44'])).
% 4.57/4.75  thf('46', plain,
% 4.57/4.75      (((v1_funct_2 @ (k7_relat_1 @ sk_D @ k1_xboole_0) @ k1_xboole_0 @ sk_B))
% 4.57/4.75         <= ((((sk_A) = (k1_xboole_0))))),
% 4.57/4.75      inference('simplify', [status(thm)], ['45'])).
% 4.57/4.75  thf('47', plain,
% 4.57/4.75      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.57/4.75      inference('split', [status(esa)], ['18'])).
% 4.57/4.75  thf('48', plain, ((r1_tarski @ sk_C @ sk_A)),
% 4.57/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.75  thf('49', plain,
% 4.57/4.75      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 4.57/4.75      inference('sup+', [status(thm)], ['47', '48'])).
% 4.57/4.75  thf(t3_xboole_1, axiom,
% 4.57/4.75    (![A:$i]:
% 4.57/4.75     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 4.57/4.75  thf('50', plain,
% 4.57/4.75      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ k1_xboole_0))),
% 4.57/4.75      inference('cnf', [status(esa)], [t3_xboole_1])).
% 4.57/4.75  thf('51', plain,
% 4.57/4.75      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.57/4.75      inference('sup-', [status(thm)], ['49', '50'])).
% 4.57/4.75  thf('52', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 4.57/4.75      inference('demod', [status(thm)], ['4', '5'])).
% 4.57/4.75  thf('53', plain,
% 4.57/4.75      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B))
% 4.57/4.75         <= (~
% 4.57/4.75             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 4.57/4.75               sk_B)))),
% 4.57/4.75      inference('split', [status(esa)], ['0'])).
% 4.57/4.75  thf('54', plain,
% 4.57/4.75      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B))
% 4.57/4.75         <= (~
% 4.57/4.75             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 4.57/4.75               sk_B)))),
% 4.57/4.75      inference('sup-', [status(thm)], ['52', '53'])).
% 4.57/4.75  thf('55', plain,
% 4.57/4.75      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ k1_xboole_0) @ sk_C @ sk_B))
% 4.57/4.75         <= (~
% 4.57/4.75             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 4.57/4.75               sk_B)) & 
% 4.57/4.75             (((sk_A) = (k1_xboole_0))))),
% 4.57/4.75      inference('sup-', [status(thm)], ['51', '54'])).
% 4.57/4.75  thf('56', plain,
% 4.57/4.75      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.57/4.75      inference('sup-', [status(thm)], ['49', '50'])).
% 4.57/4.75  thf('57', plain,
% 4.57/4.75      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ k1_xboole_0) @ k1_xboole_0 @ sk_B))
% 4.57/4.75         <= (~
% 4.57/4.75             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 4.57/4.75               sk_B)) & 
% 4.57/4.75             (((sk_A) = (k1_xboole_0))))),
% 4.57/4.75      inference('demod', [status(thm)], ['55', '56'])).
% 4.57/4.75  thf('58', plain,
% 4.57/4.75      (((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)) | 
% 4.57/4.75       ~ (((sk_A) = (k1_xboole_0)))),
% 4.57/4.75      inference('sup-', [status(thm)], ['46', '57'])).
% 4.57/4.75  thf('59', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 4.57/4.75          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.57/4.75      inference('demod', [status(thm)], ['22', '23'])).
% 4.57/4.75  thf(cc2_relset_1, axiom,
% 4.57/4.75    (![A:$i,B:$i,C:$i]:
% 4.57/4.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.57/4.75       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 4.57/4.75  thf('60', plain,
% 4.57/4.75      (![X13 : $i, X14 : $i, X15 : $i]:
% 4.57/4.75         ((v5_relat_1 @ X13 @ X15)
% 4.57/4.75          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 4.57/4.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.57/4.75  thf('61', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         (v5_relat_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ sk_B)),
% 4.57/4.75      inference('sup-', [status(thm)], ['59', '60'])).
% 4.57/4.75  thf('62', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 4.57/4.75      inference('demod', [status(thm)], ['4', '5'])).
% 4.57/4.75  thf('63', plain,
% 4.57/4.75      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B)),
% 4.57/4.75      inference('demod', [status(thm)], ['61', '62'])).
% 4.57/4.75  thf(d19_relat_1, axiom,
% 4.57/4.75    (![A:$i,B:$i]:
% 4.57/4.75     ( ( v1_relat_1 @ B ) =>
% 4.57/4.75       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 4.57/4.75  thf('64', plain,
% 4.57/4.75      (![X4 : $i, X5 : $i]:
% 4.57/4.75         (~ (v5_relat_1 @ X4 @ X5)
% 4.57/4.75          | (r1_tarski @ (k2_relat_1 @ X4) @ X5)
% 4.57/4.75          | ~ (v1_relat_1 @ X4))),
% 4.57/4.75      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.57/4.75  thf('65', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 4.57/4.75          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 4.57/4.75      inference('sup-', [status(thm)], ['63', '64'])).
% 4.57/4.75  thf('66', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 4.57/4.75          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.57/4.75      inference('demod', [status(thm)], ['22', '23'])).
% 4.57/4.75  thf(cc1_relset_1, axiom,
% 4.57/4.75    (![A:$i,B:$i,C:$i]:
% 4.57/4.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.57/4.75       ( v1_relat_1 @ C ) ))).
% 4.57/4.75  thf('67', plain,
% 4.57/4.75      (![X10 : $i, X11 : $i, X12 : $i]:
% 4.57/4.75         ((v1_relat_1 @ X10)
% 4.57/4.75          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 4.57/4.75      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.57/4.75  thf('68', plain,
% 4.57/4.75      (![X0 : $i]: (v1_relat_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 4.57/4.75      inference('sup-', [status(thm)], ['66', '67'])).
% 4.57/4.75  thf('69', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 4.57/4.75      inference('demod', [status(thm)], ['4', '5'])).
% 4.57/4.75  thf('70', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 4.57/4.75      inference('demod', [status(thm)], ['68', '69'])).
% 4.57/4.75  thf('71', plain,
% 4.57/4.75      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 4.57/4.75      inference('demod', [status(thm)], ['65', '70'])).
% 4.57/4.75  thf('72', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         (~ (v1_relat_1 @ X0)
% 4.57/4.75          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 4.57/4.75      inference('sup-', [status(thm)], ['15', '16'])).
% 4.57/4.75  thf(t11_relset_1, axiom,
% 4.57/4.75    (![A:$i,B:$i,C:$i]:
% 4.57/4.75     ( ( v1_relat_1 @ C ) =>
% 4.57/4.75       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 4.57/4.75           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 4.57/4.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 4.57/4.75  thf('73', plain,
% 4.57/4.75      (![X19 : $i, X20 : $i, X21 : $i]:
% 4.57/4.75         (~ (r1_tarski @ (k1_relat_1 @ X19) @ X20)
% 4.57/4.75          | ~ (r1_tarski @ (k2_relat_1 @ X19) @ X21)
% 4.57/4.75          | (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 4.57/4.75          | ~ (v1_relat_1 @ X19))),
% 4.57/4.75      inference('cnf', [status(esa)], [t11_relset_1])).
% 4.57/4.75  thf('74', plain,
% 4.57/4.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.57/4.75         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 4.57/4.75          | ~ (v1_relat_1 @ X1)
% 4.57/4.75          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ k1_xboole_0))
% 4.57/4.75          | (m1_subset_1 @ (k7_relat_1 @ X1 @ k1_xboole_0) @ 
% 4.57/4.75             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 4.57/4.75          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X1 @ k1_xboole_0)) @ X2))),
% 4.57/4.75      inference('sup-', [status(thm)], ['72', '73'])).
% 4.57/4.75  thf('75', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 4.57/4.75      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.57/4.75  thf('76', plain,
% 4.57/4.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.57/4.75         (~ (v1_relat_1 @ X1)
% 4.57/4.75          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ k1_xboole_0))
% 4.57/4.75          | (m1_subset_1 @ (k7_relat_1 @ X1 @ k1_xboole_0) @ 
% 4.57/4.75             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 4.57/4.75          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X1 @ k1_xboole_0)) @ X2))),
% 4.57/4.75      inference('demod', [status(thm)], ['74', '75'])).
% 4.57/4.75  thf('77', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ k1_xboole_0) @ 
% 4.57/4.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 4.57/4.75          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ k1_xboole_0))
% 4.57/4.75          | ~ (v1_relat_1 @ sk_D))),
% 4.57/4.75      inference('sup-', [status(thm)], ['71', '76'])).
% 4.57/4.75  thf('78', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 4.57/4.75      inference('demod', [status(thm)], ['68', '69'])).
% 4.57/4.75  thf('79', plain, ((v1_relat_1 @ sk_D)),
% 4.57/4.75      inference('demod', [status(thm)], ['42', '43'])).
% 4.57/4.75  thf('80', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         (m1_subset_1 @ (k7_relat_1 @ sk_D @ k1_xboole_0) @ 
% 4.57/4.75          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 4.57/4.75      inference('demod', [status(thm)], ['77', '78', '79'])).
% 4.57/4.75  thf('81', plain,
% 4.57/4.75      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.57/4.75      inference('sup-', [status(thm)], ['49', '50'])).
% 4.57/4.75  thf('82', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 4.57/4.75      inference('demod', [status(thm)], ['4', '5'])).
% 4.57/4.75  thf('83', plain,
% 4.57/4.75      ((~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 4.57/4.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))
% 4.57/4.75         <= (~
% 4.57/4.75             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 4.57/4.75               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 4.57/4.75      inference('split', [status(esa)], ['0'])).
% 4.57/4.75  thf('84', plain,
% 4.57/4.75      ((~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 4.57/4.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))
% 4.57/4.75         <= (~
% 4.57/4.75             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 4.57/4.75               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 4.57/4.75      inference('sup-', [status(thm)], ['82', '83'])).
% 4.57/4.75  thf('85', plain,
% 4.57/4.75      ((~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ k1_xboole_0) @ 
% 4.57/4.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))
% 4.57/4.75         <= (~
% 4.57/4.75             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 4.57/4.75               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))) & 
% 4.57/4.75             (((sk_A) = (k1_xboole_0))))),
% 4.57/4.75      inference('sup-', [status(thm)], ['81', '84'])).
% 4.57/4.75  thf('86', plain,
% 4.57/4.75      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 4.57/4.75      inference('sup-', [status(thm)], ['49', '50'])).
% 4.57/4.75  thf('87', plain,
% 4.57/4.75      ((~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ k1_xboole_0) @ 
% 4.57/4.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 4.57/4.75         <= (~
% 4.57/4.75             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 4.57/4.75               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))) & 
% 4.57/4.75             (((sk_A) = (k1_xboole_0))))),
% 4.57/4.75      inference('demod', [status(thm)], ['85', '86'])).
% 4.57/4.75  thf('88', plain,
% 4.57/4.75      (~ (((sk_A) = (k1_xboole_0))) | 
% 4.57/4.75       ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 4.57/4.75         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 4.57/4.75      inference('sup-', [status(thm)], ['80', '87'])).
% 4.57/4.75  thf('89', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 4.57/4.75      inference('split', [status(esa)], ['18'])).
% 4.57/4.75  thf('90', plain, ((r1_tarski @ sk_C @ sk_A)),
% 4.57/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.75  thf('91', plain,
% 4.57/4.75      (![X22 : $i, X23 : $i]:
% 4.57/4.75         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 4.57/4.75      inference('cnf', [status(esa)], [zf_stmt_4])).
% 4.57/4.75  thf('92', plain,
% 4.57/4.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.57/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.75  thf('93', plain,
% 4.57/4.75      (![X27 : $i, X28 : $i, X29 : $i]:
% 4.57/4.75         (~ (zip_tseitin_0 @ X27 @ X28)
% 4.57/4.75          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 4.57/4.75          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 4.57/4.75      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.57/4.75  thf('94', plain,
% 4.57/4.75      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 4.57/4.75      inference('sup-', [status(thm)], ['92', '93'])).
% 4.57/4.75  thf('95', plain,
% 4.57/4.75      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 4.57/4.75      inference('sup-', [status(thm)], ['91', '94'])).
% 4.57/4.75  thf('96', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 4.57/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.75  thf('97', plain,
% 4.57/4.75      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.57/4.75         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 4.57/4.75          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 4.57/4.75          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 4.57/4.75      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.57/4.75  thf('98', plain,
% 4.57/4.75      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 4.57/4.75        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 4.57/4.75      inference('sup-', [status(thm)], ['96', '97'])).
% 4.57/4.75  thf('99', plain,
% 4.57/4.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.57/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.75  thf('100', plain,
% 4.57/4.75      (![X16 : $i, X17 : $i, X18 : $i]:
% 4.57/4.75         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 4.57/4.75          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 4.57/4.75      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.57/4.75  thf('101', plain,
% 4.57/4.75      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 4.57/4.75      inference('sup-', [status(thm)], ['99', '100'])).
% 4.57/4.75  thf('102', plain,
% 4.57/4.75      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.57/4.75      inference('demod', [status(thm)], ['98', '101'])).
% 4.57/4.75  thf('103', plain,
% 4.57/4.75      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.57/4.75      inference('sup-', [status(thm)], ['95', '102'])).
% 4.57/4.75  thf('104', plain,
% 4.57/4.75      (![X8 : $i, X9 : $i]:
% 4.57/4.75         (~ (r1_tarski @ X8 @ (k1_relat_1 @ X9))
% 4.57/4.75          | ((k1_relat_1 @ (k7_relat_1 @ X9 @ X8)) = (X8))
% 4.57/4.75          | ~ (v1_relat_1 @ X9))),
% 4.57/4.75      inference('cnf', [status(esa)], [t91_relat_1])).
% 4.57/4.75  thf('105', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         (~ (r1_tarski @ X0 @ sk_A)
% 4.57/4.75          | ((sk_B) = (k1_xboole_0))
% 4.57/4.75          | ~ (v1_relat_1 @ sk_D)
% 4.57/4.75          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 4.57/4.75      inference('sup-', [status(thm)], ['103', '104'])).
% 4.57/4.75  thf('106', plain, ((v1_relat_1 @ sk_D)),
% 4.57/4.75      inference('demod', [status(thm)], ['42', '43'])).
% 4.57/4.75  thf('107', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         (~ (r1_tarski @ X0 @ sk_A)
% 4.57/4.75          | ((sk_B) = (k1_xboole_0))
% 4.57/4.75          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 4.57/4.75      inference('demod', [status(thm)], ['105', '106'])).
% 4.57/4.75  thf('108', plain,
% 4.57/4.75      ((((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))
% 4.57/4.75        | ((sk_B) = (k1_xboole_0)))),
% 4.57/4.75      inference('sup-', [status(thm)], ['90', '107'])).
% 4.57/4.75  thf('109', plain,
% 4.57/4.75      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 4.57/4.75      inference('demod', [status(thm)], ['65', '70'])).
% 4.57/4.75  thf(t4_funct_2, axiom,
% 4.57/4.75    (![A:$i,B:$i]:
% 4.57/4.75     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.57/4.75       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 4.57/4.75         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 4.57/4.75           ( m1_subset_1 @
% 4.57/4.75             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 4.57/4.75  thf('110', plain,
% 4.57/4.75      (![X38 : $i, X39 : $i]:
% 4.57/4.75         (~ (r1_tarski @ (k2_relat_1 @ X38) @ X39)
% 4.57/4.75          | (v1_funct_2 @ X38 @ (k1_relat_1 @ X38) @ X39)
% 4.57/4.75          | ~ (v1_funct_1 @ X38)
% 4.57/4.75          | ~ (v1_relat_1 @ X38))),
% 4.57/4.75      inference('cnf', [status(esa)], [t4_funct_2])).
% 4.57/4.75  thf('111', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 4.57/4.75          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 4.57/4.75          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 4.57/4.75             (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 4.57/4.75      inference('sup-', [status(thm)], ['109', '110'])).
% 4.57/4.75  thf('112', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 4.57/4.75      inference('demod', [status(thm)], ['68', '69'])).
% 4.57/4.75  thf('113', plain,
% 4.57/4.75      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 4.57/4.75      inference('demod', [status(thm)], ['10', '11'])).
% 4.57/4.75  thf('114', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 4.57/4.75      inference('demod', [status(thm)], ['4', '5'])).
% 4.57/4.75  thf('115', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 4.57/4.75      inference('demod', [status(thm)], ['113', '114'])).
% 4.57/4.75  thf('116', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 4.57/4.75          (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 4.57/4.75      inference('demod', [status(thm)], ['111', '112', '115'])).
% 4.57/4.75  thf('117', plain,
% 4.57/4.75      (((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 4.57/4.75        | ((sk_B) = (k1_xboole_0)))),
% 4.57/4.75      inference('sup+', [status(thm)], ['108', '116'])).
% 4.57/4.75  thf('118', plain,
% 4.57/4.75      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B))
% 4.57/4.75         <= (~
% 4.57/4.75             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 4.57/4.75               sk_B)))),
% 4.57/4.75      inference('sup-', [status(thm)], ['52', '53'])).
% 4.57/4.75  thf('119', plain,
% 4.57/4.75      ((((sk_B) = (k1_xboole_0)))
% 4.57/4.75         <= (~
% 4.57/4.75             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 4.57/4.75               sk_B)))),
% 4.57/4.75      inference('sup-', [status(thm)], ['117', '118'])).
% 4.57/4.75  thf('120', plain,
% 4.57/4.75      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 4.57/4.75      inference('split', [status(esa)], ['18'])).
% 4.57/4.75  thf('121', plain,
% 4.57/4.75      ((((k1_xboole_0) != (k1_xboole_0)))
% 4.57/4.75         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 4.57/4.75             ~
% 4.57/4.75             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 4.57/4.75               sk_B)))),
% 4.57/4.75      inference('sup-', [status(thm)], ['119', '120'])).
% 4.57/4.75  thf('122', plain,
% 4.57/4.75      (((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)) | 
% 4.57/4.75       (((sk_B) = (k1_xboole_0)))),
% 4.57/4.75      inference('simplify', [status(thm)], ['121'])).
% 4.57/4.75  thf('123', plain,
% 4.57/4.75      (~
% 4.57/4.75       ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 4.57/4.75         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))) | 
% 4.57/4.75       ~
% 4.57/4.75       ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)) | 
% 4.57/4.75       ~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C)))),
% 4.57/4.75      inference('split', [status(esa)], ['0'])).
% 4.57/4.75  thf('124', plain,
% 4.57/4.75      (~
% 4.57/4.75       ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 4.57/4.75         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 4.57/4.75      inference('sat_resolution*', [status(thm)],
% 4.57/4.75                ['14', '58', '88', '89', '122', '123'])).
% 4.57/4.75  thf('125', plain,
% 4.57/4.75      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 4.57/4.75          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 4.57/4.75      inference('simpl_trail', [status(thm)], ['7', '124'])).
% 4.57/4.75  thf('126', plain, ((r1_tarski @ sk_C @ sk_A)),
% 4.57/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.75  thf('127', plain,
% 4.57/4.75      (![X22 : $i, X23 : $i]:
% 4.57/4.75         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 4.57/4.75      inference('cnf', [status(esa)], [zf_stmt_4])).
% 4.57/4.75  thf('128', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 4.57/4.75      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.57/4.75  thf('129', plain,
% 4.57/4.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.57/4.75         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 4.57/4.75      inference('sup+', [status(thm)], ['127', '128'])).
% 4.57/4.75  thf('130', plain,
% 4.57/4.75      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 4.57/4.75      inference('sup-', [status(thm)], ['92', '93'])).
% 4.57/4.75  thf('131', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         ((r1_tarski @ sk_B @ X0) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 4.57/4.75      inference('sup-', [status(thm)], ['129', '130'])).
% 4.57/4.75  thf('132', plain,
% 4.57/4.75      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.57/4.75      inference('demod', [status(thm)], ['98', '101'])).
% 4.57/4.75  thf('133', plain,
% 4.57/4.75      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.57/4.75      inference('sup-', [status(thm)], ['131', '132'])).
% 4.57/4.75  thf('134', plain,
% 4.57/4.75      (![X8 : $i, X9 : $i]:
% 4.57/4.75         (~ (r1_tarski @ X8 @ (k1_relat_1 @ X9))
% 4.57/4.75          | ((k1_relat_1 @ (k7_relat_1 @ X9 @ X8)) = (X8))
% 4.57/4.75          | ~ (v1_relat_1 @ X9))),
% 4.57/4.75      inference('cnf', [status(esa)], [t91_relat_1])).
% 4.57/4.75  thf('135', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         (((sk_A) = (k1_relat_1 @ sk_D))
% 4.57/4.75          | ~ (v1_relat_1 @ X0)
% 4.57/4.75          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ sk_B)) = (sk_B)))),
% 4.57/4.75      inference('sup-', [status(thm)], ['133', '134'])).
% 4.57/4.75  thf('136', plain,
% 4.57/4.75      (![X22 : $i, X23 : $i]:
% 4.57/4.75         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 4.57/4.75      inference('cnf', [status(esa)], [zf_stmt_4])).
% 4.57/4.75  thf('137', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         (~ (v1_relat_1 @ X0)
% 4.57/4.75          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 4.57/4.75      inference('sup-', [status(thm)], ['15', '16'])).
% 4.57/4.75  thf('138', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 4.57/4.75          (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 4.57/4.75      inference('demod', [status(thm)], ['111', '112', '115'])).
% 4.57/4.75  thf('139', plain,
% 4.57/4.75      (((v1_funct_2 @ (k7_relat_1 @ sk_D @ k1_xboole_0) @ k1_xboole_0 @ sk_B)
% 4.57/4.75        | ~ (v1_relat_1 @ sk_D))),
% 4.57/4.75      inference('sup+', [status(thm)], ['137', '138'])).
% 4.57/4.75  thf('140', plain, ((v1_relat_1 @ sk_D)),
% 4.57/4.75      inference('demod', [status(thm)], ['42', '43'])).
% 4.57/4.75  thf('141', plain,
% 4.57/4.75      ((v1_funct_2 @ (k7_relat_1 @ sk_D @ k1_xboole_0) @ k1_xboole_0 @ sk_B)),
% 4.57/4.75      inference('demod', [status(thm)], ['139', '140'])).
% 4.57/4.75  thf('142', plain,
% 4.57/4.75      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.57/4.75         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 4.57/4.75          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 4.57/4.75          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 4.57/4.75      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.57/4.75  thf('143', plain,
% 4.57/4.75      ((~ (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ k1_xboole_0) @ sk_B @ 
% 4.57/4.75           k1_xboole_0)
% 4.57/4.75        | ((k1_xboole_0)
% 4.57/4.75            = (k1_relset_1 @ k1_xboole_0 @ sk_B @ 
% 4.57/4.75               (k7_relat_1 @ sk_D @ k1_xboole_0))))),
% 4.57/4.75      inference('sup-', [status(thm)], ['141', '142'])).
% 4.57/4.75  thf('144', plain, (![X22 : $i]: (zip_tseitin_0 @ X22 @ k1_xboole_0)),
% 4.57/4.75      inference('simplify', [status(thm)], ['35'])).
% 4.57/4.75  thf('145', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         (m1_subset_1 @ (k7_relat_1 @ sk_D @ k1_xboole_0) @ 
% 4.57/4.75          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 4.57/4.75      inference('demod', [status(thm)], ['77', '78', '79'])).
% 4.57/4.75  thf('146', plain,
% 4.57/4.75      (![X27 : $i, X28 : $i, X29 : $i]:
% 4.57/4.75         (~ (zip_tseitin_0 @ X27 @ X28)
% 4.57/4.75          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 4.57/4.75          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 4.57/4.75      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.57/4.75  thf('147', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         ((zip_tseitin_1 @ (k7_relat_1 @ sk_D @ k1_xboole_0) @ sk_B @ X0)
% 4.57/4.75          | ~ (zip_tseitin_0 @ sk_B @ X0))),
% 4.57/4.75      inference('sup-', [status(thm)], ['145', '146'])).
% 4.57/4.75  thf('148', plain,
% 4.57/4.75      ((zip_tseitin_1 @ (k7_relat_1 @ sk_D @ k1_xboole_0) @ sk_B @ k1_xboole_0)),
% 4.57/4.75      inference('sup-', [status(thm)], ['144', '147'])).
% 4.57/4.75  thf('149', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         (m1_subset_1 @ (k7_relat_1 @ sk_D @ k1_xboole_0) @ 
% 4.57/4.75          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 4.57/4.75      inference('demod', [status(thm)], ['77', '78', '79'])).
% 4.57/4.75  thf('150', plain,
% 4.57/4.75      (![X16 : $i, X17 : $i, X18 : $i]:
% 4.57/4.75         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 4.57/4.75          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 4.57/4.75      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.57/4.75  thf('151', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         ((k1_relset_1 @ X0 @ sk_B @ (k7_relat_1 @ sk_D @ k1_xboole_0))
% 4.57/4.75           = (k1_relat_1 @ (k7_relat_1 @ sk_D @ k1_xboole_0)))),
% 4.57/4.75      inference('sup-', [status(thm)], ['149', '150'])).
% 4.57/4.75  thf('152', plain,
% 4.57/4.75      (((k1_xboole_0) = (k1_relat_1 @ (k7_relat_1 @ sk_D @ k1_xboole_0)))),
% 4.57/4.75      inference('demod', [status(thm)], ['143', '148', '151'])).
% 4.57/4.75  thf('153', plain,
% 4.57/4.75      (![X0 : $i, X1 : $i]:
% 4.57/4.75         (((k1_xboole_0) = (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))
% 4.57/4.75          | (zip_tseitin_0 @ X0 @ X1))),
% 4.57/4.75      inference('sup+', [status(thm)], ['136', '152'])).
% 4.57/4.75  thf('154', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         (((k1_xboole_0) = (sk_B))
% 4.57/4.75          | ~ (v1_relat_1 @ sk_D)
% 4.57/4.75          | ((sk_A) = (k1_relat_1 @ sk_D))
% 4.57/4.75          | (zip_tseitin_0 @ sk_B @ X0))),
% 4.57/4.75      inference('sup+', [status(thm)], ['135', '153'])).
% 4.57/4.75  thf('155', plain, ((v1_relat_1 @ sk_D)),
% 4.57/4.75      inference('demod', [status(thm)], ['42', '43'])).
% 4.57/4.75  thf('156', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         (((k1_xboole_0) = (sk_B))
% 4.57/4.75          | ((sk_A) = (k1_relat_1 @ sk_D))
% 4.57/4.75          | (zip_tseitin_0 @ sk_B @ X0))),
% 4.57/4.75      inference('demod', [status(thm)], ['154', '155'])).
% 4.57/4.75  thf('157', plain,
% 4.57/4.75      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 4.57/4.75      inference('split', [status(esa)], ['18'])).
% 4.57/4.75  thf('158', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 4.57/4.75      inference('sat_resolution*', [status(thm)],
% 4.57/4.75                ['14', '58', '88', '123', '89'])).
% 4.57/4.75  thf('159', plain, (((sk_B) != (k1_xboole_0))),
% 4.57/4.75      inference('simpl_trail', [status(thm)], ['157', '158'])).
% 4.57/4.75  thf('160', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         (((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_0 @ sk_B @ X0))),
% 4.57/4.75      inference('simplify_reflect-', [status(thm)], ['156', '159'])).
% 4.57/4.75  thf('161', plain,
% 4.57/4.75      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 4.57/4.75      inference('sup-', [status(thm)], ['92', '93'])).
% 4.57/4.75  thf('162', plain,
% 4.57/4.75      ((((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 4.57/4.75      inference('sup-', [status(thm)], ['160', '161'])).
% 4.57/4.75  thf('163', plain,
% 4.57/4.75      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 4.57/4.75      inference('demod', [status(thm)], ['98', '101'])).
% 4.57/4.75  thf('164', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 4.57/4.75      inference('clc', [status(thm)], ['162', '163'])).
% 4.57/4.75  thf('165', plain,
% 4.57/4.75      (![X8 : $i, X9 : $i]:
% 4.57/4.75         (~ (r1_tarski @ X8 @ (k1_relat_1 @ X9))
% 4.57/4.75          | ((k1_relat_1 @ (k7_relat_1 @ X9 @ X8)) = (X8))
% 4.57/4.75          | ~ (v1_relat_1 @ X9))),
% 4.57/4.75      inference('cnf', [status(esa)], [t91_relat_1])).
% 4.57/4.75  thf('166', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         (~ (r1_tarski @ X0 @ sk_A)
% 4.57/4.75          | ~ (v1_relat_1 @ sk_D)
% 4.57/4.75          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 4.57/4.75      inference('sup-', [status(thm)], ['164', '165'])).
% 4.57/4.75  thf('167', plain, ((v1_relat_1 @ sk_D)),
% 4.57/4.75      inference('demod', [status(thm)], ['42', '43'])).
% 4.57/4.75  thf('168', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         (~ (r1_tarski @ X0 @ sk_A)
% 4.57/4.75          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 4.57/4.75      inference('demod', [status(thm)], ['166', '167'])).
% 4.57/4.75  thf('169', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 4.57/4.75      inference('sup-', [status(thm)], ['126', '168'])).
% 4.57/4.75  thf('170', plain,
% 4.57/4.75      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 4.57/4.75      inference('demod', [status(thm)], ['65', '70'])).
% 4.57/4.75  thf('171', plain,
% 4.57/4.75      (![X38 : $i, X39 : $i]:
% 4.57/4.75         (~ (r1_tarski @ (k2_relat_1 @ X38) @ X39)
% 4.57/4.75          | (m1_subset_1 @ X38 @ 
% 4.57/4.75             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X38) @ X39)))
% 4.57/4.75          | ~ (v1_funct_1 @ X38)
% 4.57/4.75          | ~ (v1_relat_1 @ X38))),
% 4.57/4.75      inference('cnf', [status(esa)], [t4_funct_2])).
% 4.57/4.75  thf('172', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 4.57/4.75          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 4.57/4.75          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 4.57/4.75             (k1_zfmisc_1 @ 
% 4.57/4.75              (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))))),
% 4.57/4.75      inference('sup-', [status(thm)], ['170', '171'])).
% 4.57/4.75  thf('173', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 4.57/4.75      inference('demod', [status(thm)], ['68', '69'])).
% 4.57/4.75  thf('174', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 4.57/4.75      inference('demod', [status(thm)], ['113', '114'])).
% 4.57/4.75  thf('175', plain,
% 4.57/4.75      (![X0 : $i]:
% 4.57/4.75         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 4.57/4.75          (k1_zfmisc_1 @ 
% 4.57/4.75           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)))),
% 4.57/4.75      inference('demod', [status(thm)], ['172', '173', '174'])).
% 4.57/4.75  thf('176', plain,
% 4.57/4.75      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 4.57/4.75        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 4.57/4.75      inference('sup+', [status(thm)], ['169', '175'])).
% 4.57/4.75  thf('177', plain, ($false), inference('demod', [status(thm)], ['125', '176'])).
% 4.57/4.75  
% 4.57/4.75  % SZS output end Refutation
% 4.57/4.75  
% 4.57/4.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
