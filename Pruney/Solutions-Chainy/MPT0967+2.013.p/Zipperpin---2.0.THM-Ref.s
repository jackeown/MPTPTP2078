%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Zohcmamnll

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:12 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  163 (1936 expanded)
%              Number of leaves         :   34 ( 529 expanded)
%              Depth                    :   25
%              Number of atoms          : 1206 (28765 expanded)
%              Number of equality atoms :  102 (2079 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    v5_relat_1 @ sk_D_1 @ sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v5_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_B ),
    inference(demod,[status(thm)],['10','13'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_C ),
    inference('sup-',[status(thm)],['5','16'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('20',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X22 )
      | ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('24',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
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

thf('26',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('27',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('30',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('32',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('33',plain,(
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

thf('34',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('35',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['37'])).

thf('39',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['37'])).

thf('40',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v1_funct_2 @ sk_D_1 @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('43',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['37'])).

thf('45',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('48',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D_1 )
      = ( k1_relat_1 @ sk_D_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ sk_D_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','48'])).

thf('50',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('51',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('52',plain,
    ( ( ( zip_tseitin_1 @ sk_D_1 @ sk_B @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X24 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('54',plain,(
    ! [X23: $i] :
      ( zip_tseitin_0 @ X23 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','54'])).

thf('56',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('58',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('59',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_C @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_D_1 )
      = ( k1_relat_1 @ sk_D_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf('61',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','55'])).

thf('62',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_D_1 )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X25
       != ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('64',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ k1_xboole_0 )
      | ( v1_funct_2 @ sk_D_1 @ k1_xboole_0 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','55'])).

thf('66',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('67',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('69',plain,
    ( ( ( zip_tseitin_1 @ sk_D_1 @ sk_C @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_C @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X23: $i] :
      ( zip_tseitin_0 @ X23 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('71',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v1_funct_2 @ sk_D_1 @ k1_xboole_0 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','71'])).

thf('73',plain,
    ( ( v1_funct_2 @ sk_D_1 @ k1_xboole_0 @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['37'])).

thf('75',plain,
    ( ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('76',plain,
    ( ~ ( v1_funct_2 @ sk_D_1 @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('79',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['37'])).

thf('80',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('81',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C )
    | ~ ( v1_funct_1 @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('84',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['37'])).

thf('85',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['4','77','82','83','84'])).

thf('86',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['38','85'])).

thf('87',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['36','86'])).

thf('88',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['31','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['24','88'])).

thf('90',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('91',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('93',plain,(
    ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['4','91','92'])).

thf('94',plain,(
    ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','93'])).

thf('95',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_C @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('96',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X25
       != ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('97',plain,
    ( ( ( k1_relat_1 @ sk_D_1 )
     != ( k1_relat_1 @ sk_D_1 ) )
    | ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ ( k1_relat_1 @ sk_D_1 ) )
    | ( v1_funct_2 @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( v1_funct_2 @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_C )
    | ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['31','87'])).

thf('100',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['31','87'])).

thf('101',plain,
    ( ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C )
    | ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['24','88'])).

thf('103',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('104',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('106',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('107',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X1 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('114',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X2 )
      | ( sk_B = X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['112','115'])).

thf('117',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['37'])).

thf('118',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( X0 != k1_xboole_0 )
        | ( zip_tseitin_0 @ X0 @ X1 )
        | ( zip_tseitin_0 @ sk_C @ X2 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ! [X1: $i,X2: $i] :
        ( ( zip_tseitin_0 @ sk_C @ X2 )
        | ( zip_tseitin_0 @ k1_xboole_0 @ X1 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i] :
        ( ( zip_tseitin_0 @ X0 @ X1 )
        | ( zip_tseitin_0 @ X0 @ X3 )
        | ( zip_tseitin_0 @ sk_C @ X2 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['105','119'])).

thf('121',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_0 @ sk_C @ X0 )
        | ( zip_tseitin_0 @ X2 @ X1 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['120'])).

thf('122',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_C @ X0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['121'])).

thf('123',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['4','77','82','83','84'])).

thf('124',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference(simpl_trail,[status(thm)],['122','123'])).

thf('125',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['104','124'])).

thf('126',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_C ),
    inference(demod,[status(thm)],['101','125'])).

thf('127',plain,(
    $false ),
    inference(demod,[status(thm)],['94','126'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Zohcmamnll
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:59:35 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.45/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.64  % Solved by: fo/fo7.sh
% 0.45/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.64  % done 250 iterations in 0.181s
% 0.45/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.64  % SZS output start Refutation
% 0.45/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.64  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.45/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.64  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.45/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.64  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.45/0.64  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.45/0.64  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.45/0.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.64  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.45/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.64  thf(t9_funct_2, conjecture,
% 0.45/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.64     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.64         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.64       ( ( r1_tarski @ B @ C ) =>
% 0.45/0.64         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.45/0.64           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.45/0.64             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.45/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.64    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.64        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.64            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.64          ( ( r1_tarski @ B @ C ) =>
% 0.45/0.64            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.45/0.64              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.45/0.64                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.45/0.64    inference('cnf.neg', [status(esa)], [t9_funct_2])).
% 0.45/0.64  thf('0', plain,
% 0.45/0.64      ((~ (v1_funct_1 @ sk_D_1)
% 0.45/0.64        | ~ (v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)
% 0.45/0.64        | ~ (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('1', plain,
% 0.45/0.64      ((~ (v1_funct_2 @ sk_D_1 @ sk_A @ sk_C))
% 0.45/0.64         <= (~ ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)))),
% 0.45/0.64      inference('split', [status(esa)], ['0'])).
% 0.45/0.64  thf('2', plain, ((v1_funct_1 @ sk_D_1)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('3', plain, ((~ (v1_funct_1 @ sk_D_1)) <= (~ ((v1_funct_1 @ sk_D_1)))),
% 0.45/0.64      inference('split', [status(esa)], ['0'])).
% 0.45/0.64  thf('4', plain, (((v1_funct_1 @ sk_D_1))),
% 0.45/0.64      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.64  thf('5', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('6', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(cc2_relset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.45/0.64  thf('7', plain,
% 0.45/0.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.64         ((v5_relat_1 @ X14 @ X16)
% 0.45/0.64          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.64  thf('8', plain, ((v5_relat_1 @ sk_D_1 @ sk_B)),
% 0.45/0.64      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.64  thf(d19_relat_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( v1_relat_1 @ B ) =>
% 0.45/0.64       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.45/0.64  thf('9', plain,
% 0.45/0.64      (![X7 : $i, X8 : $i]:
% 0.45/0.64         (~ (v5_relat_1 @ X7 @ X8)
% 0.45/0.64          | (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 0.45/0.64          | ~ (v1_relat_1 @ X7))),
% 0.45/0.64      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.45/0.64  thf('10', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_B))),
% 0.45/0.64      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.64  thf('11', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(cc1_relset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64       ( v1_relat_1 @ C ) ))).
% 0.45/0.64  thf('12', plain,
% 0.45/0.64      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.45/0.64         ((v1_relat_1 @ X11)
% 0.45/0.64          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.64  thf('13', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.64      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.64  thf('14', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_B)),
% 0.45/0.64      inference('demod', [status(thm)], ['10', '13'])).
% 0.45/0.64  thf(t1_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.45/0.64       ( r1_tarski @ A @ C ) ))).
% 0.45/0.64  thf('15', plain,
% 0.45/0.64      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.45/0.64         (~ (r1_tarski @ X3 @ X4)
% 0.45/0.64          | ~ (r1_tarski @ X4 @ X5)
% 0.45/0.64          | (r1_tarski @ X3 @ X5))),
% 0.45/0.64      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.45/0.64  thf('16', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ X0) | ~ (r1_tarski @ sk_B @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.64  thf('17', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_C)),
% 0.45/0.64      inference('sup-', [status(thm)], ['5', '16'])).
% 0.45/0.64  thf(d10_xboole_0, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.64  thf('18', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.45/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.64  thf('19', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.45/0.64      inference('simplify', [status(thm)], ['18'])).
% 0.45/0.64  thf(t11_relset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( v1_relat_1 @ C ) =>
% 0.45/0.64       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.45/0.64           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.45/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.45/0.64  thf('20', plain,
% 0.45/0.64      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.45/0.64         (~ (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.45/0.64          | ~ (r1_tarski @ (k2_relat_1 @ X20) @ X22)
% 0.45/0.64          | (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.45/0.64          | ~ (v1_relat_1 @ X20))),
% 0.45/0.64      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.45/0.64  thf('21', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ X0)
% 0.45/0.64          | (m1_subset_1 @ X0 @ 
% 0.45/0.64             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.45/0.64          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.45/0.64      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.64  thf('22', plain,
% 0.45/0.64      (((m1_subset_1 @ sk_D_1 @ 
% 0.45/0.64         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ sk_C)))
% 0.45/0.64        | ~ (v1_relat_1 @ sk_D_1))),
% 0.45/0.64      inference('sup-', [status(thm)], ['17', '21'])).
% 0.45/0.64  thf('23', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.64      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.64  thf('24', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_D_1 @ 
% 0.45/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['22', '23'])).
% 0.45/0.64  thf('25', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(d1_funct_2, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.64           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.45/0.64             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.45/0.64         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.64           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.45/0.64             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.45/0.64  thf(zf_stmt_1, axiom,
% 0.45/0.64    (![C:$i,B:$i,A:$i]:
% 0.45/0.64     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.45/0.64       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.45/0.64  thf('26', plain,
% 0.45/0.64      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.64         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.45/0.64          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 0.45/0.64          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.64  thf('27', plain,
% 0.45/0.64      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.45/0.64        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_1)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['25', '26'])).
% 0.45/0.64  thf('28', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(redefinition_k1_relset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.45/0.64  thf('29', plain,
% 0.45/0.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.64         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.45/0.64          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.64  thf('30', plain,
% 0.45/0.64      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.45/0.64      inference('sup-', [status(thm)], ['28', '29'])).
% 0.45/0.64  thf('31', plain,
% 0.45/0.64      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.45/0.64        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.45/0.64      inference('demod', [status(thm)], ['27', '30'])).
% 0.45/0.64  thf(zf_stmt_2, axiom,
% 0.45/0.64    (![B:$i,A:$i]:
% 0.45/0.64     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.64       ( zip_tseitin_0 @ B @ A ) ))).
% 0.45/0.64  thf('32', plain,
% 0.45/0.64      (![X23 : $i, X24 : $i]:
% 0.45/0.64         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.64  thf('33', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.45/0.64  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.45/0.64  thf(zf_stmt_5, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.45/0.64         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.64           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.45/0.64             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.45/0.64  thf('34', plain,
% 0.45/0.64      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.45/0.64         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.45/0.64          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.45/0.64          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.64  thf('35', plain,
% 0.45/0.64      (((zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.45/0.64        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['33', '34'])).
% 0.45/0.64  thf('36', plain,
% 0.45/0.64      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['32', '35'])).
% 0.45/0.64  thf('37', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('38', plain,
% 0.45/0.64      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.45/0.64      inference('split', [status(esa)], ['37'])).
% 0.45/0.64  thf('39', plain,
% 0.45/0.64      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('split', [status(esa)], ['37'])).
% 0.45/0.64  thf('40', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('41', plain,
% 0.45/0.64      (((v1_funct_2 @ sk_D_1 @ k1_xboole_0 @ sk_B))
% 0.45/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('sup+', [status(thm)], ['39', '40'])).
% 0.45/0.64  thf('42', plain,
% 0.45/0.64      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.64         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.45/0.64          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 0.45/0.64          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.64  thf('43', plain,
% 0.45/0.64      (((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ k1_xboole_0)
% 0.45/0.64         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D_1))))
% 0.45/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['41', '42'])).
% 0.45/0.64  thf('44', plain,
% 0.45/0.64      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('split', [status(esa)], ['37'])).
% 0.45/0.64  thf('45', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('46', plain,
% 0.45/0.64      (((m1_subset_1 @ sk_D_1 @ 
% 0.45/0.64         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.45/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('sup+', [status(thm)], ['44', '45'])).
% 0.45/0.64  thf('47', plain,
% 0.45/0.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.64         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.45/0.64          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.64  thf('48', plain,
% 0.45/0.64      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D_1) = (k1_relat_1 @ sk_D_1)))
% 0.45/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['46', '47'])).
% 0.45/0.64  thf('49', plain,
% 0.45/0.64      (((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ k1_xboole_0)
% 0.45/0.64         | ((k1_xboole_0) = (k1_relat_1 @ sk_D_1))))
% 0.45/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('demod', [status(thm)], ['43', '48'])).
% 0.45/0.64  thf('50', plain,
% 0.45/0.64      (((m1_subset_1 @ sk_D_1 @ 
% 0.45/0.64         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.45/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('sup+', [status(thm)], ['44', '45'])).
% 0.45/0.64  thf('51', plain,
% 0.45/0.64      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.45/0.64         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.45/0.64          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.45/0.64          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.64  thf('52', plain,
% 0.45/0.64      ((((zip_tseitin_1 @ sk_D_1 @ sk_B @ k1_xboole_0)
% 0.45/0.64         | ~ (zip_tseitin_0 @ sk_B @ k1_xboole_0)))
% 0.45/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['50', '51'])).
% 0.45/0.64  thf('53', plain,
% 0.45/0.64      (![X23 : $i, X24 : $i]:
% 0.45/0.64         ((zip_tseitin_0 @ X23 @ X24) | ((X24) != (k1_xboole_0)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.64  thf('54', plain, (![X23 : $i]: (zip_tseitin_0 @ X23 @ k1_xboole_0)),
% 0.45/0.64      inference('simplify', [status(thm)], ['53'])).
% 0.45/0.64  thf('55', plain,
% 0.45/0.64      (((zip_tseitin_1 @ sk_D_1 @ sk_B @ k1_xboole_0))
% 0.45/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('demod', [status(thm)], ['52', '54'])).
% 0.45/0.64  thf('56', plain,
% 0.45/0.64      ((((k1_xboole_0) = (k1_relat_1 @ sk_D_1)))
% 0.45/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('demod', [status(thm)], ['49', '55'])).
% 0.45/0.64  thf('57', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_D_1 @ 
% 0.45/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['22', '23'])).
% 0.45/0.64  thf('58', plain,
% 0.45/0.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.64         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.45/0.64          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.64  thf('59', plain,
% 0.45/0.64      (((k1_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_C @ sk_D_1)
% 0.45/0.64         = (k1_relat_1 @ sk_D_1))),
% 0.45/0.64      inference('sup-', [status(thm)], ['57', '58'])).
% 0.45/0.64  thf('60', plain,
% 0.45/0.64      ((((k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_D_1) = (k1_relat_1 @ sk_D_1)))
% 0.45/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('sup+', [status(thm)], ['56', '59'])).
% 0.45/0.64  thf('61', plain,
% 0.45/0.64      ((((k1_xboole_0) = (k1_relat_1 @ sk_D_1)))
% 0.45/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('demod', [status(thm)], ['49', '55'])).
% 0.45/0.64  thf('62', plain,
% 0.45/0.64      ((((k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_D_1) = (k1_xboole_0)))
% 0.45/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('demod', [status(thm)], ['60', '61'])).
% 0.45/0.64  thf('63', plain,
% 0.45/0.64      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.64         (((X25) != (k1_relset_1 @ X25 @ X26 @ X27))
% 0.45/0.64          | (v1_funct_2 @ X27 @ X25 @ X26)
% 0.45/0.64          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.64  thf('64', plain,
% 0.45/0.64      (((((k1_xboole_0) != (k1_xboole_0))
% 0.45/0.64         | ~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ k1_xboole_0)
% 0.45/0.64         | (v1_funct_2 @ sk_D_1 @ k1_xboole_0 @ sk_C)))
% 0.45/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['62', '63'])).
% 0.45/0.64  thf('65', plain,
% 0.45/0.64      ((((k1_xboole_0) = (k1_relat_1 @ sk_D_1)))
% 0.45/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('demod', [status(thm)], ['49', '55'])).
% 0.45/0.64  thf('66', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_D_1 @ 
% 0.45/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['22', '23'])).
% 0.45/0.64  thf('67', plain,
% 0.45/0.64      (((m1_subset_1 @ sk_D_1 @ 
% 0.45/0.64         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.45/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('sup+', [status(thm)], ['65', '66'])).
% 0.45/0.64  thf('68', plain,
% 0.45/0.64      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.45/0.64         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.45/0.64          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.45/0.64          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.64  thf('69', plain,
% 0.45/0.64      ((((zip_tseitin_1 @ sk_D_1 @ sk_C @ k1_xboole_0)
% 0.45/0.64         | ~ (zip_tseitin_0 @ sk_C @ k1_xboole_0)))
% 0.45/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['67', '68'])).
% 0.45/0.64  thf('70', plain, (![X23 : $i]: (zip_tseitin_0 @ X23 @ k1_xboole_0)),
% 0.45/0.64      inference('simplify', [status(thm)], ['53'])).
% 0.45/0.64  thf('71', plain,
% 0.45/0.64      (((zip_tseitin_1 @ sk_D_1 @ sk_C @ k1_xboole_0))
% 0.45/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('demod', [status(thm)], ['69', '70'])).
% 0.45/0.64  thf('72', plain,
% 0.45/0.64      (((((k1_xboole_0) != (k1_xboole_0))
% 0.45/0.64         | (v1_funct_2 @ sk_D_1 @ k1_xboole_0 @ sk_C)))
% 0.45/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('demod', [status(thm)], ['64', '71'])).
% 0.45/0.64  thf('73', plain,
% 0.45/0.64      (((v1_funct_2 @ sk_D_1 @ k1_xboole_0 @ sk_C))
% 0.45/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('simplify', [status(thm)], ['72'])).
% 0.45/0.64  thf('74', plain,
% 0.45/0.64      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('split', [status(esa)], ['37'])).
% 0.45/0.64  thf('75', plain,
% 0.45/0.64      ((~ (v1_funct_2 @ sk_D_1 @ sk_A @ sk_C))
% 0.45/0.64         <= (~ ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)))),
% 0.45/0.64      inference('split', [status(esa)], ['0'])).
% 0.45/0.64  thf('76', plain,
% 0.45/0.64      ((~ (v1_funct_2 @ sk_D_1 @ k1_xboole_0 @ sk_C))
% 0.45/0.64         <= (~ ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)) & 
% 0.45/0.64             (((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['74', '75'])).
% 0.45/0.64  thf('77', plain,
% 0.45/0.64      (((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['73', '76'])).
% 0.45/0.64  thf('78', plain,
% 0.45/0.64      (((m1_subset_1 @ sk_D_1 @ 
% 0.45/0.64         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.45/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('sup+', [status(thm)], ['65', '66'])).
% 0.45/0.64  thf('79', plain,
% 0.45/0.64      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('split', [status(esa)], ['37'])).
% 0.45/0.64  thf('80', plain,
% 0.45/0.64      ((~ (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.45/0.64         <= (~
% 0.45/0.64             ((m1_subset_1 @ sk_D_1 @ 
% 0.45/0.64               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.45/0.64      inference('split', [status(esa)], ['0'])).
% 0.45/0.64  thf('81', plain,
% 0.45/0.64      ((~ (m1_subset_1 @ sk_D_1 @ 
% 0.45/0.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.45/0.64         <= (~
% 0.45/0.64             ((m1_subset_1 @ sk_D_1 @ 
% 0.45/0.64               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 0.45/0.64             (((sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['79', '80'])).
% 0.45/0.64  thf('82', plain,
% 0.45/0.64      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.45/0.64       ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['78', '81'])).
% 0.45/0.64  thf('83', plain,
% 0.45/0.64      (~ ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.45/0.64       ~ ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)) | ~ ((v1_funct_1 @ sk_D_1))),
% 0.45/0.64      inference('split', [status(esa)], ['0'])).
% 0.45/0.64  thf('84', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.45/0.64      inference('split', [status(esa)], ['37'])).
% 0.45/0.64  thf('85', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.45/0.64      inference('sat_resolution*', [status(thm)], ['4', '77', '82', '83', '84'])).
% 0.45/0.64  thf('86', plain, (((sk_B) != (k1_xboole_0))),
% 0.45/0.64      inference('simpl_trail', [status(thm)], ['38', '85'])).
% 0.45/0.64  thf('87', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)),
% 0.45/0.64      inference('simplify_reflect-', [status(thm)], ['36', '86'])).
% 0.45/0.64  thf('88', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.45/0.64      inference('demod', [status(thm)], ['31', '87'])).
% 0.45/0.64  thf('89', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['24', '88'])).
% 0.45/0.64  thf('90', plain,
% 0.45/0.64      ((~ (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.45/0.64         <= (~
% 0.45/0.64             ((m1_subset_1 @ sk_D_1 @ 
% 0.45/0.64               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.45/0.64      inference('split', [status(esa)], ['0'])).
% 0.45/0.64  thf('91', plain,
% 0.45/0.64      (((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['89', '90'])).
% 0.45/0.64  thf('92', plain,
% 0.45/0.64      (~ ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)) | 
% 0.45/0.64       ~ ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.45/0.64       ~ ((v1_funct_1 @ sk_D_1))),
% 0.45/0.64      inference('split', [status(esa)], ['0'])).
% 0.45/0.64  thf('93', plain, (~ ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C))),
% 0.45/0.64      inference('sat_resolution*', [status(thm)], ['4', '91', '92'])).
% 0.45/0.64  thf('94', plain, (~ (v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)),
% 0.45/0.64      inference('simpl_trail', [status(thm)], ['1', '93'])).
% 0.45/0.64  thf('95', plain,
% 0.45/0.64      (((k1_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_C @ sk_D_1)
% 0.45/0.64         = (k1_relat_1 @ sk_D_1))),
% 0.45/0.64      inference('sup-', [status(thm)], ['57', '58'])).
% 0.45/0.64  thf('96', plain,
% 0.45/0.64      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.64         (((X25) != (k1_relset_1 @ X25 @ X26 @ X27))
% 0.45/0.64          | (v1_funct_2 @ X27 @ X25 @ X26)
% 0.45/0.64          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.64  thf('97', plain,
% 0.45/0.64      ((((k1_relat_1 @ sk_D_1) != (k1_relat_1 @ sk_D_1))
% 0.45/0.64        | ~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ (k1_relat_1 @ sk_D_1))
% 0.45/0.64        | (v1_funct_2 @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['95', '96'])).
% 0.45/0.64  thf('98', plain,
% 0.45/0.64      (((v1_funct_2 @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_C)
% 0.45/0.64        | ~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ (k1_relat_1 @ sk_D_1)))),
% 0.45/0.64      inference('simplify', [status(thm)], ['97'])).
% 0.45/0.64  thf('99', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.45/0.64      inference('demod', [status(thm)], ['31', '87'])).
% 0.45/0.64  thf('100', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.45/0.64      inference('demod', [status(thm)], ['31', '87'])).
% 0.45/0.64  thf('101', plain,
% 0.45/0.64      (((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)
% 0.45/0.64        | ~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['98', '99', '100'])).
% 0.45/0.64  thf('102', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['24', '88'])).
% 0.45/0.64  thf('103', plain,
% 0.45/0.64      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.45/0.64         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.45/0.64          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.45/0.64          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.64  thf('104', plain,
% 0.45/0.64      (((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_A)
% 0.45/0.64        | ~ (zip_tseitin_0 @ sk_C @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['102', '103'])).
% 0.45/0.64  thf('105', plain,
% 0.45/0.64      (![X23 : $i, X24 : $i]:
% 0.45/0.64         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.64  thf('106', plain,
% 0.45/0.64      (![X23 : $i, X24 : $i]:
% 0.45/0.64         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.64  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.45/0.64  thf('107', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.45/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.64  thf('108', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.45/0.64      inference('sup+', [status(thm)], ['106', '107'])).
% 0.45/0.64  thf('109', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('110', plain,
% 0.45/0.64      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.45/0.64         (~ (r1_tarski @ X3 @ X4)
% 0.45/0.64          | ~ (r1_tarski @ X4 @ X5)
% 0.45/0.64          | (r1_tarski @ X3 @ X5))),
% 0.45/0.64      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.45/0.64  thf('111', plain,
% 0.45/0.64      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ~ (r1_tarski @ sk_C @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['109', '110'])).
% 0.45/0.64  thf('112', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         ((zip_tseitin_0 @ sk_C @ X1) | (r1_tarski @ sk_B @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['108', '111'])).
% 0.45/0.64  thf('113', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.45/0.64      inference('sup+', [status(thm)], ['106', '107'])).
% 0.45/0.64  thf('114', plain,
% 0.45/0.64      (![X0 : $i, X2 : $i]:
% 0.45/0.64         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.45/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.64  thf('115', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         ((zip_tseitin_0 @ X1 @ X2) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['113', '114'])).
% 0.45/0.64  thf('116', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         ((zip_tseitin_0 @ sk_C @ X2)
% 0.45/0.64          | ((sk_B) = (X0))
% 0.45/0.64          | (zip_tseitin_0 @ X0 @ X1))),
% 0.45/0.64      inference('sup-', [status(thm)], ['112', '115'])).
% 0.45/0.64  thf('117', plain,
% 0.45/0.64      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.45/0.64      inference('split', [status(esa)], ['37'])).
% 0.45/0.64  thf('118', plain,
% 0.45/0.64      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64          (((X0) != (k1_xboole_0))
% 0.45/0.64           | (zip_tseitin_0 @ X0 @ X1)
% 0.45/0.64           | (zip_tseitin_0 @ sk_C @ X2)))
% 0.45/0.64         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['116', '117'])).
% 0.45/0.64  thf('119', plain,
% 0.45/0.64      ((![X1 : $i, X2 : $i]:
% 0.45/0.64          ((zip_tseitin_0 @ sk_C @ X2) | (zip_tseitin_0 @ k1_xboole_0 @ X1)))
% 0.45/0.64         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.45/0.64      inference('simplify', [status(thm)], ['118'])).
% 0.45/0.64  thf('120', plain,
% 0.45/0.64      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.64          ((zip_tseitin_0 @ X0 @ X1)
% 0.45/0.64           | (zip_tseitin_0 @ X0 @ X3)
% 0.45/0.64           | (zip_tseitin_0 @ sk_C @ X2)))
% 0.45/0.64         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.45/0.64      inference('sup+', [status(thm)], ['105', '119'])).
% 0.45/0.64  thf('121', plain,
% 0.45/0.64      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64          ((zip_tseitin_0 @ sk_C @ X0) | (zip_tseitin_0 @ X2 @ X1)))
% 0.45/0.64         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.45/0.64      inference('condensation', [status(thm)], ['120'])).
% 0.45/0.64  thf('122', plain,
% 0.45/0.64      ((![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0))
% 0.45/0.64         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.45/0.64      inference('condensation', [status(thm)], ['121'])).
% 0.45/0.64  thf('123', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.45/0.64      inference('sat_resolution*', [status(thm)], ['4', '77', '82', '83', '84'])).
% 0.45/0.64  thf('124', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 0.45/0.64      inference('simpl_trail', [status(thm)], ['122', '123'])).
% 0.45/0.64  thf('125', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_A)),
% 0.45/0.64      inference('demod', [status(thm)], ['104', '124'])).
% 0.45/0.64  thf('126', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['101', '125'])).
% 0.45/0.64  thf('127', plain, ($false), inference('demod', [status(thm)], ['94', '126'])).
% 0.45/0.64  
% 0.45/0.64  % SZS output end Refutation
% 0.45/0.64  
% 0.45/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
