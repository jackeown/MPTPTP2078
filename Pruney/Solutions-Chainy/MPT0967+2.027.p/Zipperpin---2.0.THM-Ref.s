%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FlFrF54nrV

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:14 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 617 expanded)
%              Number of leaves         :   35 ( 183 expanded)
%              Depth                    :   25
%              Number of atoms          : 1125 (8882 expanded)
%              Number of equality atoms :   92 ( 562 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('10',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v5_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['12','17'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['7','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t14_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf('23',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

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

thf('26',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('27',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('30',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('33',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('36',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('41',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['43'])).

thf('45',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['7','20'])).

thf('50',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['43'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) )
        | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('57',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_D )
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X25
       != ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('59',plain,
    ( ( ( k1_xboole_0
       != ( k1_relat_1 @ sk_D ) )
      | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ k1_xboole_0 )
      | ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('61',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('62',plain,
    ( ( ( zip_tseitin_1 @ sk_D @ sk_C @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_C @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X24 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('64',plain,(
    ! [X23: $i] :
      ( zip_tseitin_0 @ X23 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','64'])).

thf('66',plain,
    ( ( ( k1_xboole_0
       != ( k1_relat_1 @ sk_D ) )
      | ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','65'])).

thf('67',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['43'])).

thf('68',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('71',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('73',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('74',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D )
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','74'])).

thf('76',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('77',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('78',plain,
    ( ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X23: $i] :
      ( zip_tseitin_0 @ X23 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('80',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','80'])).

thf('82',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','81'])).

thf('83',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['43'])).

thf('85',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['46'])).

thf('86',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('89',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['43'])).

thf('90',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['46'])).

thf('91',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['46'])).

thf('94',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['43'])).

thf('95',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['48','87','92','93','94'])).

thf('96',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['44','95'])).

thf('97',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['42','96'])).

thf('98',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['37','97'])).

thf('99',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['30','98'])).

thf('100',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X25
       != ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('101',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['46'])).

thf('104',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('105',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['46'])).

thf('106',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['46'])).

thf('108',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['48','106','107'])).

thf('109',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['103','108'])).

thf('110',plain,(
    ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['102','109'])).

thf('111',plain,(
    ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['27','110'])).

thf('112',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','111'])).

thf('113',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['44','95'])).

thf('114',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['112','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FlFrF54nrV
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:31:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.58  % Solved by: fo/fo7.sh
% 0.38/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.58  % done 231 iterations in 0.158s
% 0.38/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.58  % SZS output start Refutation
% 0.38/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.58  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.38/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.38/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.38/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.58  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.38/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.58  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.38/0.58  thf(t9_funct_2, conjecture,
% 0.38/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.58     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.38/0.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.58       ( ( r1_tarski @ B @ C ) =>
% 0.38/0.58         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.38/0.58           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.38/0.58             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.38/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.58    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.58        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.38/0.58            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.58          ( ( r1_tarski @ B @ C ) =>
% 0.38/0.58            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.38/0.58              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.38/0.58                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.38/0.58    inference('cnf.neg', [status(esa)], [t9_funct_2])).
% 0.38/0.58  thf('0', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(d1_funct_2, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.58       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.58           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.38/0.58             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.38/0.58         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.58           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.38/0.58             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.38/0.58  thf(zf_stmt_1, axiom,
% 0.38/0.58    (![B:$i,A:$i]:
% 0.38/0.58     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.58       ( zip_tseitin_0 @ B @ A ) ))).
% 0.38/0.58  thf('1', plain,
% 0.38/0.58      (![X23 : $i, X24 : $i]:
% 0.38/0.58         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.38/0.58  thf('2', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.38/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.58  thf(d10_xboole_0, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.58  thf('3', plain,
% 0.38/0.58      (![X0 : $i, X2 : $i]:
% 0.38/0.58         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.38/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.58  thf('4', plain,
% 0.38/0.58      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.58  thf('5', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.58         (~ (r1_tarski @ X1 @ X0)
% 0.38/0.58          | (zip_tseitin_0 @ X0 @ X2)
% 0.38/0.58          | ((X1) = (k1_xboole_0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['1', '4'])).
% 0.38/0.58  thf('6', plain,
% 0.38/0.58      (![X0 : $i]: (((sk_B) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_C @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['0', '5'])).
% 0.38/0.58  thf('7', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('8', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(cc2_relset_1, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.58       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.38/0.58  thf('9', plain,
% 0.38/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.58         ((v5_relat_1 @ X13 @ X15)
% 0.38/0.58          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.38/0.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.58  thf('10', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 0.38/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.38/0.58  thf(d19_relat_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ B ) =>
% 0.38/0.58       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.38/0.58  thf('11', plain,
% 0.38/0.58      (![X9 : $i, X10 : $i]:
% 0.38/0.58         (~ (v5_relat_1 @ X9 @ X10)
% 0.38/0.58          | (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 0.38/0.58          | ~ (v1_relat_1 @ X9))),
% 0.38/0.58      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.38/0.58  thf('12', plain,
% 0.38/0.58      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.58  thf('13', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(cc2_relat_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ A ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.38/0.58  thf('14', plain,
% 0.38/0.58      (![X7 : $i, X8 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.38/0.58          | (v1_relat_1 @ X7)
% 0.38/0.58          | ~ (v1_relat_1 @ X8))),
% 0.38/0.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.38/0.58  thf('15', plain,
% 0.38/0.58      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.38/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.38/0.58  thf(fc6_relat_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.38/0.58  thf('16', plain,
% 0.38/0.58      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.38/0.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.38/0.58  thf('17', plain, ((v1_relat_1 @ sk_D)),
% 0.38/0.58      inference('demod', [status(thm)], ['15', '16'])).
% 0.38/0.58  thf('18', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 0.38/0.58      inference('demod', [status(thm)], ['12', '17'])).
% 0.38/0.58  thf(t1_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.38/0.58       ( r1_tarski @ A @ C ) ))).
% 0.38/0.58  thf('19', plain,
% 0.38/0.58      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.58         (~ (r1_tarski @ X3 @ X4)
% 0.38/0.58          | ~ (r1_tarski @ X4 @ X5)
% 0.38/0.58          | (r1_tarski @ X3 @ X5))),
% 0.38/0.58      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.38/0.58  thf('20', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((r1_tarski @ (k2_relat_1 @ sk_D) @ X0) | ~ (r1_tarski @ sk_B @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.38/0.58  thf('21', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.38/0.58      inference('sup-', [status(thm)], ['7', '20'])).
% 0.38/0.58  thf('22', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(t14_relset_1, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.38/0.58       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 0.38/0.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 0.38/0.58  thf('23', plain,
% 0.38/0.58      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.38/0.58         (~ (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 0.38/0.58          | (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20)))
% 0.38/0.58          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.38/0.58      inference('cnf', [status(esa)], [t14_relset_1])).
% 0.38/0.58  thf('24', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.38/0.58          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.58  thf('25', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['21', '24'])).
% 0.38/0.58  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.38/0.58  thf(zf_stmt_3, axiom,
% 0.38/0.58    (![C:$i,B:$i,A:$i]:
% 0.38/0.58     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.38/0.58       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.38/0.58  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.38/0.58  thf(zf_stmt_5, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.58       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.38/0.58         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.58           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.38/0.58             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.38/0.58  thf('26', plain,
% 0.38/0.58      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.38/0.58         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.38/0.58          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.38/0.58          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.38/0.58  thf('27', plain,
% 0.38/0.58      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_A) | ~ (zip_tseitin_0 @ sk_C @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.58  thf('28', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['21', '24'])).
% 0.38/0.58  thf(redefinition_k1_relset_1, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.58       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.38/0.58  thf('29', plain,
% 0.38/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.58         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.38/0.58          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.38/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.38/0.58  thf('30', plain,
% 0.38/0.58      (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.38/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.38/0.58  thf('31', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('32', plain,
% 0.38/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.38/0.58         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.38/0.58          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 0.38/0.58          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.58  thf('33', plain,
% 0.38/0.58      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.38/0.58        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.38/0.58  thf('34', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('35', plain,
% 0.38/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.58         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.38/0.58          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.38/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.38/0.58  thf('36', plain,
% 0.38/0.58      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.38/0.58      inference('sup-', [status(thm)], ['34', '35'])).
% 0.38/0.58  thf('37', plain,
% 0.38/0.58      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.38/0.58      inference('demod', [status(thm)], ['33', '36'])).
% 0.38/0.58  thf('38', plain,
% 0.38/0.58      (![X23 : $i, X24 : $i]:
% 0.38/0.58         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.58  thf('39', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('40', plain,
% 0.38/0.58      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.38/0.58         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.38/0.58          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.38/0.58          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.38/0.58  thf('41', plain,
% 0.38/0.58      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['39', '40'])).
% 0.38/0.58  thf('42', plain,
% 0.38/0.58      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['38', '41'])).
% 0.38/0.58  thf('43', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('44', plain,
% 0.38/0.58      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.38/0.58      inference('split', [status(esa)], ['43'])).
% 0.38/0.58  thf('45', plain, ((v1_funct_1 @ sk_D)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('46', plain,
% 0.38/0.58      ((~ (v1_funct_1 @ sk_D)
% 0.38/0.58        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.38/0.58        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('47', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.38/0.58      inference('split', [status(esa)], ['46'])).
% 0.38/0.58  thf('48', plain, (((v1_funct_1 @ sk_D))),
% 0.38/0.58      inference('sup-', [status(thm)], ['45', '47'])).
% 0.38/0.58  thf('49', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.38/0.58      inference('sup-', [status(thm)], ['7', '20'])).
% 0.38/0.58  thf('50', plain,
% 0.38/0.58      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.58      inference('split', [status(esa)], ['43'])).
% 0.38/0.58  thf('51', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('52', plain,
% 0.38/0.58      (((m1_subset_1 @ sk_D @ 
% 0.38/0.58         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.38/0.58         <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.58      inference('sup+', [status(thm)], ['50', '51'])).
% 0.38/0.58  thf('53', plain,
% 0.38/0.58      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.38/0.58         (~ (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 0.38/0.58          | (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20)))
% 0.38/0.58          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.38/0.58      inference('cnf', [status(esa)], [t14_relset_1])).
% 0.38/0.58  thf('54', plain,
% 0.38/0.58      ((![X0 : $i]:
% 0.38/0.58          ((m1_subset_1 @ sk_D @ 
% 0.38/0.58            (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)))
% 0.38/0.58           | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0)))
% 0.38/0.58         <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['52', '53'])).
% 0.38/0.58  thf('55', plain,
% 0.38/0.58      (((m1_subset_1 @ sk_D @ 
% 0.38/0.58         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.38/0.58         <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['49', '54'])).
% 0.38/0.58  thf('56', plain,
% 0.38/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.58         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.38/0.58          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.38/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.38/0.58  thf('57', plain,
% 0.38/0.58      ((((k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_D) = (k1_relat_1 @ sk_D)))
% 0.38/0.58         <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['55', '56'])).
% 0.38/0.58  thf('58', plain,
% 0.38/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.38/0.58         (((X25) != (k1_relset_1 @ X25 @ X26 @ X27))
% 0.38/0.58          | (v1_funct_2 @ X27 @ X25 @ X26)
% 0.38/0.58          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.58  thf('59', plain,
% 0.38/0.58      (((((k1_xboole_0) != (k1_relat_1 @ sk_D))
% 0.38/0.58         | ~ (zip_tseitin_1 @ sk_D @ sk_C @ k1_xboole_0)
% 0.38/0.58         | (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C)))
% 0.38/0.58         <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['57', '58'])).
% 0.38/0.58  thf('60', plain,
% 0.38/0.58      (((m1_subset_1 @ sk_D @ 
% 0.38/0.58         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.38/0.58         <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['49', '54'])).
% 0.38/0.58  thf('61', plain,
% 0.38/0.58      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.38/0.58         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.38/0.58          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.38/0.58          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.38/0.58  thf('62', plain,
% 0.38/0.58      ((((zip_tseitin_1 @ sk_D @ sk_C @ k1_xboole_0)
% 0.38/0.58         | ~ (zip_tseitin_0 @ sk_C @ k1_xboole_0)))
% 0.38/0.58         <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['60', '61'])).
% 0.38/0.58  thf('63', plain,
% 0.38/0.58      (![X23 : $i, X24 : $i]:
% 0.38/0.58         ((zip_tseitin_0 @ X23 @ X24) | ((X24) != (k1_xboole_0)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.58  thf('64', plain, (![X23 : $i]: (zip_tseitin_0 @ X23 @ k1_xboole_0)),
% 0.38/0.58      inference('simplify', [status(thm)], ['63'])).
% 0.38/0.58  thf('65', plain,
% 0.38/0.58      (((zip_tseitin_1 @ sk_D @ sk_C @ k1_xboole_0))
% 0.38/0.58         <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.58      inference('demod', [status(thm)], ['62', '64'])).
% 0.38/0.58  thf('66', plain,
% 0.38/0.58      (((((k1_xboole_0) != (k1_relat_1 @ sk_D))
% 0.38/0.58         | (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C)))
% 0.38/0.58         <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.58      inference('demod', [status(thm)], ['59', '65'])).
% 0.38/0.58  thf('67', plain,
% 0.38/0.58      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.58      inference('split', [status(esa)], ['43'])).
% 0.38/0.58  thf('68', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('69', plain,
% 0.38/0.58      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 0.38/0.58         <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.58      inference('sup+', [status(thm)], ['67', '68'])).
% 0.38/0.58  thf('70', plain,
% 0.38/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.38/0.58         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.38/0.58          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 0.38/0.58          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.58  thf('71', plain,
% 0.38/0.58      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.38/0.58         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D))))
% 0.38/0.58         <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['69', '70'])).
% 0.38/0.58  thf('72', plain,
% 0.38/0.58      (((m1_subset_1 @ sk_D @ 
% 0.38/0.58         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.38/0.58         <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.58      inference('sup+', [status(thm)], ['50', '51'])).
% 0.38/0.58  thf('73', plain,
% 0.38/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.58         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.38/0.58          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.38/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.38/0.58  thf('74', plain,
% 0.38/0.58      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D) = (k1_relat_1 @ sk_D)))
% 0.38/0.58         <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['72', '73'])).
% 0.38/0.58  thf('75', plain,
% 0.38/0.58      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.38/0.58         | ((k1_xboole_0) = (k1_relat_1 @ sk_D))))
% 0.38/0.58         <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.58      inference('demod', [status(thm)], ['71', '74'])).
% 0.38/0.58  thf('76', plain,
% 0.38/0.58      (((m1_subset_1 @ sk_D @ 
% 0.38/0.58         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.38/0.58         <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.58      inference('sup+', [status(thm)], ['50', '51'])).
% 0.38/0.58  thf('77', plain,
% 0.38/0.58      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.38/0.58         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.38/0.58          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.38/0.58          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.38/0.58  thf('78', plain,
% 0.38/0.58      ((((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.38/0.58         | ~ (zip_tseitin_0 @ sk_B @ k1_xboole_0)))
% 0.38/0.58         <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['76', '77'])).
% 0.38/0.58  thf('79', plain, (![X23 : $i]: (zip_tseitin_0 @ X23 @ k1_xboole_0)),
% 0.38/0.58      inference('simplify', [status(thm)], ['63'])).
% 0.38/0.58  thf('80', plain,
% 0.38/0.58      (((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0))
% 0.38/0.58         <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.58      inference('demod', [status(thm)], ['78', '79'])).
% 0.38/0.58  thf('81', plain,
% 0.38/0.58      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.58      inference('demod', [status(thm)], ['75', '80'])).
% 0.38/0.58  thf('82', plain,
% 0.38/0.58      (((((k1_xboole_0) != (k1_xboole_0))
% 0.38/0.58         | (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C)))
% 0.38/0.58         <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.58      inference('demod', [status(thm)], ['66', '81'])).
% 0.38/0.58  thf('83', plain,
% 0.38/0.58      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.38/0.58         <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.58      inference('simplify', [status(thm)], ['82'])).
% 0.38/0.58  thf('84', plain,
% 0.38/0.58      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.58      inference('split', [status(esa)], ['43'])).
% 0.38/0.58  thf('85', plain,
% 0.38/0.58      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.38/0.58         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.38/0.58      inference('split', [status(esa)], ['46'])).
% 0.38/0.58  thf('86', plain,
% 0.38/0.58      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.38/0.58         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['84', '85'])).
% 0.38/0.58  thf('87', plain,
% 0.38/0.58      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['83', '86'])).
% 0.38/0.58  thf('88', plain,
% 0.38/0.58      (((m1_subset_1 @ sk_D @ 
% 0.38/0.58         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.38/0.58         <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['49', '54'])).
% 0.38/0.58  thf('89', plain,
% 0.38/0.58      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.58      inference('split', [status(esa)], ['43'])).
% 0.38/0.58  thf('90', plain,
% 0.38/0.58      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.38/0.58         <= (~
% 0.38/0.58             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.38/0.58      inference('split', [status(esa)], ['46'])).
% 0.38/0.58  thf('91', plain,
% 0.38/0.58      ((~ (m1_subset_1 @ sk_D @ 
% 0.38/0.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.38/0.58         <= (~
% 0.38/0.58             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 0.38/0.58             (((sk_A) = (k1_xboole_0))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['89', '90'])).
% 0.38/0.58  thf('92', plain,
% 0.38/0.58      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.38/0.58       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['88', '91'])).
% 0.38/0.58  thf('93', plain,
% 0.38/0.58      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.38/0.58       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ ((v1_funct_1 @ sk_D))),
% 0.38/0.58      inference('split', [status(esa)], ['46'])).
% 0.38/0.58  thf('94', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.38/0.58      inference('split', [status(esa)], ['43'])).
% 0.38/0.58  thf('95', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.38/0.58      inference('sat_resolution*', [status(thm)],
% 0.38/0.58                ['48', '87', '92', '93', '94'])).
% 0.38/0.58  thf('96', plain, (((sk_B) != (k1_xboole_0))),
% 0.38/0.58      inference('simpl_trail', [status(thm)], ['44', '95'])).
% 0.38/0.58  thf('97', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 0.38/0.58      inference('simplify_reflect-', [status(thm)], ['42', '96'])).
% 0.38/0.58  thf('98', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.38/0.58      inference('demod', [status(thm)], ['37', '97'])).
% 0.38/0.58  thf('99', plain, (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['30', '98'])).
% 0.38/0.58  thf('100', plain,
% 0.38/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.38/0.58         (((X25) != (k1_relset_1 @ X25 @ X26 @ X27))
% 0.38/0.58          | (v1_funct_2 @ X27 @ X25 @ X26)
% 0.38/0.58          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.58  thf('101', plain,
% 0.38/0.58      ((((sk_A) != (sk_A))
% 0.38/0.58        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)
% 0.38/0.58        | (v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.38/0.58      inference('sup-', [status(thm)], ['99', '100'])).
% 0.38/0.58  thf('102', plain,
% 0.38/0.58      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.38/0.58        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A))),
% 0.38/0.58      inference('simplify', [status(thm)], ['101'])).
% 0.38/0.58  thf('103', plain,
% 0.38/0.58      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.38/0.58         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.38/0.58      inference('split', [status(esa)], ['46'])).
% 0.38/0.58  thf('104', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['21', '24'])).
% 0.38/0.58  thf('105', plain,
% 0.38/0.58      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.38/0.58         <= (~
% 0.38/0.58             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.38/0.58      inference('split', [status(esa)], ['46'])).
% 0.38/0.58  thf('106', plain,
% 0.38/0.58      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['104', '105'])).
% 0.38/0.58  thf('107', plain,
% 0.38/0.58      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | 
% 0.38/0.58       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.38/0.58       ~ ((v1_funct_1 @ sk_D))),
% 0.38/0.58      inference('split', [status(esa)], ['46'])).
% 0.38/0.58  thf('108', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.38/0.58      inference('sat_resolution*', [status(thm)], ['48', '106', '107'])).
% 0.38/0.58  thf('109', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.38/0.58      inference('simpl_trail', [status(thm)], ['103', '108'])).
% 0.38/0.58  thf('110', plain, (~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)),
% 0.38/0.58      inference('clc', [status(thm)], ['102', '109'])).
% 0.38/0.58  thf('111', plain, (~ (zip_tseitin_0 @ sk_C @ sk_A)),
% 0.38/0.58      inference('clc', [status(thm)], ['27', '110'])).
% 0.38/0.58  thf('112', plain, (((sk_B) = (k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['6', '111'])).
% 0.38/0.58  thf('113', plain, (((sk_B) != (k1_xboole_0))),
% 0.38/0.58      inference('simpl_trail', [status(thm)], ['44', '95'])).
% 0.38/0.58  thf('114', plain, ($false),
% 0.38/0.58      inference('simplify_reflect-', [status(thm)], ['112', '113'])).
% 0.38/0.58  
% 0.38/0.58  % SZS output end Refutation
% 0.38/0.58  
% 0.38/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
