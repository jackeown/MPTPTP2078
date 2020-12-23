%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.q2bD3mvBk1

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:55 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 323 expanded)
%              Number of leaves         :   40 ( 111 expanded)
%              Depth                    :   16
%              Number of atoms          : 1111 (6270 expanded)
%              Number of equality atoms :   38 (  76 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t178_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ~ ( v1_xboole_0 @ D )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ A @ D )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) )
         => ( ( ( r1_tarski @ B @ A )
              & ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) )
           => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) )
              & ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C )
              & ( m1_subset_1 @ ( k2_partfun1 @ A @ D @ E @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ~ ( v1_xboole_0 @ D )
       => ! [E: $i] :
            ( ( ( v1_funct_1 @ E )
              & ( v1_funct_2 @ E @ A @ D )
              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) )
           => ( ( ( r1_tarski @ B @ A )
                & ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) )
             => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) )
                & ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C )
                & ( m1_subset_1 @ ( k2_partfun1 @ A @ D @ E @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t178_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ( ( k2_partfun1 @ X28 @ X29 @ X27 @ X30 )
        = ( k7_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['1','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X24 @ X25 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) )
   <= ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,(
    v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k7_relset_1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( ( k7_relset_1 @ X12 @ X13 @ X11 @ X14 )
        = ( k9_relat_1 @ X11 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k9_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_E @ sk_B ) @ sk_C ),
    inference(demod,[status(thm)],['15','18'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
        = ( k9_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X31 ) @ X32 )
      | ( v1_funct_2 @ X31 @ ( k1_relat_1 @ X31 ) @ X32 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) @ sk_C )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_E @ sk_A @ sk_D ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ( X17
        = ( k1_relset_1 @ X17 @ X18 @ X19 ) )
      | ~ ( zip_tseitin_1 @ X19 @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('27',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('28',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('29',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
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

thf('32',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X20 @ X21 )
      | ( zip_tseitin_1 @ X22 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('33',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    zip_tseitin_1 @ sk_E @ sk_D @ sk_A ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('38',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('39',plain,
    ( ( k1_relset_1 @ sk_A @ sk_D @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['27','36','39'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('41',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X6 @ ( k1_relat_1 @ X7 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X7 @ X6 ) )
        = X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('46',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('47',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['42','47'])).

thf('49',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['24','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['45','46'])).

thf('51',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('54',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X24 @ X25 @ X23 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) )
      | ( v1_relat_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('66',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['55','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('69',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('70',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
    | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('73',plain,(
    ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference('sat_resolution*',[status(thm)],['14','71','72'])).

thf('74',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(simpl_trail,[status(thm)],['7','73'])).

thf('75',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_E @ sk_B ) @ sk_C ),
    inference(demod,[status(thm)],['15','18'])).

thf('76',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
        = ( k9_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('77',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X31 ) @ X32 )
      | ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X31 ) @ X32 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['24','48'])).

thf('81',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['45','46'])).

thf('82',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('84',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('86',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    $false ),
    inference(demod,[status(thm)],['74','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.q2bD3mvBk1
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:33:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.43/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.43/0.63  % Solved by: fo/fo7.sh
% 0.43/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.63  % done 137 iterations in 0.167s
% 0.43/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.43/0.63  % SZS output start Refutation
% 0.43/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.63  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.43/0.63  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.43/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.43/0.63  thf(sk_E_type, type, sk_E: $i).
% 0.43/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.43/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.43/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.43/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.63  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.43/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.43/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.43/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.43/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.43/0.63  thf(sk_D_type, type, sk_D: $i).
% 0.43/0.63  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.43/0.63  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.43/0.63  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.43/0.63  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.43/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.43/0.63  thf(t178_funct_2, conjecture,
% 0.43/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.63     ( ( ~( v1_xboole_0 @ D ) ) =>
% 0.43/0.63       ( ![E:$i]:
% 0.43/0.63         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ D ) & 
% 0.43/0.63             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) =>
% 0.43/0.63           ( ( ( r1_tarski @ B @ A ) & 
% 0.43/0.63               ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) ) =>
% 0.43/0.63             ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) ) & 
% 0.43/0.63               ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C ) & 
% 0.43/0.63               ( m1_subset_1 @
% 0.43/0.63                 ( k2_partfun1 @ A @ D @ E @ B ) @ 
% 0.43/0.63                 ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.43/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.63    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.63        ( ( ~( v1_xboole_0 @ D ) ) =>
% 0.43/0.63          ( ![E:$i]:
% 0.43/0.63            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ D ) & 
% 0.43/0.63                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) =>
% 0.43/0.63              ( ( ( r1_tarski @ B @ A ) & 
% 0.43/0.63                  ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) ) =>
% 0.43/0.63                ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) ) & 
% 0.43/0.63                  ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C ) & 
% 0.43/0.63                  ( m1_subset_1 @
% 0.43/0.63                    ( k2_partfun1 @ A @ D @ E @ B ) @ 
% 0.43/0.63                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ) )),
% 0.43/0.63    inference('cnf.neg', [status(esa)], [t178_funct_2])).
% 0.43/0.63  thf('0', plain,
% 0.43/0.63      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B))
% 0.43/0.63        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ 
% 0.43/0.63             sk_C)
% 0.43/0.63        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 0.43/0.63             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('1', plain,
% 0.43/0.63      ((~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 0.43/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))
% 0.43/0.63         <= (~
% 0.43/0.63             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 0.43/0.63               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))))),
% 0.43/0.63      inference('split', [status(esa)], ['0'])).
% 0.43/0.63  thf('2', plain,
% 0.43/0.63      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf(redefinition_k2_partfun1, axiom,
% 0.43/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.63     ( ( ( v1_funct_1 @ C ) & 
% 0.43/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.43/0.63       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.43/0.63  thf('3', plain,
% 0.43/0.63      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.43/0.63         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.43/0.63          | ~ (v1_funct_1 @ X27)
% 0.43/0.63          | ((k2_partfun1 @ X28 @ X29 @ X27 @ X30) = (k7_relat_1 @ X27 @ X30)))),
% 0.43/0.63      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.43/0.63  thf('4', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 0.43/0.63          | ~ (v1_funct_1 @ sk_E))),
% 0.43/0.63      inference('sup-', [status(thm)], ['2', '3'])).
% 0.43/0.63  thf('5', plain, ((v1_funct_1 @ sk_E)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('6', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.43/0.63      inference('demod', [status(thm)], ['4', '5'])).
% 0.43/0.63  thf('7', plain,
% 0.43/0.63      ((~ (m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.43/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))
% 0.43/0.63         <= (~
% 0.43/0.63             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 0.43/0.63               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))))),
% 0.43/0.63      inference('demod', [status(thm)], ['1', '6'])).
% 0.43/0.63  thf('8', plain,
% 0.43/0.63      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf(dt_k2_partfun1, axiom,
% 0.43/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.63     ( ( ( v1_funct_1 @ C ) & 
% 0.43/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.43/0.63       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 0.43/0.63         ( m1_subset_1 @
% 0.43/0.63           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 0.43/0.63           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.43/0.63  thf('9', plain,
% 0.43/0.63      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.43/0.63         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.43/0.63          | ~ (v1_funct_1 @ X23)
% 0.43/0.63          | (v1_funct_1 @ (k2_partfun1 @ X24 @ X25 @ X23 @ X26)))),
% 0.43/0.63      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 0.43/0.63  thf('10', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))
% 0.43/0.63          | ~ (v1_funct_1 @ sk_E))),
% 0.43/0.63      inference('sup-', [status(thm)], ['8', '9'])).
% 0.43/0.63  thf('11', plain, ((v1_funct_1 @ sk_E)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('12', plain,
% 0.43/0.63      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))),
% 0.43/0.63      inference('demod', [status(thm)], ['10', '11'])).
% 0.43/0.63  thf('13', plain,
% 0.43/0.63      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B)))
% 0.43/0.63         <= (~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B))))),
% 0.43/0.63      inference('split', [status(esa)], ['0'])).
% 0.43/0.63  thf('14', plain,
% 0.43/0.63      (((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['12', '13'])).
% 0.43/0.63  thf('15', plain,
% 0.43/0.63      ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_C)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('16', plain,
% 0.43/0.63      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf(redefinition_k7_relset_1, axiom,
% 0.43/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.63       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.43/0.63  thf('17', plain,
% 0.43/0.63      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.43/0.63         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.43/0.63          | ((k7_relset_1 @ X12 @ X13 @ X11 @ X14) = (k9_relat_1 @ X11 @ X14)))),
% 0.43/0.63      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.43/0.63  thf('18', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         ((k7_relset_1 @ sk_A @ sk_D @ sk_E @ X0) = (k9_relat_1 @ sk_E @ X0))),
% 0.43/0.63      inference('sup-', [status(thm)], ['16', '17'])).
% 0.43/0.63  thf('19', plain, ((r1_tarski @ (k9_relat_1 @ sk_E @ sk_B) @ sk_C)),
% 0.43/0.63      inference('demod', [status(thm)], ['15', '18'])).
% 0.43/0.63  thf(t148_relat_1, axiom,
% 0.43/0.63    (![A:$i,B:$i]:
% 0.43/0.63     ( ( v1_relat_1 @ B ) =>
% 0.43/0.63       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.43/0.63  thf('20', plain,
% 0.43/0.63      (![X4 : $i, X5 : $i]:
% 0.43/0.63         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.43/0.63          | ~ (v1_relat_1 @ X4))),
% 0.43/0.63      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.43/0.63  thf(t4_funct_2, axiom,
% 0.43/0.63    (![A:$i,B:$i]:
% 0.43/0.63     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.43/0.63       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.43/0.63         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.43/0.63           ( m1_subset_1 @
% 0.43/0.63             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.43/0.63  thf('21', plain,
% 0.43/0.63      (![X31 : $i, X32 : $i]:
% 0.43/0.63         (~ (r1_tarski @ (k2_relat_1 @ X31) @ X32)
% 0.43/0.63          | (v1_funct_2 @ X31 @ (k1_relat_1 @ X31) @ X32)
% 0.43/0.63          | ~ (v1_funct_1 @ X31)
% 0.43/0.63          | ~ (v1_relat_1 @ X31))),
% 0.43/0.63      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.43/0.63  thf('22', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.63         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.43/0.63          | ~ (v1_relat_1 @ X1)
% 0.43/0.63          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.43/0.63          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 0.43/0.63          | (v1_funct_2 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.43/0.63             (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))),
% 0.43/0.63      inference('sup-', [status(thm)], ['20', '21'])).
% 0.43/0.63  thf('23', plain,
% 0.43/0.63      (((v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.43/0.63         (k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) @ sk_C)
% 0.43/0.63        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_E @ sk_B))
% 0.43/0.63        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B))
% 0.43/0.63        | ~ (v1_relat_1 @ sk_E))),
% 0.43/0.63      inference('sup-', [status(thm)], ['19', '22'])).
% 0.43/0.63  thf('24', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('25', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_D)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf(d1_funct_2, axiom,
% 0.43/0.63    (![A:$i,B:$i,C:$i]:
% 0.43/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.63       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.43/0.63           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.43/0.63             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.43/0.63         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.43/0.63           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.43/0.63             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.43/0.63  thf(zf_stmt_1, axiom,
% 0.43/0.63    (![C:$i,B:$i,A:$i]:
% 0.43/0.63     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.43/0.63       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.43/0.63  thf('26', plain,
% 0.43/0.63      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.43/0.63         (~ (v1_funct_2 @ X19 @ X17 @ X18)
% 0.43/0.63          | ((X17) = (k1_relset_1 @ X17 @ X18 @ X19))
% 0.43/0.63          | ~ (zip_tseitin_1 @ X19 @ X18 @ X17))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.43/0.63  thf('27', plain,
% 0.43/0.63      ((~ (zip_tseitin_1 @ sk_E @ sk_D @ sk_A)
% 0.43/0.63        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_D @ sk_E)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['25', '26'])).
% 0.43/0.63  thf(zf_stmt_2, axiom,
% 0.43/0.63    (![B:$i,A:$i]:
% 0.43/0.63     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.43/0.63       ( zip_tseitin_0 @ B @ A ) ))).
% 0.43/0.63  thf('28', plain,
% 0.43/0.63      (![X15 : $i, X16 : $i]:
% 0.43/0.63         ((zip_tseitin_0 @ X15 @ X16) | ((X15) = (k1_xboole_0)))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.43/0.63  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.43/0.63  thf('29', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.43/0.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.43/0.63  thf('30', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.43/0.63      inference('sup+', [status(thm)], ['28', '29'])).
% 0.43/0.63  thf('31', plain,
% 0.43/0.63      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.43/0.63  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.43/0.63  thf(zf_stmt_5, axiom,
% 0.43/0.63    (![A:$i,B:$i,C:$i]:
% 0.43/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.63       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.43/0.63         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.43/0.63           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.43/0.63             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.43/0.63  thf('32', plain,
% 0.43/0.63      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.43/0.63         (~ (zip_tseitin_0 @ X20 @ X21)
% 0.43/0.63          | (zip_tseitin_1 @ X22 @ X20 @ X21)
% 0.43/0.63          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20))))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.43/0.63  thf('33', plain,
% 0.43/0.63      (((zip_tseitin_1 @ sk_E @ sk_D @ sk_A) | ~ (zip_tseitin_0 @ sk_D @ sk_A))),
% 0.43/0.63      inference('sup-', [status(thm)], ['31', '32'])).
% 0.43/0.63  thf('34', plain,
% 0.43/0.63      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_E @ sk_D @ sk_A))),
% 0.43/0.63      inference('sup-', [status(thm)], ['30', '33'])).
% 0.43/0.63  thf('35', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('36', plain, ((zip_tseitin_1 @ sk_E @ sk_D @ sk_A)),
% 0.43/0.63      inference('clc', [status(thm)], ['34', '35'])).
% 0.43/0.63  thf('37', plain,
% 0.43/0.63      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf(redefinition_k1_relset_1, axiom,
% 0.43/0.63    (![A:$i,B:$i,C:$i]:
% 0.43/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.63       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.43/0.63  thf('38', plain,
% 0.43/0.63      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.43/0.63         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.43/0.63          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.43/0.63      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.43/0.63  thf('39', plain,
% 0.43/0.63      (((k1_relset_1 @ sk_A @ sk_D @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.43/0.63      inference('sup-', [status(thm)], ['37', '38'])).
% 0.43/0.63  thf('40', plain, (((sk_A) = (k1_relat_1 @ sk_E))),
% 0.43/0.63      inference('demod', [status(thm)], ['27', '36', '39'])).
% 0.43/0.63  thf(t91_relat_1, axiom,
% 0.43/0.63    (![A:$i,B:$i]:
% 0.43/0.63     ( ( v1_relat_1 @ B ) =>
% 0.43/0.63       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.43/0.63         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.43/0.63  thf('41', plain,
% 0.43/0.63      (![X6 : $i, X7 : $i]:
% 0.43/0.63         (~ (r1_tarski @ X6 @ (k1_relat_1 @ X7))
% 0.43/0.63          | ((k1_relat_1 @ (k7_relat_1 @ X7 @ X6)) = (X6))
% 0.43/0.63          | ~ (v1_relat_1 @ X7))),
% 0.43/0.63      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.43/0.63  thf('42', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (r1_tarski @ X0 @ sk_A)
% 0.43/0.63          | ~ (v1_relat_1 @ sk_E)
% 0.43/0.63          | ((k1_relat_1 @ (k7_relat_1 @ sk_E @ X0)) = (X0)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['40', '41'])).
% 0.43/0.63  thf('43', plain,
% 0.43/0.63      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf(cc2_relat_1, axiom,
% 0.43/0.63    (![A:$i]:
% 0.43/0.63     ( ( v1_relat_1 @ A ) =>
% 0.43/0.63       ( ![B:$i]:
% 0.43/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.43/0.63  thf('44', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i]:
% 0.43/0.63         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.43/0.63          | (v1_relat_1 @ X0)
% 0.43/0.63          | ~ (v1_relat_1 @ X1))),
% 0.43/0.63      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.43/0.63  thf('45', plain,
% 0.43/0.63      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)) | (v1_relat_1 @ sk_E))),
% 0.43/0.63      inference('sup-', [status(thm)], ['43', '44'])).
% 0.43/0.63  thf(fc6_relat_1, axiom,
% 0.43/0.63    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.43/0.63  thf('46', plain,
% 0.43/0.63      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.43/0.63      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.43/0.63  thf('47', plain, ((v1_relat_1 @ sk_E)),
% 0.43/0.63      inference('demod', [status(thm)], ['45', '46'])).
% 0.43/0.63  thf('48', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (r1_tarski @ X0 @ sk_A)
% 0.43/0.63          | ((k1_relat_1 @ (k7_relat_1 @ sk_E @ X0)) = (X0)))),
% 0.43/0.63      inference('demod', [status(thm)], ['42', '47'])).
% 0.43/0.63  thf('49', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 0.43/0.63      inference('sup-', [status(thm)], ['24', '48'])).
% 0.43/0.63  thf('50', plain, ((v1_relat_1 @ sk_E)),
% 0.43/0.63      inference('demod', [status(thm)], ['45', '46'])).
% 0.43/0.63  thf('51', plain,
% 0.43/0.63      (((v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)
% 0.43/0.63        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_E @ sk_B))
% 0.43/0.63        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 0.43/0.63      inference('demod', [status(thm)], ['23', '49', '50'])).
% 0.43/0.63  thf('52', plain,
% 0.43/0.63      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))),
% 0.43/0.63      inference('demod', [status(thm)], ['10', '11'])).
% 0.43/0.63  thf('53', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.43/0.63      inference('demod', [status(thm)], ['4', '5'])).
% 0.43/0.63  thf('54', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_E @ X0))),
% 0.43/0.63      inference('demod', [status(thm)], ['52', '53'])).
% 0.43/0.63  thf('55', plain,
% 0.43/0.63      (((v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)
% 0.43/0.63        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 0.43/0.63      inference('demod', [status(thm)], ['51', '54'])).
% 0.43/0.63  thf('56', plain,
% 0.43/0.63      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('57', plain,
% 0.43/0.63      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.43/0.63         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.43/0.63          | ~ (v1_funct_1 @ X23)
% 0.43/0.63          | (m1_subset_1 @ (k2_partfun1 @ X24 @ X25 @ X23 @ X26) @ 
% 0.43/0.63             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.43/0.63      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 0.43/0.63  thf('58', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) @ 
% 0.43/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))
% 0.43/0.63          | ~ (v1_funct_1 @ sk_E))),
% 0.43/0.63      inference('sup-', [status(thm)], ['56', '57'])).
% 0.43/0.63  thf('59', plain, ((v1_funct_1 @ sk_E)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('60', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) @ 
% 0.43/0.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.43/0.63      inference('demod', [status(thm)], ['58', '59'])).
% 0.43/0.63  thf('61', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i]:
% 0.43/0.63         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.43/0.63          | (v1_relat_1 @ X0)
% 0.43/0.63          | ~ (v1_relat_1 @ X1))),
% 0.43/0.63      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.43/0.63  thf('62', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_D))
% 0.43/0.63          | (v1_relat_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['60', '61'])).
% 0.43/0.63  thf('63', plain,
% 0.43/0.63      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.43/0.63      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.43/0.63  thf('64', plain,
% 0.43/0.63      (![X0 : $i]: (v1_relat_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))),
% 0.43/0.63      inference('demod', [status(thm)], ['62', '63'])).
% 0.43/0.63  thf('65', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.43/0.63      inference('demod', [status(thm)], ['4', '5'])).
% 0.43/0.63  thf('66', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))),
% 0.43/0.63      inference('demod', [status(thm)], ['64', '65'])).
% 0.43/0.63  thf('67', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)),
% 0.43/0.63      inference('demod', [status(thm)], ['55', '66'])).
% 0.43/0.63  thf('68', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.43/0.63      inference('demod', [status(thm)], ['4', '5'])).
% 0.43/0.63  thf('69', plain,
% 0.43/0.63      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ sk_C))
% 0.43/0.63         <= (~
% 0.43/0.63             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ 
% 0.43/0.63               sk_C)))),
% 0.43/0.63      inference('split', [status(esa)], ['0'])).
% 0.43/0.63  thf('70', plain,
% 0.43/0.63      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C))
% 0.43/0.63         <= (~
% 0.43/0.63             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ 
% 0.43/0.63               sk_C)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['68', '69'])).
% 0.43/0.63  thf('71', plain,
% 0.43/0.63      (((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ sk_C))),
% 0.43/0.63      inference('sup-', [status(thm)], ['67', '70'])).
% 0.43/0.63  thf('72', plain,
% 0.43/0.63      (~
% 0.43/0.63       ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 0.43/0.63         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))) | 
% 0.43/0.63       ~
% 0.43/0.63       ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ sk_C)) | 
% 0.43/0.63       ~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B)))),
% 0.43/0.63      inference('split', [status(esa)], ['0'])).
% 0.43/0.63  thf('73', plain,
% 0.43/0.63      (~
% 0.43/0.63       ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 0.43/0.63         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.43/0.63      inference('sat_resolution*', [status(thm)], ['14', '71', '72'])).
% 0.43/0.63  thf('74', plain,
% 0.43/0.63      (~ (m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.43/0.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.43/0.63      inference('simpl_trail', [status(thm)], ['7', '73'])).
% 0.43/0.63  thf('75', plain, ((r1_tarski @ (k9_relat_1 @ sk_E @ sk_B) @ sk_C)),
% 0.43/0.63      inference('demod', [status(thm)], ['15', '18'])).
% 0.43/0.63  thf('76', plain,
% 0.43/0.63      (![X4 : $i, X5 : $i]:
% 0.43/0.63         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.43/0.63          | ~ (v1_relat_1 @ X4))),
% 0.43/0.63      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.43/0.63  thf('77', plain,
% 0.43/0.63      (![X31 : $i, X32 : $i]:
% 0.43/0.63         (~ (r1_tarski @ (k2_relat_1 @ X31) @ X32)
% 0.43/0.63          | (m1_subset_1 @ X31 @ 
% 0.43/0.63             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X31) @ X32)))
% 0.43/0.63          | ~ (v1_funct_1 @ X31)
% 0.43/0.63          | ~ (v1_relat_1 @ X31))),
% 0.43/0.63      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.43/0.63  thf('78', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.63         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.43/0.63          | ~ (v1_relat_1 @ X1)
% 0.43/0.63          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.43/0.63          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 0.43/0.63          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.43/0.63             (k1_zfmisc_1 @ 
% 0.43/0.63              (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))))),
% 0.43/0.63      inference('sup-', [status(thm)], ['76', '77'])).
% 0.43/0.63  thf('79', plain,
% 0.43/0.63      (((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.43/0.63         (k1_zfmisc_1 @ 
% 0.43/0.63          (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) @ sk_C)))
% 0.43/0.63        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_E @ sk_B))
% 0.43/0.63        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B))
% 0.43/0.63        | ~ (v1_relat_1 @ sk_E))),
% 0.43/0.63      inference('sup-', [status(thm)], ['75', '78'])).
% 0.43/0.63  thf('80', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 0.43/0.63      inference('sup-', [status(thm)], ['24', '48'])).
% 0.43/0.63  thf('81', plain, ((v1_relat_1 @ sk_E)),
% 0.43/0.63      inference('demod', [status(thm)], ['45', '46'])).
% 0.43/0.63  thf('82', plain,
% 0.43/0.63      (((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.43/0.63         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))
% 0.43/0.63        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_E @ sk_B))
% 0.43/0.63        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 0.43/0.63      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.43/0.63  thf('83', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_E @ X0))),
% 0.43/0.63      inference('demod', [status(thm)], ['52', '53'])).
% 0.43/0.63  thf('84', plain,
% 0.43/0.63      (((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.43/0.63         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))
% 0.43/0.63        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 0.43/0.63      inference('demod', [status(thm)], ['82', '83'])).
% 0.43/0.63  thf('85', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))),
% 0.43/0.63      inference('demod', [status(thm)], ['64', '65'])).
% 0.43/0.63  thf('86', plain,
% 0.43/0.63      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.43/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.43/0.63      inference('demod', [status(thm)], ['84', '85'])).
% 0.43/0.63  thf('87', plain, ($false), inference('demod', [status(thm)], ['74', '86'])).
% 0.43/0.63  
% 0.43/0.63  % SZS output end Refutation
% 0.43/0.63  
% 0.50/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
