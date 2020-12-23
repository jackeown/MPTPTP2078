%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sBYzHj9EOI

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:44 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 567 expanded)
%              Number of leaves         :   37 ( 180 expanded)
%              Depth                    :   29
%              Number of atoms          : 1349 (9480 expanded)
%              Number of equality atoms :   70 ( 531 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(t21_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_relat_1 @ E )
            & ( v1_funct_1 @ E ) )
         => ( ( r2_hidden @ C @ A )
           => ( ( B = k1_xboole_0 )
              | ( ( k1_funct_1 @ ( k5_relat_1 @ D @ E ) @ C )
                = ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ( ( ( v1_relat_1 @ E )
              & ( v1_funct_1 @ E ) )
           => ( ( r2_hidden @ C @ A )
             => ( ( B = k1_xboole_0 )
                | ( ( k1_funct_1 @ ( k5_relat_1 @ D @ E ) @ C )
                  = ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t21_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t22_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) )
      <=> ( ( k1_relset_1 @ B @ A @ C )
          = B ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X23 )
       != X21 )
      | ~ ( r2_hidden @ X24 @ X21 )
      | ( r2_hidden @ ( k4_tarski @ X24 @ ( sk_E @ X24 @ X23 ) ) @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_D_1 ) ) @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 )
       != sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('14',plain,
    ( sk_A
    = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ),
    inference(demod,[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_D_1 ) ) @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_A != sk_A ) ) ),
    inference(demod,[status(thm)],['3','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_D_1 ) ) @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    r2_hidden @ ( k4_tarski @ sk_C @ ( sk_E @ sk_C @ sk_D_1 ) ) @ sk_D_1 ),
    inference('sup-',[status(thm)],['0','16'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X18 @ X20 ) @ X19 )
      | ( r2_hidden @ X18 @ ( k1_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( r2_hidden @ sk_C @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('23',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('24',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r2_hidden @ sk_C @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['19','24','25'])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ ( k1_relat_1 @ X7 ) )
      | ( X8 = k1_xboole_0 )
      | ( X8
       != ( k1_funct_1 @ X7 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('28',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( ( k1_funct_1 @ X7 @ X6 )
        = k1_xboole_0 )
      | ( r2_hidden @ X6 @ ( k1_relat_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf(t21_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
          <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
              & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X12 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X12 @ X13 ) @ ( k1_relat_1 @ X14 ) )
      | ( r2_hidden @ X13 @ ( k1_relat_1 @ ( k5_relat_1 @ X12 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X2 @ X1 ) )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X2 ) )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X2 @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D_1 @ sk_C ) )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_D_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D_1 @ sk_C ) )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_D_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf(t22_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A )
              = ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X15 @ X16 ) @ X17 )
        = ( k1_funct_1 @ X16 @ ( k1_funct_1 @ X15 @ X17 ) ) )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ ( k5_relat_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D_1 @ sk_C ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D_1 @ X0 ) @ sk_C )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D_1 @ sk_C ) ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D_1 @ sk_C ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D_1 @ X0 ) @ sk_C )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D_1 @ X0 ) @ sk_C )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D_1 @ sk_C ) ) )
      | ( ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D_1 @ sk_C ) )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ( k1_funct_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E_1 ) @ sk_C )
 != ( k1_funct_1 @ sk_E_1 @ ( k1_funct_1 @ sk_D_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( k1_funct_1 @ sk_E_1 @ ( k1_funct_1 @ sk_D_1 @ sk_C ) )
     != ( k1_funct_1 @ sk_E_1 @ ( k1_funct_1 @ sk_D_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_E_1 )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ( ( k1_funct_1 @ sk_E_1 @ ( k1_funct_1 @ sk_D_1 @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( k1_funct_1 @ sk_E_1 @ ( k1_funct_1 @ sk_D_1 @ sk_C ) )
     != ( k1_funct_1 @ sk_E_1 @ ( k1_funct_1 @ sk_D_1 @ sk_C ) ) )
    | ( ( k1_funct_1 @ sk_E_1 @ ( k1_funct_1 @ sk_D_1 @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( k1_funct_1 @ sk_E_1 @ ( k1_funct_1 @ sk_D_1 @ sk_C ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['46'])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('48',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(fc2_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('49',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('50',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( ( k1_funct_1 @ X7 @ X6 )
        = k1_xboole_0 )
      | ( r2_hidden @ X6 @ ( k1_relat_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('51',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ ( k5_relat_1 @ X12 @ X14 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X12 @ X13 ) @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ X2 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ X2 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ X2 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ X2 ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ X2 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X7 ) )
      | ( r2_hidden @ ( k4_tarski @ X6 @ X9 ) @ X7 )
      | ( X9
       != ( k1_funct_1 @ X7 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('58',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( r2_hidden @ ( k4_tarski @ X6 @ ( k1_funct_1 @ X7 @ X6 ) ) @ X7 )
      | ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X2 @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ X2 @ X1 ) @ ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X2 @ X1 ) ) ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ X2 @ X1 ) @ ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X2 @ X1 ) ) ) @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X2 @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_C ) @ k1_xboole_0 ) @ sk_E_1 )
    | ~ ( v1_relat_1 @ sk_E_1 )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E_1 ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf('64',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_C ) @ k1_xboole_0 ) @ sk_E_1 )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E_1 ) @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62','63','64','65'])).

thf('67',plain,(
    ( k1_funct_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E_1 ) @ sk_C )
 != ( k1_funct_1 @ sk_E_1 @ ( k1_funct_1 @ sk_D_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( k1_funct_1 @ sk_E_1 @ ( k1_funct_1 @ sk_D_1 @ sk_C ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['46'])).

thf('69',plain,(
    ( k1_funct_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E_1 ) @ sk_C )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_C ) @ k1_xboole_0 ) @ sk_E_1 ),
    inference('simplify_reflect-',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X18 @ X20 ) @ X19 )
      | ( r2_hidden @ X18 @ ( k1_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ sk_E_1 )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C ) @ ( k1_relat_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C ) @ ( k1_relat_1 @ sk_E_1 ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X12 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X12 @ X13 ) @ ( k1_relat_1 @ X14 ) )
      | ( r2_hidden @ X13 @ ( k1_relat_1 @ ( k5_relat_1 @ X12 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('77',plain,
    ( ~ ( v1_relat_1 @ sk_E_1 )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ( r2_hidden @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E_1 ) ) )
    | ~ ( r2_hidden @ sk_C @ ( k1_relat_1 @ sk_D_1 ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    r2_hidden @ sk_C @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['19','24','25'])).

thf('81',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf('83',plain,(
    r2_hidden @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['77','78','79','80','81','82'])).

thf('84',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X15 @ X16 ) @ X17 )
        = ( k1_funct_1 @ X16 @ ( k1_funct_1 @ X15 @ X17 ) ) )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ ( k5_relat_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('85',plain,
    ( ~ ( v1_relat_1 @ sk_E_1 )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E_1 ) @ sk_C )
      = ( k1_funct_1 @ sk_E_1 @ ( k1_funct_1 @ sk_D_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( k1_funct_1 @ sk_E_1 @ ( k1_funct_1 @ sk_D_1 @ sk_C ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['46'])).

thf('89',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf('91',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E_1 ) @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['85','86','87','88','89','90'])).

thf('92',plain,(
    ( k1_funct_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E_1 ) @ sk_C )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['67','68'])).

thf('93',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['91','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sBYzHj9EOI
% 0.14/0.36  % Computer   : n011.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 09:18:57 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.48/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.72  % Solved by: fo/fo7.sh
% 0.48/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.72  % done 135 iterations in 0.242s
% 0.48/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.72  % SZS output start Refutation
% 0.48/0.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.48/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.72  thf(sk_E_type, type, sk_E: $i > $i > $i).
% 0.48/0.72  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.48/0.72  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.48/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.48/0.72  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.48/0.72  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.48/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.48/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.48/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.72  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.48/0.72  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.48/0.72  thf(sk_C_type, type, sk_C: $i).
% 0.48/0.72  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.48/0.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.48/0.72  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.48/0.72  thf(t21_funct_2, conjecture,
% 0.48/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.72     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.48/0.72         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.48/0.72       ( ![E:$i]:
% 0.48/0.72         ( ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) ) =>
% 0.48/0.72           ( ( r2_hidden @ C @ A ) =>
% 0.48/0.72             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.48/0.72               ( ( k1_funct_1 @ ( k5_relat_1 @ D @ E ) @ C ) =
% 0.48/0.72                 ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ C ) ) ) ) ) ) ) ))).
% 0.48/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.72    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.72        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.48/0.72            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.48/0.72          ( ![E:$i]:
% 0.48/0.72            ( ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) ) =>
% 0.48/0.72              ( ( r2_hidden @ C @ A ) =>
% 0.48/0.72                ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.48/0.72                  ( ( k1_funct_1 @ ( k5_relat_1 @ D @ E ) @ C ) =
% 0.48/0.72                    ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ C ) ) ) ) ) ) ) ) )),
% 0.48/0.72    inference('cnf.neg', [status(esa)], [t21_funct_2])).
% 0.48/0.72  thf('0', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('1', plain,
% 0.48/0.72      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf(t22_relset_1, axiom,
% 0.48/0.72    (![A:$i,B:$i,C:$i]:
% 0.48/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.48/0.72       ( ( ![D:$i]:
% 0.48/0.72           ( ~( ( r2_hidden @ D @ B ) & 
% 0.48/0.72                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.48/0.72         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 0.48/0.72  thf('2', plain,
% 0.48/0.72      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.48/0.72         (((k1_relset_1 @ X21 @ X22 @ X23) != (X21))
% 0.48/0.72          | ~ (r2_hidden @ X24 @ X21)
% 0.48/0.72          | (r2_hidden @ (k4_tarski @ X24 @ (sk_E @ X24 @ X23)) @ X23)
% 0.48/0.72          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.48/0.72      inference('cnf', [status(esa)], [t22_relset_1])).
% 0.48/0.72  thf('3', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_D_1)) @ sk_D_1)
% 0.48/0.72          | ~ (r2_hidden @ X0 @ sk_A)
% 0.48/0.72          | ((k1_relset_1 @ sk_A @ sk_B @ sk_D_1) != (sk_A)))),
% 0.48/0.72      inference('sup-', [status(thm)], ['1', '2'])).
% 0.48/0.72  thf('4', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf(d1_funct_2, axiom,
% 0.48/0.72    (![A:$i,B:$i,C:$i]:
% 0.48/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.72       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.48/0.72           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.48/0.72             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.48/0.72         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.48/0.72           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.48/0.72             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.48/0.72  thf(zf_stmt_1, axiom,
% 0.48/0.72    (![C:$i,B:$i,A:$i]:
% 0.48/0.72     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.48/0.72       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.48/0.72  thf('5', plain,
% 0.48/0.72      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.48/0.72         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 0.48/0.72          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 0.48/0.72          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.48/0.72  thf('6', plain,
% 0.48/0.72      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.48/0.72        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_1)))),
% 0.48/0.72      inference('sup-', [status(thm)], ['4', '5'])).
% 0.48/0.72  thf(zf_stmt_2, axiom,
% 0.48/0.72    (![B:$i,A:$i]:
% 0.48/0.72     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.48/0.72       ( zip_tseitin_0 @ B @ A ) ))).
% 0.48/0.72  thf('7', plain,
% 0.48/0.72      (![X26 : $i, X27 : $i]:
% 0.48/0.72         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.48/0.72  thf('8', plain,
% 0.48/0.72      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.48/0.72  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.48/0.72  thf(zf_stmt_5, axiom,
% 0.48/0.72    (![A:$i,B:$i,C:$i]:
% 0.48/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.72       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.48/0.72         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.48/0.72           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.48/0.72             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.48/0.72  thf('9', plain,
% 0.48/0.72      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.48/0.72         (~ (zip_tseitin_0 @ X31 @ X32)
% 0.48/0.72          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 0.48/0.72          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.48/0.72  thf('10', plain,
% 0.48/0.72      (((zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.48/0.72        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.48/0.72      inference('sup-', [status(thm)], ['8', '9'])).
% 0.48/0.72  thf('11', plain,
% 0.48/0.72      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A))),
% 0.48/0.72      inference('sup-', [status(thm)], ['7', '10'])).
% 0.48/0.72  thf('12', plain, (((sk_B) != (k1_xboole_0))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('13', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)),
% 0.48/0.72      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.48/0.72  thf('14', plain, (((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_1))),
% 0.48/0.72      inference('demod', [status(thm)], ['6', '13'])).
% 0.48/0.72  thf('15', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_D_1)) @ sk_D_1)
% 0.48/0.72          | ~ (r2_hidden @ X0 @ sk_A)
% 0.48/0.72          | ((sk_A) != (sk_A)))),
% 0.48/0.72      inference('demod', [status(thm)], ['3', '14'])).
% 0.48/0.72  thf('16', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         (~ (r2_hidden @ X0 @ sk_A)
% 0.48/0.72          | (r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_D_1)) @ sk_D_1))),
% 0.48/0.72      inference('simplify', [status(thm)], ['15'])).
% 0.48/0.72  thf('17', plain,
% 0.48/0.72      ((r2_hidden @ (k4_tarski @ sk_C @ (sk_E @ sk_C @ sk_D_1)) @ sk_D_1)),
% 0.48/0.72      inference('sup-', [status(thm)], ['0', '16'])).
% 0.48/0.72  thf(t8_funct_1, axiom,
% 0.48/0.72    (![A:$i,B:$i,C:$i]:
% 0.48/0.72     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.48/0.72       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.48/0.72         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.48/0.72           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.48/0.72  thf('18', plain,
% 0.48/0.72      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.48/0.72         (~ (r2_hidden @ (k4_tarski @ X18 @ X20) @ X19)
% 0.48/0.72          | (r2_hidden @ X18 @ (k1_relat_1 @ X19))
% 0.48/0.72          | ~ (v1_funct_1 @ X19)
% 0.48/0.72          | ~ (v1_relat_1 @ X19))),
% 0.48/0.72      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.48/0.72  thf('19', plain,
% 0.48/0.72      ((~ (v1_relat_1 @ sk_D_1)
% 0.48/0.72        | ~ (v1_funct_1 @ sk_D_1)
% 0.48/0.72        | (r2_hidden @ sk_C @ (k1_relat_1 @ sk_D_1)))),
% 0.48/0.72      inference('sup-', [status(thm)], ['17', '18'])).
% 0.48/0.72  thf('20', plain,
% 0.48/0.72      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf(cc2_relat_1, axiom,
% 0.48/0.72    (![A:$i]:
% 0.48/0.72     ( ( v1_relat_1 @ A ) =>
% 0.48/0.72       ( ![B:$i]:
% 0.48/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.48/0.72  thf('21', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i]:
% 0.48/0.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.48/0.72          | (v1_relat_1 @ X0)
% 0.48/0.72          | ~ (v1_relat_1 @ X1))),
% 0.48/0.72      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.48/0.72  thf('22', plain,
% 0.48/0.72      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_1))),
% 0.48/0.72      inference('sup-', [status(thm)], ['20', '21'])).
% 0.48/0.72  thf(fc6_relat_1, axiom,
% 0.48/0.72    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.48/0.72  thf('23', plain,
% 0.48/0.72      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.48/0.72      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.48/0.72  thf('24', plain, ((v1_relat_1 @ sk_D_1)),
% 0.48/0.72      inference('demod', [status(thm)], ['22', '23'])).
% 0.48/0.72  thf('25', plain, ((v1_funct_1 @ sk_D_1)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('26', plain, ((r2_hidden @ sk_C @ (k1_relat_1 @ sk_D_1))),
% 0.48/0.72      inference('demod', [status(thm)], ['19', '24', '25'])).
% 0.48/0.72  thf(d4_funct_1, axiom,
% 0.48/0.72    (![A:$i]:
% 0.48/0.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.48/0.72       ( ![B:$i,C:$i]:
% 0.48/0.72         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.48/0.72             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.48/0.72               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.48/0.72           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.48/0.72             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.48/0.72               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.48/0.72  thf('27', plain,
% 0.48/0.72      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.48/0.72         ((r2_hidden @ X6 @ (k1_relat_1 @ X7))
% 0.48/0.72          | ((X8) = (k1_xboole_0))
% 0.48/0.72          | ((X8) != (k1_funct_1 @ X7 @ X6))
% 0.48/0.72          | ~ (v1_funct_1 @ X7)
% 0.48/0.72          | ~ (v1_relat_1 @ X7))),
% 0.48/0.72      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.48/0.72  thf('28', plain,
% 0.48/0.72      (![X6 : $i, X7 : $i]:
% 0.48/0.72         (~ (v1_relat_1 @ X7)
% 0.48/0.72          | ~ (v1_funct_1 @ X7)
% 0.48/0.72          | ((k1_funct_1 @ X7 @ X6) = (k1_xboole_0))
% 0.48/0.72          | (r2_hidden @ X6 @ (k1_relat_1 @ X7)))),
% 0.48/0.72      inference('simplify', [status(thm)], ['27'])).
% 0.48/0.72  thf(t21_funct_1, axiom,
% 0.48/0.72    (![A:$i,B:$i]:
% 0.48/0.72     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.48/0.72       ( ![C:$i]:
% 0.48/0.72         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.48/0.72           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) <=>
% 0.48/0.72             ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.48/0.72               ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.48/0.72  thf('29', plain,
% 0.48/0.72      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.48/0.72         (~ (v1_relat_1 @ X12)
% 0.48/0.72          | ~ (v1_funct_1 @ X12)
% 0.48/0.72          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X12))
% 0.48/0.72          | ~ (r2_hidden @ (k1_funct_1 @ X12 @ X13) @ (k1_relat_1 @ X14))
% 0.48/0.72          | (r2_hidden @ X13 @ (k1_relat_1 @ (k5_relat_1 @ X12 @ X14)))
% 0.48/0.72          | ~ (v1_funct_1 @ X14)
% 0.48/0.72          | ~ (v1_relat_1 @ X14))),
% 0.48/0.72      inference('cnf', [status(esa)], [t21_funct_1])).
% 0.48/0.72  thf('30', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.72         (((k1_funct_1 @ X0 @ (k1_funct_1 @ X2 @ X1)) = (k1_xboole_0))
% 0.48/0.72          | ~ (v1_funct_1 @ X0)
% 0.48/0.72          | ~ (v1_relat_1 @ X0)
% 0.48/0.72          | ~ (v1_relat_1 @ X0)
% 0.48/0.72          | ~ (v1_funct_1 @ X0)
% 0.48/0.72          | (r2_hidden @ X1 @ (k1_relat_1 @ (k5_relat_1 @ X2 @ X0)))
% 0.48/0.72          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X2))
% 0.48/0.72          | ~ (v1_funct_1 @ X2)
% 0.48/0.72          | ~ (v1_relat_1 @ X2))),
% 0.48/0.72      inference('sup-', [status(thm)], ['28', '29'])).
% 0.48/0.72  thf('31', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.72         (~ (v1_relat_1 @ X2)
% 0.48/0.72          | ~ (v1_funct_1 @ X2)
% 0.48/0.72          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X2))
% 0.48/0.72          | (r2_hidden @ X1 @ (k1_relat_1 @ (k5_relat_1 @ X2 @ X0)))
% 0.48/0.72          | ~ (v1_relat_1 @ X0)
% 0.48/0.72          | ~ (v1_funct_1 @ X0)
% 0.48/0.72          | ((k1_funct_1 @ X0 @ (k1_funct_1 @ X2 @ X1)) = (k1_xboole_0)))),
% 0.48/0.72      inference('simplify', [status(thm)], ['30'])).
% 0.48/0.72  thf('32', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         (((k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_1 @ sk_C)) = (k1_xboole_0))
% 0.48/0.72          | ~ (v1_funct_1 @ X0)
% 0.48/0.72          | ~ (v1_relat_1 @ X0)
% 0.48/0.72          | (r2_hidden @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_D_1 @ X0)))
% 0.48/0.72          | ~ (v1_funct_1 @ sk_D_1)
% 0.48/0.72          | ~ (v1_relat_1 @ sk_D_1))),
% 0.48/0.72      inference('sup-', [status(thm)], ['26', '31'])).
% 0.48/0.72  thf('33', plain, ((v1_funct_1 @ sk_D_1)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('34', plain, ((v1_relat_1 @ sk_D_1)),
% 0.48/0.72      inference('demod', [status(thm)], ['22', '23'])).
% 0.48/0.72  thf('35', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         (((k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_1 @ sk_C)) = (k1_xboole_0))
% 0.48/0.72          | ~ (v1_funct_1 @ X0)
% 0.48/0.72          | ~ (v1_relat_1 @ X0)
% 0.48/0.72          | (r2_hidden @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_D_1 @ X0))))),
% 0.48/0.72      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.48/0.72  thf(t22_funct_1, axiom,
% 0.48/0.72    (![A:$i,B:$i]:
% 0.48/0.72     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.48/0.72       ( ![C:$i]:
% 0.48/0.72         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.48/0.72           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.48/0.72             ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A ) =
% 0.48/0.72               ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) ))).
% 0.48/0.72  thf('36', plain,
% 0.48/0.72      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.48/0.72         (~ (v1_relat_1 @ X15)
% 0.48/0.72          | ~ (v1_funct_1 @ X15)
% 0.48/0.72          | ((k1_funct_1 @ (k5_relat_1 @ X15 @ X16) @ X17)
% 0.48/0.72              = (k1_funct_1 @ X16 @ (k1_funct_1 @ X15 @ X17)))
% 0.48/0.72          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ (k5_relat_1 @ X15 @ X16)))
% 0.48/0.72          | ~ (v1_funct_1 @ X16)
% 0.48/0.72          | ~ (v1_relat_1 @ X16))),
% 0.48/0.72      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.48/0.72  thf('37', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         (~ (v1_relat_1 @ X0)
% 0.48/0.72          | ~ (v1_funct_1 @ X0)
% 0.48/0.72          | ((k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_1 @ sk_C)) = (k1_xboole_0))
% 0.48/0.72          | ~ (v1_relat_1 @ X0)
% 0.48/0.72          | ~ (v1_funct_1 @ X0)
% 0.48/0.72          | ((k1_funct_1 @ (k5_relat_1 @ sk_D_1 @ X0) @ sk_C)
% 0.48/0.72              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_1 @ sk_C)))
% 0.48/0.72          | ~ (v1_funct_1 @ sk_D_1)
% 0.48/0.72          | ~ (v1_relat_1 @ sk_D_1))),
% 0.48/0.72      inference('sup-', [status(thm)], ['35', '36'])).
% 0.48/0.72  thf('38', plain, ((v1_funct_1 @ sk_D_1)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('39', plain, ((v1_relat_1 @ sk_D_1)),
% 0.48/0.72      inference('demod', [status(thm)], ['22', '23'])).
% 0.48/0.72  thf('40', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         (~ (v1_relat_1 @ X0)
% 0.48/0.72          | ~ (v1_funct_1 @ X0)
% 0.48/0.72          | ((k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_1 @ sk_C)) = (k1_xboole_0))
% 0.48/0.72          | ~ (v1_relat_1 @ X0)
% 0.48/0.72          | ~ (v1_funct_1 @ X0)
% 0.48/0.72          | ((k1_funct_1 @ (k5_relat_1 @ sk_D_1 @ X0) @ sk_C)
% 0.48/0.72              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_1 @ sk_C))))),
% 0.48/0.72      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.48/0.72  thf('41', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         (((k1_funct_1 @ (k5_relat_1 @ sk_D_1 @ X0) @ sk_C)
% 0.48/0.72            = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_1 @ sk_C)))
% 0.48/0.72          | ((k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_1 @ sk_C)) = (k1_xboole_0))
% 0.48/0.72          | ~ (v1_funct_1 @ X0)
% 0.48/0.72          | ~ (v1_relat_1 @ X0))),
% 0.48/0.72      inference('simplify', [status(thm)], ['40'])).
% 0.48/0.72  thf('42', plain,
% 0.48/0.72      (((k1_funct_1 @ (k5_relat_1 @ sk_D_1 @ sk_E_1) @ sk_C)
% 0.48/0.72         != (k1_funct_1 @ sk_E_1 @ (k1_funct_1 @ sk_D_1 @ sk_C)))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('43', plain,
% 0.48/0.72      ((((k1_funct_1 @ sk_E_1 @ (k1_funct_1 @ sk_D_1 @ sk_C))
% 0.48/0.72          != (k1_funct_1 @ sk_E_1 @ (k1_funct_1 @ sk_D_1 @ sk_C)))
% 0.48/0.72        | ~ (v1_relat_1 @ sk_E_1)
% 0.48/0.72        | ~ (v1_funct_1 @ sk_E_1)
% 0.48/0.72        | ((k1_funct_1 @ sk_E_1 @ (k1_funct_1 @ sk_D_1 @ sk_C)) = (k1_xboole_0)))),
% 0.48/0.72      inference('sup-', [status(thm)], ['41', '42'])).
% 0.48/0.72  thf('44', plain, ((v1_relat_1 @ sk_E_1)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('45', plain, ((v1_funct_1 @ sk_E_1)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('46', plain,
% 0.48/0.72      ((((k1_funct_1 @ sk_E_1 @ (k1_funct_1 @ sk_D_1 @ sk_C))
% 0.48/0.72          != (k1_funct_1 @ sk_E_1 @ (k1_funct_1 @ sk_D_1 @ sk_C)))
% 0.48/0.72        | ((k1_funct_1 @ sk_E_1 @ (k1_funct_1 @ sk_D_1 @ sk_C)) = (k1_xboole_0)))),
% 0.48/0.72      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.48/0.72  thf('47', plain,
% 0.48/0.72      (((k1_funct_1 @ sk_E_1 @ (k1_funct_1 @ sk_D_1 @ sk_C)) = (k1_xboole_0))),
% 0.48/0.72      inference('simplify', [status(thm)], ['46'])).
% 0.48/0.72  thf(dt_k5_relat_1, axiom,
% 0.48/0.72    (![A:$i,B:$i]:
% 0.48/0.72     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.48/0.72       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.48/0.72  thf('48', plain,
% 0.48/0.72      (![X2 : $i, X3 : $i]:
% 0.48/0.72         (~ (v1_relat_1 @ X2)
% 0.48/0.72          | ~ (v1_relat_1 @ X3)
% 0.48/0.72          | (v1_relat_1 @ (k5_relat_1 @ X2 @ X3)))),
% 0.48/0.72      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.48/0.72  thf(fc2_funct_1, axiom,
% 0.48/0.72    (![A:$i,B:$i]:
% 0.48/0.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_relat_1 @ B ) & 
% 0.48/0.72         ( v1_funct_1 @ B ) ) =>
% 0.48/0.72       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 0.48/0.72         ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 0.48/0.72  thf('49', plain,
% 0.48/0.72      (![X10 : $i, X11 : $i]:
% 0.48/0.72         (~ (v1_funct_1 @ X10)
% 0.48/0.72          | ~ (v1_relat_1 @ X10)
% 0.48/0.72          | ~ (v1_relat_1 @ X11)
% 0.48/0.72          | ~ (v1_funct_1 @ X11)
% 0.48/0.72          | (v1_funct_1 @ (k5_relat_1 @ X10 @ X11)))),
% 0.48/0.72      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.48/0.72  thf('50', plain,
% 0.48/0.72      (![X6 : $i, X7 : $i]:
% 0.48/0.72         (~ (v1_relat_1 @ X7)
% 0.48/0.72          | ~ (v1_funct_1 @ X7)
% 0.48/0.72          | ((k1_funct_1 @ X7 @ X6) = (k1_xboole_0))
% 0.48/0.72          | (r2_hidden @ X6 @ (k1_relat_1 @ X7)))),
% 0.48/0.72      inference('simplify', [status(thm)], ['27'])).
% 0.48/0.72  thf('51', plain,
% 0.48/0.72      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.48/0.72         (~ (v1_relat_1 @ X12)
% 0.48/0.72          | ~ (v1_funct_1 @ X12)
% 0.48/0.72          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ (k5_relat_1 @ X12 @ X14)))
% 0.48/0.72          | (r2_hidden @ (k1_funct_1 @ X12 @ X13) @ (k1_relat_1 @ X14))
% 0.48/0.72          | ~ (v1_funct_1 @ X14)
% 0.48/0.72          | ~ (v1_relat_1 @ X14))),
% 0.48/0.72      inference('cnf', [status(esa)], [t21_funct_1])).
% 0.48/0.72  thf('52', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.72         (((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2) = (k1_xboole_0))
% 0.48/0.72          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.48/0.72          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.48/0.72          | ~ (v1_relat_1 @ X0)
% 0.48/0.72          | ~ (v1_funct_1 @ X0)
% 0.48/0.72          | (r2_hidden @ (k1_funct_1 @ X1 @ X2) @ (k1_relat_1 @ X0))
% 0.48/0.72          | ~ (v1_funct_1 @ X1)
% 0.48/0.72          | ~ (v1_relat_1 @ X1))),
% 0.48/0.72      inference('sup-', [status(thm)], ['50', '51'])).
% 0.48/0.72  thf('53', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.72         (~ (v1_funct_1 @ X0)
% 0.48/0.72          | ~ (v1_relat_1 @ X0)
% 0.48/0.72          | ~ (v1_relat_1 @ X1)
% 0.48/0.72          | ~ (v1_funct_1 @ X1)
% 0.48/0.72          | ~ (v1_relat_1 @ X1)
% 0.48/0.72          | ~ (v1_funct_1 @ X1)
% 0.48/0.72          | (r2_hidden @ (k1_funct_1 @ X1 @ X2) @ (k1_relat_1 @ X0))
% 0.48/0.72          | ~ (v1_funct_1 @ X0)
% 0.48/0.72          | ~ (v1_relat_1 @ X0)
% 0.48/0.72          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.48/0.72          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2) = (k1_xboole_0)))),
% 0.48/0.72      inference('sup-', [status(thm)], ['49', '52'])).
% 0.48/0.72  thf('54', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.72         (((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2) = (k1_xboole_0))
% 0.48/0.72          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.48/0.72          | (r2_hidden @ (k1_funct_1 @ X1 @ X2) @ (k1_relat_1 @ X0))
% 0.48/0.72          | ~ (v1_funct_1 @ X1)
% 0.48/0.72          | ~ (v1_relat_1 @ X1)
% 0.48/0.72          | ~ (v1_relat_1 @ X0)
% 0.48/0.72          | ~ (v1_funct_1 @ X0))),
% 0.48/0.72      inference('simplify', [status(thm)], ['53'])).
% 0.48/0.72  thf('55', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.72         (~ (v1_relat_1 @ X0)
% 0.48/0.72          | ~ (v1_relat_1 @ X1)
% 0.48/0.72          | ~ (v1_funct_1 @ X0)
% 0.48/0.72          | ~ (v1_relat_1 @ X0)
% 0.48/0.72          | ~ (v1_relat_1 @ X1)
% 0.48/0.72          | ~ (v1_funct_1 @ X1)
% 0.48/0.72          | (r2_hidden @ (k1_funct_1 @ X1 @ X2) @ (k1_relat_1 @ X0))
% 0.48/0.72          | ((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2) = (k1_xboole_0)))),
% 0.48/0.72      inference('sup-', [status(thm)], ['48', '54'])).
% 0.48/0.72  thf('56', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.72         (((k1_funct_1 @ (k5_relat_1 @ X1 @ X0) @ X2) = (k1_xboole_0))
% 0.48/0.72          | (r2_hidden @ (k1_funct_1 @ X1 @ X2) @ (k1_relat_1 @ X0))
% 0.48/0.72          | ~ (v1_funct_1 @ X1)
% 0.48/0.72          | ~ (v1_funct_1 @ X0)
% 0.48/0.72          | ~ (v1_relat_1 @ X1)
% 0.48/0.72          | ~ (v1_relat_1 @ X0))),
% 0.48/0.72      inference('simplify', [status(thm)], ['55'])).
% 0.48/0.72  thf('57', plain,
% 0.48/0.72      (![X6 : $i, X7 : $i, X9 : $i]:
% 0.48/0.72         (~ (r2_hidden @ X6 @ (k1_relat_1 @ X7))
% 0.48/0.72          | (r2_hidden @ (k4_tarski @ X6 @ X9) @ X7)
% 0.48/0.72          | ((X9) != (k1_funct_1 @ X7 @ X6))
% 0.48/0.72          | ~ (v1_funct_1 @ X7)
% 0.48/0.72          | ~ (v1_relat_1 @ X7))),
% 0.48/0.72      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.48/0.72  thf('58', plain,
% 0.48/0.72      (![X6 : $i, X7 : $i]:
% 0.48/0.72         (~ (v1_relat_1 @ X7)
% 0.48/0.72          | ~ (v1_funct_1 @ X7)
% 0.48/0.72          | (r2_hidden @ (k4_tarski @ X6 @ (k1_funct_1 @ X7 @ X6)) @ X7)
% 0.48/0.72          | ~ (r2_hidden @ X6 @ (k1_relat_1 @ X7)))),
% 0.48/0.72      inference('simplify', [status(thm)], ['57'])).
% 0.48/0.72  thf('59', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.72         (~ (v1_relat_1 @ X0)
% 0.48/0.72          | ~ (v1_relat_1 @ X2)
% 0.48/0.72          | ~ (v1_funct_1 @ X0)
% 0.48/0.72          | ~ (v1_funct_1 @ X2)
% 0.48/0.72          | ((k1_funct_1 @ (k5_relat_1 @ X2 @ X0) @ X1) = (k1_xboole_0))
% 0.48/0.72          | (r2_hidden @ 
% 0.48/0.72             (k4_tarski @ (k1_funct_1 @ X2 @ X1) @ 
% 0.48/0.72              (k1_funct_1 @ X0 @ (k1_funct_1 @ X2 @ X1))) @ 
% 0.48/0.72             X0)
% 0.48/0.72          | ~ (v1_funct_1 @ X0)
% 0.48/0.72          | ~ (v1_relat_1 @ X0))),
% 0.48/0.72      inference('sup-', [status(thm)], ['56', '58'])).
% 0.48/0.72  thf('60', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.72         ((r2_hidden @ 
% 0.48/0.72           (k4_tarski @ (k1_funct_1 @ X2 @ X1) @ 
% 0.48/0.72            (k1_funct_1 @ X0 @ (k1_funct_1 @ X2 @ X1))) @ 
% 0.48/0.72           X0)
% 0.48/0.72          | ((k1_funct_1 @ (k5_relat_1 @ X2 @ X0) @ X1) = (k1_xboole_0))
% 0.48/0.72          | ~ (v1_funct_1 @ X2)
% 0.48/0.72          | ~ (v1_funct_1 @ X0)
% 0.48/0.72          | ~ (v1_relat_1 @ X2)
% 0.48/0.72          | ~ (v1_relat_1 @ X0))),
% 0.48/0.72      inference('simplify', [status(thm)], ['59'])).
% 0.48/0.72  thf('61', plain,
% 0.48/0.72      (((r2_hidden @ 
% 0.48/0.72         (k4_tarski @ (k1_funct_1 @ sk_D_1 @ sk_C) @ k1_xboole_0) @ sk_E_1)
% 0.48/0.72        | ~ (v1_relat_1 @ sk_E_1)
% 0.48/0.72        | ~ (v1_relat_1 @ sk_D_1)
% 0.48/0.72        | ~ (v1_funct_1 @ sk_E_1)
% 0.48/0.72        | ~ (v1_funct_1 @ sk_D_1)
% 0.48/0.72        | ((k1_funct_1 @ (k5_relat_1 @ sk_D_1 @ sk_E_1) @ sk_C) = (k1_xboole_0)))),
% 0.48/0.72      inference('sup+', [status(thm)], ['47', '60'])).
% 0.48/0.72  thf('62', plain, ((v1_relat_1 @ sk_E_1)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('63', plain, ((v1_relat_1 @ sk_D_1)),
% 0.48/0.72      inference('demod', [status(thm)], ['22', '23'])).
% 0.48/0.72  thf('64', plain, ((v1_funct_1 @ sk_E_1)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('65', plain, ((v1_funct_1 @ sk_D_1)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('66', plain,
% 0.48/0.72      (((r2_hidden @ 
% 0.48/0.72         (k4_tarski @ (k1_funct_1 @ sk_D_1 @ sk_C) @ k1_xboole_0) @ sk_E_1)
% 0.48/0.72        | ((k1_funct_1 @ (k5_relat_1 @ sk_D_1 @ sk_E_1) @ sk_C) = (k1_xboole_0)))),
% 0.48/0.72      inference('demod', [status(thm)], ['61', '62', '63', '64', '65'])).
% 0.48/0.72  thf('67', plain,
% 0.48/0.72      (((k1_funct_1 @ (k5_relat_1 @ sk_D_1 @ sk_E_1) @ sk_C)
% 0.48/0.72         != (k1_funct_1 @ sk_E_1 @ (k1_funct_1 @ sk_D_1 @ sk_C)))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('68', plain,
% 0.48/0.72      (((k1_funct_1 @ sk_E_1 @ (k1_funct_1 @ sk_D_1 @ sk_C)) = (k1_xboole_0))),
% 0.48/0.72      inference('simplify', [status(thm)], ['46'])).
% 0.48/0.72  thf('69', plain,
% 0.48/0.72      (((k1_funct_1 @ (k5_relat_1 @ sk_D_1 @ sk_E_1) @ sk_C) != (k1_xboole_0))),
% 0.48/0.72      inference('demod', [status(thm)], ['67', '68'])).
% 0.48/0.72  thf('70', plain,
% 0.48/0.72      ((r2_hidden @ (k4_tarski @ (k1_funct_1 @ sk_D_1 @ sk_C) @ k1_xboole_0) @ 
% 0.48/0.72        sk_E_1)),
% 0.48/0.72      inference('simplify_reflect-', [status(thm)], ['66', '69'])).
% 0.48/0.72  thf('71', plain,
% 0.48/0.72      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.48/0.72         (~ (r2_hidden @ (k4_tarski @ X18 @ X20) @ X19)
% 0.48/0.72          | (r2_hidden @ X18 @ (k1_relat_1 @ X19))
% 0.48/0.72          | ~ (v1_funct_1 @ X19)
% 0.48/0.72          | ~ (v1_relat_1 @ X19))),
% 0.48/0.72      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.48/0.72  thf('72', plain,
% 0.48/0.72      ((~ (v1_relat_1 @ sk_E_1)
% 0.48/0.72        | ~ (v1_funct_1 @ sk_E_1)
% 0.48/0.72        | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C) @ (k1_relat_1 @ sk_E_1)))),
% 0.48/0.72      inference('sup-', [status(thm)], ['70', '71'])).
% 0.48/0.72  thf('73', plain, ((v1_relat_1 @ sk_E_1)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('74', plain, ((v1_funct_1 @ sk_E_1)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('75', plain,
% 0.48/0.72      ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C) @ (k1_relat_1 @ sk_E_1))),
% 0.48/0.72      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.48/0.72  thf('76', plain,
% 0.48/0.72      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.48/0.72         (~ (v1_relat_1 @ X12)
% 0.48/0.72          | ~ (v1_funct_1 @ X12)
% 0.48/0.72          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X12))
% 0.48/0.72          | ~ (r2_hidden @ (k1_funct_1 @ X12 @ X13) @ (k1_relat_1 @ X14))
% 0.48/0.72          | (r2_hidden @ X13 @ (k1_relat_1 @ (k5_relat_1 @ X12 @ X14)))
% 0.48/0.72          | ~ (v1_funct_1 @ X14)
% 0.48/0.72          | ~ (v1_relat_1 @ X14))),
% 0.48/0.72      inference('cnf', [status(esa)], [t21_funct_1])).
% 0.48/0.72  thf('77', plain,
% 0.48/0.72      ((~ (v1_relat_1 @ sk_E_1)
% 0.48/0.72        | ~ (v1_funct_1 @ sk_E_1)
% 0.48/0.72        | (r2_hidden @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_D_1 @ sk_E_1)))
% 0.48/0.72        | ~ (r2_hidden @ sk_C @ (k1_relat_1 @ sk_D_1))
% 0.48/0.72        | ~ (v1_funct_1 @ sk_D_1)
% 0.48/0.72        | ~ (v1_relat_1 @ sk_D_1))),
% 0.48/0.72      inference('sup-', [status(thm)], ['75', '76'])).
% 0.48/0.72  thf('78', plain, ((v1_relat_1 @ sk_E_1)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('79', plain, ((v1_funct_1 @ sk_E_1)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('80', plain, ((r2_hidden @ sk_C @ (k1_relat_1 @ sk_D_1))),
% 0.48/0.72      inference('demod', [status(thm)], ['19', '24', '25'])).
% 0.48/0.72  thf('81', plain, ((v1_funct_1 @ sk_D_1)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('82', plain, ((v1_relat_1 @ sk_D_1)),
% 0.48/0.72      inference('demod', [status(thm)], ['22', '23'])).
% 0.48/0.72  thf('83', plain,
% 0.48/0.72      ((r2_hidden @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_D_1 @ sk_E_1)))),
% 0.48/0.72      inference('demod', [status(thm)], ['77', '78', '79', '80', '81', '82'])).
% 0.48/0.72  thf('84', plain,
% 0.48/0.72      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.48/0.72         (~ (v1_relat_1 @ X15)
% 0.48/0.72          | ~ (v1_funct_1 @ X15)
% 0.48/0.72          | ((k1_funct_1 @ (k5_relat_1 @ X15 @ X16) @ X17)
% 0.48/0.72              = (k1_funct_1 @ X16 @ (k1_funct_1 @ X15 @ X17)))
% 0.48/0.72          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ (k5_relat_1 @ X15 @ X16)))
% 0.48/0.72          | ~ (v1_funct_1 @ X16)
% 0.48/0.72          | ~ (v1_relat_1 @ X16))),
% 0.48/0.72      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.48/0.72  thf('85', plain,
% 0.48/0.72      ((~ (v1_relat_1 @ sk_E_1)
% 0.48/0.72        | ~ (v1_funct_1 @ sk_E_1)
% 0.48/0.72        | ((k1_funct_1 @ (k5_relat_1 @ sk_D_1 @ sk_E_1) @ sk_C)
% 0.48/0.72            = (k1_funct_1 @ sk_E_1 @ (k1_funct_1 @ sk_D_1 @ sk_C)))
% 0.48/0.72        | ~ (v1_funct_1 @ sk_D_1)
% 0.48/0.72        | ~ (v1_relat_1 @ sk_D_1))),
% 0.48/0.72      inference('sup-', [status(thm)], ['83', '84'])).
% 0.48/0.72  thf('86', plain, ((v1_relat_1 @ sk_E_1)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('87', plain, ((v1_funct_1 @ sk_E_1)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('88', plain,
% 0.48/0.72      (((k1_funct_1 @ sk_E_1 @ (k1_funct_1 @ sk_D_1 @ sk_C)) = (k1_xboole_0))),
% 0.48/0.72      inference('simplify', [status(thm)], ['46'])).
% 0.48/0.72  thf('89', plain, ((v1_funct_1 @ sk_D_1)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('90', plain, ((v1_relat_1 @ sk_D_1)),
% 0.48/0.72      inference('demod', [status(thm)], ['22', '23'])).
% 0.48/0.72  thf('91', plain,
% 0.48/0.72      (((k1_funct_1 @ (k5_relat_1 @ sk_D_1 @ sk_E_1) @ sk_C) = (k1_xboole_0))),
% 0.48/0.72      inference('demod', [status(thm)], ['85', '86', '87', '88', '89', '90'])).
% 0.48/0.72  thf('92', plain,
% 0.48/0.72      (((k1_funct_1 @ (k5_relat_1 @ sk_D_1 @ sk_E_1) @ sk_C) != (k1_xboole_0))),
% 0.48/0.72      inference('demod', [status(thm)], ['67', '68'])).
% 0.48/0.72  thf('93', plain, ($false),
% 0.48/0.72      inference('simplify_reflect-', [status(thm)], ['91', '92'])).
% 0.48/0.72  
% 0.48/0.72  % SZS output end Refutation
% 0.48/0.72  
% 0.57/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
