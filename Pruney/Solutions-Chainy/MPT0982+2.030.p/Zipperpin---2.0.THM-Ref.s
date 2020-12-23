%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fqYUxfGhvY

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:59 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 350 expanded)
%              Number of leaves         :   42 ( 120 expanded)
%              Depth                    :   15
%              Number of atoms          : 1049 (7479 expanded)
%              Number of equality atoms :   59 ( 430 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t28_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                = C )
              & ( v2_funct_1 @ E ) )
           => ( ( C = k1_xboole_0 )
              | ( ( k2_relset_1 @ A @ B @ D )
                = B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ( ( ( v1_funct_1 @ E )
              & ( v1_funct_2 @ E @ B @ C )
              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                  = C )
                & ( v2_funct_1 @ E ) )
             => ( ( C = k1_xboole_0 )
                | ( ( k2_relset_1 @ A @ B @ D )
                  = B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('9',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['4','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) )
    | ( sk_B
      = ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('15',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('23',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 )
        = ( k5_relat_1 @ X36 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','20','29'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('31',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('32',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('35',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['32','35'])).

thf(t51_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
                = ( k2_relat_1 @ A ) )
              & ( v2_funct_1 @ A ) )
           => ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('37',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( r1_tarski @ ( k1_relat_1 @ X12 ) @ ( k2_relat_1 @ X11 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X11 @ X12 ) )
       != ( k2_relat_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t51_funct_1])).

thf('38',plain,
    ( ( sk_C
     != ( k2_relat_1 @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E )
    | ( r1_tarski @ ( k1_relat_1 @ sk_E ) @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('43',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_2 @ sk_E @ sk_B @ sk_C ),
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

thf('47',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('48',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('49',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('50',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('52',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    zip_tseitin_1 @ sk_E @ sk_C @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('57',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('58',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['48','55','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['7','8'])).

thf('62',plain,
    ( ( sk_C
     != ( k2_relat_1 @ sk_E ) )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['38','43','44','45','59','60','61'])).

thf('63',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['32','35'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('64',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) ) @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('65',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C )
    | ( ( k2_relat_1 @ sk_E )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('70',plain,(
    v5_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['41','42'])).

thf('74',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['32','35'])).

thf('76',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['41','42'])).

thf('77',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['7','8'])).

thf('78',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['67','74','75','76','77'])).

thf('79',plain,
    ( ( sk_C != sk_C )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['62','78'])).

thf('80',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['12','80'])).

thf('82',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('85',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ( k2_relat_1 @ sk_D )
 != sk_B ),
    inference(demod,[status(thm)],['82','85'])).

thf('87',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['81','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fqYUxfGhvY
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:44:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.91/1.14  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.91/1.14  % Solved by: fo/fo7.sh
% 0.91/1.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.14  % done 674 iterations in 0.689s
% 0.91/1.14  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.91/1.14  % SZS output start Refutation
% 0.91/1.14  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.14  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.91/1.14  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.91/1.14  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.91/1.14  thf(sk_E_type, type, sk_E: $i).
% 0.91/1.14  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.91/1.14  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.14  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.91/1.14  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.14  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.91/1.14  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.91/1.14  thf(sk_C_type, type, sk_C: $i).
% 0.91/1.14  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.14  thf(sk_D_type, type, sk_D: $i).
% 0.91/1.14  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.91/1.14  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.91/1.14  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.91/1.14  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.91/1.14  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.91/1.14  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.91/1.14  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.91/1.14  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.91/1.14  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.91/1.14  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.91/1.14  thf(t28_funct_2, conjecture,
% 0.91/1.14    (![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.14     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.91/1.14         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.14       ( ![E:$i]:
% 0.91/1.14         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.91/1.14             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.91/1.14           ( ( ( ( k2_relset_1 @
% 0.91/1.14                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 0.91/1.14                 ( C ) ) & 
% 0.91/1.14               ( v2_funct_1 @ E ) ) =>
% 0.91/1.14             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.91/1.14               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ))).
% 0.91/1.14  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.14    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.14        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.91/1.14            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.14          ( ![E:$i]:
% 0.91/1.14            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.91/1.14                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.91/1.14              ( ( ( ( k2_relset_1 @
% 0.91/1.14                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 0.91/1.14                    ( C ) ) & 
% 0.91/1.14                  ( v2_funct_1 @ E ) ) =>
% 0.91/1.14                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.91/1.14                  ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ) )),
% 0.91/1.14    inference('cnf.neg', [status(esa)], [t28_funct_2])).
% 0.91/1.14  thf('0', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf(cc2_relset_1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i]:
% 0.91/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.14       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.91/1.14  thf('1', plain,
% 0.91/1.14      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.91/1.14         ((v5_relat_1 @ X13 @ X15)
% 0.91/1.14          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.91/1.14      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.91/1.14  thf('2', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 0.91/1.14      inference('sup-', [status(thm)], ['0', '1'])).
% 0.91/1.14  thf(d19_relat_1, axiom,
% 0.91/1.14    (![A:$i,B:$i]:
% 0.91/1.14     ( ( v1_relat_1 @ B ) =>
% 0.91/1.14       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.91/1.14  thf('3', plain,
% 0.91/1.14      (![X5 : $i, X6 : $i]:
% 0.91/1.14         (~ (v5_relat_1 @ X5 @ X6)
% 0.91/1.14          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.91/1.14          | ~ (v1_relat_1 @ X5))),
% 0.91/1.14      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.91/1.14  thf('4', plain,
% 0.91/1.14      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 0.91/1.14      inference('sup-', [status(thm)], ['2', '3'])).
% 0.91/1.14  thf('5', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf(cc2_relat_1, axiom,
% 0.91/1.14    (![A:$i]:
% 0.91/1.14     ( ( v1_relat_1 @ A ) =>
% 0.91/1.14       ( ![B:$i]:
% 0.91/1.14         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.91/1.14  thf('6', plain,
% 0.91/1.14      (![X3 : $i, X4 : $i]:
% 0.91/1.14         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.91/1.14          | (v1_relat_1 @ X3)
% 0.91/1.14          | ~ (v1_relat_1 @ X4))),
% 0.91/1.14      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.91/1.14  thf('7', plain,
% 0.91/1.14      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.91/1.14      inference('sup-', [status(thm)], ['5', '6'])).
% 0.91/1.14  thf(fc6_relat_1, axiom,
% 0.91/1.14    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.91/1.14  thf('8', plain,
% 0.91/1.14      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.91/1.14      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.91/1.14  thf('9', plain, ((v1_relat_1 @ sk_D)),
% 0.91/1.14      inference('demod', [status(thm)], ['7', '8'])).
% 0.91/1.14  thf('10', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 0.91/1.14      inference('demod', [status(thm)], ['4', '9'])).
% 0.91/1.14  thf(d10_xboole_0, axiom,
% 0.91/1.14    (![A:$i,B:$i]:
% 0.91/1.14     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.91/1.14  thf('11', plain,
% 0.91/1.14      (![X0 : $i, X2 : $i]:
% 0.91/1.14         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.91/1.14      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.91/1.14  thf('12', plain,
% 0.91/1.14      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D))
% 0.91/1.14        | ((sk_B) = (k2_relat_1 @ sk_D)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['10', '11'])).
% 0.91/1.14  thf('13', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('14', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf(dt_k1_partfun1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.91/1.14     ( ( ( v1_funct_1 @ E ) & 
% 0.91/1.14         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.91/1.14         ( v1_funct_1 @ F ) & 
% 0.91/1.14         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.91/1.14       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.91/1.14         ( m1_subset_1 @
% 0.91/1.14           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.91/1.14           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.91/1.14  thf('15', plain,
% 0.91/1.14      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.91/1.14         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.91/1.14          | ~ (v1_funct_1 @ X30)
% 0.91/1.14          | ~ (v1_funct_1 @ X33)
% 0.91/1.14          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.91/1.14          | (m1_subset_1 @ (k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33) @ 
% 0.91/1.14             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X35))))),
% 0.91/1.14      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.91/1.14  thf('16', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 0.91/1.14           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.91/1.14          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.91/1.14          | ~ (v1_funct_1 @ X1)
% 0.91/1.14          | ~ (v1_funct_1 @ sk_D))),
% 0.91/1.14      inference('sup-', [status(thm)], ['14', '15'])).
% 0.91/1.14  thf('17', plain, ((v1_funct_1 @ sk_D)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('18', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 0.91/1.14           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.91/1.14          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.91/1.14          | ~ (v1_funct_1 @ X1))),
% 0.91/1.14      inference('demod', [status(thm)], ['16', '17'])).
% 0.91/1.14  thf('19', plain,
% 0.91/1.14      ((~ (v1_funct_1 @ sk_E)
% 0.91/1.14        | (m1_subset_1 @ 
% 0.91/1.14           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.91/1.14           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.91/1.14      inference('sup-', [status(thm)], ['13', '18'])).
% 0.91/1.14  thf('20', plain, ((v1_funct_1 @ sk_E)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('21', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('22', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf(redefinition_k1_partfun1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.91/1.14     ( ( ( v1_funct_1 @ E ) & 
% 0.91/1.14         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.91/1.14         ( v1_funct_1 @ F ) & 
% 0.91/1.14         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.91/1.14       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.91/1.14  thf('23', plain,
% 0.91/1.14      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.91/1.14         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.91/1.14          | ~ (v1_funct_1 @ X36)
% 0.91/1.14          | ~ (v1_funct_1 @ X39)
% 0.91/1.14          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.91/1.14          | ((k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39)
% 0.91/1.14              = (k5_relat_1 @ X36 @ X39)))),
% 0.91/1.14      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.91/1.14  thf('24', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 0.91/1.14            = (k5_relat_1 @ sk_D @ X0))
% 0.91/1.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.91/1.14          | ~ (v1_funct_1 @ X0)
% 0.91/1.14          | ~ (v1_funct_1 @ sk_D))),
% 0.91/1.14      inference('sup-', [status(thm)], ['22', '23'])).
% 0.91/1.14  thf('25', plain, ((v1_funct_1 @ sk_D)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('26', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 0.91/1.14            = (k5_relat_1 @ sk_D @ X0))
% 0.91/1.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.91/1.14          | ~ (v1_funct_1 @ X0))),
% 0.91/1.14      inference('demod', [status(thm)], ['24', '25'])).
% 0.91/1.14  thf('27', plain,
% 0.91/1.14      ((~ (v1_funct_1 @ sk_E)
% 0.91/1.14        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.91/1.14            = (k5_relat_1 @ sk_D @ sk_E)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['21', '26'])).
% 0.91/1.14  thf('28', plain, ((v1_funct_1 @ sk_E)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('29', plain,
% 0.91/1.14      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.91/1.14         = (k5_relat_1 @ sk_D @ sk_E))),
% 0.91/1.14      inference('demod', [status(thm)], ['27', '28'])).
% 0.91/1.14  thf('30', plain,
% 0.91/1.14      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 0.91/1.14        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.91/1.14      inference('demod', [status(thm)], ['19', '20', '29'])).
% 0.91/1.14  thf(redefinition_k2_relset_1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i]:
% 0.91/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.14       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.91/1.14  thf('31', plain,
% 0.91/1.14      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.91/1.14         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 0.91/1.14          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.91/1.14      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.91/1.14  thf('32', plain,
% 0.91/1.14      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 0.91/1.14         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['30', '31'])).
% 0.91/1.14  thf('33', plain,
% 0.91/1.14      (((k2_relset_1 @ sk_A @ sk_C @ 
% 0.91/1.14         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) = (sk_C))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('34', plain,
% 0.91/1.14      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.91/1.14         = (k5_relat_1 @ sk_D @ sk_E))),
% 0.91/1.14      inference('demod', [status(thm)], ['27', '28'])).
% 0.91/1.14  thf('35', plain,
% 0.91/1.14      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 0.91/1.14      inference('demod', [status(thm)], ['33', '34'])).
% 0.91/1.14  thf('36', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 0.91/1.14      inference('sup+', [status(thm)], ['32', '35'])).
% 0.91/1.14  thf(t51_funct_1, axiom,
% 0.91/1.14    (![A:$i]:
% 0.91/1.14     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.91/1.14       ( ![B:$i]:
% 0.91/1.14         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.91/1.14           ( ( ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) & 
% 0.91/1.14               ( v2_funct_1 @ A ) ) =>
% 0.91/1.14             ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 0.91/1.14  thf('37', plain,
% 0.91/1.14      (![X11 : $i, X12 : $i]:
% 0.91/1.14         (~ (v1_relat_1 @ X11)
% 0.91/1.14          | ~ (v1_funct_1 @ X11)
% 0.91/1.14          | (r1_tarski @ (k1_relat_1 @ X12) @ (k2_relat_1 @ X11))
% 0.91/1.14          | ((k2_relat_1 @ (k5_relat_1 @ X11 @ X12)) != (k2_relat_1 @ X12))
% 0.91/1.14          | ~ (v2_funct_1 @ X12)
% 0.91/1.14          | ~ (v1_funct_1 @ X12)
% 0.91/1.14          | ~ (v1_relat_1 @ X12))),
% 0.91/1.14      inference('cnf', [status(esa)], [t51_funct_1])).
% 0.91/1.14  thf('38', plain,
% 0.91/1.14      ((((sk_C) != (k2_relat_1 @ sk_E))
% 0.91/1.14        | ~ (v1_relat_1 @ sk_E)
% 0.91/1.14        | ~ (v1_funct_1 @ sk_E)
% 0.91/1.14        | ~ (v2_funct_1 @ sk_E)
% 0.91/1.14        | (r1_tarski @ (k1_relat_1 @ sk_E) @ (k2_relat_1 @ sk_D))
% 0.91/1.14        | ~ (v1_funct_1 @ sk_D)
% 0.91/1.14        | ~ (v1_relat_1 @ sk_D))),
% 0.91/1.14      inference('sup-', [status(thm)], ['36', '37'])).
% 0.91/1.14  thf('39', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('40', plain,
% 0.91/1.14      (![X3 : $i, X4 : $i]:
% 0.91/1.14         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.91/1.14          | (v1_relat_1 @ X3)
% 0.91/1.14          | ~ (v1_relat_1 @ X4))),
% 0.91/1.14      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.91/1.14  thf('41', plain,
% 0.91/1.14      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_E))),
% 0.91/1.14      inference('sup-', [status(thm)], ['39', '40'])).
% 0.91/1.14  thf('42', plain,
% 0.91/1.14      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.91/1.14      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.91/1.14  thf('43', plain, ((v1_relat_1 @ sk_E)),
% 0.91/1.14      inference('demod', [status(thm)], ['41', '42'])).
% 0.91/1.14  thf('44', plain, ((v1_funct_1 @ sk_E)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('45', plain, ((v2_funct_1 @ sk_E)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('46', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf(d1_funct_2, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i]:
% 0.91/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.14       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.91/1.14           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.91/1.14             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.91/1.14         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.91/1.14           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.91/1.14             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.91/1.14  thf(zf_stmt_1, axiom,
% 0.91/1.14    (![C:$i,B:$i,A:$i]:
% 0.91/1.14     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.91/1.14       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.91/1.14  thf('47', plain,
% 0.91/1.14      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.91/1.14         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.91/1.14          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 0.91/1.14          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.14  thf('48', plain,
% 0.91/1.14      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 0.91/1.14        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['46', '47'])).
% 0.91/1.14  thf(zf_stmt_2, axiom,
% 0.91/1.14    (![B:$i,A:$i]:
% 0.91/1.14     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.91/1.14       ( zip_tseitin_0 @ B @ A ) ))).
% 0.91/1.14  thf('49', plain,
% 0.91/1.14      (![X22 : $i, X23 : $i]:
% 0.91/1.14         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.91/1.14  thf('50', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.91/1.14  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.91/1.14  thf(zf_stmt_5, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i]:
% 0.91/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.14       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.91/1.14         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.91/1.14           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.91/1.14             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.91/1.14  thf('51', plain,
% 0.91/1.14      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.91/1.14         (~ (zip_tseitin_0 @ X27 @ X28)
% 0.91/1.14          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 0.91/1.14          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.91/1.14  thf('52', plain,
% 0.91/1.14      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 0.91/1.14      inference('sup-', [status(thm)], ['50', '51'])).
% 0.91/1.14  thf('53', plain,
% 0.91/1.14      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 0.91/1.14      inference('sup-', [status(thm)], ['49', '52'])).
% 0.91/1.14  thf('54', plain, (((sk_C) != (k1_xboole_0))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('55', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 0.91/1.14      inference('simplify_reflect-', [status(thm)], ['53', '54'])).
% 0.91/1.14  thf('56', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf(redefinition_k1_relset_1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i]:
% 0.91/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.14       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.91/1.14  thf('57', plain,
% 0.91/1.14      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.91/1.14         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.91/1.14          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.91/1.14      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.91/1.14  thf('58', plain,
% 0.91/1.14      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.91/1.14      inference('sup-', [status(thm)], ['56', '57'])).
% 0.91/1.14  thf('59', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 0.91/1.14      inference('demod', [status(thm)], ['48', '55', '58'])).
% 0.91/1.14  thf('60', plain, ((v1_funct_1 @ sk_D)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('61', plain, ((v1_relat_1 @ sk_D)),
% 0.91/1.14      inference('demod', [status(thm)], ['7', '8'])).
% 0.91/1.14  thf('62', plain,
% 0.91/1.14      ((((sk_C) != (k2_relat_1 @ sk_E))
% 0.91/1.14        | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D)))),
% 0.91/1.14      inference('demod', [status(thm)],
% 0.91/1.14                ['38', '43', '44', '45', '59', '60', '61'])).
% 0.91/1.14  thf('63', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 0.91/1.14      inference('sup+', [status(thm)], ['32', '35'])).
% 0.91/1.14  thf(t45_relat_1, axiom,
% 0.91/1.14    (![A:$i]:
% 0.91/1.14     ( ( v1_relat_1 @ A ) =>
% 0.91/1.14       ( ![B:$i]:
% 0.91/1.14         ( ( v1_relat_1 @ B ) =>
% 0.91/1.14           ( r1_tarski @
% 0.91/1.14             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.91/1.14  thf('64', plain,
% 0.91/1.14      (![X9 : $i, X10 : $i]:
% 0.91/1.14         (~ (v1_relat_1 @ X9)
% 0.91/1.14          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X10 @ X9)) @ 
% 0.91/1.14             (k2_relat_1 @ X9))
% 0.91/1.14          | ~ (v1_relat_1 @ X10))),
% 0.91/1.14      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.91/1.14  thf('65', plain,
% 0.91/1.14      (![X0 : $i, X2 : $i]:
% 0.91/1.14         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.91/1.14      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.91/1.14  thf('66', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         (~ (v1_relat_1 @ X1)
% 0.91/1.14          | ~ (v1_relat_1 @ X0)
% 0.91/1.14          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 0.91/1.14               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.91/1.14          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 0.91/1.14      inference('sup-', [status(thm)], ['64', '65'])).
% 0.91/1.14  thf('67', plain,
% 0.91/1.14      ((~ (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)
% 0.91/1.14        | ((k2_relat_1 @ sk_E) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 0.91/1.14        | ~ (v1_relat_1 @ sk_E)
% 0.91/1.14        | ~ (v1_relat_1 @ sk_D))),
% 0.91/1.14      inference('sup-', [status(thm)], ['63', '66'])).
% 0.91/1.14  thf('68', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('69', plain,
% 0.91/1.14      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.91/1.14         ((v5_relat_1 @ X13 @ X15)
% 0.91/1.14          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.91/1.14      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.91/1.14  thf('70', plain, ((v5_relat_1 @ sk_E @ sk_C)),
% 0.91/1.14      inference('sup-', [status(thm)], ['68', '69'])).
% 0.91/1.14  thf('71', plain,
% 0.91/1.14      (![X5 : $i, X6 : $i]:
% 0.91/1.14         (~ (v5_relat_1 @ X5 @ X6)
% 0.91/1.14          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.91/1.14          | ~ (v1_relat_1 @ X5))),
% 0.91/1.14      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.91/1.14  thf('72', plain,
% 0.91/1.14      ((~ (v1_relat_1 @ sk_E) | (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C))),
% 0.91/1.14      inference('sup-', [status(thm)], ['70', '71'])).
% 0.91/1.14  thf('73', plain, ((v1_relat_1 @ sk_E)),
% 0.91/1.14      inference('demod', [status(thm)], ['41', '42'])).
% 0.91/1.14  thf('74', plain, ((r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)),
% 0.91/1.14      inference('demod', [status(thm)], ['72', '73'])).
% 0.91/1.14  thf('75', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 0.91/1.14      inference('sup+', [status(thm)], ['32', '35'])).
% 0.91/1.14  thf('76', plain, ((v1_relat_1 @ sk_E)),
% 0.91/1.14      inference('demod', [status(thm)], ['41', '42'])).
% 0.91/1.14  thf('77', plain, ((v1_relat_1 @ sk_D)),
% 0.91/1.14      inference('demod', [status(thm)], ['7', '8'])).
% 0.91/1.14  thf('78', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 0.91/1.14      inference('demod', [status(thm)], ['67', '74', '75', '76', '77'])).
% 0.91/1.14  thf('79', plain,
% 0.91/1.14      ((((sk_C) != (sk_C)) | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D)))),
% 0.91/1.14      inference('demod', [status(thm)], ['62', '78'])).
% 0.91/1.14  thf('80', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_D))),
% 0.91/1.14      inference('simplify', [status(thm)], ['79'])).
% 0.91/1.14  thf('81', plain, (((sk_B) = (k2_relat_1 @ sk_D))),
% 0.91/1.14      inference('demod', [status(thm)], ['12', '80'])).
% 0.91/1.14  thf('82', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) != (sk_B))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('83', plain,
% 0.91/1.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('84', plain,
% 0.91/1.14      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.91/1.14         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 0.91/1.14          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.91/1.14      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.91/1.14  thf('85', plain,
% 0.91/1.14      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.91/1.14      inference('sup-', [status(thm)], ['83', '84'])).
% 0.91/1.14  thf('86', plain, (((k2_relat_1 @ sk_D) != (sk_B))),
% 0.91/1.14      inference('demod', [status(thm)], ['82', '85'])).
% 0.91/1.14  thf('87', plain, ($false),
% 0.91/1.14      inference('simplify_reflect-', [status(thm)], ['81', '86'])).
% 0.91/1.14  
% 0.91/1.14  % SZS output end Refutation
% 0.91/1.14  
% 0.91/1.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
