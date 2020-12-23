%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KBRvCp28BG

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:22 EST 2020

% Result     : Theorem 19.23s
% Output     : Refutation 19.23s
% Verified   : 
% Statistics : Number of formulae       :  244 (49702 expanded)
%              Number of leaves         :   31 (13174 expanded)
%              Depth                    :   51
%              Number of atoms          : 4564 (1090904 expanded)
%              Number of equality atoms :  209 (35171 expanded)
%              Maximal formula depth    :   18 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(t164_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
         => ( ( k5_partfun1 @ A @ ( k1_tarski @ B ) @ C )
            = ( k1_tarski @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
           => ( ( k5_partfun1 @ A @ ( k1_tarski @ B ) @ C )
              = ( k1_tarski @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t164_funct_2])).

thf('0',plain,(
    ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ C ) )
     => ! [D: $i] :
          ( ( D
            = ( k5_partfun1 @ A @ B @ C ) )
        <=> ! [E: $i] :
              ( ( r2_hidden @ E @ D )
            <=> ? [F: $i] :
                  ( ( v1_funct_1 @ F )
                  & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
                  & ( F = E )
                  & ( v1_partfun1 @ F @ A )
                  & ( r1_partfun1 @ C @ F ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ C @ B @ A )
    <=> ( ( r1_partfun1 @ C @ F )
        & ( v1_partfun1 @ F @ A )
        & ( F = E )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( D
            = ( k5_partfun1 @ A @ B @ C ) )
        <=> ! [E: $i] :
              ( ( r2_hidden @ E @ D )
            <=> ? [F: $i] :
                  ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ ( sk_E @ X14 @ X15 @ X16 @ X17 ) @ X14 )
      | ( zip_tseitin_0 @ ( sk_F @ X14 @ X15 @ X16 @ X17 ) @ ( sk_E @ X14 @ X15 @ X16 @ X17 ) @ X15 @ X16 @ X17 )
      | ( X14
        = ( k5_partfun1 @ X17 @ X16 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_C )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( zip_tseitin_0 @ ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( zip_tseitin_0 @ ( sk_F @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X15: $i,X16: $i,X17: $i,X19: $i,X21: $i,X22: $i] :
      ( ( X19
       != ( k5_partfun1 @ X17 @ X16 @ X15 ) )
      | ( r2_hidden @ X21 @ X19 )
      | ~ ( zip_tseitin_0 @ X22 @ X21 @ X15 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,(
    ! [X15: $i,X16: $i,X17: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( zip_tseitin_0 @ X22 @ X21 @ X15 @ X16 @ X17 )
      | ( r2_hidden @ X21 @ ( k5_partfun1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X15: $i,X16: $i,X17: $i,X19: $i,X20: $i] :
      ( ( X19
       != ( k5_partfun1 @ X17 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X20 @ X15 @ X16 @ X17 ) @ X20 @ X15 @ X16 @ X17 )
      | ~ ( r2_hidden @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('16',plain,(
    ! [X15: $i,X16: $i,X17: $i,X20: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( r2_hidden @ X20 @ ( k5_partfun1 @ X17 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X20 @ X15 @ X16 @ X17 ) @ X20 @ X15 @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X9 = X10 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( ( sk_F_1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
        = ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('24',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( v1_funct_1 @ X9 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( v1_funct_1 @ ( sk_F_1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( v1_funct_1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t155_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( r1_partfun1 @ C @ D )
           => ( ( ( B = k1_xboole_0 )
                & ( A != k1_xboole_0 ) )
              | ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( r2_hidden @ X27 @ ( k5_partfun1 @ X28 @ X29 @ X30 ) )
      | ~ ( r1_partfun1 @ X30 @ X27 )
      | ( X29 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_2])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
    | ~ ( r1_partfun1 @ sk_C @ sk_D )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t143_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
         => ( r1_partfun1 @ C @ D ) ) ) )).

thf('38',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ ( k1_tarski @ X25 ) ) ) )
      | ( r1_partfun1 @ X26 @ X23 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ ( k1_tarski @ X25 ) ) ) )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t143_partfun1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r1_partfun1 @ sk_C @ sk_D )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('48',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X9 = X10 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('50',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_D ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_F_1 @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('52',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_0 @ sk_D @ sk_D @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( v1_partfun1 @ X9 @ X12 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('55',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t174_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_partfun1 @ C @ A )
      <=> ( ( k5_partfun1 @ A @ B @ C )
          = ( k1_tarski @ C ) ) ) ) )).

thf('57',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_partfun1 @ X31 @ X32 )
      | ( ( k5_partfun1 @ X32 @ X33 @ X31 )
        = ( k1_tarski @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t174_partfun1])).

thf('58',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ~ ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ~ ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D )
      = ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X15: $i,X16: $i,X17: $i,X20: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( r2_hidden @ X20 @ ( k5_partfun1 @ X17 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X20 @ X15 @ X16 @ X17 ) @ X20 @ X15 @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X0 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X0 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_D ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X0 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,
    ( ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_D )
      = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
    | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','67'])).

thf('69',plain,(
    ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X9 = X10 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('72',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf('74',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( v1_funct_1 @ X9 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('75',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( v1_funct_1 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','75'])).

thf('77',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( ( sk_F_1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
        = ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('80',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r1_partfun1 @ X8 @ X9 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( r1_partfun1 @ sk_C @ ( sk_F_1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r1_partfun1 @ sk_C @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( r1_partfun1 @ sk_C @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_D ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X0 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('85',plain,
    ( ( r1_partfun1 @ sk_C @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_D )
      = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
    | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( r1_partfun1 @ sk_C @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X9 = X10 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('89',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r1_partfun1 @ sk_C @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( r1_partfun1 @ sk_C @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['85','86'])).

thf('91',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X11 ) ) )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('92',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r1_partfun1 @ sk_C @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( m1_subset_1 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( m1_subset_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
    | ( r1_partfun1 @ sk_C @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r1_partfun1 @ sk_C @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['89','92'])).

thf('94',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r1_partfun1 @ sk_C @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ ( k1_tarski @ X25 ) ) ) )
      | ( r1_partfun1 @ X26 @ X23 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ ( k1_tarski @ X25 ) ) ) )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t143_partfun1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( r1_partfun1 @ sk_C @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( r1_partfun1 @ X0 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( r1_partfun1 @ X0 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( r1_partfun1 @ sk_C @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['77','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( r1_partfun1 @ sk_C @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( r1_partfun1 @ X0 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r1_partfun1 @ sk_C @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_partfun1 @ sk_C @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','98'])).

thf('100',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r1_partfun1 @ sk_C @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( r1_partfun1 @ sk_C @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( r1_partfun1 @ sk_C @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( ( sk_F_1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
        = ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('106',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( v1_partfun1 @ X9 @ X12 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( v1_partfun1 @ ( sk_F_1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['104','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( v1_partfun1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_D ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X0 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('111',plain,
    ( ( v1_partfun1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A )
    | ( ( k1_tarski @ sk_D )
      = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
    | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( v1_partfun1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A )
    | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X9 = X10 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('115',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A )
    | ( ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( v1_partfun1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A )
    | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['111','112'])).

thf('117',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( v1_partfun1 @ X9 @ X12 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('118',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A )
    | ( v1_partfun1 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( v1_partfun1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A )
    | ( v1_partfun1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['115','118'])).

thf('120',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D )
      = ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('122',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('123',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( ( sk_F_1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
        = ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( zip_tseitin_0 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X11 ) ) )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( m1_subset_1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ ( k1_tarski @ X25 ) ) ) )
      | ( r1_partfun1 @ X26 @ X23 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ ( k1_tarski @ X25 ) ) ) )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t143_partfun1])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( r1_partfun1 @ X1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ( r1_partfun1 @ sk_D @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['123','131'])).

thf('133',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ( r1_partfun1 @ sk_D @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_D ) )
    | ( ( k1_tarski @ sk_D )
      = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
    | ( r1_partfun1 @ sk_D @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['122','134'])).

thf('136',plain,(
    ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_D ) )
    | ( r1_partfun1 @ sk_D @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_D ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X0 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('139',plain,
    ( ( r1_partfun1 @ sk_D @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r1_partfun1 @ sk_D @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X9 = X10 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('142',plain,
    ( ( r1_partfun1 @ sk_D @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r1_partfun1 @ sk_D @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('144',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r1_partfun1 @ X8 @ X9 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('145',plain,
    ( ( r1_partfun1 @ sk_D @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r1_partfun1 @ sk_D @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,
    ( ( r1_partfun1 @ sk_D @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r1_partfun1 @ sk_D @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r1_partfun1 @ sk_D @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['142','145'])).

thf('147',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r1_partfun1 @ sk_D @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( v1_partfun1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( m1_subset_1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('151',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X13 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X11 ) ) )
      | ( X9 != X10 )
      | ~ ( v1_partfun1 @ X9 @ X13 )
      | ~ ( r1_partfun1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('152',plain,(
    ! [X8: $i,X10: $i,X11: $i,X13: $i] :
      ( ~ ( r1_partfun1 @ X8 @ X10 )
      | ~ ( v1_partfun1 @ X10 @ X13 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ( zip_tseitin_0 @ X10 @ X10 @ X8 @ X11 @ X13 ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( zip_tseitin_0 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X1 @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( v1_funct_1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ~ ( v1_partfun1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A )
      | ~ ( r1_partfun1 @ X1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['150','152'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( r1_partfun1 @ X1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X1 @ ( k1_tarski @ sk_B ) @ sk_A )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['149','153'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X1 @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( v1_funct_1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ~ ( r1_partfun1 @ X1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_D )
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ( r2_hidden @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_D ) )
      | ~ ( r1_partfun1 @ X0 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['148','155'])).

thf('157',plain,(
    ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_D ) )
      | ~ ( r1_partfun1 @ X0 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['156','157'])).

thf('159',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( r2_hidden @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_D ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['147','158'])).

thf('160',plain,
    ( ( r2_hidden @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_D ) )
    | ( zip_tseitin_0 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    ! [X15: $i,X16: $i,X17: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( zip_tseitin_0 @ X22 @ X21 @ X15 @ X16 @ X17 )
      | ( r2_hidden @ X21 @ ( k5_partfun1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_D ) )
    | ( r2_hidden @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['160','165'])).

thf('167',plain,
    ( ( r2_hidden @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_D ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_D ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['121','166'])).

thf('168',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_D ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_D ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X0 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('170',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,
    ( ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X9 = X10 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('173',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,
    ( ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['170'])).

thf('175',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X11 ) ) )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('176',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_F_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,
    ( ( m1_subset_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['173','176'])).

thf('178',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,(
    ! [X8: $i,X10: $i,X11: $i,X13: $i] :
      ( ~ ( r1_partfun1 @ X8 @ X10 )
      | ~ ( v1_partfun1 @ X10 @ X13 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ( zip_tseitin_0 @ X10 @ X10 @ X8 @ X11 @ X13 ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ~ ( v1_partfun1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r1_partfun1 @ X0 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 @ ( k1_tarski @ sk_B ) @ sk_A )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['120','180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( v1_funct_1 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ~ ( r1_partfun1 @ X0 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r1_partfun1 @ X0 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['102','184'])).

thf('186',plain,
    ( ( zip_tseitin_0 @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( sk_E @ X14 @ X15 @ X16 @ X17 ) @ X14 )
      | ~ ( zip_tseitin_0 @ X18 @ ( sk_E @ X14 @ X15 @ X16 @ X17 ) @ X15 @ X16 @ X17 )
      | ( X14
        = ( k5_partfun1 @ X17 @ X16 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ sk_C )
      | ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ~ ( zip_tseitin_0 @ X1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) )
      | ~ ( zip_tseitin_0 @ X1 @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( r2_hidden @ ( sk_E @ X0 @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('192',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_D ) )
    | ( ( k1_tarski @ sk_D )
      = ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['186','191'])).

thf('193',plain,(
    ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['192','193'])).

thf('195',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_E @ ( k1_tarski @ sk_D ) @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_D ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('196',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['194','195'])).

thf('197',plain,(
    ( k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C )
 != ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['0','196'])).

thf('198',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['194','195'])).

thf(t130_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != k1_xboole_0 )
     => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
         != k1_xboole_0 )
        & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
         != k1_xboole_0 ) ) ) )).

thf('199',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ ( k1_tarski @ X7 ) @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t130_zfmisc_1])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('201',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('202',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['201'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['200','202'])).

thf('204',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['203'])).

thf('206',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['203'])).

thf('207',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['203'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('208',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('209',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['203'])).

thf('210',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['197','204','205','206','207','208','209'])).

thf('211',plain,(
    $false ),
    inference(simplify,[status(thm)],['210'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KBRvCp28BG
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:03:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.22/0.36  % Running in FO mode
% 19.23/19.38  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 19.23/19.38  % Solved by: fo/fo7.sh
% 19.23/19.38  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 19.23/19.38  % done 19855 iterations in 18.911s
% 19.23/19.38  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 19.23/19.38  % SZS output start Refutation
% 19.23/19.38  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 19.23/19.38  thf(sk_B_type, type, sk_B: $i).
% 19.23/19.38  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 19.23/19.38  thf(sk_C_type, type, sk_C: $i).
% 19.23/19.38  thf(sk_A_type, type, sk_A: $i).
% 19.23/19.38  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 19.23/19.38  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 19.23/19.38  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 19.23/19.38  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 19.23/19.38  thf(sk_D_type, type, sk_D: $i).
% 19.23/19.38  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 19.23/19.38  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 19.23/19.38  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 19.23/19.38  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 19.23/19.38  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i > $i).
% 19.23/19.38  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 19.23/19.38  thf(k5_partfun1_type, type, k5_partfun1: $i > $i > $i > $i).
% 19.23/19.38  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 19.23/19.38  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i).
% 19.23/19.38  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 19.23/19.38  thf(t164_funct_2, conjecture,
% 19.23/19.38    (![A:$i,B:$i,C:$i]:
% 19.23/19.38     ( ( ( v1_funct_1 @ C ) & 
% 19.23/19.38         ( m1_subset_1 @
% 19.23/19.38           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 19.23/19.38       ( ![D:$i]:
% 19.23/19.38         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 19.23/19.38             ( m1_subset_1 @
% 19.23/19.38               D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 19.23/19.38           ( ( k5_partfun1 @ A @ ( k1_tarski @ B ) @ C ) = ( k1_tarski @ D ) ) ) ) ))).
% 19.23/19.38  thf(zf_stmt_0, negated_conjecture,
% 19.23/19.38    (~( ![A:$i,B:$i,C:$i]:
% 19.23/19.38        ( ( ( v1_funct_1 @ C ) & 
% 19.23/19.38            ( m1_subset_1 @
% 19.23/19.38              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 19.23/19.38          ( ![D:$i]:
% 19.23/19.38            ( ( ( v1_funct_1 @ D ) & 
% 19.23/19.38                ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 19.23/19.38                ( m1_subset_1 @
% 19.23/19.38                  D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 19.23/19.38              ( ( k5_partfun1 @ A @ ( k1_tarski @ B ) @ C ) = ( k1_tarski @ D ) ) ) ) ) )),
% 19.23/19.38    inference('cnf.neg', [status(esa)], [t164_funct_2])).
% 19.23/19.38  thf('0', plain,
% 19.23/19.38      (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C) != (k1_tarski @ sk_D))),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.38  thf('1', plain,
% 19.23/19.38      ((m1_subset_1 @ sk_C @ 
% 19.23/19.38        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.38  thf('2', plain,
% 19.23/19.38      ((m1_subset_1 @ sk_C @ 
% 19.23/19.38        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.38  thf(d7_partfun1, axiom,
% 19.23/19.38    (![A:$i,B:$i,C:$i]:
% 19.23/19.38     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 19.23/19.38         ( v1_funct_1 @ C ) ) =>
% 19.23/19.38       ( ![D:$i]:
% 19.23/19.38         ( ( ( D ) = ( k5_partfun1 @ A @ B @ C ) ) <=>
% 19.23/19.38           ( ![E:$i]:
% 19.23/19.38             ( ( r2_hidden @ E @ D ) <=>
% 19.23/19.38               ( ?[F:$i]:
% 19.23/19.38                 ( ( v1_funct_1 @ F ) & 
% 19.23/19.38                   ( m1_subset_1 @
% 19.23/19.38                     F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 19.23/19.38                   ( ( F ) = ( E ) ) & ( v1_partfun1 @ F @ A ) & 
% 19.23/19.38                   ( r1_partfun1 @ C @ F ) ) ) ) ) ) ) ))).
% 19.23/19.38  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 19.23/19.38  thf(zf_stmt_2, axiom,
% 19.23/19.38    (![F:$i,E:$i,C:$i,B:$i,A:$i]:
% 19.23/19.38     ( ( zip_tseitin_0 @ F @ E @ C @ B @ A ) <=>
% 19.23/19.38       ( ( r1_partfun1 @ C @ F ) & ( v1_partfun1 @ F @ A ) & 
% 19.23/19.38         ( ( F ) = ( E ) ) & 
% 19.23/19.38         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 19.23/19.38         ( v1_funct_1 @ F ) ) ))).
% 19.23/19.38  thf(zf_stmt_3, axiom,
% 19.23/19.38    (![A:$i,B:$i,C:$i]:
% 19.23/19.38     ( ( ( v1_funct_1 @ C ) & 
% 19.23/19.38         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 19.23/19.38       ( ![D:$i]:
% 19.23/19.38         ( ( ( D ) = ( k5_partfun1 @ A @ B @ C ) ) <=>
% 19.23/19.38           ( ![E:$i]:
% 19.23/19.38             ( ( r2_hidden @ E @ D ) <=>
% 19.23/19.38               ( ?[F:$i]: ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) ) ) ))).
% 19.23/19.38  thf('3', plain,
% 19.23/19.38      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 19.23/19.38         ((r2_hidden @ (sk_E @ X14 @ X15 @ X16 @ X17) @ X14)
% 19.23/19.38          | (zip_tseitin_0 @ (sk_F @ X14 @ X15 @ X16 @ X17) @ 
% 19.23/19.38             (sk_E @ X14 @ X15 @ X16 @ X17) @ X15 @ X16 @ X17)
% 19.23/19.38          | ((X14) = (k5_partfun1 @ X17 @ X16 @ X15))
% 19.23/19.38          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 19.23/19.38          | ~ (v1_funct_1 @ X15))),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_3])).
% 19.23/19.38  thf('4', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         (~ (v1_funct_1 @ sk_C)
% 19.23/19.38          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38          | (zip_tseitin_0 @ (sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38             (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 19.23/19.38             (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.38          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0))),
% 19.23/19.38      inference('sup-', [status(thm)], ['2', '3'])).
% 19.23/19.38  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.38  thf('6', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         (((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38          | (zip_tseitin_0 @ (sk_F @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38             (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 19.23/19.38             (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.38          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0))),
% 19.23/19.38      inference('demod', [status(thm)], ['4', '5'])).
% 19.23/19.38  thf('7', plain,
% 19.23/19.38      ((m1_subset_1 @ sk_C @ 
% 19.23/19.38        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.38  thf('8', plain,
% 19.23/19.38      (![X15 : $i, X16 : $i, X17 : $i, X19 : $i, X21 : $i, X22 : $i]:
% 19.23/19.38         (((X19) != (k5_partfun1 @ X17 @ X16 @ X15))
% 19.23/19.38          | (r2_hidden @ X21 @ X19)
% 19.23/19.38          | ~ (zip_tseitin_0 @ X22 @ X21 @ X15 @ X16 @ X17)
% 19.23/19.38          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 19.23/19.38          | ~ (v1_funct_1 @ X15))),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_3])).
% 19.23/19.38  thf('9', plain,
% 19.23/19.38      (![X15 : $i, X16 : $i, X17 : $i, X21 : $i, X22 : $i]:
% 19.23/19.38         (~ (v1_funct_1 @ X15)
% 19.23/19.38          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 19.23/19.38          | ~ (zip_tseitin_0 @ X22 @ X21 @ X15 @ X16 @ X17)
% 19.23/19.38          | (r2_hidden @ X21 @ (k5_partfun1 @ X17 @ X16 @ X15)))),
% 19.23/19.38      inference('simplify', [status(thm)], ['8'])).
% 19.23/19.38  thf('10', plain,
% 19.23/19.38      (![X0 : $i, X1 : $i]:
% 19.23/19.38         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.38          | ~ (v1_funct_1 @ sk_C))),
% 19.23/19.38      inference('sup-', [status(thm)], ['7', '9'])).
% 19.23/19.38  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.38  thf('12', plain,
% 19.23/19.38      (![X0 : $i, X1 : $i]:
% 19.23/19.38         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A))),
% 19.23/19.38      inference('demod', [status(thm)], ['10', '11'])).
% 19.23/19.38  thf('13', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         ((r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 19.23/19.38          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38             (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C)))),
% 19.23/19.38      inference('sup-', [status(thm)], ['6', '12'])).
% 19.23/19.38  thf('14', plain,
% 19.23/19.38      ((m1_subset_1 @ sk_C @ 
% 19.23/19.38        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.38  thf('15', plain,
% 19.23/19.38      (![X15 : $i, X16 : $i, X17 : $i, X19 : $i, X20 : $i]:
% 19.23/19.38         (((X19) != (k5_partfun1 @ X17 @ X16 @ X15))
% 19.23/19.38          | (zip_tseitin_0 @ (sk_F_1 @ X20 @ X15 @ X16 @ X17) @ X20 @ X15 @ 
% 19.23/19.38             X16 @ X17)
% 19.23/19.38          | ~ (r2_hidden @ X20 @ X19)
% 19.23/19.38          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 19.23/19.38          | ~ (v1_funct_1 @ X15))),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_3])).
% 19.23/19.38  thf('16', plain,
% 19.23/19.38      (![X15 : $i, X16 : $i, X17 : $i, X20 : $i]:
% 19.23/19.38         (~ (v1_funct_1 @ X15)
% 19.23/19.38          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 19.23/19.38          | ~ (r2_hidden @ X20 @ (k5_partfun1 @ X17 @ X16 @ X15))
% 19.23/19.38          | (zip_tseitin_0 @ (sk_F_1 @ X20 @ X15 @ X16 @ X17) @ X20 @ X15 @ 
% 19.23/19.38             X16 @ X17))),
% 19.23/19.38      inference('simplify', [status(thm)], ['15'])).
% 19.23/19.38  thf('17', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         ((zip_tseitin_0 @ (sk_F_1 @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38           X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.38          | ~ (r2_hidden @ X0 @ 
% 19.23/19.38               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38          | ~ (v1_funct_1 @ sk_C))),
% 19.23/19.38      inference('sup-', [status(thm)], ['14', '16'])).
% 19.23/19.38  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.38  thf('19', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         ((zip_tseitin_0 @ (sk_F_1 @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38           X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.38          | ~ (r2_hidden @ X0 @ 
% 19.23/19.38               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C)))),
% 19.23/19.38      inference('demod', [status(thm)], ['17', '18'])).
% 19.23/19.38  thf('20', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         (((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 19.23/19.38          | (zip_tseitin_0 @ 
% 19.23/19.38             (sk_F_1 @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 19.23/19.38              (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38             (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 19.23/19.38             (k1_tarski @ sk_B) @ sk_A))),
% 19.23/19.38      inference('sup-', [status(thm)], ['13', '19'])).
% 19.23/19.38  thf('21', plain,
% 19.23/19.38      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 19.23/19.38         (((X9) = (X10)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_2])).
% 19.23/19.38  thf('22', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         ((r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 19.23/19.38          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38          | ((sk_F_1 @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 19.23/19.38              (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.38              = (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 19.23/19.38      inference('sup-', [status(thm)], ['20', '21'])).
% 19.23/19.38  thf('23', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         (((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 19.23/19.38          | (zip_tseitin_0 @ 
% 19.23/19.38             (sk_F_1 @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 19.23/19.38              (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38             (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 19.23/19.38             (k1_tarski @ sk_B) @ sk_A))),
% 19.23/19.38      inference('sup-', [status(thm)], ['13', '19'])).
% 19.23/19.38  thf('24', plain,
% 19.23/19.38      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 19.23/19.38         ((v1_funct_1 @ X9) | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_2])).
% 19.23/19.38  thf('25', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         ((r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 19.23/19.38          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38          | (v1_funct_1 @ 
% 19.23/19.38             (sk_F_1 @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 19.23/19.38              (k1_tarski @ sk_B) @ sk_A)))),
% 19.23/19.38      inference('sup-', [status(thm)], ['23', '24'])).
% 19.23/19.38  thf('26', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         ((v1_funct_1 @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.38          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 19.23/19.38          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0))),
% 19.23/19.38      inference('sup+', [status(thm)], ['22', '25'])).
% 19.23/19.38  thf('27', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         ((r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 19.23/19.38          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38          | (v1_funct_1 @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 19.23/19.38      inference('simplify', [status(thm)], ['26'])).
% 19.23/19.38  thf('28', plain,
% 19.23/19.38      ((m1_subset_1 @ sk_C @ 
% 19.23/19.38        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.38  thf('29', plain,
% 19.23/19.38      ((m1_subset_1 @ sk_D @ 
% 19.23/19.38        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.38  thf(t155_funct_2, axiom,
% 19.23/19.38    (![A:$i,B:$i,C:$i]:
% 19.23/19.38     ( ( ( v1_funct_1 @ C ) & 
% 19.23/19.38         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 19.23/19.38       ( ![D:$i]:
% 19.23/19.38         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 19.23/19.38             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 19.23/19.38           ( ( r1_partfun1 @ C @ D ) =>
% 19.23/19.38             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 19.23/19.38               ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) ) ) ) ) ))).
% 19.23/19.38  thf('30', plain,
% 19.23/19.38      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 19.23/19.38         (~ (v1_funct_1 @ X27)
% 19.23/19.38          | ~ (v1_funct_2 @ X27 @ X28 @ X29)
% 19.23/19.38          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 19.23/19.38          | (r2_hidden @ X27 @ (k5_partfun1 @ X28 @ X29 @ X30))
% 19.23/19.38          | ~ (r1_partfun1 @ X30 @ X27)
% 19.23/19.38          | ((X29) = (k1_xboole_0))
% 19.23/19.38          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 19.23/19.38          | ~ (v1_funct_1 @ X30))),
% 19.23/19.38      inference('cnf', [status(esa)], [t155_funct_2])).
% 19.23/19.38  thf('31', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         (~ (v1_funct_1 @ X0)
% 19.23/19.38          | ~ (m1_subset_1 @ X0 @ 
% 19.23/19.38               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 19.23/19.38          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.38          | ~ (r1_partfun1 @ X0 @ sk_D)
% 19.23/19.38          | (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ X0))
% 19.23/19.38          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))
% 19.23/19.38          | ~ (v1_funct_1 @ sk_D))),
% 19.23/19.38      inference('sup-', [status(thm)], ['29', '30'])).
% 19.23/19.38  thf('32', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.38  thf('33', plain, ((v1_funct_1 @ sk_D)),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.38  thf('34', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         (~ (v1_funct_1 @ X0)
% 19.23/19.38          | ~ (m1_subset_1 @ X0 @ 
% 19.23/19.38               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 19.23/19.38          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.38          | ~ (r1_partfun1 @ X0 @ sk_D)
% 19.23/19.38          | (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ X0)))),
% 19.23/19.38      inference('demod', [status(thm)], ['31', '32', '33'])).
% 19.23/19.38  thf('35', plain,
% 19.23/19.38      (((r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38        | ~ (r1_partfun1 @ sk_C @ sk_D)
% 19.23/19.38        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.38        | ~ (v1_funct_1 @ sk_C))),
% 19.23/19.38      inference('sup-', [status(thm)], ['28', '34'])).
% 19.23/19.38  thf('36', plain,
% 19.23/19.38      ((m1_subset_1 @ sk_C @ 
% 19.23/19.38        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.38  thf('37', plain,
% 19.23/19.38      ((m1_subset_1 @ sk_D @ 
% 19.23/19.38        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.38  thf(t143_partfun1, axiom,
% 19.23/19.38    (![A:$i,B:$i,C:$i]:
% 19.23/19.38     ( ( ( v1_funct_1 @ C ) & 
% 19.23/19.38         ( m1_subset_1 @
% 19.23/19.38           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 19.23/19.38       ( ![D:$i]:
% 19.23/19.38         ( ( ( v1_funct_1 @ D ) & 
% 19.23/19.38             ( m1_subset_1 @
% 19.23/19.38               D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 19.23/19.38           ( r1_partfun1 @ C @ D ) ) ) ))).
% 19.23/19.38  thf('38', plain,
% 19.23/19.38      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 19.23/19.38         (~ (v1_funct_1 @ X23)
% 19.23/19.38          | ~ (m1_subset_1 @ X23 @ 
% 19.23/19.38               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ (k1_tarski @ X25))))
% 19.23/19.38          | (r1_partfun1 @ X26 @ X23)
% 19.23/19.38          | ~ (m1_subset_1 @ X26 @ 
% 19.23/19.38               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ (k1_tarski @ X25))))
% 19.23/19.38          | ~ (v1_funct_1 @ X26))),
% 19.23/19.38      inference('cnf', [status(esa)], [t143_partfun1])).
% 19.23/19.38  thf('39', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         (~ (v1_funct_1 @ X0)
% 19.23/19.38          | ~ (m1_subset_1 @ X0 @ 
% 19.23/19.38               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 19.23/19.38          | (r1_partfun1 @ X0 @ sk_D)
% 19.23/19.38          | ~ (v1_funct_1 @ sk_D))),
% 19.23/19.38      inference('sup-', [status(thm)], ['37', '38'])).
% 19.23/19.38  thf('40', plain, ((v1_funct_1 @ sk_D)),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.38  thf('41', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         (~ (v1_funct_1 @ X0)
% 19.23/19.38          | ~ (m1_subset_1 @ X0 @ 
% 19.23/19.38               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 19.23/19.38          | (r1_partfun1 @ X0 @ sk_D))),
% 19.23/19.38      inference('demod', [status(thm)], ['39', '40'])).
% 19.23/19.38  thf('42', plain, (((r1_partfun1 @ sk_C @ sk_D) | ~ (v1_funct_1 @ sk_C))),
% 19.23/19.38      inference('sup-', [status(thm)], ['36', '41'])).
% 19.23/19.38  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.38  thf('44', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 19.23/19.38      inference('demod', [status(thm)], ['42', '43'])).
% 19.23/19.38  thf('45', plain, ((v1_funct_1 @ sk_C)),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.38  thf('46', plain,
% 19.23/19.38      (((r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 19.23/19.38      inference('demod', [status(thm)], ['35', '44', '45'])).
% 19.23/19.38  thf('47', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         ((zip_tseitin_0 @ (sk_F_1 @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38           X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.38          | ~ (r2_hidden @ X0 @ 
% 19.23/19.38               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C)))),
% 19.23/19.38      inference('demod', [status(thm)], ['17', '18'])).
% 19.23/19.38  thf('48', plain,
% 19.23/19.38      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.38        | (zip_tseitin_0 @ 
% 19.23/19.38           (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_D @ sk_C @ 
% 19.23/19.38           (k1_tarski @ sk_B) @ sk_A))),
% 19.23/19.38      inference('sup-', [status(thm)], ['46', '47'])).
% 19.23/19.38  thf('49', plain,
% 19.23/19.38      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 19.23/19.38         (((X9) = (X10)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_2])).
% 19.23/19.38  thf('50', plain,
% 19.23/19.38      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.38        | ((sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A) = (sk_D)))),
% 19.23/19.38      inference('sup-', [status(thm)], ['48', '49'])).
% 19.23/19.38  thf('51', plain,
% 19.23/19.38      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.38        | (zip_tseitin_0 @ 
% 19.23/19.38           (sk_F_1 @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_D @ sk_C @ 
% 19.23/19.38           (k1_tarski @ sk_B) @ sk_A))),
% 19.23/19.38      inference('sup-', [status(thm)], ['46', '47'])).
% 19.23/19.38  thf('52', plain,
% 19.23/19.38      (((zip_tseitin_0 @ sk_D @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.38        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.38        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 19.23/19.38      inference('sup+', [status(thm)], ['50', '51'])).
% 19.23/19.38  thf('53', plain,
% 19.23/19.38      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.38        | (zip_tseitin_0 @ sk_D @ sk_D @ sk_C @ (k1_tarski @ sk_B) @ sk_A))),
% 19.23/19.38      inference('simplify', [status(thm)], ['52'])).
% 19.23/19.38  thf('54', plain,
% 19.23/19.38      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 19.23/19.38         ((v1_partfun1 @ X9 @ X12)
% 19.23/19.38          | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_2])).
% 19.23/19.38  thf('55', plain,
% 19.23/19.38      ((((k1_tarski @ sk_B) = (k1_xboole_0)) | (v1_partfun1 @ sk_D @ sk_A))),
% 19.23/19.38      inference('sup-', [status(thm)], ['53', '54'])).
% 19.23/19.38  thf('56', plain,
% 19.23/19.38      ((m1_subset_1 @ sk_D @ 
% 19.23/19.38        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.38  thf(t174_partfun1, axiom,
% 19.23/19.38    (![A:$i,B:$i,C:$i]:
% 19.23/19.38     ( ( ( v1_funct_1 @ C ) & 
% 19.23/19.38         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 19.23/19.38       ( ( v1_partfun1 @ C @ A ) <=>
% 19.23/19.38         ( ( k5_partfun1 @ A @ B @ C ) = ( k1_tarski @ C ) ) ) ))).
% 19.23/19.38  thf('57', plain,
% 19.23/19.38      (![X31 : $i, X32 : $i, X33 : $i]:
% 19.23/19.38         (~ (v1_partfun1 @ X31 @ X32)
% 19.23/19.38          | ((k5_partfun1 @ X32 @ X33 @ X31) = (k1_tarski @ X31))
% 19.23/19.38          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 19.23/19.38          | ~ (v1_funct_1 @ X31))),
% 19.23/19.38      inference('cnf', [status(esa)], [t174_partfun1])).
% 19.23/19.38  thf('58', plain,
% 19.23/19.38      ((~ (v1_funct_1 @ sk_D)
% 19.23/19.38        | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D)
% 19.23/19.38            = (k1_tarski @ sk_D))
% 19.23/19.38        | ~ (v1_partfun1 @ sk_D @ sk_A))),
% 19.23/19.38      inference('sup-', [status(thm)], ['56', '57'])).
% 19.23/19.38  thf('59', plain, ((v1_funct_1 @ sk_D)),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.38  thf('60', plain,
% 19.23/19.38      ((((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D) = (k1_tarski @ sk_D))
% 19.23/19.38        | ~ (v1_partfun1 @ sk_D @ sk_A))),
% 19.23/19.38      inference('demod', [status(thm)], ['58', '59'])).
% 19.23/19.38  thf('61', plain,
% 19.23/19.38      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.38        | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D)
% 19.23/19.38            = (k1_tarski @ sk_D)))),
% 19.23/19.38      inference('sup-', [status(thm)], ['55', '60'])).
% 19.23/19.38  thf('62', plain,
% 19.23/19.38      ((m1_subset_1 @ sk_D @ 
% 19.23/19.38        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.38  thf('63', plain,
% 19.23/19.38      (![X15 : $i, X16 : $i, X17 : $i, X20 : $i]:
% 19.23/19.38         (~ (v1_funct_1 @ X15)
% 19.23/19.38          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 19.23/19.38          | ~ (r2_hidden @ X20 @ (k5_partfun1 @ X17 @ X16 @ X15))
% 19.23/19.38          | (zip_tseitin_0 @ (sk_F_1 @ X20 @ X15 @ X16 @ X17) @ X20 @ X15 @ 
% 19.23/19.38             X16 @ X17))),
% 19.23/19.38      inference('simplify', [status(thm)], ['15'])).
% 19.23/19.38  thf('64', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         ((zip_tseitin_0 @ (sk_F_1 @ X0 @ sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38           X0 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.38          | ~ (r2_hidden @ X0 @ 
% 19.23/19.38               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D))
% 19.23/19.38          | ~ (v1_funct_1 @ sk_D))),
% 19.23/19.38      inference('sup-', [status(thm)], ['62', '63'])).
% 19.23/19.38  thf('65', plain, ((v1_funct_1 @ sk_D)),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.38  thf('66', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         ((zip_tseitin_0 @ (sk_F_1 @ X0 @ sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38           X0 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.38          | ~ (r2_hidden @ X0 @ 
% 19.23/19.38               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D)))),
% 19.23/19.38      inference('demod', [status(thm)], ['64', '65'])).
% 19.23/19.38  thf('67', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_D))
% 19.23/19.38          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.38          | (zip_tseitin_0 @ 
% 19.23/19.38             (sk_F_1 @ X0 @ sk_D @ (k1_tarski @ sk_B) @ sk_A) @ X0 @ sk_D @ 
% 19.23/19.38             (k1_tarski @ sk_B) @ sk_A))),
% 19.23/19.38      inference('sup-', [status(thm)], ['61', '66'])).
% 19.23/19.38  thf('68', plain,
% 19.23/19.38      (((v1_funct_1 @ 
% 19.23/19.38         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.38        | ((k1_tarski @ sk_D)
% 19.23/19.38            = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38        | (zip_tseitin_0 @ 
% 19.23/19.38           (sk_F_1 @ 
% 19.23/19.38            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38            sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38           sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.38        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 19.23/19.38      inference('sup-', [status(thm)], ['27', '67'])).
% 19.23/19.38  thf('69', plain,
% 19.23/19.38      (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C) != (k1_tarski @ sk_D))),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.38  thf('70', plain,
% 19.23/19.38      (((v1_funct_1 @ 
% 19.23/19.38         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.38        | (zip_tseitin_0 @ 
% 19.23/19.38           (sk_F_1 @ 
% 19.23/19.38            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38            sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38           sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.38        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 19.23/19.38      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 19.23/19.38  thf('71', plain,
% 19.23/19.38      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 19.23/19.38         (((X9) = (X10)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_2])).
% 19.23/19.38  thf('72', plain,
% 19.23/19.38      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.38        | (v1_funct_1 @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.38        | ((sk_F_1 @ 
% 19.23/19.38            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38            sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.38            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 19.23/19.38      inference('sup-', [status(thm)], ['70', '71'])).
% 19.23/19.38  thf('73', plain,
% 19.23/19.38      (((v1_funct_1 @ 
% 19.23/19.38         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.38        | (zip_tseitin_0 @ 
% 19.23/19.38           (sk_F_1 @ 
% 19.23/19.38            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38            sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38           sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.38        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 19.23/19.38      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 19.23/19.38  thf('74', plain,
% 19.23/19.38      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 19.23/19.38         ((v1_funct_1 @ X9) | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_2])).
% 19.23/19.38  thf('75', plain,
% 19.23/19.38      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.38        | (v1_funct_1 @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.38        | (v1_funct_1 @ 
% 19.23/19.38           (sk_F_1 @ 
% 19.23/19.38            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38            sk_D @ (k1_tarski @ sk_B) @ sk_A)))),
% 19.23/19.38      inference('sup-', [status(thm)], ['73', '74'])).
% 19.23/19.38  thf('76', plain,
% 19.23/19.38      (((v1_funct_1 @ 
% 19.23/19.38         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.38        | (v1_funct_1 @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.38        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.38        | (v1_funct_1 @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.38        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 19.23/19.38      inference('sup+', [status(thm)], ['72', '75'])).
% 19.23/19.38  thf('77', plain,
% 19.23/19.38      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.38        | (v1_funct_1 @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 19.23/19.38      inference('simplify', [status(thm)], ['76'])).
% 19.23/19.38  thf('78', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         ((r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 19.23/19.38          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38          | ((sk_F_1 @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 19.23/19.38              (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.38              = (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 19.23/19.38      inference('sup-', [status(thm)], ['20', '21'])).
% 19.23/19.38  thf('79', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         (((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 19.23/19.38          | (zip_tseitin_0 @ 
% 19.23/19.38             (sk_F_1 @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 19.23/19.38              (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38             (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 19.23/19.38             (k1_tarski @ sk_B) @ sk_A))),
% 19.23/19.38      inference('sup-', [status(thm)], ['13', '19'])).
% 19.23/19.38  thf('80', plain,
% 19.23/19.38      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 19.23/19.38         ((r1_partfun1 @ X8 @ X9)
% 19.23/19.38          | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_2])).
% 19.23/19.38  thf('81', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         ((r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 19.23/19.38          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38          | (r1_partfun1 @ sk_C @ 
% 19.23/19.38             (sk_F_1 @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 19.23/19.38              (k1_tarski @ sk_B) @ sk_A)))),
% 19.23/19.38      inference('sup-', [status(thm)], ['79', '80'])).
% 19.23/19.38  thf('82', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         ((r1_partfun1 @ sk_C @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.38          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 19.23/19.38          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0))),
% 19.23/19.38      inference('sup+', [status(thm)], ['78', '81'])).
% 19.23/19.38  thf('83', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         ((r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 19.23/19.38          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38          | (r1_partfun1 @ sk_C @ 
% 19.23/19.38             (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 19.23/19.38      inference('simplify', [status(thm)], ['82'])).
% 19.23/19.38  thf('84', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_D))
% 19.23/19.38          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.38          | (zip_tseitin_0 @ 
% 19.23/19.38             (sk_F_1 @ X0 @ sk_D @ (k1_tarski @ sk_B) @ sk_A) @ X0 @ sk_D @ 
% 19.23/19.38             (k1_tarski @ sk_B) @ sk_A))),
% 19.23/19.38      inference('sup-', [status(thm)], ['61', '66'])).
% 19.23/19.38  thf('85', plain,
% 19.23/19.38      (((r1_partfun1 @ sk_C @ 
% 19.23/19.38         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.38        | ((k1_tarski @ sk_D)
% 19.23/19.38            = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38        | (zip_tseitin_0 @ 
% 19.23/19.38           (sk_F_1 @ 
% 19.23/19.38            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38            sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38           sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.38        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 19.23/19.38      inference('sup-', [status(thm)], ['83', '84'])).
% 19.23/19.38  thf('86', plain,
% 19.23/19.38      (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C) != (k1_tarski @ sk_D))),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.38  thf('87', plain,
% 19.23/19.38      (((r1_partfun1 @ sk_C @ 
% 19.23/19.38         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.38        | (zip_tseitin_0 @ 
% 19.23/19.38           (sk_F_1 @ 
% 19.23/19.38            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38            sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38           sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.38        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 19.23/19.38      inference('simplify_reflect-', [status(thm)], ['85', '86'])).
% 19.23/19.38  thf('88', plain,
% 19.23/19.38      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 19.23/19.38         (((X9) = (X10)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_2])).
% 19.23/19.38  thf('89', plain,
% 19.23/19.38      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.38        | (r1_partfun1 @ sk_C @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.38        | ((sk_F_1 @ 
% 19.23/19.38            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38            sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.38            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 19.23/19.38      inference('sup-', [status(thm)], ['87', '88'])).
% 19.23/19.38  thf('90', plain,
% 19.23/19.38      (((r1_partfun1 @ sk_C @ 
% 19.23/19.38         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.38        | (zip_tseitin_0 @ 
% 19.23/19.38           (sk_F_1 @ 
% 19.23/19.38            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38            sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38           sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.38        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 19.23/19.38      inference('simplify_reflect-', [status(thm)], ['85', '86'])).
% 19.23/19.38  thf('91', plain,
% 19.23/19.38      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 19.23/19.38         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X11)))
% 19.23/19.38          | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_2])).
% 19.23/19.38  thf('92', plain,
% 19.23/19.38      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.38        | (r1_partfun1 @ sk_C @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.38        | (m1_subset_1 @ 
% 19.23/19.38           (sk_F_1 @ 
% 19.23/19.38            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38            sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))))),
% 19.23/19.38      inference('sup-', [status(thm)], ['90', '91'])).
% 19.23/19.38  thf('93', plain,
% 19.23/19.38      (((m1_subset_1 @ 
% 19.23/19.38         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 19.23/19.38        | (r1_partfun1 @ sk_C @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.38        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.38        | (r1_partfun1 @ sk_C @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.38        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 19.23/19.38      inference('sup+', [status(thm)], ['89', '92'])).
% 19.23/19.38  thf('94', plain,
% 19.23/19.38      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.38        | (r1_partfun1 @ sk_C @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.38        | (m1_subset_1 @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))))),
% 19.23/19.38      inference('simplify', [status(thm)], ['93'])).
% 19.23/19.38  thf('95', plain,
% 19.23/19.38      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 19.23/19.38         (~ (v1_funct_1 @ X23)
% 19.23/19.38          | ~ (m1_subset_1 @ X23 @ 
% 19.23/19.38               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ (k1_tarski @ X25))))
% 19.23/19.38          | (r1_partfun1 @ X26 @ X23)
% 19.23/19.38          | ~ (m1_subset_1 @ X26 @ 
% 19.23/19.38               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ (k1_tarski @ X25))))
% 19.23/19.38          | ~ (v1_funct_1 @ X26))),
% 19.23/19.38      inference('cnf', [status(esa)], [t143_partfun1])).
% 19.23/19.38  thf('96', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         ((r1_partfun1 @ sk_C @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.38          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.38          | ~ (v1_funct_1 @ X0)
% 19.23/19.38          | ~ (m1_subset_1 @ X0 @ 
% 19.23/19.38               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 19.23/19.38          | (r1_partfun1 @ X0 @ 
% 19.23/19.38             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.38          | ~ (v1_funct_1 @ 
% 19.23/19.38               (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 19.23/19.38      inference('sup-', [status(thm)], ['94', '95'])).
% 19.23/19.38  thf('97', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         (((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.38          | (r1_partfun1 @ X0 @ 
% 19.23/19.38             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.38          | ~ (m1_subset_1 @ X0 @ 
% 19.23/19.38               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 19.23/19.38          | ~ (v1_funct_1 @ X0)
% 19.23/19.38          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.38          | (r1_partfun1 @ sk_C @ 
% 19.23/19.38             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 19.23/19.38      inference('sup-', [status(thm)], ['77', '96'])).
% 19.23/19.38  thf('98', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         ((r1_partfun1 @ sk_C @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.38          | ~ (v1_funct_1 @ X0)
% 19.23/19.38          | ~ (m1_subset_1 @ X0 @ 
% 19.23/19.38               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 19.23/19.38          | (r1_partfun1 @ X0 @ 
% 19.23/19.38             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.38          | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 19.23/19.38      inference('simplify', [status(thm)], ['97'])).
% 19.23/19.38  thf('99', plain,
% 19.23/19.38      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.38        | (r1_partfun1 @ sk_C @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.38        | ~ (v1_funct_1 @ sk_C)
% 19.23/19.38        | (r1_partfun1 @ sk_C @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 19.23/19.38      inference('sup-', [status(thm)], ['1', '98'])).
% 19.23/19.38  thf('100', plain, ((v1_funct_1 @ sk_C)),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.38  thf('101', plain,
% 19.23/19.38      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.38        | (r1_partfun1 @ sk_C @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.38        | (r1_partfun1 @ sk_C @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 19.23/19.38      inference('demod', [status(thm)], ['99', '100'])).
% 19.23/19.38  thf('102', plain,
% 19.23/19.38      (((r1_partfun1 @ sk_C @ 
% 19.23/19.38         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.38        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 19.23/19.38      inference('simplify', [status(thm)], ['101'])).
% 19.23/19.38  thf('103', plain,
% 19.23/19.38      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.38        | (v1_funct_1 @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 19.23/19.38      inference('simplify', [status(thm)], ['76'])).
% 19.23/19.38  thf('104', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         ((r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 19.23/19.38          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38          | ((sk_F_1 @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 19.23/19.38              (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.38              = (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 19.23/19.38      inference('sup-', [status(thm)], ['20', '21'])).
% 19.23/19.38  thf('105', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         (((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 19.23/19.38          | (zip_tseitin_0 @ 
% 19.23/19.38             (sk_F_1 @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 19.23/19.38              (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38             (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 19.23/19.38             (k1_tarski @ sk_B) @ sk_A))),
% 19.23/19.38      inference('sup-', [status(thm)], ['13', '19'])).
% 19.23/19.38  thf('106', plain,
% 19.23/19.38      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 19.23/19.38         ((v1_partfun1 @ X9 @ X12)
% 19.23/19.38          | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_2])).
% 19.23/19.38  thf('107', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         ((r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 19.23/19.38          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38          | (v1_partfun1 @ 
% 19.23/19.38             (sk_F_1 @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 19.23/19.38              (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38             sk_A))),
% 19.23/19.38      inference('sup-', [status(thm)], ['105', '106'])).
% 19.23/19.38  thf('108', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         ((v1_partfun1 @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_A)
% 19.23/19.38          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 19.23/19.38          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0))),
% 19.23/19.38      inference('sup+', [status(thm)], ['104', '107'])).
% 19.23/19.38  thf('109', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         ((r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 19.23/19.38          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38          | (v1_partfun1 @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38             sk_A))),
% 19.23/19.38      inference('simplify', [status(thm)], ['108'])).
% 19.23/19.38  thf('110', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_D))
% 19.23/19.38          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.38          | (zip_tseitin_0 @ 
% 19.23/19.38             (sk_F_1 @ X0 @ sk_D @ (k1_tarski @ sk_B) @ sk_A) @ X0 @ sk_D @ 
% 19.23/19.38             (k1_tarski @ sk_B) @ sk_A))),
% 19.23/19.38      inference('sup-', [status(thm)], ['61', '66'])).
% 19.23/19.38  thf('111', plain,
% 19.23/19.38      (((v1_partfun1 @ 
% 19.23/19.38         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_A)
% 19.23/19.38        | ((k1_tarski @ sk_D)
% 19.23/19.38            = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38        | (zip_tseitin_0 @ 
% 19.23/19.38           (sk_F_1 @ 
% 19.23/19.38            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38            sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38           sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.38        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 19.23/19.38      inference('sup-', [status(thm)], ['109', '110'])).
% 19.23/19.38  thf('112', plain,
% 19.23/19.38      (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C) != (k1_tarski @ sk_D))),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.38  thf('113', plain,
% 19.23/19.38      (((v1_partfun1 @ 
% 19.23/19.38         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_A)
% 19.23/19.38        | (zip_tseitin_0 @ 
% 19.23/19.38           (sk_F_1 @ 
% 19.23/19.38            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38            sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38           sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.38        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 19.23/19.38      inference('simplify_reflect-', [status(thm)], ['111', '112'])).
% 19.23/19.38  thf('114', plain,
% 19.23/19.38      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 19.23/19.38         (((X9) = (X10)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_2])).
% 19.23/19.38  thf('115', plain,
% 19.23/19.38      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.38        | (v1_partfun1 @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38           sk_A)
% 19.23/19.38        | ((sk_F_1 @ 
% 19.23/19.38            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38            sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.38            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 19.23/19.38      inference('sup-', [status(thm)], ['113', '114'])).
% 19.23/19.38  thf('116', plain,
% 19.23/19.38      (((v1_partfun1 @ 
% 19.23/19.38         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_A)
% 19.23/19.38        | (zip_tseitin_0 @ 
% 19.23/19.38           (sk_F_1 @ 
% 19.23/19.38            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38            sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38           sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.38        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 19.23/19.38      inference('simplify_reflect-', [status(thm)], ['111', '112'])).
% 19.23/19.38  thf('117', plain,
% 19.23/19.38      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 19.23/19.38         ((v1_partfun1 @ X9 @ X12)
% 19.23/19.38          | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_2])).
% 19.23/19.38  thf('118', plain,
% 19.23/19.38      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.38        | (v1_partfun1 @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38           sk_A)
% 19.23/19.38        | (v1_partfun1 @ 
% 19.23/19.38           (sk_F_1 @ 
% 19.23/19.38            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38            sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38           sk_A))),
% 19.23/19.38      inference('sup-', [status(thm)], ['116', '117'])).
% 19.23/19.38  thf('119', plain,
% 19.23/19.38      (((v1_partfun1 @ 
% 19.23/19.38         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_A)
% 19.23/19.38        | (v1_partfun1 @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38           sk_A)
% 19.23/19.38        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.38        | (v1_partfun1 @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38           sk_A)
% 19.23/19.38        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 19.23/19.38      inference('sup+', [status(thm)], ['115', '118'])).
% 19.23/19.38  thf('120', plain,
% 19.23/19.38      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.38        | (v1_partfun1 @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38           sk_A))),
% 19.23/19.38      inference('simplify', [status(thm)], ['119'])).
% 19.23/19.38  thf('121', plain,
% 19.23/19.38      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.38        | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D)
% 19.23/19.38            = (k1_tarski @ sk_D)))),
% 19.23/19.38      inference('sup-', [status(thm)], ['55', '60'])).
% 19.23/19.38  thf('122', plain,
% 19.23/19.38      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.38        | (v1_funct_1 @ 
% 19.23/19.38           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 19.23/19.38      inference('simplify', [status(thm)], ['76'])).
% 19.23/19.38  thf('123', plain,
% 19.23/19.38      ((m1_subset_1 @ sk_D @ 
% 19.23/19.38        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 19.23/19.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.38  thf('124', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         ((r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 19.23/19.38          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38          | ((sk_F_1 @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 19.23/19.38              (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.38              = (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 19.23/19.38      inference('sup-', [status(thm)], ['20', '21'])).
% 19.23/19.38  thf('125', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         (((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 19.23/19.38          | (zip_tseitin_0 @ 
% 19.23/19.38             (sk_F_1 @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 19.23/19.38              (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38             (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 19.23/19.38             (k1_tarski @ sk_B) @ sk_A))),
% 19.23/19.38      inference('sup-', [status(thm)], ['13', '19'])).
% 19.23/19.38  thf('126', plain,
% 19.23/19.38      (![X0 : $i]:
% 19.23/19.38         ((zip_tseitin_0 @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.38           (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 19.23/19.38           (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.38          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.38          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 19.23/19.38          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 19.23/19.38          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C)))),
% 19.23/19.38      inference('sup+', [status(thm)], ['124', '125'])).
% 19.23/19.39  thf('127', plain,
% 19.23/19.39      (![X0 : $i]:
% 19.23/19.39         ((r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 19.23/19.39          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.39          | (zip_tseitin_0 @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39             (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 19.23/19.39             (k1_tarski @ sk_B) @ sk_A))),
% 19.23/19.39      inference('simplify', [status(thm)], ['126'])).
% 19.23/19.39  thf('128', plain,
% 19.23/19.39      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 19.23/19.39         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X11)))
% 19.23/19.39          | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 19.23/19.39      inference('cnf', [status(esa)], [zf_stmt_2])).
% 19.23/19.39  thf('129', plain,
% 19.23/19.39      (![X0 : $i]:
% 19.23/19.39         (((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.39          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 19.23/19.39          | (m1_subset_1 @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))))),
% 19.23/19.39      inference('sup-', [status(thm)], ['127', '128'])).
% 19.23/19.39  thf('130', plain,
% 19.23/19.39      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 19.23/19.39         (~ (v1_funct_1 @ X23)
% 19.23/19.39          | ~ (m1_subset_1 @ X23 @ 
% 19.23/19.39               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ (k1_tarski @ X25))))
% 19.23/19.39          | (r1_partfun1 @ X26 @ X23)
% 19.23/19.39          | ~ (m1_subset_1 @ X26 @ 
% 19.23/19.39               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ (k1_tarski @ X25))))
% 19.23/19.39          | ~ (v1_funct_1 @ X26))),
% 19.23/19.39      inference('cnf', [status(esa)], [t143_partfun1])).
% 19.23/19.39  thf('131', plain,
% 19.23/19.39      (![X0 : $i, X1 : $i]:
% 19.23/19.39         ((r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 19.23/19.39          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.39          | ~ (v1_funct_1 @ X1)
% 19.23/19.39          | ~ (m1_subset_1 @ X1 @ 
% 19.23/19.39               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 19.23/19.39          | (r1_partfun1 @ X1 @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.39          | ~ (v1_funct_1 @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 19.23/19.39      inference('sup-', [status(thm)], ['129', '130'])).
% 19.23/19.39  thf('132', plain,
% 19.23/19.39      (![X0 : $i]:
% 19.23/19.39         (~ (v1_funct_1 @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.39          | (r1_partfun1 @ sk_D @ 
% 19.23/19.39             (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.39          | ~ (v1_funct_1 @ sk_D)
% 19.23/19.39          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.39          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0))),
% 19.23/19.39      inference('sup-', [status(thm)], ['123', '131'])).
% 19.23/19.39  thf('133', plain, ((v1_funct_1 @ sk_D)),
% 19.23/19.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.39  thf('134', plain,
% 19.23/19.39      (![X0 : $i]:
% 19.23/19.39         (~ (v1_funct_1 @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.39          | (r1_partfun1 @ sk_D @ 
% 19.23/19.39             (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.39          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.39          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0))),
% 19.23/19.39      inference('demod', [status(thm)], ['132', '133'])).
% 19.23/19.39  thf('135', plain,
% 19.23/19.39      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39        | (r2_hidden @ 
% 19.23/19.39           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39           (k1_tarski @ sk_D))
% 19.23/19.39        | ((k1_tarski @ sk_D)
% 19.23/19.39            = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.39        | (r1_partfun1 @ sk_D @ 
% 19.23/19.39           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 19.23/19.39      inference('sup-', [status(thm)], ['122', '134'])).
% 19.23/19.39  thf('136', plain,
% 19.23/19.39      (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C) != (k1_tarski @ sk_D))),
% 19.23/19.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.39  thf('137', plain,
% 19.23/19.39      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39        | (r2_hidden @ 
% 19.23/19.39           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39           (k1_tarski @ sk_D))
% 19.23/19.39        | (r1_partfun1 @ sk_D @ 
% 19.23/19.39           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 19.23/19.39      inference('simplify_reflect-', [status(thm)], ['135', '136'])).
% 19.23/19.39  thf('138', plain,
% 19.23/19.39      (![X0 : $i]:
% 19.23/19.39         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_D))
% 19.23/19.39          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39          | (zip_tseitin_0 @ 
% 19.23/19.39             (sk_F_1 @ X0 @ sk_D @ (k1_tarski @ sk_B) @ sk_A) @ X0 @ sk_D @ 
% 19.23/19.39             (k1_tarski @ sk_B) @ sk_A))),
% 19.23/19.39      inference('sup-', [status(thm)], ['61', '66'])).
% 19.23/19.39  thf('139', plain,
% 19.23/19.39      (((r1_partfun1 @ sk_D @ 
% 19.23/19.39         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.39        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39        | (zip_tseitin_0 @ 
% 19.23/19.39           (sk_F_1 @ 
% 19.23/19.39            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39            sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39           sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.39        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 19.23/19.39      inference('sup-', [status(thm)], ['137', '138'])).
% 19.23/19.39  thf('140', plain,
% 19.23/19.39      (((zip_tseitin_0 @ 
% 19.23/19.39         (sk_F_1 @ 
% 19.23/19.39          (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39          sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39         sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.39        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39        | (r1_partfun1 @ sk_D @ 
% 19.23/19.39           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 19.23/19.39      inference('simplify', [status(thm)], ['139'])).
% 19.23/19.39  thf('141', plain,
% 19.23/19.39      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 19.23/19.39         (((X9) = (X10)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 19.23/19.39      inference('cnf', [status(esa)], [zf_stmt_2])).
% 19.23/19.39  thf('142', plain,
% 19.23/19.39      (((r1_partfun1 @ sk_D @ 
% 19.23/19.39         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.39        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39        | ((sk_F_1 @ 
% 19.23/19.39            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39            sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.39            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 19.23/19.39      inference('sup-', [status(thm)], ['140', '141'])).
% 19.23/19.39  thf('143', plain,
% 19.23/19.39      (((zip_tseitin_0 @ 
% 19.23/19.39         (sk_F_1 @ 
% 19.23/19.39          (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39          sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39         sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.39        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39        | (r1_partfun1 @ sk_D @ 
% 19.23/19.39           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 19.23/19.39      inference('simplify', [status(thm)], ['139'])).
% 19.23/19.39  thf('144', plain,
% 19.23/19.39      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 19.23/19.39         ((r1_partfun1 @ X8 @ X9)
% 19.23/19.39          | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 19.23/19.39      inference('cnf', [status(esa)], [zf_stmt_2])).
% 19.23/19.39  thf('145', plain,
% 19.23/19.39      (((r1_partfun1 @ sk_D @ 
% 19.23/19.39         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.39        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39        | (r1_partfun1 @ sk_D @ 
% 19.23/19.39           (sk_F_1 @ 
% 19.23/19.39            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39            sk_D @ (k1_tarski @ sk_B) @ sk_A)))),
% 19.23/19.39      inference('sup-', [status(thm)], ['143', '144'])).
% 19.23/19.39  thf('146', plain,
% 19.23/19.39      (((r1_partfun1 @ sk_D @ 
% 19.23/19.39         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.39        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39        | (r1_partfun1 @ sk_D @ 
% 19.23/19.39           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.39        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39        | (r1_partfun1 @ sk_D @ 
% 19.23/19.39           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 19.23/19.39      inference('sup+', [status(thm)], ['142', '145'])).
% 19.23/19.39  thf('147', plain,
% 19.23/19.39      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39        | (r1_partfun1 @ sk_D @ 
% 19.23/19.39           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 19.23/19.39      inference('simplify', [status(thm)], ['146'])).
% 19.23/19.39  thf('148', plain,
% 19.23/19.39      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39        | (v1_funct_1 @ 
% 19.23/19.39           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 19.23/19.39      inference('simplify', [status(thm)], ['76'])).
% 19.23/19.39  thf('149', plain,
% 19.23/19.39      (![X0 : $i]:
% 19.23/19.39         ((r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 19.23/19.39          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.39          | (v1_partfun1 @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39             sk_A))),
% 19.23/19.39      inference('simplify', [status(thm)], ['108'])).
% 19.23/19.39  thf('150', plain,
% 19.23/19.39      (![X0 : $i]:
% 19.23/19.39         (((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.39          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 19.23/19.39          | (m1_subset_1 @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))))),
% 19.23/19.39      inference('sup-', [status(thm)], ['127', '128'])).
% 19.23/19.39  thf('151', plain,
% 19.23/19.39      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X13 : $i]:
% 19.23/19.39         ((zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X13)
% 19.23/19.39          | ~ (v1_funct_1 @ X9)
% 19.23/19.39          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X11)))
% 19.23/19.39          | ((X9) != (X10))
% 19.23/19.39          | ~ (v1_partfun1 @ X9 @ X13)
% 19.23/19.39          | ~ (r1_partfun1 @ X8 @ X9))),
% 19.23/19.39      inference('cnf', [status(esa)], [zf_stmt_2])).
% 19.23/19.39  thf('152', plain,
% 19.23/19.39      (![X8 : $i, X10 : $i, X11 : $i, X13 : $i]:
% 19.23/19.39         (~ (r1_partfun1 @ X8 @ X10)
% 19.23/19.39          | ~ (v1_partfun1 @ X10 @ X13)
% 19.23/19.39          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X11)))
% 19.23/19.39          | ~ (v1_funct_1 @ X10)
% 19.23/19.39          | (zip_tseitin_0 @ X10 @ X10 @ X8 @ X11 @ X13))),
% 19.23/19.39      inference('simplify', [status(thm)], ['151'])).
% 19.23/19.39  thf('153', plain,
% 19.23/19.39      (![X0 : $i, X1 : $i]:
% 19.23/19.39         ((r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 19.23/19.39          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.39          | (zip_tseitin_0 @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39             (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X1 @ 
% 19.23/19.39             (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.39          | ~ (v1_funct_1 @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.39          | ~ (v1_partfun1 @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39               sk_A)
% 19.23/19.39          | ~ (r1_partfun1 @ X1 @ 
% 19.23/19.39               (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 19.23/19.39      inference('sup-', [status(thm)], ['150', '152'])).
% 19.23/19.39  thf('154', plain,
% 19.23/19.39      (![X0 : $i, X1 : $i]:
% 19.23/19.39         (((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.39          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 19.23/19.39          | ~ (r1_partfun1 @ X1 @ 
% 19.23/19.39               (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.39          | ~ (v1_funct_1 @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.39          | (zip_tseitin_0 @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39             (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X1 @ 
% 19.23/19.39             (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.39          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.39          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0))),
% 19.23/19.39      inference('sup-', [status(thm)], ['149', '153'])).
% 19.23/19.39  thf('155', plain,
% 19.23/19.39      (![X0 : $i, X1 : $i]:
% 19.23/19.39         ((zip_tseitin_0 @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39           (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X1 @ 
% 19.23/19.39           (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.39          | ~ (v1_funct_1 @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.39          | ~ (r1_partfun1 @ X1 @ 
% 19.23/19.39               (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.39          | (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0)
% 19.23/19.39          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C)))),
% 19.23/19.39      inference('simplify', [status(thm)], ['154'])).
% 19.23/19.39  thf('156', plain,
% 19.23/19.39      (![X0 : $i]:
% 19.23/19.39         (((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39          | ((k1_tarski @ sk_D)
% 19.23/19.39              = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.39          | (r2_hidden @ 
% 19.23/19.39             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39             (k1_tarski @ sk_D))
% 19.23/19.39          | ~ (r1_partfun1 @ X0 @ 
% 19.23/19.39               (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.39          | (zip_tseitin_0 @ 
% 19.23/19.39             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39             X0 @ (k1_tarski @ sk_B) @ sk_A))),
% 19.23/19.39      inference('sup-', [status(thm)], ['148', '155'])).
% 19.23/19.39  thf('157', plain,
% 19.23/19.39      (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C) != (k1_tarski @ sk_D))),
% 19.23/19.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.39  thf('158', plain,
% 19.23/19.39      (![X0 : $i]:
% 19.23/19.39         (((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39          | (r2_hidden @ 
% 19.23/19.39             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39             (k1_tarski @ sk_D))
% 19.23/19.39          | ~ (r1_partfun1 @ X0 @ 
% 19.23/19.39               (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.39          | (zip_tseitin_0 @ 
% 19.23/19.39             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39             X0 @ (k1_tarski @ sk_B) @ sk_A))),
% 19.23/19.39      inference('simplify_reflect-', [status(thm)], ['156', '157'])).
% 19.23/19.39  thf('159', plain,
% 19.23/19.39      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39        | (zip_tseitin_0 @ 
% 19.23/19.39           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39           sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.39        | (r2_hidden @ 
% 19.23/19.39           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39           (k1_tarski @ sk_D))
% 19.23/19.39        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 19.23/19.39      inference('sup-', [status(thm)], ['147', '158'])).
% 19.23/19.39  thf('160', plain,
% 19.23/19.39      (((r2_hidden @ 
% 19.23/19.39         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39         (k1_tarski @ sk_D))
% 19.23/19.39        | (zip_tseitin_0 @ 
% 19.23/19.39           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39           sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.39        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 19.23/19.39      inference('simplify', [status(thm)], ['159'])).
% 19.23/19.39  thf('161', plain,
% 19.23/19.39      ((m1_subset_1 @ sk_D @ 
% 19.23/19.39        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 19.23/19.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.39  thf('162', plain,
% 19.23/19.39      (![X15 : $i, X16 : $i, X17 : $i, X21 : $i, X22 : $i]:
% 19.23/19.39         (~ (v1_funct_1 @ X15)
% 19.23/19.39          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 19.23/19.39          | ~ (zip_tseitin_0 @ X22 @ X21 @ X15 @ X16 @ X17)
% 19.23/19.39          | (r2_hidden @ X21 @ (k5_partfun1 @ X17 @ X16 @ X15)))),
% 19.23/19.39      inference('simplify', [status(thm)], ['8'])).
% 19.23/19.39  thf('163', plain,
% 19.23/19.39      (![X0 : $i, X1 : $i]:
% 19.23/19.39         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D))
% 19.23/19.39          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.39          | ~ (v1_funct_1 @ sk_D))),
% 19.23/19.39      inference('sup-', [status(thm)], ['161', '162'])).
% 19.23/19.39  thf('164', plain, ((v1_funct_1 @ sk_D)),
% 19.23/19.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.39  thf('165', plain,
% 19.23/19.39      (![X0 : $i, X1 : $i]:
% 19.23/19.39         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D))
% 19.23/19.39          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_D @ (k1_tarski @ sk_B) @ sk_A))),
% 19.23/19.39      inference('demod', [status(thm)], ['163', '164'])).
% 19.23/19.39  thf('166', plain,
% 19.23/19.39      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39        | (r2_hidden @ 
% 19.23/19.39           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39           (k1_tarski @ sk_D))
% 19.23/19.39        | (r2_hidden @ 
% 19.23/19.39           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39           (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D)))),
% 19.23/19.39      inference('sup-', [status(thm)], ['160', '165'])).
% 19.23/19.39  thf('167', plain,
% 19.23/19.39      (((r2_hidden @ 
% 19.23/19.39         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39         (k1_tarski @ sk_D))
% 19.23/19.39        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39        | (r2_hidden @ 
% 19.23/19.39           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39           (k1_tarski @ sk_D))
% 19.23/19.39        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 19.23/19.39      inference('sup+', [status(thm)], ['121', '166'])).
% 19.23/19.39  thf('168', plain,
% 19.23/19.39      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39        | (r2_hidden @ 
% 19.23/19.39           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39           (k1_tarski @ sk_D)))),
% 19.23/19.39      inference('simplify', [status(thm)], ['167'])).
% 19.23/19.39  thf('169', plain,
% 19.23/19.39      (![X0 : $i]:
% 19.23/19.39         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_D))
% 19.23/19.39          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39          | (zip_tseitin_0 @ 
% 19.23/19.39             (sk_F_1 @ X0 @ sk_D @ (k1_tarski @ sk_B) @ sk_A) @ X0 @ sk_D @ 
% 19.23/19.39             (k1_tarski @ sk_B) @ sk_A))),
% 19.23/19.39      inference('sup-', [status(thm)], ['61', '66'])).
% 19.23/19.39  thf('170', plain,
% 19.23/19.39      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39        | (zip_tseitin_0 @ 
% 19.23/19.39           (sk_F_1 @ 
% 19.23/19.39            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39            sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39           sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.39        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 19.23/19.39      inference('sup-', [status(thm)], ['168', '169'])).
% 19.23/19.39  thf('171', plain,
% 19.23/19.39      (((zip_tseitin_0 @ 
% 19.23/19.39         (sk_F_1 @ 
% 19.23/19.39          (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39          sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39         sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.39        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 19.23/19.39      inference('simplify', [status(thm)], ['170'])).
% 19.23/19.39  thf('172', plain,
% 19.23/19.39      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 19.23/19.39         (((X9) = (X10)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 19.23/19.39      inference('cnf', [status(esa)], [zf_stmt_2])).
% 19.23/19.39  thf('173', plain,
% 19.23/19.39      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39        | ((sk_F_1 @ 
% 19.23/19.39            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39            sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.39            = (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 19.23/19.39      inference('sup-', [status(thm)], ['171', '172'])).
% 19.23/19.39  thf('174', plain,
% 19.23/19.39      (((zip_tseitin_0 @ 
% 19.23/19.39         (sk_F_1 @ 
% 19.23/19.39          (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39          sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39         sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.39        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 19.23/19.39      inference('simplify', [status(thm)], ['170'])).
% 19.23/19.39  thf('175', plain,
% 19.23/19.39      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 19.23/19.39         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X11)))
% 19.23/19.39          | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X12))),
% 19.23/19.39      inference('cnf', [status(esa)], [zf_stmt_2])).
% 19.23/19.39  thf('176', plain,
% 19.23/19.39      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39        | (m1_subset_1 @ 
% 19.23/19.39           (sk_F_1 @ 
% 19.23/19.39            (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39            sk_D @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))))),
% 19.23/19.39      inference('sup-', [status(thm)], ['174', '175'])).
% 19.23/19.39  thf('177', plain,
% 19.23/19.39      (((m1_subset_1 @ 
% 19.23/19.39         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 19.23/19.39        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 19.23/19.39      inference('sup+', [status(thm)], ['173', '176'])).
% 19.23/19.39  thf('178', plain,
% 19.23/19.39      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39        | (m1_subset_1 @ 
% 19.23/19.39           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))))),
% 19.23/19.39      inference('simplify', [status(thm)], ['177'])).
% 19.23/19.39  thf('179', plain,
% 19.23/19.39      (![X8 : $i, X10 : $i, X11 : $i, X13 : $i]:
% 19.23/19.39         (~ (r1_partfun1 @ X8 @ X10)
% 19.23/19.39          | ~ (v1_partfun1 @ X10 @ X13)
% 19.23/19.39          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X11)))
% 19.23/19.39          | ~ (v1_funct_1 @ X10)
% 19.23/19.39          | (zip_tseitin_0 @ X10 @ X10 @ X8 @ X11 @ X13))),
% 19.23/19.39      inference('simplify', [status(thm)], ['151'])).
% 19.23/19.39  thf('180', plain,
% 19.23/19.39      (![X0 : $i]:
% 19.23/19.39         (((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39          | (zip_tseitin_0 @ 
% 19.23/19.39             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39             X0 @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.39          | ~ (v1_funct_1 @ 
% 19.23/19.39               (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.39          | ~ (v1_partfun1 @ 
% 19.23/19.39               (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39               sk_A)
% 19.23/19.39          | ~ (r1_partfun1 @ X0 @ 
% 19.23/19.39               (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A)))),
% 19.23/19.39      inference('sup-', [status(thm)], ['178', '179'])).
% 19.23/19.39  thf('181', plain,
% 19.23/19.39      (![X0 : $i]:
% 19.23/19.39         (((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39          | ~ (r1_partfun1 @ X0 @ 
% 19.23/19.39               (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.39          | ~ (v1_funct_1 @ 
% 19.23/19.39               (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.39          | (zip_tseitin_0 @ 
% 19.23/19.39             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39             X0 @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.39          | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 19.23/19.39      inference('sup-', [status(thm)], ['120', '180'])).
% 19.23/19.39  thf('182', plain,
% 19.23/19.39      (![X0 : $i]:
% 19.23/19.39         ((zip_tseitin_0 @ 
% 19.23/19.39           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39           X0 @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.39          | ~ (v1_funct_1 @ 
% 19.23/19.39               (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.39          | ~ (r1_partfun1 @ X0 @ 
% 19.23/19.39               (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.39          | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 19.23/19.39      inference('simplify', [status(thm)], ['181'])).
% 19.23/19.39  thf('183', plain,
% 19.23/19.39      (![X0 : $i]:
% 19.23/19.39         (((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39          | ~ (r1_partfun1 @ X0 @ 
% 19.23/19.39               (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.39          | (zip_tseitin_0 @ 
% 19.23/19.39             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39             X0 @ (k1_tarski @ sk_B) @ sk_A))),
% 19.23/19.39      inference('sup-', [status(thm)], ['103', '182'])).
% 19.23/19.39  thf('184', plain,
% 19.23/19.39      (![X0 : $i]:
% 19.23/19.39         ((zip_tseitin_0 @ 
% 19.23/19.39           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39           X0 @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.39          | ~ (r1_partfun1 @ X0 @ 
% 19.23/19.39               (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A))
% 19.23/19.39          | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 19.23/19.39      inference('simplify', [status(thm)], ['183'])).
% 19.23/19.39  thf('185', plain,
% 19.23/19.39      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39        | (zip_tseitin_0 @ 
% 19.23/19.39           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39           sk_C @ (k1_tarski @ sk_B) @ sk_A))),
% 19.23/19.39      inference('sup-', [status(thm)], ['102', '184'])).
% 19.23/19.39  thf('186', plain,
% 19.23/19.39      (((zip_tseitin_0 @ 
% 19.23/19.39         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39         (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39         sk_C @ (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.39        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 19.23/19.39      inference('simplify', [status(thm)], ['185'])).
% 19.23/19.39  thf('187', plain,
% 19.23/19.39      ((m1_subset_1 @ sk_C @ 
% 19.23/19.39        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 19.23/19.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.39  thf('188', plain,
% 19.23/19.39      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 19.23/19.39         (~ (r2_hidden @ (sk_E @ X14 @ X15 @ X16 @ X17) @ X14)
% 19.23/19.39          | ~ (zip_tseitin_0 @ X18 @ (sk_E @ X14 @ X15 @ X16 @ X17) @ X15 @ 
% 19.23/19.39               X16 @ X17)
% 19.23/19.39          | ((X14) = (k5_partfun1 @ X17 @ X16 @ X15))
% 19.23/19.39          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 19.23/19.39          | ~ (v1_funct_1 @ X15))),
% 19.23/19.39      inference('cnf', [status(esa)], [zf_stmt_3])).
% 19.23/19.39  thf('189', plain,
% 19.23/19.39      (![X0 : $i, X1 : $i]:
% 19.23/19.39         (~ (v1_funct_1 @ sk_C)
% 19.23/19.39          | ((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.39          | ~ (zip_tseitin_0 @ X1 @ 
% 19.23/19.39               (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 19.23/19.39               (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.39          | ~ (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0))),
% 19.23/19.39      inference('sup-', [status(thm)], ['187', '188'])).
% 19.23/19.39  thf('190', plain, ((v1_funct_1 @ sk_C)),
% 19.23/19.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.39  thf('191', plain,
% 19.23/19.39      (![X0 : $i, X1 : $i]:
% 19.23/19.39         (((X0) = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C))
% 19.23/19.39          | ~ (zip_tseitin_0 @ X1 @ 
% 19.23/19.39               (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ sk_C @ 
% 19.23/19.39               (k1_tarski @ sk_B) @ sk_A)
% 19.23/19.39          | ~ (r2_hidden @ (sk_E @ X0 @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ X0))),
% 19.23/19.39      inference('demod', [status(thm)], ['189', '190'])).
% 19.23/19.39  thf('192', plain,
% 19.23/19.39      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39        | ~ (r2_hidden @ 
% 19.23/19.39             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39             (k1_tarski @ sk_D))
% 19.23/19.39        | ((k1_tarski @ sk_D)
% 19.23/19.39            = (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C)))),
% 19.23/19.39      inference('sup-', [status(thm)], ['186', '191'])).
% 19.23/19.39  thf('193', plain,
% 19.23/19.39      (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C) != (k1_tarski @ sk_D))),
% 19.23/19.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.23/19.39  thf('194', plain,
% 19.23/19.39      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39        | ~ (r2_hidden @ 
% 19.23/19.39             (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39             (k1_tarski @ sk_D)))),
% 19.23/19.39      inference('simplify_reflect-', [status(thm)], ['192', '193'])).
% 19.23/19.39  thf('195', plain,
% 19.23/19.39      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 19.23/19.39        | (r2_hidden @ 
% 19.23/19.39           (sk_E @ (k1_tarski @ sk_D) @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 19.23/19.39           (k1_tarski @ sk_D)))),
% 19.23/19.39      inference('simplify', [status(thm)], ['167'])).
% 19.23/19.39  thf('196', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 19.23/19.39      inference('clc', [status(thm)], ['194', '195'])).
% 19.23/19.39  thf('197', plain,
% 19.23/19.39      (((k5_partfun1 @ sk_A @ k1_xboole_0 @ sk_C) != (k1_tarski @ sk_D))),
% 19.23/19.39      inference('demod', [status(thm)], ['0', '196'])).
% 19.23/19.39  thf('198', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 19.23/19.39      inference('clc', [status(thm)], ['194', '195'])).
% 19.23/19.39  thf(t130_zfmisc_1, axiom,
% 19.23/19.39    (![A:$i,B:$i]:
% 19.23/19.39     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 19.23/19.39       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 19.23/19.39         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 19.23/19.39  thf('199', plain,
% 19.23/19.39      (![X6 : $i, X7 : $i]:
% 19.23/19.39         (((X6) = (k1_xboole_0))
% 19.23/19.39          | ((k2_zfmisc_1 @ (k1_tarski @ X7) @ X6) != (k1_xboole_0)))),
% 19.23/19.39      inference('cnf', [status(esa)], [t130_zfmisc_1])).
% 19.23/19.39  thf('200', plain,
% 19.23/19.39      (![X0 : $i]:
% 19.23/19.39         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 19.23/19.39          | ((X0) = (k1_xboole_0)))),
% 19.23/19.39      inference('sup-', [status(thm)], ['198', '199'])).
% 19.23/19.39  thf(t113_zfmisc_1, axiom,
% 19.23/19.39    (![A:$i,B:$i]:
% 19.23/19.39     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 19.23/19.39       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 19.23/19.39  thf('201', plain,
% 19.23/19.39      (![X4 : $i, X5 : $i]:
% 19.23/19.39         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 19.23/19.39      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 19.23/19.39  thf('202', plain,
% 19.23/19.39      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 19.23/19.39      inference('simplify', [status(thm)], ['201'])).
% 19.23/19.39  thf('203', plain,
% 19.23/19.39      (![X0 : $i]: (((k1_xboole_0) != (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 19.23/19.39      inference('demod', [status(thm)], ['200', '202'])).
% 19.23/19.39  thf('204', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 19.23/19.39      inference('simplify', [status(thm)], ['203'])).
% 19.23/19.39  thf('205', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 19.23/19.39      inference('simplify', [status(thm)], ['203'])).
% 19.23/19.39  thf('206', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 19.23/19.39      inference('simplify', [status(thm)], ['203'])).
% 19.23/19.39  thf('207', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 19.23/19.39      inference('simplify', [status(thm)], ['203'])).
% 19.23/19.39  thf(t69_enumset1, axiom,
% 19.23/19.39    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 19.23/19.39  thf('208', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 19.23/19.39      inference('cnf', [status(esa)], [t69_enumset1])).
% 19.23/19.39  thf('209', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 19.23/19.39      inference('simplify', [status(thm)], ['203'])).
% 19.23/19.39  thf('210', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 19.23/19.39      inference('demod', [status(thm)],
% 19.23/19.39                ['197', '204', '205', '206', '207', '208', '209'])).
% 19.23/19.39  thf('211', plain, ($false), inference('simplify', [status(thm)], ['210'])).
% 19.23/19.39  
% 19.23/19.39  % SZS output end Refutation
% 19.23/19.39  
% 19.23/19.39  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
