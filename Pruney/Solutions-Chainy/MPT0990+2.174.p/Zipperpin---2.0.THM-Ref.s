%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fxyF5pry0c

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:25 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 182 expanded)
%              Number of leaves         :   43 (  74 expanded)
%              Depth                    :   13
%              Number of atoms          : 1107 (3778 expanded)
%              Number of equality atoms :   77 ( 277 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t36_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ C )
                = B )
              & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( v2_funct_1 @ C ) )
           => ( ( A = k1_xboole_0 )
              | ( B = k1_xboole_0 )
              | ( D
                = ( k2_funct_1 @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ B @ C )
                  = B )
                & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
                & ( v2_funct_1 @ C ) )
             => ( ( A = k1_xboole_0 )
                | ( B = k1_xboole_0 )
                | ( D
                  = ( k2_funct_1 @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_funct_2])).

thf('0',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('3',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 )
        = ( k5_relat_1 @ X37 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X7 @ X8 @ X10 @ X11 @ X6 @ X9 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( ( k4_relset_1 @ X19 @ X20 @ X22 @ X23 @ X18 @ X21 )
        = ( k5_relat_1 @ X18 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('22',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( X24 = X27 )
      | ~ ( r2_relset_1 @ X25 @ X26 @ X24 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','23'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('25',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('26',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('27',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','27'])).

thf(t63_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ( ( k5_relat_1 @ A @ B )
                = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('29',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( X4
        = ( k2_funct_1 @ X5 ) )
      | ( ( k5_relat_1 @ X5 @ X4 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X5 ) ) )
      | ( ( k2_relat_1 @ X5 )
       != ( k1_relat_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('30',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('31',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( X4
        = ( k2_funct_1 @ X5 ) )
      | ( ( k5_relat_1 @ X5 @ X4 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X5 ) ) )
      | ( ( k2_relat_1 @ X5 )
       != ( k1_relat_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
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

thf('34',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('35',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('36',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('38',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('39',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('44',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('45',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['35','42','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('50',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('55',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('56',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('61',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('63',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('65',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('71',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['61','68','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('76',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('78',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ( sk_B != sk_B )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['32','46','51','52','53','58','72','73','78'])).

thf('80',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['80','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fxyF5pry0c
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:51:23 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.69/0.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.69/0.91  % Solved by: fo/fo7.sh
% 0.69/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.91  % done 291 iterations in 0.467s
% 0.69/0.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.69/0.91  % SZS output start Refutation
% 0.69/0.91  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.69/0.91  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.69/0.91  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.69/0.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.69/0.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.69/0.91  thf(sk_C_type, type, sk_C: $i).
% 0.69/0.91  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.69/0.91  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.91  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.69/0.91  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.69/0.91  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.69/0.91  thf(sk_D_type, type, sk_D: $i).
% 0.69/0.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.91  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 0.69/0.91  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.69/0.91  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.69/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.91  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.69/0.91  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.69/0.91  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.69/0.91  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.69/0.91  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.69/0.91  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.69/0.91  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.69/0.91  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.69/0.91  thf(t36_funct_2, conjecture,
% 0.69/0.91    (![A:$i,B:$i,C:$i]:
% 0.69/0.91     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.69/0.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.69/0.91       ( ![D:$i]:
% 0.69/0.91         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.69/0.91             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.69/0.91           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.69/0.91               ( r2_relset_1 @
% 0.69/0.91                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.69/0.91                 ( k6_partfun1 @ A ) ) & 
% 0.69/0.91               ( v2_funct_1 @ C ) ) =>
% 0.69/0.91             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.69/0.91               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.69/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.91    (~( ![A:$i,B:$i,C:$i]:
% 0.69/0.91        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.69/0.91            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.69/0.91          ( ![D:$i]:
% 0.69/0.91            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.69/0.91                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.69/0.91              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.69/0.91                  ( r2_relset_1 @
% 0.69/0.91                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.69/0.91                    ( k6_partfun1 @ A ) ) & 
% 0.69/0.91                  ( v2_funct_1 @ C ) ) =>
% 0.69/0.91                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.69/0.91                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.69/0.91    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.69/0.91  thf('0', plain,
% 0.69/0.91      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.69/0.91        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.69/0.91        (k6_partfun1 @ sk_A))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('1', plain,
% 0.69/0.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('2', plain,
% 0.69/0.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf(redefinition_k1_partfun1, axiom,
% 0.69/0.91    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.69/0.91     ( ( ( v1_funct_1 @ E ) & 
% 0.69/0.91         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.69/0.91         ( v1_funct_1 @ F ) & 
% 0.69/0.91         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.69/0.91       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.69/0.91  thf('3', plain,
% 0.69/0.91      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.69/0.91         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.69/0.91          | ~ (v1_funct_1 @ X37)
% 0.69/0.91          | ~ (v1_funct_1 @ X40)
% 0.69/0.91          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.69/0.91          | ((k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40)
% 0.69/0.91              = (k5_relat_1 @ X37 @ X40)))),
% 0.69/0.91      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.69/0.91  thf('4', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.91         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.69/0.91            = (k5_relat_1 @ sk_C @ X0))
% 0.69/0.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.69/0.91          | ~ (v1_funct_1 @ X0)
% 0.69/0.91          | ~ (v1_funct_1 @ sk_C))),
% 0.69/0.91      inference('sup-', [status(thm)], ['2', '3'])).
% 0.69/0.91  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('6', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.91         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.69/0.91            = (k5_relat_1 @ sk_C @ X0))
% 0.69/0.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.69/0.91          | ~ (v1_funct_1 @ X0))),
% 0.69/0.91      inference('demod', [status(thm)], ['4', '5'])).
% 0.69/0.91  thf('7', plain,
% 0.69/0.91      ((~ (v1_funct_1 @ sk_D)
% 0.69/0.91        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.69/0.91            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['1', '6'])).
% 0.69/0.91  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('9', plain,
% 0.69/0.91      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.69/0.91         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.69/0.91      inference('demod', [status(thm)], ['7', '8'])).
% 0.69/0.91  thf('10', plain,
% 0.69/0.91      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.69/0.91        (k6_partfun1 @ sk_A))),
% 0.69/0.91      inference('demod', [status(thm)], ['0', '9'])).
% 0.69/0.91  thf('11', plain,
% 0.69/0.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('12', plain,
% 0.69/0.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf(dt_k4_relset_1, axiom,
% 0.69/0.91    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.69/0.91     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.69/0.91         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.69/0.91       ( m1_subset_1 @
% 0.69/0.91         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.69/0.91         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 0.69/0.91  thf('13', plain,
% 0.69/0.91      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.69/0.91         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.69/0.91          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.69/0.91          | (m1_subset_1 @ (k4_relset_1 @ X7 @ X8 @ X10 @ X11 @ X6 @ X9) @ 
% 0.69/0.91             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X11))))),
% 0.69/0.91      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 0.69/0.91  thf('14', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.91         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.69/0.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.69/0.91          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 0.69/0.91      inference('sup-', [status(thm)], ['12', '13'])).
% 0.69/0.91  thf('15', plain,
% 0.69/0.91      ((m1_subset_1 @ 
% 0.69/0.91        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.69/0.91        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['11', '14'])).
% 0.69/0.91  thf('16', plain,
% 0.69/0.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('17', plain,
% 0.69/0.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf(redefinition_k4_relset_1, axiom,
% 0.69/0.91    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.69/0.91     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.69/0.91         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.69/0.91       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.69/0.91  thf('18', plain,
% 0.69/0.91      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.69/0.91         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.69/0.91          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.69/0.91          | ((k4_relset_1 @ X19 @ X20 @ X22 @ X23 @ X18 @ X21)
% 0.69/0.91              = (k5_relat_1 @ X18 @ X21)))),
% 0.69/0.91      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.69/0.91  thf('19', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.91         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.69/0.91            = (k5_relat_1 @ sk_C @ X0))
% 0.69/0.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.69/0.91      inference('sup-', [status(thm)], ['17', '18'])).
% 0.69/0.91  thf('20', plain,
% 0.69/0.91      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.69/0.91         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.69/0.91      inference('sup-', [status(thm)], ['16', '19'])).
% 0.69/0.91  thf('21', plain,
% 0.69/0.91      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.69/0.91        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.69/0.91      inference('demod', [status(thm)], ['15', '20'])).
% 0.69/0.91  thf(redefinition_r2_relset_1, axiom,
% 0.69/0.91    (![A:$i,B:$i,C:$i,D:$i]:
% 0.69/0.91     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.69/0.91         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.69/0.91       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.69/0.91  thf('22', plain,
% 0.69/0.91      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.69/0.91         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.69/0.91          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.69/0.91          | ((X24) = (X27))
% 0.69/0.91          | ~ (r2_relset_1 @ X25 @ X26 @ X24 @ X27))),
% 0.69/0.91      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.69/0.91  thf('23', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.69/0.91          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.69/0.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.69/0.91      inference('sup-', [status(thm)], ['21', '22'])).
% 0.69/0.91  thf('24', plain,
% 0.69/0.91      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.69/0.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.69/0.91        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['10', '23'])).
% 0.69/0.91  thf(t29_relset_1, axiom,
% 0.69/0.91    (![A:$i]:
% 0.69/0.91     ( m1_subset_1 @
% 0.69/0.91       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.69/0.91  thf('25', plain,
% 0.69/0.91      (![X28 : $i]:
% 0.69/0.91         (m1_subset_1 @ (k6_relat_1 @ X28) @ 
% 0.69/0.91          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 0.69/0.91      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.69/0.91  thf(redefinition_k6_partfun1, axiom,
% 0.69/0.91    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.69/0.91  thf('26', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 0.69/0.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.69/0.91  thf('27', plain,
% 0.69/0.91      (![X28 : $i]:
% 0.69/0.91         (m1_subset_1 @ (k6_partfun1 @ X28) @ 
% 0.69/0.91          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 0.69/0.91      inference('demod', [status(thm)], ['25', '26'])).
% 0.69/0.91  thf('28', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.69/0.91      inference('demod', [status(thm)], ['24', '27'])).
% 0.69/0.91  thf(t63_funct_1, axiom,
% 0.69/0.91    (![A:$i]:
% 0.69/0.91     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.69/0.91       ( ![B:$i]:
% 0.69/0.91         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.69/0.91           ( ( ( v2_funct_1 @ A ) & 
% 0.69/0.91               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.69/0.91               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.69/0.91             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.69/0.91  thf('29', plain,
% 0.69/0.91      (![X4 : $i, X5 : $i]:
% 0.69/0.91         (~ (v1_relat_1 @ X4)
% 0.69/0.91          | ~ (v1_funct_1 @ X4)
% 0.69/0.91          | ((X4) = (k2_funct_1 @ X5))
% 0.69/0.91          | ((k5_relat_1 @ X5 @ X4) != (k6_relat_1 @ (k1_relat_1 @ X5)))
% 0.69/0.91          | ((k2_relat_1 @ X5) != (k1_relat_1 @ X4))
% 0.69/0.91          | ~ (v2_funct_1 @ X5)
% 0.69/0.91          | ~ (v1_funct_1 @ X5)
% 0.69/0.91          | ~ (v1_relat_1 @ X5))),
% 0.69/0.91      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.69/0.91  thf('30', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 0.69/0.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.69/0.91  thf('31', plain,
% 0.69/0.91      (![X4 : $i, X5 : $i]:
% 0.69/0.91         (~ (v1_relat_1 @ X4)
% 0.69/0.91          | ~ (v1_funct_1 @ X4)
% 0.69/0.91          | ((X4) = (k2_funct_1 @ X5))
% 0.69/0.91          | ((k5_relat_1 @ X5 @ X4) != (k6_partfun1 @ (k1_relat_1 @ X5)))
% 0.69/0.91          | ((k2_relat_1 @ X5) != (k1_relat_1 @ X4))
% 0.69/0.91          | ~ (v2_funct_1 @ X5)
% 0.69/0.91          | ~ (v1_funct_1 @ X5)
% 0.69/0.91          | ~ (v1_relat_1 @ X5))),
% 0.69/0.91      inference('demod', [status(thm)], ['29', '30'])).
% 0.69/0.91  thf('32', plain,
% 0.69/0.91      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 0.69/0.91        | ~ (v1_relat_1 @ sk_C)
% 0.69/0.91        | ~ (v1_funct_1 @ sk_C)
% 0.69/0.91        | ~ (v2_funct_1 @ sk_C)
% 0.69/0.91        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.69/0.91        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.69/0.91        | ~ (v1_funct_1 @ sk_D)
% 0.69/0.91        | ~ (v1_relat_1 @ sk_D))),
% 0.69/0.91      inference('sup-', [status(thm)], ['28', '31'])).
% 0.69/0.91  thf('33', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf(d1_funct_2, axiom,
% 0.69/0.91    (![A:$i,B:$i,C:$i]:
% 0.69/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.91       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.69/0.91           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.69/0.91             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.69/0.91         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.69/0.91           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.69/0.91             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.69/0.91  thf(zf_stmt_1, axiom,
% 0.69/0.91    (![C:$i,B:$i,A:$i]:
% 0.69/0.91     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.69/0.91       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.69/0.91  thf('34', plain,
% 0.69/0.91      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.69/0.91         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 0.69/0.91          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 0.69/0.91          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.69/0.91  thf('35', plain,
% 0.69/0.91      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.69/0.91        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['33', '34'])).
% 0.69/0.91  thf(zf_stmt_2, axiom,
% 0.69/0.91    (![B:$i,A:$i]:
% 0.69/0.91     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.69/0.91       ( zip_tseitin_0 @ B @ A ) ))).
% 0.69/0.91  thf('36', plain,
% 0.69/0.91      (![X29 : $i, X30 : $i]:
% 0.69/0.91         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.69/0.91  thf('37', plain,
% 0.69/0.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.69/0.91  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.69/0.91  thf(zf_stmt_5, axiom,
% 0.69/0.91    (![A:$i,B:$i,C:$i]:
% 0.69/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.91       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.69/0.91         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.69/0.91           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.69/0.91             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.69/0.91  thf('38', plain,
% 0.69/0.91      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.69/0.91         (~ (zip_tseitin_0 @ X34 @ X35)
% 0.69/0.91          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 0.69/0.91          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.69/0.91  thf('39', plain,
% 0.69/0.91      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.69/0.91      inference('sup-', [status(thm)], ['37', '38'])).
% 0.69/0.91  thf('40', plain,
% 0.69/0.91      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.69/0.91      inference('sup-', [status(thm)], ['36', '39'])).
% 0.69/0.91  thf('41', plain, (((sk_B) != (k1_xboole_0))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('42', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.69/0.91      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.69/0.91  thf('43', plain,
% 0.69/0.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf(redefinition_k1_relset_1, axiom,
% 0.69/0.91    (![A:$i,B:$i,C:$i]:
% 0.69/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.91       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.69/0.91  thf('44', plain,
% 0.69/0.91      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.69/0.91         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 0.69/0.91          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.69/0.91      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.69/0.91  thf('45', plain,
% 0.69/0.91      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.69/0.91      inference('sup-', [status(thm)], ['43', '44'])).
% 0.69/0.91  thf('46', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.69/0.91      inference('demod', [status(thm)], ['35', '42', '45'])).
% 0.69/0.91  thf('47', plain,
% 0.69/0.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf(cc2_relat_1, axiom,
% 0.69/0.91    (![A:$i]:
% 0.69/0.91     ( ( v1_relat_1 @ A ) =>
% 0.69/0.91       ( ![B:$i]:
% 0.69/0.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.69/0.91  thf('48', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.69/0.91          | (v1_relat_1 @ X0)
% 0.69/0.91          | ~ (v1_relat_1 @ X1))),
% 0.69/0.91      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.69/0.91  thf('49', plain,
% 0.69/0.91      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.69/0.91      inference('sup-', [status(thm)], ['47', '48'])).
% 0.69/0.91  thf(fc6_relat_1, axiom,
% 0.69/0.91    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.69/0.91  thf('50', plain,
% 0.69/0.91      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.69/0.91      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.69/0.91  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.69/0.91      inference('demod', [status(thm)], ['49', '50'])).
% 0.69/0.91  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('53', plain, ((v2_funct_1 @ sk_C)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('54', plain,
% 0.69/0.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf(redefinition_k2_relset_1, axiom,
% 0.69/0.91    (![A:$i,B:$i,C:$i]:
% 0.69/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.91       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.69/0.91  thf('55', plain,
% 0.69/0.91      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.69/0.91         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 0.69/0.91          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.69/0.91      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.69/0.91  thf('56', plain,
% 0.69/0.91      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.69/0.91      inference('sup-', [status(thm)], ['54', '55'])).
% 0.69/0.91  thf('57', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('58', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.69/0.91      inference('sup+', [status(thm)], ['56', '57'])).
% 0.69/0.91  thf('59', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('60', plain,
% 0.69/0.91      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.69/0.91         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 0.69/0.91          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 0.69/0.91          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.69/0.91  thf('61', plain,
% 0.69/0.91      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 0.69/0.91        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['59', '60'])).
% 0.69/0.91  thf('62', plain,
% 0.69/0.91      (![X29 : $i, X30 : $i]:
% 0.69/0.91         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.69/0.91  thf('63', plain,
% 0.69/0.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('64', plain,
% 0.69/0.91      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.69/0.91         (~ (zip_tseitin_0 @ X34 @ X35)
% 0.69/0.91          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 0.69/0.91          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.69/0.91  thf('65', plain,
% 0.69/0.91      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.69/0.91      inference('sup-', [status(thm)], ['63', '64'])).
% 0.69/0.91  thf('66', plain,
% 0.69/0.91      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 0.69/0.91      inference('sup-', [status(thm)], ['62', '65'])).
% 0.69/0.91  thf('67', plain, (((sk_A) != (k1_xboole_0))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('68', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 0.69/0.91      inference('simplify_reflect-', [status(thm)], ['66', '67'])).
% 0.69/0.91  thf('69', plain,
% 0.69/0.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('70', plain,
% 0.69/0.91      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.69/0.91         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 0.69/0.91          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.69/0.91      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.69/0.91  thf('71', plain,
% 0.69/0.91      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.69/0.91      inference('sup-', [status(thm)], ['69', '70'])).
% 0.69/0.91  thf('72', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.69/0.91      inference('demod', [status(thm)], ['61', '68', '71'])).
% 0.69/0.91  thf('73', plain, ((v1_funct_1 @ sk_D)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('74', plain,
% 0.69/0.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('75', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.69/0.91          | (v1_relat_1 @ X0)
% 0.69/0.91          | ~ (v1_relat_1 @ X1))),
% 0.69/0.91      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.69/0.91  thf('76', plain,
% 0.69/0.91      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.69/0.91      inference('sup-', [status(thm)], ['74', '75'])).
% 0.69/0.91  thf('77', plain,
% 0.69/0.91      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.69/0.91      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.69/0.91  thf('78', plain, ((v1_relat_1 @ sk_D)),
% 0.69/0.91      inference('demod', [status(thm)], ['76', '77'])).
% 0.69/0.91  thf('79', plain,
% 0.69/0.91      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 0.69/0.91        | ((sk_B) != (sk_B))
% 0.69/0.91        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 0.69/0.91      inference('demod', [status(thm)],
% 0.69/0.91                ['32', '46', '51', '52', '53', '58', '72', '73', '78'])).
% 0.69/0.91  thf('80', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 0.69/0.91      inference('simplify', [status(thm)], ['79'])).
% 0.69/0.91  thf('81', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('82', plain, ($false),
% 0.69/0.91      inference('simplify_reflect-', [status(thm)], ['80', '81'])).
% 0.69/0.91  
% 0.69/0.91  % SZS output end Refutation
% 0.69/0.91  
% 0.69/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
