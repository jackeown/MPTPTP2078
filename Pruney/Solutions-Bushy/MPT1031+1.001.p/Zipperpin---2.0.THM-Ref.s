%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1031+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0zeaWqkc58

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:55 EST 2020

% Result     : Theorem 11.60s
% Output     : Refutation 11.60s
% Verified   : 
% Statistics : Number of formulae       :  257 (14254 expanded)
%              Number of leaves         :   53 (4255 expanded)
%              Depth                    :   70
%              Number of atoms          : 2882 (247885 expanded)
%              Number of equality atoms :   85 (9269 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(o_1_1_funct_2_type,type,(
    o_1_1_funct_2: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t136_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ~ ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
          & ! [D: $i] :
              ( ( ( v1_funct_1 @ D )
                & ( v1_funct_2 @ D @ A @ B )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
             => ? [E: $i] :
                  ( ( ( k1_funct_1 @ D @ E )
                   != ( k1_funct_1 @ C @ E ) )
                  & ( r2_hidden @ E @ ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ~ ( ( ( B = k1_xboole_0 )
             => ( A = k1_xboole_0 ) )
            & ! [D: $i] :
                ( ( ( v1_funct_1 @ D )
                  & ( v1_funct_2 @ D @ A @ B )
                  & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
               => ? [E: $i] :
                    ( ( ( k1_funct_1 @ D @ E )
                     != ( k1_funct_1 @ C @ E ) )
                    & ( r2_hidden @ E @ ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t136_funct_2])).

thf('0',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_o_1_1_funct_2,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( o_1_1_funct_2 @ A ) @ A ) )).

thf('2',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( o_1_1_funct_2 @ X15 ) @ X15 ) ),
    inference(cnf,[status(esa)],[dt_o_1_1_funct_2])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r2_hidden @ X47 @ X48 )
      | ( v1_xboole_0 @ X48 )
      | ~ ( m1_subset_1 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( o_1_1_funct_2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(s5_funct_2__e3_154_1_2__funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ C ) )
     => ( ! [D: $i] :
            ( ( r2_hidden @ D @ A )
           => ( ( ~ ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) )
               => ( r2_hidden @ ( o_1_1_funct_2 @ B ) @ B ) )
              & ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) )
               => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) )
       => ? [D: $i] :
            ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
            & ! [E: $i] :
                ( ( r2_hidden @ E @ A )
               => ( ( ~ ( r2_hidden @ E @ ( k1_relset_1 @ A @ B @ C ) )
                   => ( ( k1_funct_1 @ D @ E )
                      = ( o_1_1_funct_2 @ B ) ) )
                  & ( ( r2_hidden @ E @ ( k1_relset_1 @ A @ B @ C ) )
                   => ( ( k1_funct_1 @ D @ E )
                      = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ~ ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) )
       => ( r2_hidden @ ( o_1_1_funct_2 @ B ) @ B ) )
     => ( zip_tseitin_0 @ D @ C @ B @ A ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 )
      | ~ ( r2_hidden @ ( o_1_1_funct_2 @ X21 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X3 @ X2 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v5_relat_1 @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('9',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X3 @ X2 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('11',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X3 @ X2 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('15',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) )
       => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
     => ( zip_tseitin_1 @ D @ C @ B @ A ) ) )).

thf('16',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( zip_tseitin_1 @ X23 @ X24 @ X25 @ X26 )
      | ( r2_hidden @ X23 @ ( k1_relset_1 @ X26 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C ) )
      | ( zip_tseitin_1 @ X0 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(zf_stmt_3,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r2_hidden @ D @ A )
       => ( ( zip_tseitin_1 @ D @ C @ B @ A )
          & ( zip_tseitin_0 @ D @ C @ B @ A ) ) )
     => ( zip_tseitin_2 @ D @ C @ B @ A ) ) )).

thf('18',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_2 @ X27 @ X28 @ X29 @ X30 )
      | ~ ( zip_tseitin_1 @ X27 @ X28 @ X29 @ X30 )
      | ~ ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C ) )
      | ~ ( zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( zip_tseitin_2 @ X0 @ sk_C @ sk_B @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_4,type,(
    zip_tseitin_4: $i > $i > $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_4 @ D @ C @ B @ A )
     => ( ! [E: $i] :
            ( ( r2_hidden @ E @ A )
           => ( zip_tseitin_3 @ E @ D @ C @ B @ A ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ D @ A @ B )
        & ( v1_funct_1 @ D ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_3: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_3 @ E @ D @ C @ B @ A )
     => ( ( ( r2_hidden @ E @ ( k1_relset_1 @ A @ B @ C ) )
         => ( ( k1_funct_1 @ D @ E )
            = ( k1_funct_1 @ C @ E ) ) )
        & ( ~ ( r2_hidden @ E @ ( k1_relset_1 @ A @ B @ C ) )
         => ( ( k1_funct_1 @ D @ E )
            = ( o_1_1_funct_2 @ B ) ) ) ) ) )).

thf(zf_stmt_8,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(zf_stmt_9,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_10,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_11,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ! [D: $i] :
            ( zip_tseitin_2 @ D @ C @ B @ A )
       => ? [D: $i] :
            ( zip_tseitin_4 @ D @ C @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ X41 @ X42 @ X43 ) @ X41 @ X42 @ X43 )
      | ( zip_tseitin_4 @ ( sk_D_1 @ X41 @ X42 @ X43 ) @ X41 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) )
      | ~ ( v1_funct_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('23',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( zip_tseitin_4 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( zip_tseitin_4 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_4 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v1_funct_1 @ X38 )
      | ~ ( zip_tseitin_4 @ X38 @ X39 @ X40 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('28',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t27_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v5_relat_1 @ C @ A )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) )
       => ( r2_hidden @ ( k1_funct_1 @ C @ B ) @ A ) ) ) )).

thf('29',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ X44 @ ( k1_relat_1 @ X45 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X45 @ X44 ) @ X46 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v5_relat_1 @ X45 @ X46 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t27_partfun1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v5_relat_1 @ sk_C @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('32',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v5_relat_1 @ sk_C @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['30','33','34'])).

thf('36',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_B )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','35'])).

thf('37',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( zip_tseitin_1 @ X23 @ X24 @ X25 @ X26 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X24 @ X23 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( zip_tseitin_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_2 @ X27 @ X28 @ X29 @ X30 )
      | ~ ( zip_tseitin_1 @ X27 @ X28 @ X29 @ X30 )
      | ~ ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( v1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ X0 )
      | ( zip_tseitin_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( zip_tseitin_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ X0 )
      | ( v1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ( zip_tseitin_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( zip_tseitin_4 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('44',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ( zip_tseitin_4 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v1_funct_1 @ X38 )
      | ~ ( zip_tseitin_4 @ X38 @ X39 @ X40 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('46',plain,
    ( ( v1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_4 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('48',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v1_funct_2 @ X38 @ X37 @ X40 )
      | ~ ( zip_tseitin_4 @ X38 @ X39 @ X40 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('49',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('51',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('52',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_4 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('53',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X40 ) ) )
      | ~ ( zip_tseitin_4 @ X38 @ X39 @ X40 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('54',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X53: $i] :
      ( ( r2_hidden @ ( sk_E @ X53 ) @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X53 @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('57',plain,(
    ! [X53: $i] :
      ( ( r2_hidden @ ( sk_E @ X53 ) @ ( k1_relat_1 @ sk_C ) )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X53 @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ X53 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_funct_2 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ( r2_hidden @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['51','58'])).

thf('60',plain,
    ( ~ ( v1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','60'])).

thf('62',plain,
    ( ( r2_hidden @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_relat_1 @ sk_C ) )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( r2_hidden @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_relat_1 @ sk_C ) )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['61'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('65',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X12 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('66',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('68',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('69',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( r2_hidden @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X51 ) )
      | ( m1_subset_1 @ X49 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['63','70'])).

thf('72',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r2_hidden @ X47 @ X48 )
      | ( v1_xboole_0 @ X48 )
      | ~ ( m1_subset_1 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('73',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_4 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('75',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X36 @ X37 )
      | ( zip_tseitin_3 @ X36 @ X38 @ X39 @ X40 @ X37 )
      | ~ ( zip_tseitin_4 @ X38 @ X39 @ X40 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
      | ( zip_tseitin_3 @ X0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( zip_tseitin_3 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,
    ( ( zip_tseitin_3 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('80',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X31 @ ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ( ( k1_funct_1 @ X35 @ X31 )
        = ( k1_funct_1 @ X34 @ X31 ) )
      | ~ ( zip_tseitin_3 @ X31 @ X35 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C ) )
      | ~ ( zip_tseitin_3 @ X0 @ X1 @ sk_C @ sk_B @ sk_A )
      | ( ( k1_funct_1 @ X1 @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      = ( k1_funct_1 @ sk_C @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ~ ( r2_hidden @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      = ( k1_funct_1 @ sk_C @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','82'])).

thf('84',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      = ( k1_funct_1 @ sk_C @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('86',plain,(
    ! [X53: $i] :
      ( ( ( k1_funct_1 @ X53 @ ( sk_E @ X53 ) )
       != ( k1_funct_1 @ sk_C @ ( sk_E @ X53 ) ) )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X53 @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_funct_2 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ( ( k1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
     != ( k1_funct_1 @ sk_C @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( k1_funct_1 @ sk_C @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
     != ( k1_funct_1 @ sk_C @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_2 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,
    ( ~ ( v1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_funct_2 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','89'])).

thf('91',plain,
    ( ~ ( v1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','91'])).

thf('93',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ X44 @ ( k1_relat_1 @ X45 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X45 @ X44 ) @ X46 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v5_relat_1 @ X45 @ X46 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t27_partfun1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v5_relat_1 @ sk_C @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['31','32'])).

thf('97',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v5_relat_1 @ sk_C @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['9','98'])).

thf('100',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( zip_tseitin_1 @ X23 @ X24 @ X25 @ X26 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X24 @ X23 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( zip_tseitin_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_2 @ X27 @ X28 @ X29 @ X30 )
      | ~ ( zip_tseitin_1 @ X27 @ X28 @ X29 @ X30 )
      | ~ ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( zip_tseitin_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ X0 )
      | ( zip_tseitin_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( zip_tseitin_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( zip_tseitin_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ( zip_tseitin_4 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('107',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( zip_tseitin_4 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v1_funct_2 @ X38 @ X37 @ X40 )
      | ~ ( zip_tseitin_4 @ X38 @ X39 @ X40 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('109',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_funct_2 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( v1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('111',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_funct_2 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('112',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( zip_tseitin_4 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('113',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X40 ) ) )
      | ~ ( zip_tseitin_4 @ X38 @ X39 @ X40 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('114',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X53: $i] :
      ( ( r2_hidden @ ( sk_E @ X53 ) @ ( k1_relat_1 @ sk_C ) )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X53 @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ X53 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('116',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_funct_2 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ( r2_hidden @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['111','116'])).

thf('118',plain,
    ( ~ ( v1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['110','118'])).

thf('120',plain,
    ( ( r2_hidden @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,
    ( ( r2_hidden @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['119'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('123',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r2_hidden @ X47 @ X48 )
      | ( v1_xboole_0 @ X48 )
      | ~ ( m1_subset_1 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('125',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( r2_hidden @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( zip_tseitin_4 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('128',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X36 @ X37 )
      | ( zip_tseitin_3 @ X36 @ X38 @ X39 @ X40 @ X37 )
      | ~ ( zip_tseitin_4 @ X38 @ X39 @ X40 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( zip_tseitin_3 @ X0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_3 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['126','129'])).

thf('131',plain,
    ( ( zip_tseitin_3 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C ) )
      | ~ ( zip_tseitin_3 @ X0 @ X1 @ sk_C @ sk_B @ sk_A )
      | ( ( k1_funct_1 @ X1 @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('133',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( ( k1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      = ( k1_funct_1 @ sk_C @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ~ ( r2_hidden @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      = ( k1_funct_1 @ sk_C @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['120','133'])).

thf('135',plain,
    ( ( ( k1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      = ( k1_funct_1 @ sk_C @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('137',plain,(
    ! [X53: $i] :
      ( ( ( k1_funct_1 @ X53 @ ( sk_E @ X53 ) )
       != ( k1_funct_1 @ sk_C @ ( sk_E @ X53 ) ) )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X53 @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_funct_2 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ( ( k1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
     != ( k1_funct_1 @ sk_C @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ( ( k1_funct_1 @ sk_C @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
     != ( k1_funct_1 @ sk_C @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_2 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['135','138'])).

thf('140',plain,
    ( ~ ( v1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_funct_2 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','140'])).

thf('142',plain,
    ( ~ ( v1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,
    ( ( v1_funct_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('144',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['142','143'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('145',plain,(
    ! [X52: $i] :
      ( ( X52 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('146',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('147',plain,(
    ! [X52: $i] :
      ( ( X52 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X52 ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_B = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['144','147'])).

thf('149',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('150',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X5 ) ) )
      | ( v1_partfun1 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('151',plain,
    ( ( v1_partfun1 @ sk_C @ sk_A )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,
    ( ( sk_B = o_0_0_xboole_0 )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['148','151'])).

thf('153',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('154',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_partfun1 @ X0 @ X1 )
      | ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('155',plain,
    ( ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_partfun1 @ sk_C @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,
    ( ( sk_B = o_0_0_xboole_0 )
    | ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['152','157'])).

thf('159',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    ! [X53: $i] :
      ( ( ( k1_funct_1 @ X53 @ ( sk_E @ X53 ) )
       != ( k1_funct_1 @ sk_C @ ( sk_E @ X53 ) ) )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X53 @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( ( k1_funct_1 @ sk_C @ ( sk_E @ sk_C ) )
     != ( k1_funct_1 @ sk_C @ ( sk_E @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( ( k1_funct_1 @ sk_C @ ( sk_E @ sk_C ) )
     != ( k1_funct_1 @ sk_C @ ( sk_E @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,(
    sk_B = o_0_0_xboole_0 ),
    inference(clc,[status(thm)],['158','164'])).

thf('166',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('167',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['1','165','166'])).

thf('168',plain,
    ( $false
   <= ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('170',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['163'])).

thf('171',plain,
    ( ~ ( v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('173',plain,
    ( ~ ( v1_funct_2 @ sk_C @ o_0_0_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('175',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['174','175'])).

thf('177',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('178',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ o_0_0_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_partfun1 @ X0 @ X1 )
      | ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('180',plain,
    ( ( ( v1_funct_2 @ sk_C @ o_0_0_xboole_0 @ sk_B )
      | ~ ( v1_partfun1 @ sk_C @ o_0_0_xboole_0 )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( ( v1_funct_2 @ sk_C @ o_0_0_xboole_0 @ sk_B )
      | ~ ( v1_partfun1 @ sk_C @ o_0_0_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ o_0_0_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['176','177'])).

thf('184',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X5 ) ) )
      | ( v1_partfun1 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('185',plain,
    ( ( ( v1_partfun1 @ sk_C @ o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ o_0_0_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('187',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_B = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['144','147'])).

thf('188',plain,
    ( ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_B = o_0_0_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['186','187'])).

thf('189',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('190',plain,
    ( ( ( v1_xboole_0 @ o_0_0_xboole_0 )
      | ( sk_B = o_0_0_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('192',plain,
    ( ( ( v1_xboole_0 @ o_0_0_xboole_0 )
      | ( v1_xboole_0 @ o_0_0_xboole_0 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['190','191'])).

thf('193',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('194',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('195',plain,
    ( ( ( v1_xboole_0 @ o_0_0_xboole_0 )
      | ( v1_xboole_0 @ o_0_0_xboole_0 )
      | ( v1_xboole_0 @ o_0_0_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['192','193','194'])).

thf('196',plain,
    ( ( v1_xboole_0 @ o_0_0_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,
    ( ( v1_partfun1 @ sk_C @ o_0_0_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['185','196'])).

thf('198',plain,
    ( ( v1_funct_2 @ sk_C @ o_0_0_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['182','197'])).

thf('199',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['173','198'])).

thf('200',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('201',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['199','200'])).

thf('202',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['168','201'])).


%------------------------------------------------------------------------------
