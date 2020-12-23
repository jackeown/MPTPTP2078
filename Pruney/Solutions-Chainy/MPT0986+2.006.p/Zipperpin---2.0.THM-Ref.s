%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KRAKH41395

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:51 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 103 expanded)
%              Number of leaves         :   45 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  672 (1130 expanded)
%              Number of equality atoms :   44 (  76 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t32_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ D )
          & ( r2_hidden @ C @ A ) )
       => ( ( B = k1_xboole_0 )
          | ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) )
            = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v2_funct_1 @ D )
            & ( r2_hidden @ C @ A ) )
         => ( ( B = k1_xboole_0 )
            | ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) )
              = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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
      ( ( zip_tseitin_5 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('2',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ( X34
        = ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ~ ( zip_tseitin_5 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_5 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_4 @ B @ A ) ) )).

thf('4',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_4 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_5: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_4 @ B @ A )
         => ( zip_tseitin_5 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_4 @ X37 @ X38 )
      | ( zip_tseitin_5 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_5 @ sk_D_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_4 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_5 @ sk_D_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    zip_tseitin_5 @ sk_D_1 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('13',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf(t54_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_funct_1 @ A )
        & ( v1_relat_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ! [B: $i] :
            ( ( ( v1_funct_1 @ B )
              & ( v1_relat_1 @ B ) )
           => ( ( B
                = ( k2_funct_1 @ A ) )
            <=> ( ! [C: $i,D: $i] :
                    ( ( ( ( D
                          = ( k1_funct_1 @ B @ C ) )
                        & ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) )
                     => ( ( C
                          = ( k1_funct_1 @ A @ D ) )
                        & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) )
                    & ( ( ( C
                          = ( k1_funct_1 @ A @ D ) )
                        & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) )
                     => ( ( D
                          = ( k1_funct_1 @ B @ C ) )
                        & ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) ) )
                & ( ( k1_relat_1 @ B )
                  = ( k2_relat_1 @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_6,axiom,(
    ! [D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_2 @ D @ C @ A )
    <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
        & ( C
          = ( k1_funct_1 @ A @ D ) ) ) ) )).

thf('15',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_2 @ X15 @ X17 @ X18 )
      | ( X17
       != ( k1_funct_1 @ X18 @ X15 ) )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('16',plain,(
    ! [X15: $i,X18: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X18 ) )
      | ( zip_tseitin_2 @ X15 @ ( k1_funct_1 @ X18 @ X15 ) @ X18 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    zip_tseitin_2 @ sk_C_1 @ ( k1_funct_1 @ sk_D_1 @ sk_C_1 ) @ sk_D_1 ),
    inference('sup-',[status(thm)],['0','17'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('19',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('20',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(zf_stmt_7,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_3 @ D @ C @ B @ A )
    <=> ( ( zip_tseitin_2 @ D @ C @ A )
       => ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) )
          & ( D
            = ( k1_funct_1 @ B @ C ) ) ) ) ) )).

thf(zf_stmt_9,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_10,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_11,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ D @ C @ B @ A )
    <=> ( ( zip_tseitin_0 @ D @ C @ B @ A )
       => ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
          & ( C
            = ( k1_funct_1 @ A @ D ) ) ) ) ) )).

thf(zf_stmt_12,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_13,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B @ A )
    <=> ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) )
        & ( D
          = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf(zf_stmt_14,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ( ( B
                = ( k2_funct_1 @ A ) )
            <=> ( ( ( k1_relat_1 @ B )
                  = ( k2_relat_1 @ A ) )
                & ! [C: $i,D: $i] :
                    ( ( zip_tseitin_3 @ D @ C @ B @ A )
                    & ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X24: $i,X25: $i,X27: $i,X28: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ( X25
       != ( k2_funct_1 @ X24 ) )
      | ( zip_tseitin_3 @ X28 @ X27 @ X25 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_14])).

thf('22',plain,(
    ! [X24: $i,X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( zip_tseitin_3 @ X28 @ X27 @ ( k2_funct_1 @ X24 ) @ X24 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X24 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X24 ) )
      | ~ ( v2_funct_1 @ X24 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( zip_tseitin_3 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_3 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_3 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_3 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_2 @ X19 @ X20 @ X21 )
      | ( X19
        = ( k1_funct_1 @ X22 @ X20 ) )
      | ~ ( zip_tseitin_3 @ X19 @ X20 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( X2
        = ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
      | ~ ( zip_tseitin_2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_C_1
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_D_1 ) @ ( k1_funct_1 @ sk_D_1 @ sk_C_1 ) ) )
    | ~ ( v2_funct_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['18','28'])).

thf('30',plain,(
    v2_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('36',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( sk_C_1
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_D_1 ) @ ( k1_funct_1 @ sk_D_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['29','30','31','36'])).

thf('38',plain,(
    ( k1_funct_1 @ ( k2_funct_1 @ sk_D_1 ) @ ( k1_funct_1 @ sk_D_1 @ sk_C_1 ) )
 != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KRAKH41395
% 0.16/0.37  % Computer   : n005.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 16:46:33 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.40/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.59  % Solved by: fo/fo7.sh
% 0.40/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.59  % done 113 iterations in 0.113s
% 0.40/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.59  % SZS output start Refutation
% 0.40/0.59  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $i > $o).
% 0.40/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.59  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.40/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.59  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.40/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.59  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.40/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.59  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.40/0.59  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.40/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.40/0.59  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.40/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.40/0.59  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $i > $o).
% 0.40/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.40/0.59  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.40/0.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.40/0.59  thf(t32_funct_2, conjecture,
% 0.40/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.59     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.40/0.59         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.59       ( ( ( v2_funct_1 @ D ) & ( r2_hidden @ C @ A ) ) =>
% 0.40/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.40/0.59           ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) ) =
% 0.40/0.59             ( C ) ) ) ) ))).
% 0.40/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.59    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.59        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.40/0.59            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.59          ( ( ( v2_funct_1 @ D ) & ( r2_hidden @ C @ A ) ) =>
% 0.40/0.59            ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.40/0.59              ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) ) =
% 0.40/0.59                ( C ) ) ) ) ) )),
% 0.40/0.59    inference('cnf.neg', [status(esa)], [t32_funct_2])).
% 0.40/0.59  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('1', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(d1_funct_2, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.59       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.40/0.59           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.40/0.59             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.40/0.59         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.40/0.59           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.40/0.59             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.40/0.59  thf(zf_stmt_1, axiom,
% 0.40/0.59    (![C:$i,B:$i,A:$i]:
% 0.40/0.59     ( ( zip_tseitin_5 @ C @ B @ A ) =>
% 0.40/0.59       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.40/0.59  thf('2', plain,
% 0.40/0.59      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.40/0.59         (~ (v1_funct_2 @ X36 @ X34 @ X35)
% 0.40/0.59          | ((X34) = (k1_relset_1 @ X34 @ X35 @ X36))
% 0.40/0.59          | ~ (zip_tseitin_5 @ X36 @ X35 @ X34))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.40/0.59  thf('3', plain,
% 0.40/0.59      ((~ (zip_tseitin_5 @ sk_D_1 @ sk_B @ sk_A)
% 0.40/0.59        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_1)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.59  thf(zf_stmt_2, axiom,
% 0.40/0.59    (![B:$i,A:$i]:
% 0.40/0.59     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.40/0.59       ( zip_tseitin_4 @ B @ A ) ))).
% 0.40/0.59  thf('4', plain,
% 0.40/0.59      (![X32 : $i, X33 : $i]:
% 0.40/0.59         ((zip_tseitin_4 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.40/0.59  thf('5', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(zf_stmt_3, type, zip_tseitin_5 : $i > $i > $i > $o).
% 0.40/0.59  thf(zf_stmt_4, type, zip_tseitin_4 : $i > $i > $o).
% 0.40/0.59  thf(zf_stmt_5, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.59       ( ( ( zip_tseitin_4 @ B @ A ) => ( zip_tseitin_5 @ C @ B @ A ) ) & 
% 0.40/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.40/0.59           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.40/0.59             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.40/0.59  thf('6', plain,
% 0.40/0.59      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.40/0.59         (~ (zip_tseitin_4 @ X37 @ X38)
% 0.40/0.59          | (zip_tseitin_5 @ X39 @ X37 @ X38)
% 0.40/0.59          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.40/0.59  thf('7', plain,
% 0.40/0.59      (((zip_tseitin_5 @ sk_D_1 @ sk_B @ sk_A)
% 0.40/0.59        | ~ (zip_tseitin_4 @ sk_B @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['5', '6'])).
% 0.40/0.59  thf('8', plain,
% 0.40/0.59      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_5 @ sk_D_1 @ sk_B @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['4', '7'])).
% 0.40/0.59  thf('9', plain, (((sk_B) != (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('10', plain, ((zip_tseitin_5 @ sk_D_1 @ sk_B @ sk_A)),
% 0.40/0.59      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.40/0.59  thf('11', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(redefinition_k1_relset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.59       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.40/0.59  thf('12', plain,
% 0.40/0.59      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.40/0.59         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 0.40/0.59          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.40/0.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.40/0.59  thf('13', plain,
% 0.40/0.59      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.40/0.59      inference('sup-', [status(thm)], ['11', '12'])).
% 0.40/0.59  thf('14', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.40/0.59      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.40/0.59  thf(t54_funct_1, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.40/0.59       ( ( v2_funct_1 @ A ) =>
% 0.40/0.59         ( ![B:$i]:
% 0.40/0.59           ( ( ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) =>
% 0.40/0.59             ( ( ( B ) = ( k2_funct_1 @ A ) ) <=>
% 0.40/0.59               ( ( ![C:$i,D:$i]:
% 0.40/0.59                   ( ( ( ( ( D ) = ( k1_funct_1 @ B @ C ) ) & 
% 0.40/0.59                         ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) =>
% 0.40/0.59                       ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.40/0.59                         ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) & 
% 0.40/0.59                     ( ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.40/0.59                         ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) =>
% 0.40/0.59                       ( ( ( D ) = ( k1_funct_1 @ B @ C ) ) & 
% 0.40/0.59                         ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) ) ) ) & 
% 0.40/0.59                 ( ( k1_relat_1 @ B ) = ( k2_relat_1 @ A ) ) ) ) ) ) ) ))).
% 0.40/0.59  thf(zf_stmt_6, axiom,
% 0.40/0.59    (![D:$i,C:$i,A:$i]:
% 0.40/0.59     ( ( zip_tseitin_2 @ D @ C @ A ) <=>
% 0.40/0.59       ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.40/0.59         ( ( C ) = ( k1_funct_1 @ A @ D ) ) ) ))).
% 0.40/0.59  thf('15', plain,
% 0.40/0.59      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.40/0.59         ((zip_tseitin_2 @ X15 @ X17 @ X18)
% 0.40/0.59          | ((X17) != (k1_funct_1 @ X18 @ X15))
% 0.40/0.59          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X18)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.40/0.59  thf('16', plain,
% 0.40/0.59      (![X15 : $i, X18 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X15 @ (k1_relat_1 @ X18))
% 0.40/0.59          | (zip_tseitin_2 @ X15 @ (k1_funct_1 @ X18 @ X15) @ X18))),
% 0.40/0.59      inference('simplify', [status(thm)], ['15'])).
% 0.40/0.59  thf('17', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X0 @ sk_A)
% 0.40/0.59          | (zip_tseitin_2 @ X0 @ (k1_funct_1 @ sk_D_1 @ X0) @ sk_D_1))),
% 0.40/0.59      inference('sup-', [status(thm)], ['14', '16'])).
% 0.40/0.59  thf('18', plain,
% 0.40/0.59      ((zip_tseitin_2 @ sk_C_1 @ (k1_funct_1 @ sk_D_1 @ sk_C_1) @ sk_D_1)),
% 0.40/0.59      inference('sup-', [status(thm)], ['0', '17'])).
% 0.40/0.59  thf(dt_k2_funct_1, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.59       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.40/0.59         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.40/0.59  thf('19', plain,
% 0.40/0.59      (![X4 : $i]:
% 0.40/0.59         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.40/0.59          | ~ (v1_funct_1 @ X4)
% 0.40/0.59          | ~ (v1_relat_1 @ X4))),
% 0.40/0.59      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.40/0.59  thf('20', plain,
% 0.40/0.59      (![X4 : $i]:
% 0.40/0.59         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.40/0.59          | ~ (v1_funct_1 @ X4)
% 0.40/0.59          | ~ (v1_relat_1 @ X4))),
% 0.40/0.59      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.40/0.59  thf(zf_stmt_7, type, zip_tseitin_3 : $i > $i > $i > $i > $o).
% 0.40/0.59  thf(zf_stmt_8, axiom,
% 0.40/0.59    (![D:$i,C:$i,B:$i,A:$i]:
% 0.40/0.59     ( ( zip_tseitin_3 @ D @ C @ B @ A ) <=>
% 0.40/0.59       ( ( zip_tseitin_2 @ D @ C @ A ) =>
% 0.40/0.59         ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) & 
% 0.40/0.59           ( ( D ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.40/0.59  thf(zf_stmt_9, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.40/0.59  thf(zf_stmt_10, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.40/0.59  thf(zf_stmt_11, axiom,
% 0.40/0.59    (![D:$i,C:$i,B:$i,A:$i]:
% 0.40/0.59     ( ( zip_tseitin_1 @ D @ C @ B @ A ) <=>
% 0.40/0.59       ( ( zip_tseitin_0 @ D @ C @ B @ A ) =>
% 0.40/0.59         ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.40/0.59           ( ( C ) = ( k1_funct_1 @ A @ D ) ) ) ) ))).
% 0.40/0.59  thf(zf_stmt_12, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.40/0.59  thf(zf_stmt_13, axiom,
% 0.40/0.59    (![D:$i,C:$i,B:$i,A:$i]:
% 0.40/0.59     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.40/0.59       ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) & 
% 0.40/0.59         ( ( D ) = ( k1_funct_1 @ B @ C ) ) ) ))).
% 0.40/0.59  thf(zf_stmt_14, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.59       ( ( v2_funct_1 @ A ) =>
% 0.40/0.59         ( ![B:$i]:
% 0.40/0.59           ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.40/0.59             ( ( ( B ) = ( k2_funct_1 @ A ) ) <=>
% 0.40/0.59               ( ( ( k1_relat_1 @ B ) = ( k2_relat_1 @ A ) ) & 
% 0.40/0.59                 ( ![C:$i,D:$i]:
% 0.40/0.59                   ( ( zip_tseitin_3 @ D @ C @ B @ A ) & 
% 0.40/0.59                     ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ))).
% 0.40/0.59  thf('21', plain,
% 0.40/0.59      (![X24 : $i, X25 : $i, X27 : $i, X28 : $i]:
% 0.40/0.59         (~ (v2_funct_1 @ X24)
% 0.40/0.59          | ~ (v1_relat_1 @ X25)
% 0.40/0.59          | ~ (v1_funct_1 @ X25)
% 0.40/0.59          | ((X25) != (k2_funct_1 @ X24))
% 0.40/0.59          | (zip_tseitin_3 @ X28 @ X27 @ X25 @ X24)
% 0.40/0.59          | ~ (v1_funct_1 @ X24)
% 0.40/0.59          | ~ (v1_relat_1 @ X24))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_14])).
% 0.40/0.59  thf('22', plain,
% 0.40/0.59      (![X24 : $i, X27 : $i, X28 : $i]:
% 0.40/0.59         (~ (v1_relat_1 @ X24)
% 0.40/0.59          | ~ (v1_funct_1 @ X24)
% 0.40/0.59          | (zip_tseitin_3 @ X28 @ X27 @ (k2_funct_1 @ X24) @ X24)
% 0.40/0.59          | ~ (v1_funct_1 @ (k2_funct_1 @ X24))
% 0.40/0.59          | ~ (v1_relat_1 @ (k2_funct_1 @ X24))
% 0.40/0.59          | ~ (v2_funct_1 @ X24))),
% 0.40/0.59      inference('simplify', [status(thm)], ['21'])).
% 0.40/0.59  thf('23', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         (~ (v1_relat_1 @ X0)
% 0.40/0.59          | ~ (v1_funct_1 @ X0)
% 0.40/0.59          | ~ (v2_funct_1 @ X0)
% 0.40/0.59          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.40/0.59          | (zip_tseitin_3 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.40/0.59          | ~ (v1_funct_1 @ X0)
% 0.40/0.59          | ~ (v1_relat_1 @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['20', '22'])).
% 0.40/0.59  thf('24', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         ((zip_tseitin_3 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.40/0.59          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.40/0.59          | ~ (v2_funct_1 @ X0)
% 0.40/0.59          | ~ (v1_funct_1 @ X0)
% 0.40/0.59          | ~ (v1_relat_1 @ X0))),
% 0.40/0.59      inference('simplify', [status(thm)], ['23'])).
% 0.40/0.59  thf('25', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         (~ (v1_relat_1 @ X0)
% 0.40/0.59          | ~ (v1_funct_1 @ X0)
% 0.40/0.59          | ~ (v1_relat_1 @ X0)
% 0.40/0.59          | ~ (v1_funct_1 @ X0)
% 0.40/0.59          | ~ (v2_funct_1 @ X0)
% 0.40/0.59          | (zip_tseitin_3 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['19', '24'])).
% 0.40/0.59  thf('26', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         ((zip_tseitin_3 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.40/0.59          | ~ (v2_funct_1 @ X0)
% 0.40/0.59          | ~ (v1_funct_1 @ X0)
% 0.40/0.59          | ~ (v1_relat_1 @ X0))),
% 0.40/0.59      inference('simplify', [status(thm)], ['25'])).
% 0.40/0.59  thf('27', plain,
% 0.40/0.59      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.40/0.59         (~ (zip_tseitin_2 @ X19 @ X20 @ X21)
% 0.40/0.59          | ((X19) = (k1_funct_1 @ X22 @ X20))
% 0.40/0.59          | ~ (zip_tseitin_3 @ X19 @ X20 @ X22 @ X21))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.40/0.59  thf('28', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         (~ (v1_relat_1 @ X0)
% 0.40/0.59          | ~ (v1_funct_1 @ X0)
% 0.40/0.59          | ~ (v2_funct_1 @ X0)
% 0.40/0.59          | ((X2) = (k1_funct_1 @ (k2_funct_1 @ X0) @ X1))
% 0.40/0.59          | ~ (zip_tseitin_2 @ X2 @ X1 @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.40/0.59  thf('29', plain,
% 0.40/0.59      ((((sk_C_1)
% 0.40/0.59          = (k1_funct_1 @ (k2_funct_1 @ sk_D_1) @ 
% 0.40/0.59             (k1_funct_1 @ sk_D_1 @ sk_C_1)))
% 0.40/0.59        | ~ (v2_funct_1 @ sk_D_1)
% 0.40/0.59        | ~ (v1_funct_1 @ sk_D_1)
% 0.40/0.59        | ~ (v1_relat_1 @ sk_D_1))),
% 0.40/0.59      inference('sup-', [status(thm)], ['18', '28'])).
% 0.40/0.59  thf('30', plain, ((v2_funct_1 @ sk_D_1)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('31', plain, ((v1_funct_1 @ sk_D_1)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('32', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(cc2_relat_1, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( v1_relat_1 @ A ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.40/0.59  thf('33', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.40/0.59          | (v1_relat_1 @ X0)
% 0.40/0.59          | ~ (v1_relat_1 @ X1))),
% 0.40/0.59      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.40/0.59  thf('34', plain,
% 0.40/0.59      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_1))),
% 0.40/0.59      inference('sup-', [status(thm)], ['32', '33'])).
% 0.40/0.59  thf(fc6_relat_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.40/0.59  thf('35', plain,
% 0.40/0.59      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.40/0.59      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.40/0.59  thf('36', plain, ((v1_relat_1 @ sk_D_1)),
% 0.40/0.59      inference('demod', [status(thm)], ['34', '35'])).
% 0.40/0.59  thf('37', plain,
% 0.40/0.59      (((sk_C_1)
% 0.40/0.59         = (k1_funct_1 @ (k2_funct_1 @ sk_D_1) @ (k1_funct_1 @ sk_D_1 @ sk_C_1)))),
% 0.40/0.59      inference('demod', [status(thm)], ['29', '30', '31', '36'])).
% 0.40/0.59  thf('38', plain,
% 0.40/0.59      (((k1_funct_1 @ (k2_funct_1 @ sk_D_1) @ (k1_funct_1 @ sk_D_1 @ sk_C_1))
% 0.40/0.59         != (sk_C_1))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('39', plain, ($false),
% 0.40/0.59      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.40/0.59  
% 0.40/0.59  % SZS output end Refutation
% 0.40/0.59  
% 0.40/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
