%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yPZ0uAjF32

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:52 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  175 (1792 expanded)
%              Number of leaves         :   48 ( 550 expanded)
%              Depth                    :   29
%              Number of atoms          : 1698 (51341 expanded)
%              Number of equality atoms :  122 (4961 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t34_funct_2,conjecture,(
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
              & ( v2_funct_1 @ C )
              & ! [E: $i,F: $i] :
                  ( ( ( ( r2_hidden @ F @ A )
                      & ( ( k1_funct_1 @ C @ F )
                        = E ) )
                   => ( ( r2_hidden @ E @ B )
                      & ( ( k1_funct_1 @ D @ E )
                        = F ) ) )
                  & ( ( ( r2_hidden @ E @ B )
                      & ( ( k1_funct_1 @ D @ E )
                        = F ) )
                   => ( ( r2_hidden @ F @ A )
                      & ( ( k1_funct_1 @ C @ F )
                        = E ) ) ) ) )
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
                & ( v2_funct_1 @ C )
                & ! [E: $i,F: $i] :
                    ( ( ( ( r2_hidden @ F @ A )
                        & ( ( k1_funct_1 @ C @ F )
                          = E ) )
                     => ( ( r2_hidden @ E @ B )
                        & ( ( k1_funct_1 @ D @ E )
                          = F ) ) )
                    & ( ( ( r2_hidden @ E @ B )
                        & ( ( k1_funct_1 @ D @ E )
                          = F ) )
                     => ( ( r2_hidden @ F @ A )
                        & ( ( k1_funct_1 @ C @ F )
                          = E ) ) ) ) )
             => ( ( A = k1_xboole_0 )
                | ( B = k1_xboole_0 )
                | ( D
                  = ( k2_funct_1 @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X33 @ X31 )
        = ( k2_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B @ sk_A ),
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

thf('6',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ( X36
        = ( k1_relset_1 @ X36 @ X37 @ X38 ) )
      | ~ ( zip_tseitin_5 @ X38 @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,
    ( ~ ( zip_tseitin_5 @ sk_D_1 @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_4 @ B @ A ) ) )).

thf('8',plain,(
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_4 @ X34 @ X35 )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
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

thf('10',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( zip_tseitin_4 @ X39 @ X40 )
      | ( zip_tseitin_5 @ X41 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('11',plain,
    ( ( zip_tseitin_5 @ sk_D_1 @ sk_A @ sk_B )
    | ~ ( zip_tseitin_4 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_5 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    zip_tseitin_5 @ sk_D_1 @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('16',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('17',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['7','14','17'])).

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
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ D @ C @ B @ A )
    <=> ( ( zip_tseitin_0 @ D @ C @ B @ A )
       => ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
          & ( C
            = ( k1_funct_1 @ A @ D ) ) ) ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i,X11: $i,X13: $i] :
      ( ( zip_tseitin_1 @ X9 @ X10 @ X11 @ X13 )
      | ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf(zf_stmt_7,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_3 @ D @ C @ B @ A )
    <=> ( ( zip_tseitin_2 @ D @ C @ A )
       => ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) )
          & ( D
            = ( k1_funct_1 @ B @ C ) ) ) ) ) )).

thf('20',plain,(
    ! [X18: $i,X19: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_3 @ X18 @ X19 @ X21 @ X22 )
      | ( zip_tseitin_2 @ X18 @ X19 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf(zf_stmt_8,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(zf_stmt_9,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_10,axiom,(
    ! [D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_2 @ D @ C @ A )
    <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
        & ( C
          = ( k1_funct_1 @ A @ D ) ) ) ) )).

thf(zf_stmt_11,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

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
    ! [X23: $i,X24: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( ( k1_relat_1 @ X24 )
       != ( k2_relat_1 @ X23 ) )
      | ~ ( zip_tseitin_3 @ ( sk_D @ X24 @ X23 ) @ ( sk_C @ X24 @ X23 ) @ X24 @ X23 )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X24 @ X23 ) @ ( sk_C @ X24 @ X23 ) @ X24 @ X23 )
      | ( X24
        = ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_14])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_2 @ ( sk_D @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ X1 @ X0 )
      | ( ( k1_relat_1 @ X1 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_D @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ X1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != ( k2_relat_1 @ X0 ) )
      | ( X1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_2 @ ( sk_D @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( sk_B
       != ( k2_relat_1 @ X0 ) )
      | ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 ) @ ( sk_C @ sk_D_1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( sk_D_1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_0 @ ( sk_D @ sk_D_1 @ X0 ) @ ( sk_C @ sk_D_1 @ X0 ) @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('30',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( sk_B
       != ( k2_relat_1 @ X0 ) )
      | ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 ) @ ( sk_C @ sk_D_1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( sk_D_1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_0 @ ( sk_D @ sk_D_1 @ X0 ) @ ( sk_C @ sk_D_1 @ X0 ) @ sk_D_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25','30'])).

thf('32',plain,
    ( ( sk_B != sk_B )
    | ( zip_tseitin_0 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_D_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( sk_D_1
      = ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','31'])).

thf('33',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('39',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_B != sk_B )
    | ( zip_tseitin_0 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_D_1 @ sk_C_1 )
    | ( sk_D_1
      = ( k2_funct_1 @ sk_C_1 ) )
    | ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['32','33','34','39'])).

thf('41',plain,
    ( ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_C_1 )
    | ( sk_D_1
      = ( k2_funct_1 @ sk_C_1 ) )
    | ( zip_tseitin_0 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_D_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    sk_D_1
 != ( k2_funct_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_C_1 )
    | ( zip_tseitin_0 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_D_1 @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X6
        = ( k1_funct_1 @ X7 @ X4 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X4 @ X7 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('45',plain,
    ( ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_C_1 )
    | ( ( sk_D @ sk_D_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X16
        = ( k1_funct_1 @ X15 @ X14 ) )
      | ~ ( zip_tseitin_2 @ X14 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('47',plain,
    ( ( ( sk_D @ sk_D_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) )
    | ( ( sk_C @ sk_D_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_C_1 @ ( sk_D @ sk_D_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_C_1 )
    | ( ( sk_D @ sk_D_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('49',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X14 @ ( k1_relat_1 @ X15 ) )
      | ~ ( zip_tseitin_2 @ X14 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('50',plain,
    ( ( ( sk_D @ sk_D_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ( X36
        = ( k1_relset_1 @ X36 @ X37 @ X38 ) )
      | ~ ( zip_tseitin_5 @ X38 @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('53',plain,
    ( ~ ( zip_tseitin_5 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_4 @ X34 @ X35 )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('55',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( zip_tseitin_4 @ X39 @ X40 )
      | ( zip_tseitin_5 @ X41 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('57',plain,
    ( ( zip_tseitin_5 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_4 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_5 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    zip_tseitin_5 @ sk_C_1 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('63',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['53','60','63'])).

thf('65',plain,
    ( ( ( sk_D @ sk_D_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['50','64'])).

thf('66',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k1_funct_1 @ sk_D_1 @ X43 )
        = X44 )
      | ( ( k1_funct_1 @ sk_C_1 @ X44 )
       != X43 )
      | ~ ( r2_hidden @ X44 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X44: $i] :
      ( ~ ( r2_hidden @ X44 @ sk_A )
      | ( ( k1_funct_1 @ sk_D_1 @ ( k1_funct_1 @ sk_C_1 @ X44 ) )
        = X44 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( ( sk_D @ sk_D_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) )
    | ( ( k1_funct_1 @ sk_D_1 @ ( k1_funct_1 @ sk_C_1 @ ( sk_D @ sk_D_1 @ sk_C_1 ) ) )
      = ( sk_D @ sk_D_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,
    ( ( ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) )
      = ( sk_D @ sk_D_1 @ sk_C_1 ) )
    | ( ( sk_D @ sk_D_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) )
    | ( ( sk_D @ sk_D_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['47','68'])).

thf('70',plain,
    ( ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) )
    = ( sk_D @ sk_D_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_C_1 )
    | ( zip_tseitin_0 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_D_1 @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

thf('72',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k2_relat_1 @ X5 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X4 @ X7 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('73',plain,
    ( ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_C_1 )
    | ( r2_hidden @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['2','3'])).

thf('75',plain,
    ( ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_C_1 )
    | ( r2_hidden @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_B ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X16
        = ( k1_funct_1 @ X15 @ X14 ) )
      | ~ ( zip_tseitin_2 @ X14 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('77',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_B )
    | ( ( sk_C @ sk_D_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_C_1 @ ( sk_D @ sk_D_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_C_1 )
    | ( r2_hidden @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_B ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('79',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X14 @ ( k1_relat_1 @ X15 ) )
      | ~ ( zip_tseitin_2 @ X14 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('80',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['53','60','63'])).

thf('82',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X42: $i,X43: $i] :
      ( ( r2_hidden @ X42 @ sk_A )
      | ( ( k1_funct_1 @ sk_D_1 @ X43 )
       != X42 )
      | ~ ( r2_hidden @ X43 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X43: $i] :
      ( ~ ( r2_hidden @ X43 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X43 ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ sk_A )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['82','84'])).

thf('86',plain,
    ( ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) )
    = ( sk_D @ sk_D_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('87',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ sk_A )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ sk_A ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X43: $i,X44: $i] :
      ( ( r2_hidden @ X43 @ sk_B )
      | ( ( k1_funct_1 @ sk_C_1 @ X44 )
       != X43 )
      | ~ ( r2_hidden @ X44 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X44: $i] :
      ( ~ ( r2_hidden @ X44 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X44 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_D @ sk_D_1 @ sk_C_1 ) ) @ sk_B ),
    inference('sup-',[status(thm)],['88','90'])).

thf('92',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_B )
    | ( r2_hidden @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_B ) ),
    inference('sup+',[status(thm)],['77','91'])).

thf('93',plain,(
    r2_hidden @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_B ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['2','3'])).

thf('95',plain,(
    ! [X18: $i,X19: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_3 @ X18 @ X19 @ X21 @ X22 )
      | ~ ( r2_hidden @ X19 @ ( k2_relat_1 @ X22 ) )
      | ( X18
       != ( k1_funct_1 @ X21 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('96',plain,(
    ! [X19: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k2_relat_1 @ X22 ) )
      | ( zip_tseitin_3 @ ( k1_funct_1 @ X21 @ X19 ) @ X19 @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( zip_tseitin_3 @ ( k1_funct_1 @ X1 @ X0 ) @ X0 @ X1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['94','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( zip_tseitin_3 @ ( k1_funct_1 @ X0 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ X0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['93','97'])).

thf('99',plain,(
    zip_tseitin_3 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_D_1 @ sk_C_1 ),
    inference('sup+',[status(thm)],['70','98'])).

thf('100',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( ( k1_relat_1 @ X24 )
       != ( k2_relat_1 @ X23 ) )
      | ~ ( zip_tseitin_3 @ ( sk_D @ X24 @ X23 ) @ ( sk_C @ X24 @ X23 ) @ X24 @ X23 )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X24 @ X23 ) @ ( sk_C @ X24 @ X23 ) @ X24 @ X23 )
      | ( X24
        = ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_14])).

thf('101',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( sk_D_1
      = ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( zip_tseitin_1 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_D_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_D_1 )
     != ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['37','38'])).

thf('103',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ sk_A ),
    inference(simplify,[status(thm)],['87'])).

thf('105',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['53','60','63'])).

thf('106',plain,(
    ! [X9: $i,X10: $i,X11: $i,X13: $i] :
      ( ( zip_tseitin_1 @ X9 @ X10 @ X11 @ X13 )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X13 ) )
      | ( X10
       != ( k1_funct_1 @ X13 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('107',plain,(
    ! [X9: $i,X11: $i,X13: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X13 ) )
      | ( zip_tseitin_1 @ X9 @ ( k1_funct_1 @ X13 @ X9 ) @ X11 @ X13 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( zip_tseitin_1 @ X0 @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ X1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['105','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( k1_funct_1 @ sk_C_1 @ ( sk_D @ sk_D_1 @ sk_C_1 ) ) @ X0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['104','108'])).

thf('110',plain,(
    r2_hidden @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_B ),
    inference(simplify,[status(thm)],['92'])).

thf('111',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X42 )
        = X43 )
      | ( ( k1_funct_1 @ sk_D_1 @ X43 )
       != X42 )
      | ~ ( r2_hidden @ X43 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X43: $i] :
      ( ~ ( r2_hidden @ X43 @ sk_B )
      | ( ( k1_funct_1 @ sk_C_1 @ ( k1_funct_1 @ sk_D_1 @ X43 ) )
        = X43 ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) )
    = ( sk_C @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['110','112'])).

thf('114',plain,
    ( ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) )
    = ( sk_D @ sk_D_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('115',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_D @ sk_D_1 @ sk_C_1 ) )
    = ( sk_C @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ X0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['109','115'])).

thf('117',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['7','14','17'])).

thf('118',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['2','3'])).

thf('119',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['28','29'])).

thf('121',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( sk_D_1
      = ( k2_funct_1 @ sk_C_1 ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['101','102','103','116','117','118','119','120','121'])).

thf('123',plain,
    ( sk_D_1
    = ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    sk_D_1
 != ( k2_funct_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['123','124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yPZ0uAjF32
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:49:03 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.91/1.11  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.91/1.11  % Solved by: fo/fo7.sh
% 0.91/1.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.11  % done 608 iterations in 0.644s
% 0.91/1.11  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.91/1.11  % SZS output start Refutation
% 0.91/1.11  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.91/1.11  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.91/1.11  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.91/1.11  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.91/1.11  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.91/1.11  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.91/1.11  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.91/1.11  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.91/1.11  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.91/1.11  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.11  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.91/1.11  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.91/1.11  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.91/1.11  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.91/1.11  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $i > $o).
% 0.91/1.11  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.91/1.11  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.11  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.91/1.11  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $i > $o).
% 0.91/1.11  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.91/1.11  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.91/1.11  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.11  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.91/1.11  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.91/1.11  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.91/1.11  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.11  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.91/1.11  thf(t34_funct_2, conjecture,
% 0.91/1.11    (![A:$i,B:$i,C:$i]:
% 0.91/1.11     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.91/1.11         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.11       ( ![D:$i]:
% 0.91/1.11         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.91/1.11             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.91/1.11           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) & 
% 0.91/1.11               ( ![E:$i,F:$i]:
% 0.91/1.11                 ( ( ( ( r2_hidden @ F @ A ) & 
% 0.91/1.11                       ( ( k1_funct_1 @ C @ F ) = ( E ) ) ) =>
% 0.91/1.11                     ( ( r2_hidden @ E @ B ) & 
% 0.91/1.11                       ( ( k1_funct_1 @ D @ E ) = ( F ) ) ) ) & 
% 0.91/1.11                   ( ( ( r2_hidden @ E @ B ) & 
% 0.91/1.11                       ( ( k1_funct_1 @ D @ E ) = ( F ) ) ) =>
% 0.91/1.11                     ( ( r2_hidden @ F @ A ) & 
% 0.91/1.11                       ( ( k1_funct_1 @ C @ F ) = ( E ) ) ) ) ) ) ) =>
% 0.91/1.11             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.91/1.11               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.91/1.11  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.11    (~( ![A:$i,B:$i,C:$i]:
% 0.91/1.11        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.91/1.11            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.11          ( ![D:$i]:
% 0.91/1.11            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.91/1.11                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.91/1.11              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.91/1.11                  ( v2_funct_1 @ C ) & 
% 0.91/1.11                  ( ![E:$i,F:$i]:
% 0.91/1.11                    ( ( ( ( r2_hidden @ F @ A ) & 
% 0.91/1.11                          ( ( k1_funct_1 @ C @ F ) = ( E ) ) ) =>
% 0.91/1.11                        ( ( r2_hidden @ E @ B ) & 
% 0.91/1.11                          ( ( k1_funct_1 @ D @ E ) = ( F ) ) ) ) & 
% 0.91/1.11                      ( ( ( r2_hidden @ E @ B ) & 
% 0.91/1.11                          ( ( k1_funct_1 @ D @ E ) = ( F ) ) ) =>
% 0.91/1.11                        ( ( r2_hidden @ F @ A ) & 
% 0.91/1.11                          ( ( k1_funct_1 @ C @ F ) = ( E ) ) ) ) ) ) ) =>
% 0.91/1.11                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.91/1.11                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.91/1.11    inference('cnf.neg', [status(esa)], [t34_funct_2])).
% 0.91/1.11  thf('0', plain,
% 0.91/1.11      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf(redefinition_k2_relset_1, axiom,
% 0.91/1.11    (![A:$i,B:$i,C:$i]:
% 0.91/1.11     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.11       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.91/1.11  thf('1', plain,
% 0.91/1.11      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.91/1.11         (((k2_relset_1 @ X32 @ X33 @ X31) = (k2_relat_1 @ X31))
% 0.91/1.11          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.91/1.11      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.91/1.11  thf('2', plain,
% 0.91/1.11      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.91/1.11      inference('sup-', [status(thm)], ['0', '1'])).
% 0.91/1.11  thf('3', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('4', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 0.91/1.11      inference('sup+', [status(thm)], ['2', '3'])).
% 0.91/1.11  thf('5', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf(d1_funct_2, axiom,
% 0.91/1.11    (![A:$i,B:$i,C:$i]:
% 0.91/1.11     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.11       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.91/1.11           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.91/1.11             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.91/1.11         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.91/1.11           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.91/1.11             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.91/1.11  thf(zf_stmt_1, axiom,
% 0.91/1.11    (![C:$i,B:$i,A:$i]:
% 0.91/1.11     ( ( zip_tseitin_5 @ C @ B @ A ) =>
% 0.91/1.11       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.91/1.11  thf('6', plain,
% 0.91/1.11      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.91/1.11         (~ (v1_funct_2 @ X38 @ X36 @ X37)
% 0.91/1.11          | ((X36) = (k1_relset_1 @ X36 @ X37 @ X38))
% 0.91/1.11          | ~ (zip_tseitin_5 @ X38 @ X37 @ X36))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.11  thf('7', plain,
% 0.91/1.11      ((~ (zip_tseitin_5 @ sk_D_1 @ sk_A @ sk_B)
% 0.91/1.11        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D_1)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['5', '6'])).
% 0.91/1.11  thf(zf_stmt_2, axiom,
% 0.91/1.11    (![B:$i,A:$i]:
% 0.91/1.11     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.91/1.11       ( zip_tseitin_4 @ B @ A ) ))).
% 0.91/1.11  thf('8', plain,
% 0.91/1.11      (![X34 : $i, X35 : $i]:
% 0.91/1.11         ((zip_tseitin_4 @ X34 @ X35) | ((X34) = (k1_xboole_0)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.91/1.11  thf('9', plain,
% 0.91/1.11      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf(zf_stmt_3, type, zip_tseitin_5 : $i > $i > $i > $o).
% 0.91/1.11  thf(zf_stmt_4, type, zip_tseitin_4 : $i > $i > $o).
% 0.91/1.11  thf(zf_stmt_5, axiom,
% 0.91/1.11    (![A:$i,B:$i,C:$i]:
% 0.91/1.11     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.11       ( ( ( zip_tseitin_4 @ B @ A ) => ( zip_tseitin_5 @ C @ B @ A ) ) & 
% 0.91/1.11         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.91/1.11           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.91/1.11             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.91/1.11  thf('10', plain,
% 0.91/1.11      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.91/1.11         (~ (zip_tseitin_4 @ X39 @ X40)
% 0.91/1.11          | (zip_tseitin_5 @ X41 @ X39 @ X40)
% 0.91/1.11          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39))))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.91/1.11  thf('11', plain,
% 0.91/1.11      (((zip_tseitin_5 @ sk_D_1 @ sk_A @ sk_B)
% 0.91/1.11        | ~ (zip_tseitin_4 @ sk_A @ sk_B))),
% 0.91/1.11      inference('sup-', [status(thm)], ['9', '10'])).
% 0.91/1.11  thf('12', plain,
% 0.91/1.11      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_5 @ sk_D_1 @ sk_A @ sk_B))),
% 0.91/1.11      inference('sup-', [status(thm)], ['8', '11'])).
% 0.91/1.11  thf('13', plain, (((sk_A) != (k1_xboole_0))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('14', plain, ((zip_tseitin_5 @ sk_D_1 @ sk_A @ sk_B)),
% 0.91/1.11      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.91/1.11  thf('15', plain,
% 0.91/1.11      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf(redefinition_k1_relset_1, axiom,
% 0.91/1.11    (![A:$i,B:$i,C:$i]:
% 0.91/1.11     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.11       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.91/1.11  thf('16', plain,
% 0.91/1.11      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.91/1.11         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 0.91/1.11          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.91/1.11      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.91/1.11  thf('17', plain,
% 0.91/1.11      (((k1_relset_1 @ sk_B @ sk_A @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.91/1.11      inference('sup-', [status(thm)], ['15', '16'])).
% 0.91/1.11  thf('18', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 0.91/1.11      inference('demod', [status(thm)], ['7', '14', '17'])).
% 0.91/1.11  thf(t54_funct_1, axiom,
% 0.91/1.11    (![A:$i]:
% 0.91/1.11     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.91/1.11       ( ( v2_funct_1 @ A ) =>
% 0.91/1.11         ( ![B:$i]:
% 0.91/1.11           ( ( ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) =>
% 0.91/1.11             ( ( ( B ) = ( k2_funct_1 @ A ) ) <=>
% 0.91/1.11               ( ( ![C:$i,D:$i]:
% 0.91/1.11                   ( ( ( ( ( D ) = ( k1_funct_1 @ B @ C ) ) & 
% 0.91/1.11                         ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) =>
% 0.91/1.11                       ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.91/1.11                         ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) & 
% 0.91/1.11                     ( ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.91/1.11                         ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) =>
% 0.91/1.11                       ( ( ( D ) = ( k1_funct_1 @ B @ C ) ) & 
% 0.91/1.11                         ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) ) ) ) & 
% 0.91/1.11                 ( ( k1_relat_1 @ B ) = ( k2_relat_1 @ A ) ) ) ) ) ) ) ))).
% 0.91/1.11  thf(zf_stmt_6, axiom,
% 0.91/1.11    (![D:$i,C:$i,B:$i,A:$i]:
% 0.91/1.11     ( ( zip_tseitin_1 @ D @ C @ B @ A ) <=>
% 0.91/1.11       ( ( zip_tseitin_0 @ D @ C @ B @ A ) =>
% 0.91/1.11         ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.91/1.11           ( ( C ) = ( k1_funct_1 @ A @ D ) ) ) ) ))).
% 0.91/1.11  thf('19', plain,
% 0.91/1.11      (![X9 : $i, X10 : $i, X11 : $i, X13 : $i]:
% 0.91/1.11         ((zip_tseitin_1 @ X9 @ X10 @ X11 @ X13)
% 0.91/1.11          | (zip_tseitin_0 @ X9 @ X10 @ X11 @ X13))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.91/1.11  thf(zf_stmt_7, axiom,
% 0.91/1.11    (![D:$i,C:$i,B:$i,A:$i]:
% 0.91/1.11     ( ( zip_tseitin_3 @ D @ C @ B @ A ) <=>
% 0.91/1.11       ( ( zip_tseitin_2 @ D @ C @ A ) =>
% 0.91/1.11         ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) & 
% 0.91/1.11           ( ( D ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.91/1.11  thf('20', plain,
% 0.91/1.11      (![X18 : $i, X19 : $i, X21 : $i, X22 : $i]:
% 0.91/1.11         ((zip_tseitin_3 @ X18 @ X19 @ X21 @ X22)
% 0.91/1.11          | (zip_tseitin_2 @ X18 @ X19 @ X22))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.91/1.11  thf(zf_stmt_8, type, zip_tseitin_3 : $i > $i > $i > $i > $o).
% 0.91/1.11  thf(zf_stmt_9, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.91/1.11  thf(zf_stmt_10, axiom,
% 0.91/1.11    (![D:$i,C:$i,A:$i]:
% 0.91/1.11     ( ( zip_tseitin_2 @ D @ C @ A ) <=>
% 0.91/1.11       ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.91/1.11         ( ( C ) = ( k1_funct_1 @ A @ D ) ) ) ))).
% 0.91/1.11  thf(zf_stmt_11, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.91/1.11  thf(zf_stmt_12, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.91/1.11  thf(zf_stmt_13, axiom,
% 0.91/1.11    (![D:$i,C:$i,B:$i,A:$i]:
% 0.91/1.11     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.91/1.11       ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) & 
% 0.91/1.11         ( ( D ) = ( k1_funct_1 @ B @ C ) ) ) ))).
% 0.91/1.11  thf(zf_stmt_14, axiom,
% 0.91/1.11    (![A:$i]:
% 0.91/1.11     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.91/1.11       ( ( v2_funct_1 @ A ) =>
% 0.91/1.11         ( ![B:$i]:
% 0.91/1.11           ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.91/1.11             ( ( ( B ) = ( k2_funct_1 @ A ) ) <=>
% 0.91/1.11               ( ( ( k1_relat_1 @ B ) = ( k2_relat_1 @ A ) ) & 
% 0.91/1.11                 ( ![C:$i,D:$i]:
% 0.91/1.11                   ( ( zip_tseitin_3 @ D @ C @ B @ A ) & 
% 0.91/1.11                     ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ))).
% 0.91/1.11  thf('21', plain,
% 0.91/1.11      (![X23 : $i, X24 : $i]:
% 0.91/1.11         (~ (v2_funct_1 @ X23)
% 0.91/1.11          | ~ (v1_relat_1 @ X24)
% 0.91/1.11          | ~ (v1_funct_1 @ X24)
% 0.91/1.11          | ((k1_relat_1 @ X24) != (k2_relat_1 @ X23))
% 0.91/1.11          | ~ (zip_tseitin_3 @ (sk_D @ X24 @ X23) @ (sk_C @ X24 @ X23) @ X24 @ 
% 0.91/1.11               X23)
% 0.91/1.11          | ~ (zip_tseitin_1 @ (sk_D @ X24 @ X23) @ (sk_C @ X24 @ X23) @ X24 @ 
% 0.91/1.11               X23)
% 0.91/1.11          | ((X24) = (k2_funct_1 @ X23))
% 0.91/1.11          | ~ (v1_funct_1 @ X23)
% 0.91/1.11          | ~ (v1_relat_1 @ X23))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_14])).
% 0.91/1.11  thf('22', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]:
% 0.91/1.11         ((zip_tseitin_2 @ (sk_D @ X1 @ X0) @ (sk_C @ X1 @ X0) @ X0)
% 0.91/1.11          | ~ (v1_relat_1 @ X0)
% 0.91/1.11          | ~ (v1_funct_1 @ X0)
% 0.91/1.11          | ((X1) = (k2_funct_1 @ X0))
% 0.91/1.11          | ~ (zip_tseitin_1 @ (sk_D @ X1 @ X0) @ (sk_C @ X1 @ X0) @ X1 @ X0)
% 0.91/1.11          | ((k1_relat_1 @ X1) != (k2_relat_1 @ X0))
% 0.91/1.11          | ~ (v1_funct_1 @ X1)
% 0.91/1.11          | ~ (v1_relat_1 @ X1)
% 0.91/1.11          | ~ (v2_funct_1 @ X0))),
% 0.91/1.11      inference('sup-', [status(thm)], ['20', '21'])).
% 0.91/1.11  thf('23', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]:
% 0.91/1.11         ((zip_tseitin_0 @ (sk_D @ X1 @ X0) @ (sk_C @ X1 @ X0) @ X1 @ X0)
% 0.91/1.11          | ~ (v2_funct_1 @ X0)
% 0.91/1.11          | ~ (v1_relat_1 @ X1)
% 0.91/1.11          | ~ (v1_funct_1 @ X1)
% 0.91/1.11          | ((k1_relat_1 @ X1) != (k2_relat_1 @ X0))
% 0.91/1.11          | ((X1) = (k2_funct_1 @ X0))
% 0.91/1.11          | ~ (v1_funct_1 @ X0)
% 0.91/1.11          | ~ (v1_relat_1 @ X0)
% 0.91/1.11          | (zip_tseitin_2 @ (sk_D @ X1 @ X0) @ (sk_C @ X1 @ X0) @ X0))),
% 0.91/1.11      inference('sup-', [status(thm)], ['19', '22'])).
% 0.91/1.11  thf('24', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         (((sk_B) != (k2_relat_1 @ X0))
% 0.91/1.11          | (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0) @ (sk_C @ sk_D_1 @ X0) @ X0)
% 0.91/1.11          | ~ (v1_relat_1 @ X0)
% 0.91/1.11          | ~ (v1_funct_1 @ X0)
% 0.91/1.11          | ((sk_D_1) = (k2_funct_1 @ X0))
% 0.91/1.11          | ~ (v1_funct_1 @ sk_D_1)
% 0.91/1.11          | ~ (v1_relat_1 @ sk_D_1)
% 0.91/1.11          | ~ (v2_funct_1 @ X0)
% 0.91/1.11          | (zip_tseitin_0 @ (sk_D @ sk_D_1 @ X0) @ (sk_C @ sk_D_1 @ X0) @ 
% 0.91/1.11             sk_D_1 @ X0))),
% 0.91/1.11      inference('sup-', [status(thm)], ['18', '23'])).
% 0.91/1.11  thf('25', plain, ((v1_funct_1 @ sk_D_1)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('26', plain,
% 0.91/1.11      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf(cc2_relat_1, axiom,
% 0.91/1.11    (![A:$i]:
% 0.91/1.11     ( ( v1_relat_1 @ A ) =>
% 0.91/1.11       ( ![B:$i]:
% 0.91/1.11         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.91/1.11  thf('27', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]:
% 0.91/1.11         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.91/1.11          | (v1_relat_1 @ X0)
% 0.91/1.11          | ~ (v1_relat_1 @ X1))),
% 0.91/1.11      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.91/1.11  thf('28', plain,
% 0.91/1.11      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D_1))),
% 0.91/1.11      inference('sup-', [status(thm)], ['26', '27'])).
% 0.91/1.11  thf(fc6_relat_1, axiom,
% 0.91/1.11    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.91/1.11  thf('29', plain,
% 0.91/1.11      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.91/1.11      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.91/1.11  thf('30', plain, ((v1_relat_1 @ sk_D_1)),
% 0.91/1.11      inference('demod', [status(thm)], ['28', '29'])).
% 0.91/1.11  thf('31', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         (((sk_B) != (k2_relat_1 @ X0))
% 0.91/1.11          | (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0) @ (sk_C @ sk_D_1 @ X0) @ X0)
% 0.91/1.11          | ~ (v1_relat_1 @ X0)
% 0.91/1.11          | ~ (v1_funct_1 @ X0)
% 0.91/1.11          | ((sk_D_1) = (k2_funct_1 @ X0))
% 0.91/1.11          | ~ (v2_funct_1 @ X0)
% 0.91/1.11          | (zip_tseitin_0 @ (sk_D @ sk_D_1 @ X0) @ (sk_C @ sk_D_1 @ X0) @ 
% 0.91/1.11             sk_D_1 @ X0))),
% 0.91/1.11      inference('demod', [status(thm)], ['24', '25', '30'])).
% 0.91/1.11  thf('32', plain,
% 0.91/1.11      ((((sk_B) != (sk_B))
% 0.91/1.11        | (zip_tseitin_0 @ (sk_D @ sk_D_1 @ sk_C_1) @ 
% 0.91/1.11           (sk_C @ sk_D_1 @ sk_C_1) @ sk_D_1 @ sk_C_1)
% 0.91/1.11        | ~ (v2_funct_1 @ sk_C_1)
% 0.91/1.11        | ((sk_D_1) = (k2_funct_1 @ sk_C_1))
% 0.91/1.11        | ~ (v1_funct_1 @ sk_C_1)
% 0.91/1.11        | ~ (v1_relat_1 @ sk_C_1)
% 0.91/1.11        | (zip_tseitin_2 @ (sk_D @ sk_D_1 @ sk_C_1) @ 
% 0.91/1.11           (sk_C @ sk_D_1 @ sk_C_1) @ sk_C_1))),
% 0.91/1.11      inference('sup-', [status(thm)], ['4', '31'])).
% 0.91/1.11  thf('33', plain, ((v2_funct_1 @ sk_C_1)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('34', plain, ((v1_funct_1 @ sk_C_1)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('35', plain,
% 0.91/1.11      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('36', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]:
% 0.91/1.11         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.91/1.11          | (v1_relat_1 @ X0)
% 0.91/1.11          | ~ (v1_relat_1 @ X1))),
% 0.91/1.11      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.91/1.11  thf('37', plain,
% 0.91/1.11      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_1))),
% 0.91/1.11      inference('sup-', [status(thm)], ['35', '36'])).
% 0.91/1.11  thf('38', plain,
% 0.91/1.11      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.91/1.11      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.91/1.11  thf('39', plain, ((v1_relat_1 @ sk_C_1)),
% 0.91/1.11      inference('demod', [status(thm)], ['37', '38'])).
% 0.91/1.11  thf('40', plain,
% 0.91/1.11      ((((sk_B) != (sk_B))
% 0.91/1.11        | (zip_tseitin_0 @ (sk_D @ sk_D_1 @ sk_C_1) @ 
% 0.91/1.11           (sk_C @ sk_D_1 @ sk_C_1) @ sk_D_1 @ sk_C_1)
% 0.91/1.11        | ((sk_D_1) = (k2_funct_1 @ sk_C_1))
% 0.91/1.11        | (zip_tseitin_2 @ (sk_D @ sk_D_1 @ sk_C_1) @ 
% 0.91/1.11           (sk_C @ sk_D_1 @ sk_C_1) @ sk_C_1))),
% 0.91/1.11      inference('demod', [status(thm)], ['32', '33', '34', '39'])).
% 0.91/1.11  thf('41', plain,
% 0.91/1.11      (((zip_tseitin_2 @ (sk_D @ sk_D_1 @ sk_C_1) @ (sk_C @ sk_D_1 @ sk_C_1) @ 
% 0.91/1.11         sk_C_1)
% 0.91/1.11        | ((sk_D_1) = (k2_funct_1 @ sk_C_1))
% 0.91/1.11        | (zip_tseitin_0 @ (sk_D @ sk_D_1 @ sk_C_1) @ 
% 0.91/1.11           (sk_C @ sk_D_1 @ sk_C_1) @ sk_D_1 @ sk_C_1))),
% 0.91/1.11      inference('simplify', [status(thm)], ['40'])).
% 0.91/1.11  thf('42', plain, (((sk_D_1) != (k2_funct_1 @ sk_C_1))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('43', plain,
% 0.91/1.11      (((zip_tseitin_2 @ (sk_D @ sk_D_1 @ sk_C_1) @ (sk_C @ sk_D_1 @ sk_C_1) @ 
% 0.91/1.11         sk_C_1)
% 0.91/1.11        | (zip_tseitin_0 @ (sk_D @ sk_D_1 @ sk_C_1) @ 
% 0.91/1.11           (sk_C @ sk_D_1 @ sk_C_1) @ sk_D_1 @ sk_C_1))),
% 0.91/1.11      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 0.91/1.11  thf('44', plain,
% 0.91/1.11      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.91/1.11         (((X6) = (k1_funct_1 @ X7 @ X4))
% 0.91/1.11          | ~ (zip_tseitin_0 @ X6 @ X4 @ X7 @ X5))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.91/1.11  thf('45', plain,
% 0.91/1.11      (((zip_tseitin_2 @ (sk_D @ sk_D_1 @ sk_C_1) @ (sk_C @ sk_D_1 @ sk_C_1) @ 
% 0.91/1.11         sk_C_1)
% 0.91/1.11        | ((sk_D @ sk_D_1 @ sk_C_1)
% 0.91/1.11            = (k1_funct_1 @ sk_D_1 @ (sk_C @ sk_D_1 @ sk_C_1))))),
% 0.91/1.11      inference('sup-', [status(thm)], ['43', '44'])).
% 0.91/1.11  thf('46', plain,
% 0.91/1.11      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.91/1.11         (((X16) = (k1_funct_1 @ X15 @ X14))
% 0.91/1.11          | ~ (zip_tseitin_2 @ X14 @ X16 @ X15))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_10])).
% 0.91/1.11  thf('47', plain,
% 0.91/1.11      ((((sk_D @ sk_D_1 @ sk_C_1)
% 0.91/1.11          = (k1_funct_1 @ sk_D_1 @ (sk_C @ sk_D_1 @ sk_C_1)))
% 0.91/1.11        | ((sk_C @ sk_D_1 @ sk_C_1)
% 0.91/1.11            = (k1_funct_1 @ sk_C_1 @ (sk_D @ sk_D_1 @ sk_C_1))))),
% 0.91/1.11      inference('sup-', [status(thm)], ['45', '46'])).
% 0.91/1.11  thf('48', plain,
% 0.91/1.11      (((zip_tseitin_2 @ (sk_D @ sk_D_1 @ sk_C_1) @ (sk_C @ sk_D_1 @ sk_C_1) @ 
% 0.91/1.11         sk_C_1)
% 0.91/1.11        | ((sk_D @ sk_D_1 @ sk_C_1)
% 0.91/1.11            = (k1_funct_1 @ sk_D_1 @ (sk_C @ sk_D_1 @ sk_C_1))))),
% 0.91/1.11      inference('sup-', [status(thm)], ['43', '44'])).
% 0.91/1.11  thf('49', plain,
% 0.91/1.11      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.91/1.11         ((r2_hidden @ X14 @ (k1_relat_1 @ X15))
% 0.91/1.11          | ~ (zip_tseitin_2 @ X14 @ X16 @ X15))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_10])).
% 0.91/1.11  thf('50', plain,
% 0.91/1.11      ((((sk_D @ sk_D_1 @ sk_C_1)
% 0.91/1.11          = (k1_funct_1 @ sk_D_1 @ (sk_C @ sk_D_1 @ sk_C_1)))
% 0.91/1.11        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1) @ (k1_relat_1 @ sk_C_1)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['48', '49'])).
% 0.91/1.11  thf('51', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('52', plain,
% 0.91/1.11      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.91/1.11         (~ (v1_funct_2 @ X38 @ X36 @ X37)
% 0.91/1.11          | ((X36) = (k1_relset_1 @ X36 @ X37 @ X38))
% 0.91/1.11          | ~ (zip_tseitin_5 @ X38 @ X37 @ X36))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.11  thf('53', plain,
% 0.91/1.11      ((~ (zip_tseitin_5 @ sk_C_1 @ sk_B @ sk_A)
% 0.91/1.11        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['51', '52'])).
% 0.91/1.11  thf('54', plain,
% 0.91/1.11      (![X34 : $i, X35 : $i]:
% 0.91/1.11         ((zip_tseitin_4 @ X34 @ X35) | ((X34) = (k1_xboole_0)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.91/1.11  thf('55', plain,
% 0.91/1.11      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('56', plain,
% 0.91/1.11      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.91/1.11         (~ (zip_tseitin_4 @ X39 @ X40)
% 0.91/1.11          | (zip_tseitin_5 @ X41 @ X39 @ X40)
% 0.91/1.11          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39))))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.91/1.11  thf('57', plain,
% 0.91/1.11      (((zip_tseitin_5 @ sk_C_1 @ sk_B @ sk_A)
% 0.91/1.11        | ~ (zip_tseitin_4 @ sk_B @ sk_A))),
% 0.91/1.11      inference('sup-', [status(thm)], ['55', '56'])).
% 0.91/1.11  thf('58', plain,
% 0.91/1.11      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_5 @ sk_C_1 @ sk_B @ sk_A))),
% 0.91/1.11      inference('sup-', [status(thm)], ['54', '57'])).
% 0.91/1.11  thf('59', plain, (((sk_B) != (k1_xboole_0))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('60', plain, ((zip_tseitin_5 @ sk_C_1 @ sk_B @ sk_A)),
% 0.91/1.11      inference('simplify_reflect-', [status(thm)], ['58', '59'])).
% 0.91/1.11  thf('61', plain,
% 0.91/1.11      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('62', plain,
% 0.91/1.11      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.91/1.11         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 0.91/1.11          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.91/1.11      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.91/1.11  thf('63', plain,
% 0.91/1.11      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.91/1.11      inference('sup-', [status(thm)], ['61', '62'])).
% 0.91/1.11  thf('64', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.91/1.11      inference('demod', [status(thm)], ['53', '60', '63'])).
% 0.91/1.11  thf('65', plain,
% 0.91/1.11      ((((sk_D @ sk_D_1 @ sk_C_1)
% 0.91/1.11          = (k1_funct_1 @ sk_D_1 @ (sk_C @ sk_D_1 @ sk_C_1)))
% 0.91/1.11        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1) @ sk_A))),
% 0.91/1.11      inference('demod', [status(thm)], ['50', '64'])).
% 0.91/1.11  thf('66', plain,
% 0.91/1.11      (![X43 : $i, X44 : $i]:
% 0.91/1.11         (((k1_funct_1 @ sk_D_1 @ X43) = (X44))
% 0.91/1.11          | ((k1_funct_1 @ sk_C_1 @ X44) != (X43))
% 0.91/1.11          | ~ (r2_hidden @ X44 @ sk_A))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('67', plain,
% 0.91/1.11      (![X44 : $i]:
% 0.91/1.11         (~ (r2_hidden @ X44 @ sk_A)
% 0.91/1.11          | ((k1_funct_1 @ sk_D_1 @ (k1_funct_1 @ sk_C_1 @ X44)) = (X44)))),
% 0.91/1.11      inference('simplify', [status(thm)], ['66'])).
% 0.91/1.11  thf('68', plain,
% 0.91/1.11      ((((sk_D @ sk_D_1 @ sk_C_1)
% 0.91/1.11          = (k1_funct_1 @ sk_D_1 @ (sk_C @ sk_D_1 @ sk_C_1)))
% 0.91/1.11        | ((k1_funct_1 @ sk_D_1 @ 
% 0.91/1.11            (k1_funct_1 @ sk_C_1 @ (sk_D @ sk_D_1 @ sk_C_1)))
% 0.91/1.11            = (sk_D @ sk_D_1 @ sk_C_1)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['65', '67'])).
% 0.91/1.11  thf('69', plain,
% 0.91/1.11      ((((k1_funct_1 @ sk_D_1 @ (sk_C @ sk_D_1 @ sk_C_1))
% 0.91/1.11          = (sk_D @ sk_D_1 @ sk_C_1))
% 0.91/1.11        | ((sk_D @ sk_D_1 @ sk_C_1)
% 0.91/1.11            = (k1_funct_1 @ sk_D_1 @ (sk_C @ sk_D_1 @ sk_C_1)))
% 0.91/1.11        | ((sk_D @ sk_D_1 @ sk_C_1)
% 0.91/1.11            = (k1_funct_1 @ sk_D_1 @ (sk_C @ sk_D_1 @ sk_C_1))))),
% 0.91/1.11      inference('sup+', [status(thm)], ['47', '68'])).
% 0.91/1.11  thf('70', plain,
% 0.91/1.11      (((k1_funct_1 @ sk_D_1 @ (sk_C @ sk_D_1 @ sk_C_1))
% 0.91/1.11         = (sk_D @ sk_D_1 @ sk_C_1))),
% 0.91/1.11      inference('simplify', [status(thm)], ['69'])).
% 0.91/1.11  thf('71', plain,
% 0.91/1.11      (((zip_tseitin_2 @ (sk_D @ sk_D_1 @ sk_C_1) @ (sk_C @ sk_D_1 @ sk_C_1) @ 
% 0.91/1.11         sk_C_1)
% 0.91/1.11        | (zip_tseitin_0 @ (sk_D @ sk_D_1 @ sk_C_1) @ 
% 0.91/1.11           (sk_C @ sk_D_1 @ sk_C_1) @ sk_D_1 @ sk_C_1))),
% 0.91/1.11      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 0.91/1.11  thf('72', plain,
% 0.91/1.11      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.91/1.11         ((r2_hidden @ X4 @ (k2_relat_1 @ X5))
% 0.91/1.11          | ~ (zip_tseitin_0 @ X6 @ X4 @ X7 @ X5))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.91/1.11  thf('73', plain,
% 0.91/1.11      (((zip_tseitin_2 @ (sk_D @ sk_D_1 @ sk_C_1) @ (sk_C @ sk_D_1 @ sk_C_1) @ 
% 0.91/1.11         sk_C_1)
% 0.91/1.11        | (r2_hidden @ (sk_C @ sk_D_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['71', '72'])).
% 0.91/1.11  thf('74', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 0.91/1.11      inference('sup+', [status(thm)], ['2', '3'])).
% 0.91/1.11  thf('75', plain,
% 0.91/1.11      (((zip_tseitin_2 @ (sk_D @ sk_D_1 @ sk_C_1) @ (sk_C @ sk_D_1 @ sk_C_1) @ 
% 0.91/1.11         sk_C_1)
% 0.91/1.11        | (r2_hidden @ (sk_C @ sk_D_1 @ sk_C_1) @ sk_B))),
% 0.91/1.11      inference('demod', [status(thm)], ['73', '74'])).
% 0.91/1.11  thf('76', plain,
% 0.91/1.11      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.91/1.11         (((X16) = (k1_funct_1 @ X15 @ X14))
% 0.91/1.11          | ~ (zip_tseitin_2 @ X14 @ X16 @ X15))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_10])).
% 0.91/1.11  thf('77', plain,
% 0.91/1.11      (((r2_hidden @ (sk_C @ sk_D_1 @ sk_C_1) @ sk_B)
% 0.91/1.11        | ((sk_C @ sk_D_1 @ sk_C_1)
% 0.91/1.11            = (k1_funct_1 @ sk_C_1 @ (sk_D @ sk_D_1 @ sk_C_1))))),
% 0.91/1.11      inference('sup-', [status(thm)], ['75', '76'])).
% 0.91/1.11  thf('78', plain,
% 0.91/1.11      (((zip_tseitin_2 @ (sk_D @ sk_D_1 @ sk_C_1) @ (sk_C @ sk_D_1 @ sk_C_1) @ 
% 0.91/1.11         sk_C_1)
% 0.91/1.11        | (r2_hidden @ (sk_C @ sk_D_1 @ sk_C_1) @ sk_B))),
% 0.91/1.11      inference('demod', [status(thm)], ['73', '74'])).
% 0.91/1.11  thf('79', plain,
% 0.91/1.11      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.91/1.11         ((r2_hidden @ X14 @ (k1_relat_1 @ X15))
% 0.91/1.11          | ~ (zip_tseitin_2 @ X14 @ X16 @ X15))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_10])).
% 0.91/1.11  thf('80', plain,
% 0.91/1.11      (((r2_hidden @ (sk_C @ sk_D_1 @ sk_C_1) @ sk_B)
% 0.91/1.11        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1) @ (k1_relat_1 @ sk_C_1)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['78', '79'])).
% 0.91/1.11  thf('81', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.91/1.11      inference('demod', [status(thm)], ['53', '60', '63'])).
% 0.91/1.11  thf('82', plain,
% 0.91/1.11      (((r2_hidden @ (sk_C @ sk_D_1 @ sk_C_1) @ sk_B)
% 0.91/1.11        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1) @ sk_A))),
% 0.91/1.11      inference('demod', [status(thm)], ['80', '81'])).
% 0.91/1.11  thf('83', plain,
% 0.91/1.11      (![X42 : $i, X43 : $i]:
% 0.91/1.11         ((r2_hidden @ X42 @ sk_A)
% 0.91/1.11          | ((k1_funct_1 @ sk_D_1 @ X43) != (X42))
% 0.91/1.11          | ~ (r2_hidden @ X43 @ sk_B))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('84', plain,
% 0.91/1.11      (![X43 : $i]:
% 0.91/1.11         (~ (r2_hidden @ X43 @ sk_B)
% 0.91/1.11          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ X43) @ sk_A))),
% 0.91/1.11      inference('simplify', [status(thm)], ['83'])).
% 0.91/1.11  thf('85', plain,
% 0.91/1.11      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1) @ sk_A)
% 0.91/1.11        | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ (sk_C @ sk_D_1 @ sk_C_1)) @ sk_A))),
% 0.91/1.11      inference('sup-', [status(thm)], ['82', '84'])).
% 0.91/1.11  thf('86', plain,
% 0.91/1.11      (((k1_funct_1 @ sk_D_1 @ (sk_C @ sk_D_1 @ sk_C_1))
% 0.91/1.11         = (sk_D @ sk_D_1 @ sk_C_1))),
% 0.91/1.11      inference('simplify', [status(thm)], ['69'])).
% 0.91/1.11  thf('87', plain,
% 0.91/1.11      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1) @ sk_A)
% 0.91/1.11        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1) @ sk_A))),
% 0.91/1.11      inference('demod', [status(thm)], ['85', '86'])).
% 0.91/1.11  thf('88', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1) @ sk_A)),
% 0.91/1.11      inference('simplify', [status(thm)], ['87'])).
% 0.91/1.11  thf('89', plain,
% 0.91/1.11      (![X43 : $i, X44 : $i]:
% 0.91/1.11         ((r2_hidden @ X43 @ sk_B)
% 0.91/1.11          | ((k1_funct_1 @ sk_C_1 @ X44) != (X43))
% 0.91/1.11          | ~ (r2_hidden @ X44 @ sk_A))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('90', plain,
% 0.91/1.11      (![X44 : $i]:
% 0.91/1.11         (~ (r2_hidden @ X44 @ sk_A)
% 0.91/1.11          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ X44) @ sk_B))),
% 0.91/1.11      inference('simplify', [status(thm)], ['89'])).
% 0.91/1.11  thf('91', plain,
% 0.91/1.11      ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ (sk_D @ sk_D_1 @ sk_C_1)) @ sk_B)),
% 0.91/1.11      inference('sup-', [status(thm)], ['88', '90'])).
% 0.91/1.11  thf('92', plain,
% 0.91/1.11      (((r2_hidden @ (sk_C @ sk_D_1 @ sk_C_1) @ sk_B)
% 0.91/1.11        | (r2_hidden @ (sk_C @ sk_D_1 @ sk_C_1) @ sk_B))),
% 0.91/1.11      inference('sup+', [status(thm)], ['77', '91'])).
% 0.91/1.11  thf('93', plain, ((r2_hidden @ (sk_C @ sk_D_1 @ sk_C_1) @ sk_B)),
% 0.91/1.11      inference('simplify', [status(thm)], ['92'])).
% 0.91/1.11  thf('94', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 0.91/1.11      inference('sup+', [status(thm)], ['2', '3'])).
% 0.91/1.11  thf('95', plain,
% 0.91/1.11      (![X18 : $i, X19 : $i, X21 : $i, X22 : $i]:
% 0.91/1.11         ((zip_tseitin_3 @ X18 @ X19 @ X21 @ X22)
% 0.91/1.11          | ~ (r2_hidden @ X19 @ (k2_relat_1 @ X22))
% 0.91/1.11          | ((X18) != (k1_funct_1 @ X21 @ X19)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.91/1.11  thf('96', plain,
% 0.91/1.11      (![X19 : $i, X21 : $i, X22 : $i]:
% 0.91/1.11         (~ (r2_hidden @ X19 @ (k2_relat_1 @ X22))
% 0.91/1.11          | (zip_tseitin_3 @ (k1_funct_1 @ X21 @ X19) @ X19 @ X21 @ X22))),
% 0.91/1.11      inference('simplify', [status(thm)], ['95'])).
% 0.91/1.11  thf('97', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]:
% 0.91/1.11         (~ (r2_hidden @ X0 @ sk_B)
% 0.91/1.11          | (zip_tseitin_3 @ (k1_funct_1 @ X1 @ X0) @ X0 @ X1 @ sk_C_1))),
% 0.91/1.11      inference('sup-', [status(thm)], ['94', '96'])).
% 0.91/1.11  thf('98', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         (zip_tseitin_3 @ (k1_funct_1 @ X0 @ (sk_C @ sk_D_1 @ sk_C_1)) @ 
% 0.91/1.11          (sk_C @ sk_D_1 @ sk_C_1) @ X0 @ sk_C_1)),
% 0.91/1.11      inference('sup-', [status(thm)], ['93', '97'])).
% 0.91/1.11  thf('99', plain,
% 0.91/1.11      ((zip_tseitin_3 @ (sk_D @ sk_D_1 @ sk_C_1) @ (sk_C @ sk_D_1 @ sk_C_1) @ 
% 0.91/1.11        sk_D_1 @ sk_C_1)),
% 0.91/1.11      inference('sup+', [status(thm)], ['70', '98'])).
% 0.91/1.11  thf('100', plain,
% 0.91/1.11      (![X23 : $i, X24 : $i]:
% 0.91/1.11         (~ (v2_funct_1 @ X23)
% 0.91/1.11          | ~ (v1_relat_1 @ X24)
% 0.91/1.11          | ~ (v1_funct_1 @ X24)
% 0.91/1.11          | ((k1_relat_1 @ X24) != (k2_relat_1 @ X23))
% 0.91/1.11          | ~ (zip_tseitin_3 @ (sk_D @ X24 @ X23) @ (sk_C @ X24 @ X23) @ X24 @ 
% 0.91/1.11               X23)
% 0.91/1.11          | ~ (zip_tseitin_1 @ (sk_D @ X24 @ X23) @ (sk_C @ X24 @ X23) @ X24 @ 
% 0.91/1.11               X23)
% 0.91/1.11          | ((X24) = (k2_funct_1 @ X23))
% 0.91/1.11          | ~ (v1_funct_1 @ X23)
% 0.91/1.11          | ~ (v1_relat_1 @ X23))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_14])).
% 0.91/1.11  thf('101', plain,
% 0.91/1.11      ((~ (v1_relat_1 @ sk_C_1)
% 0.91/1.11        | ~ (v1_funct_1 @ sk_C_1)
% 0.91/1.11        | ((sk_D_1) = (k2_funct_1 @ sk_C_1))
% 0.91/1.11        | ~ (zip_tseitin_1 @ (sk_D @ sk_D_1 @ sk_C_1) @ 
% 0.91/1.11             (sk_C @ sk_D_1 @ sk_C_1) @ sk_D_1 @ sk_C_1)
% 0.91/1.11        | ((k1_relat_1 @ sk_D_1) != (k2_relat_1 @ sk_C_1))
% 0.91/1.11        | ~ (v1_funct_1 @ sk_D_1)
% 0.91/1.11        | ~ (v1_relat_1 @ sk_D_1)
% 0.91/1.11        | ~ (v2_funct_1 @ sk_C_1))),
% 0.91/1.11      inference('sup-', [status(thm)], ['99', '100'])).
% 0.91/1.11  thf('102', plain, ((v1_relat_1 @ sk_C_1)),
% 0.91/1.11      inference('demod', [status(thm)], ['37', '38'])).
% 0.91/1.11  thf('103', plain, ((v1_funct_1 @ sk_C_1)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('104', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1) @ sk_A)),
% 0.91/1.11      inference('simplify', [status(thm)], ['87'])).
% 0.91/1.11  thf('105', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.91/1.11      inference('demod', [status(thm)], ['53', '60', '63'])).
% 0.91/1.11  thf('106', plain,
% 0.91/1.11      (![X9 : $i, X10 : $i, X11 : $i, X13 : $i]:
% 0.91/1.11         ((zip_tseitin_1 @ X9 @ X10 @ X11 @ X13)
% 0.91/1.11          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ X13))
% 0.91/1.11          | ((X10) != (k1_funct_1 @ X13 @ X9)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.91/1.11  thf('107', plain,
% 0.91/1.11      (![X9 : $i, X11 : $i, X13 : $i]:
% 0.91/1.11         (~ (r2_hidden @ X9 @ (k1_relat_1 @ X13))
% 0.91/1.11          | (zip_tseitin_1 @ X9 @ (k1_funct_1 @ X13 @ X9) @ X11 @ X13))),
% 0.91/1.11      inference('simplify', [status(thm)], ['106'])).
% 0.91/1.11  thf('108', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]:
% 0.91/1.11         (~ (r2_hidden @ X0 @ sk_A)
% 0.91/1.11          | (zip_tseitin_1 @ X0 @ (k1_funct_1 @ sk_C_1 @ X0) @ X1 @ sk_C_1))),
% 0.91/1.11      inference('sup-', [status(thm)], ['105', '107'])).
% 0.91/1.11  thf('109', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         (zip_tseitin_1 @ (sk_D @ sk_D_1 @ sk_C_1) @ 
% 0.91/1.11          (k1_funct_1 @ sk_C_1 @ (sk_D @ sk_D_1 @ sk_C_1)) @ X0 @ sk_C_1)),
% 0.91/1.11      inference('sup-', [status(thm)], ['104', '108'])).
% 0.91/1.11  thf('110', plain, ((r2_hidden @ (sk_C @ sk_D_1 @ sk_C_1) @ sk_B)),
% 0.91/1.11      inference('simplify', [status(thm)], ['92'])).
% 0.91/1.11  thf('111', plain,
% 0.91/1.11      (![X42 : $i, X43 : $i]:
% 0.91/1.11         (((k1_funct_1 @ sk_C_1 @ X42) = (X43))
% 0.91/1.11          | ((k1_funct_1 @ sk_D_1 @ X43) != (X42))
% 0.91/1.11          | ~ (r2_hidden @ X43 @ sk_B))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('112', plain,
% 0.91/1.11      (![X43 : $i]:
% 0.91/1.11         (~ (r2_hidden @ X43 @ sk_B)
% 0.91/1.11          | ((k1_funct_1 @ sk_C_1 @ (k1_funct_1 @ sk_D_1 @ X43)) = (X43)))),
% 0.91/1.11      inference('simplify', [status(thm)], ['111'])).
% 0.91/1.11  thf('113', plain,
% 0.91/1.11      (((k1_funct_1 @ sk_C_1 @ (k1_funct_1 @ sk_D_1 @ (sk_C @ sk_D_1 @ sk_C_1)))
% 0.91/1.11         = (sk_C @ sk_D_1 @ sk_C_1))),
% 0.91/1.11      inference('sup-', [status(thm)], ['110', '112'])).
% 0.91/1.11  thf('114', plain,
% 0.91/1.11      (((k1_funct_1 @ sk_D_1 @ (sk_C @ sk_D_1 @ sk_C_1))
% 0.91/1.11         = (sk_D @ sk_D_1 @ sk_C_1))),
% 0.91/1.11      inference('simplify', [status(thm)], ['69'])).
% 0.91/1.11  thf('115', plain,
% 0.91/1.11      (((k1_funct_1 @ sk_C_1 @ (sk_D @ sk_D_1 @ sk_C_1))
% 0.91/1.11         = (sk_C @ sk_D_1 @ sk_C_1))),
% 0.91/1.11      inference('demod', [status(thm)], ['113', '114'])).
% 0.91/1.11  thf('116', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         (zip_tseitin_1 @ (sk_D @ sk_D_1 @ sk_C_1) @ 
% 0.91/1.11          (sk_C @ sk_D_1 @ sk_C_1) @ X0 @ sk_C_1)),
% 0.91/1.11      inference('demod', [status(thm)], ['109', '115'])).
% 0.91/1.11  thf('117', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 0.91/1.11      inference('demod', [status(thm)], ['7', '14', '17'])).
% 0.91/1.11  thf('118', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 0.91/1.11      inference('sup+', [status(thm)], ['2', '3'])).
% 0.91/1.11  thf('119', plain, ((v1_funct_1 @ sk_D_1)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('120', plain, ((v1_relat_1 @ sk_D_1)),
% 0.91/1.11      inference('demod', [status(thm)], ['28', '29'])).
% 0.91/1.11  thf('121', plain, ((v2_funct_1 @ sk_C_1)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('122', plain,
% 0.91/1.11      ((((sk_D_1) = (k2_funct_1 @ sk_C_1)) | ((sk_B) != (sk_B)))),
% 0.91/1.11      inference('demod', [status(thm)],
% 0.91/1.11                ['101', '102', '103', '116', '117', '118', '119', '120', '121'])).
% 0.91/1.11  thf('123', plain, (((sk_D_1) = (k2_funct_1 @ sk_C_1))),
% 0.91/1.11      inference('simplify', [status(thm)], ['122'])).
% 0.91/1.11  thf('124', plain, (((sk_D_1) != (k2_funct_1 @ sk_C_1))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('125', plain, ($false),
% 0.91/1.11      inference('simplify_reflect-', [status(thm)], ['123', '124'])).
% 0.91/1.11  
% 0.91/1.11  % SZS output end Refutation
% 0.91/1.11  
% 0.91/1.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
