%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mUBcrc8y4k

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:51 EST 2020

% Result     : Theorem 0.98s
% Output     : Refutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :  170 (1696 expanded)
%              Number of leaves         :   47 ( 518 expanded)
%              Depth                    :   29
%              Number of atoms          : 1674 (50893 expanded)
%              Number of equality atoms :  122 (4961 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X32 @ X30 )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_5 @ X37 @ X36 @ X35 ) ) ),
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
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_4 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
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
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_4 @ X38 @ X39 )
      | ( zip_tseitin_5 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ( zip_tseitin_1 @ X5 @ X6 @ X7 @ X9 )
      | ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf(zf_stmt_7,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_3 @ D @ C @ B @ A )
    <=> ( ( zip_tseitin_2 @ D @ C @ A )
       => ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) )
          & ( D
            = ( k1_funct_1 @ B @ C ) ) ) ) ) )).

thf('20',plain,(
    ! [X14: $i,X15: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_3 @ X14 @ X15 @ X17 @ X18 )
      | ( zip_tseitin_2 @ X14 @ X15 @ X18 ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( ( k1_relat_1 @ X20 )
       != ( k2_relat_1 @ X19 ) )
      | ~ ( zip_tseitin_3 @ ( sk_D @ X20 @ X19 ) @ ( sk_C @ X20 @ X19 ) @ X20 @ X19 )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X20 @ X19 ) @ ( sk_C @ X20 @ X19 ) @ X20 @ X19 )
      | ( X20
        = ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('27',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('28',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
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
    inference(demod,[status(thm)],['24','25','28'])).

thf('30',plain,
    ( ( sk_B != sk_B )
    | ( zip_tseitin_0 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_D_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( sk_D_1
      = ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','29'])).

thf('31',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('35',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B != sk_B )
    | ( zip_tseitin_0 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_D_1 @ sk_C_1 )
    | ( sk_D_1
      = ( k2_funct_1 @ sk_C_1 ) )
    | ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['30','31','32','35'])).

thf('37',plain,
    ( ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_C_1 )
    | ( sk_D_1
      = ( k2_funct_1 @ sk_C_1 ) )
    | ( zip_tseitin_0 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_D_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    sk_D_1
 != ( k2_funct_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_C_1 )
    | ( zip_tseitin_0 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_D_1 @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X2
        = ( k1_funct_1 @ X3 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X3 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('41',plain,
    ( ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_C_1 )
    | ( ( sk_D @ sk_D_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X12
        = ( k1_funct_1 @ X11 @ X10 ) )
      | ~ ( zip_tseitin_2 @ X10 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('43',plain,
    ( ( ( sk_D @ sk_D_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) )
    | ( ( sk_C @ sk_D_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_C_1 @ ( sk_D @ sk_D_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_C_1 )
    | ( ( sk_D @ sk_D_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('45',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) )
      | ~ ( zip_tseitin_2 @ X10 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('46',plain,
    ( ( ( sk_D @ sk_D_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_5 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('49',plain,
    ( ~ ( zip_tseitin_5 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_4 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('51',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_4 @ X38 @ X39 )
      | ( zip_tseitin_5 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('53',plain,
    ( ( zip_tseitin_5 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_4 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_5 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    zip_tseitin_5 @ sk_C_1 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('59',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['49','56','59'])).

thf('61',plain,
    ( ( ( sk_D @ sk_D_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['46','60'])).

thf('62',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k1_funct_1 @ sk_D_1 @ X42 )
        = X43 )
      | ( ( k1_funct_1 @ sk_C_1 @ X43 )
       != X42 )
      | ~ ( r2_hidden @ X43 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X43: $i] :
      ( ~ ( r2_hidden @ X43 @ sk_A )
      | ( ( k1_funct_1 @ sk_D_1 @ ( k1_funct_1 @ sk_C_1 @ X43 ) )
        = X43 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( ( sk_D @ sk_D_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) )
    | ( ( k1_funct_1 @ sk_D_1 @ ( k1_funct_1 @ sk_C_1 @ ( sk_D @ sk_D_1 @ sk_C_1 ) ) )
      = ( sk_D @ sk_D_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,
    ( ( ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) )
      = ( sk_D @ sk_D_1 @ sk_C_1 ) )
    | ( ( sk_D @ sk_D_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) )
    | ( ( sk_D @ sk_D_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['43','64'])).

thf('66',plain,
    ( ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) )
    = ( sk_D @ sk_D_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_C_1 )
    | ( zip_tseitin_0 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_D_1 @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ X1 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X3 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('69',plain,
    ( ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_C_1 )
    | ( r2_hidden @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['2','3'])).

thf('71',plain,
    ( ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_C_1 )
    | ( r2_hidden @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_B ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X12
        = ( k1_funct_1 @ X11 @ X10 ) )
      | ~ ( zip_tseitin_2 @ X10 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('73',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_B )
    | ( ( sk_C @ sk_D_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_C_1 @ ( sk_D @ sk_D_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_C_1 )
    | ( r2_hidden @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_B ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('75',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) )
      | ~ ( zip_tseitin_2 @ X10 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('76',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['49','56','59'])).

thf('78',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r2_hidden @ X41 @ sk_A )
      | ( ( k1_funct_1 @ sk_D_1 @ X42 )
       != X41 )
      | ~ ( r2_hidden @ X42 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X42: $i] :
      ( ~ ( r2_hidden @ X42 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X42 ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ sk_A )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['78','80'])).

thf('82',plain,
    ( ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) )
    = ( sk_D @ sk_D_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('83',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ sk_A )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ sk_A ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X42: $i,X43: $i] :
      ( ( r2_hidden @ X42 @ sk_B )
      | ( ( k1_funct_1 @ sk_C_1 @ X43 )
       != X42 )
      | ~ ( r2_hidden @ X43 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X43: $i] :
      ( ~ ( r2_hidden @ X43 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X43 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_D @ sk_D_1 @ sk_C_1 ) ) @ sk_B ),
    inference('sup-',[status(thm)],['84','86'])).

thf('88',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_B )
    | ( r2_hidden @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_B ) ),
    inference('sup+',[status(thm)],['73','87'])).

thf('89',plain,(
    r2_hidden @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_B ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['2','3'])).

thf('91',plain,(
    ! [X14: $i,X15: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_3 @ X14 @ X15 @ X17 @ X18 )
      | ~ ( r2_hidden @ X15 @ ( k2_relat_1 @ X18 ) )
      | ( X14
       != ( k1_funct_1 @ X17 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('92',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k2_relat_1 @ X18 ) )
      | ( zip_tseitin_3 @ ( k1_funct_1 @ X17 @ X15 ) @ X15 @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( zip_tseitin_3 @ ( k1_funct_1 @ X1 @ X0 ) @ X0 @ X1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['90','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( zip_tseitin_3 @ ( k1_funct_1 @ X0 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ X0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['89','93'])).

thf('95',plain,(
    zip_tseitin_3 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_D_1 @ sk_C_1 ),
    inference('sup+',[status(thm)],['66','94'])).

thf('96',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( ( k1_relat_1 @ X20 )
       != ( k2_relat_1 @ X19 ) )
      | ~ ( zip_tseitin_3 @ ( sk_D @ X20 @ X19 ) @ ( sk_C @ X20 @ X19 ) @ X20 @ X19 )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X20 @ X19 ) @ ( sk_C @ X20 @ X19 ) @ X20 @ X19 )
      | ( X20
        = ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_14])).

thf('97',plain,
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
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('99',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ sk_A ),
    inference(simplify,[status(thm)],['83'])).

thf('101',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['49','56','59'])).

thf('102',plain,(
    ! [X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ( zip_tseitin_1 @ X5 @ X6 @ X7 @ X9 )
      | ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X9 ) )
      | ( X6
       != ( k1_funct_1 @ X9 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('103',plain,(
    ! [X5: $i,X7: $i,X9: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X9 ) )
      | ( zip_tseitin_1 @ X5 @ ( k1_funct_1 @ X9 @ X5 ) @ X7 @ X9 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( zip_tseitin_1 @ X0 @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ X1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['101','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( k1_funct_1 @ sk_C_1 @ ( sk_D @ sk_D_1 @ sk_C_1 ) ) @ X0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['100','104'])).

thf('106',plain,(
    r2_hidden @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_B ),
    inference(simplify,[status(thm)],['88'])).

thf('107',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X41 )
        = X42 )
      | ( ( k1_funct_1 @ sk_D_1 @ X42 )
       != X41 )
      | ~ ( r2_hidden @ X42 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X42: $i] :
      ( ~ ( r2_hidden @ X42 @ sk_B )
      | ( ( k1_funct_1 @ sk_C_1 @ ( k1_funct_1 @ sk_D_1 @ X42 ) )
        = X42 ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) )
    = ( sk_C @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['106','108'])).

thf('110',plain,
    ( ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) )
    = ( sk_D @ sk_D_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('111',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_D @ sk_D_1 @ sk_C_1 ) )
    = ( sk_C @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ X0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['105','111'])).

thf('113',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['7','14','17'])).

thf('114',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['2','3'])).

thf('115',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('117',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( sk_D_1
      = ( k2_funct_1 @ sk_C_1 ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['97','98','99','112','113','114','115','116','117'])).

thf('119',plain,
    ( sk_D_1
    = ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    sk_D_1
 != ( k2_funct_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['119','120'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mUBcrc8y4k
% 0.16/0.38  % Computer   : n013.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 19:25:40 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.39  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.98/1.18  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.98/1.18  % Solved by: fo/fo7.sh
% 0.98/1.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.98/1.18  % done 599 iterations in 0.683s
% 0.98/1.18  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.98/1.18  % SZS output start Refutation
% 0.98/1.18  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.98/1.18  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.98/1.18  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.98/1.18  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.98/1.18  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.98/1.18  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.98/1.18  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.98/1.18  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.98/1.18  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $i > $o).
% 0.98/1.18  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.98/1.18  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.98/1.18  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.98/1.18  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.98/1.18  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.98/1.18  thf(sk_B_type, type, sk_B: $i).
% 0.98/1.18  thf(sk_A_type, type, sk_A: $i).
% 0.98/1.18  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.98/1.18  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $i > $o).
% 0.98/1.18  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.98/1.18  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.98/1.18  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.98/1.18  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.98/1.18  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.98/1.18  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.98/1.18  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.98/1.18  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.98/1.18  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.98/1.18  thf(t34_funct_2, conjecture,
% 0.98/1.18    (![A:$i,B:$i,C:$i]:
% 0.98/1.18     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.98/1.18         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.98/1.18       ( ![D:$i]:
% 0.98/1.18         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.98/1.18             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.98/1.18           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) & 
% 0.98/1.18               ( ![E:$i,F:$i]:
% 0.98/1.18                 ( ( ( ( r2_hidden @ F @ A ) & 
% 0.98/1.18                       ( ( k1_funct_1 @ C @ F ) = ( E ) ) ) =>
% 0.98/1.18                     ( ( r2_hidden @ E @ B ) & 
% 0.98/1.18                       ( ( k1_funct_1 @ D @ E ) = ( F ) ) ) ) & 
% 0.98/1.18                   ( ( ( r2_hidden @ E @ B ) & 
% 0.98/1.18                       ( ( k1_funct_1 @ D @ E ) = ( F ) ) ) =>
% 0.98/1.18                     ( ( r2_hidden @ F @ A ) & 
% 0.98/1.18                       ( ( k1_funct_1 @ C @ F ) = ( E ) ) ) ) ) ) ) =>
% 0.98/1.18             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.98/1.18               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.98/1.18  thf(zf_stmt_0, negated_conjecture,
% 0.98/1.18    (~( ![A:$i,B:$i,C:$i]:
% 0.98/1.18        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.98/1.18            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.98/1.18          ( ![D:$i]:
% 0.98/1.18            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.98/1.18                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.98/1.18              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.98/1.18                  ( v2_funct_1 @ C ) & 
% 0.98/1.18                  ( ![E:$i,F:$i]:
% 0.98/1.18                    ( ( ( ( r2_hidden @ F @ A ) & 
% 0.98/1.18                          ( ( k1_funct_1 @ C @ F ) = ( E ) ) ) =>
% 0.98/1.18                        ( ( r2_hidden @ E @ B ) & 
% 0.98/1.18                          ( ( k1_funct_1 @ D @ E ) = ( F ) ) ) ) & 
% 0.98/1.18                      ( ( ( r2_hidden @ E @ B ) & 
% 0.98/1.18                          ( ( k1_funct_1 @ D @ E ) = ( F ) ) ) =>
% 0.98/1.18                        ( ( r2_hidden @ F @ A ) & 
% 0.98/1.18                          ( ( k1_funct_1 @ C @ F ) = ( E ) ) ) ) ) ) ) =>
% 0.98/1.18                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.98/1.18                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.98/1.18    inference('cnf.neg', [status(esa)], [t34_funct_2])).
% 0.98/1.18  thf('0', plain,
% 0.98/1.18      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf(redefinition_k2_relset_1, axiom,
% 0.98/1.18    (![A:$i,B:$i,C:$i]:
% 0.98/1.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.98/1.18       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.98/1.18  thf('1', plain,
% 0.98/1.18      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.98/1.18         (((k2_relset_1 @ X31 @ X32 @ X30) = (k2_relat_1 @ X30))
% 0.98/1.18          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.98/1.18      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.98/1.18  thf('2', plain,
% 0.98/1.18      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.98/1.18      inference('sup-', [status(thm)], ['0', '1'])).
% 0.98/1.18  thf('3', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('4', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 0.98/1.18      inference('sup+', [status(thm)], ['2', '3'])).
% 0.98/1.18  thf('5', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_A)),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf(d1_funct_2, axiom,
% 0.98/1.18    (![A:$i,B:$i,C:$i]:
% 0.98/1.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.98/1.18       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.98/1.18           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.98/1.18             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.98/1.18         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.98/1.18           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.98/1.18             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.98/1.18  thf(zf_stmt_1, axiom,
% 0.98/1.18    (![C:$i,B:$i,A:$i]:
% 0.98/1.18     ( ( zip_tseitin_5 @ C @ B @ A ) =>
% 0.98/1.18       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.98/1.18  thf('6', plain,
% 0.98/1.18      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.98/1.18         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 0.98/1.18          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 0.98/1.18          | ~ (zip_tseitin_5 @ X37 @ X36 @ X35))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.98/1.18  thf('7', plain,
% 0.98/1.18      ((~ (zip_tseitin_5 @ sk_D_1 @ sk_A @ sk_B)
% 0.98/1.18        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D_1)))),
% 0.98/1.18      inference('sup-', [status(thm)], ['5', '6'])).
% 0.98/1.18  thf(zf_stmt_2, axiom,
% 0.98/1.18    (![B:$i,A:$i]:
% 0.98/1.18     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.98/1.18       ( zip_tseitin_4 @ B @ A ) ))).
% 0.98/1.18  thf('8', plain,
% 0.98/1.18      (![X33 : $i, X34 : $i]:
% 0.98/1.18         ((zip_tseitin_4 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.98/1.18  thf('9', plain,
% 0.98/1.18      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf(zf_stmt_3, type, zip_tseitin_5 : $i > $i > $i > $o).
% 0.98/1.18  thf(zf_stmt_4, type, zip_tseitin_4 : $i > $i > $o).
% 0.98/1.18  thf(zf_stmt_5, axiom,
% 0.98/1.18    (![A:$i,B:$i,C:$i]:
% 0.98/1.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.98/1.18       ( ( ( zip_tseitin_4 @ B @ A ) => ( zip_tseitin_5 @ C @ B @ A ) ) & 
% 0.98/1.18         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.98/1.18           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.98/1.18             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.98/1.18  thf('10', plain,
% 0.98/1.18      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.98/1.18         (~ (zip_tseitin_4 @ X38 @ X39)
% 0.98/1.18          | (zip_tseitin_5 @ X40 @ X38 @ X39)
% 0.98/1.18          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.98/1.18  thf('11', plain,
% 0.98/1.18      (((zip_tseitin_5 @ sk_D_1 @ sk_A @ sk_B)
% 0.98/1.18        | ~ (zip_tseitin_4 @ sk_A @ sk_B))),
% 0.98/1.18      inference('sup-', [status(thm)], ['9', '10'])).
% 0.98/1.18  thf('12', plain,
% 0.98/1.18      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_5 @ sk_D_1 @ sk_A @ sk_B))),
% 0.98/1.18      inference('sup-', [status(thm)], ['8', '11'])).
% 0.98/1.18  thf('13', plain, (((sk_A) != (k1_xboole_0))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('14', plain, ((zip_tseitin_5 @ sk_D_1 @ sk_A @ sk_B)),
% 0.98/1.18      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.98/1.18  thf('15', plain,
% 0.98/1.18      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf(redefinition_k1_relset_1, axiom,
% 0.98/1.18    (![A:$i,B:$i,C:$i]:
% 0.98/1.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.98/1.18       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.98/1.18  thf('16', plain,
% 0.98/1.18      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.98/1.18         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 0.98/1.18          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.98/1.18      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.98/1.18  thf('17', plain,
% 0.98/1.18      (((k1_relset_1 @ sk_B @ sk_A @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.98/1.18      inference('sup-', [status(thm)], ['15', '16'])).
% 0.98/1.18  thf('18', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 0.98/1.18      inference('demod', [status(thm)], ['7', '14', '17'])).
% 0.98/1.18  thf(t54_funct_1, axiom,
% 0.98/1.18    (![A:$i]:
% 0.98/1.18     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.98/1.18       ( ( v2_funct_1 @ A ) =>
% 0.98/1.18         ( ![B:$i]:
% 0.98/1.18           ( ( ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) =>
% 0.98/1.18             ( ( ( B ) = ( k2_funct_1 @ A ) ) <=>
% 0.98/1.18               ( ( ![C:$i,D:$i]:
% 0.98/1.18                   ( ( ( ( ( D ) = ( k1_funct_1 @ B @ C ) ) & 
% 0.98/1.18                         ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) =>
% 0.98/1.18                       ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.98/1.18                         ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) & 
% 0.98/1.18                     ( ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.98/1.18                         ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) =>
% 0.98/1.18                       ( ( ( D ) = ( k1_funct_1 @ B @ C ) ) & 
% 0.98/1.18                         ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) ) ) ) & 
% 0.98/1.18                 ( ( k1_relat_1 @ B ) = ( k2_relat_1 @ A ) ) ) ) ) ) ) ))).
% 0.98/1.18  thf(zf_stmt_6, axiom,
% 0.98/1.18    (![D:$i,C:$i,B:$i,A:$i]:
% 0.98/1.18     ( ( zip_tseitin_1 @ D @ C @ B @ A ) <=>
% 0.98/1.18       ( ( zip_tseitin_0 @ D @ C @ B @ A ) =>
% 0.98/1.18         ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.98/1.18           ( ( C ) = ( k1_funct_1 @ A @ D ) ) ) ) ))).
% 0.98/1.18  thf('19', plain,
% 0.98/1.18      (![X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.98/1.18         ((zip_tseitin_1 @ X5 @ X6 @ X7 @ X9)
% 0.98/1.18          | (zip_tseitin_0 @ X5 @ X6 @ X7 @ X9))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.98/1.18  thf(zf_stmt_7, axiom,
% 0.98/1.18    (![D:$i,C:$i,B:$i,A:$i]:
% 0.98/1.18     ( ( zip_tseitin_3 @ D @ C @ B @ A ) <=>
% 0.98/1.18       ( ( zip_tseitin_2 @ D @ C @ A ) =>
% 0.98/1.18         ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) & 
% 0.98/1.18           ( ( D ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.98/1.18  thf('20', plain,
% 0.98/1.18      (![X14 : $i, X15 : $i, X17 : $i, X18 : $i]:
% 0.98/1.18         ((zip_tseitin_3 @ X14 @ X15 @ X17 @ X18)
% 0.98/1.18          | (zip_tseitin_2 @ X14 @ X15 @ X18))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.98/1.18  thf(zf_stmt_8, type, zip_tseitin_3 : $i > $i > $i > $i > $o).
% 0.98/1.18  thf(zf_stmt_9, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.98/1.18  thf(zf_stmt_10, axiom,
% 0.98/1.18    (![D:$i,C:$i,A:$i]:
% 0.98/1.18     ( ( zip_tseitin_2 @ D @ C @ A ) <=>
% 0.98/1.18       ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.98/1.18         ( ( C ) = ( k1_funct_1 @ A @ D ) ) ) ))).
% 0.98/1.18  thf(zf_stmt_11, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.98/1.18  thf(zf_stmt_12, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.98/1.18  thf(zf_stmt_13, axiom,
% 0.98/1.18    (![D:$i,C:$i,B:$i,A:$i]:
% 0.98/1.18     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.98/1.18       ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) & 
% 0.98/1.18         ( ( D ) = ( k1_funct_1 @ B @ C ) ) ) ))).
% 0.98/1.18  thf(zf_stmt_14, axiom,
% 0.98/1.18    (![A:$i]:
% 0.98/1.18     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.98/1.18       ( ( v2_funct_1 @ A ) =>
% 0.98/1.18         ( ![B:$i]:
% 0.98/1.18           ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.98/1.18             ( ( ( B ) = ( k2_funct_1 @ A ) ) <=>
% 0.98/1.18               ( ( ( k1_relat_1 @ B ) = ( k2_relat_1 @ A ) ) & 
% 0.98/1.18                 ( ![C:$i,D:$i]:
% 0.98/1.18                   ( ( zip_tseitin_3 @ D @ C @ B @ A ) & 
% 0.98/1.18                     ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ))).
% 0.98/1.18  thf('21', plain,
% 0.98/1.18      (![X19 : $i, X20 : $i]:
% 0.98/1.18         (~ (v2_funct_1 @ X19)
% 0.98/1.18          | ~ (v1_relat_1 @ X20)
% 0.98/1.18          | ~ (v1_funct_1 @ X20)
% 0.98/1.18          | ((k1_relat_1 @ X20) != (k2_relat_1 @ X19))
% 0.98/1.18          | ~ (zip_tseitin_3 @ (sk_D @ X20 @ X19) @ (sk_C @ X20 @ X19) @ X20 @ 
% 0.98/1.18               X19)
% 0.98/1.18          | ~ (zip_tseitin_1 @ (sk_D @ X20 @ X19) @ (sk_C @ X20 @ X19) @ X20 @ 
% 0.98/1.18               X19)
% 0.98/1.18          | ((X20) = (k2_funct_1 @ X19))
% 0.98/1.18          | ~ (v1_funct_1 @ X19)
% 0.98/1.18          | ~ (v1_relat_1 @ X19))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_14])).
% 0.98/1.18  thf('22', plain,
% 0.98/1.18      (![X0 : $i, X1 : $i]:
% 0.98/1.18         ((zip_tseitin_2 @ (sk_D @ X1 @ X0) @ (sk_C @ X1 @ X0) @ X0)
% 0.98/1.18          | ~ (v1_relat_1 @ X0)
% 0.98/1.18          | ~ (v1_funct_1 @ X0)
% 0.98/1.18          | ((X1) = (k2_funct_1 @ X0))
% 0.98/1.18          | ~ (zip_tseitin_1 @ (sk_D @ X1 @ X0) @ (sk_C @ X1 @ X0) @ X1 @ X0)
% 0.98/1.18          | ((k1_relat_1 @ X1) != (k2_relat_1 @ X0))
% 0.98/1.18          | ~ (v1_funct_1 @ X1)
% 0.98/1.18          | ~ (v1_relat_1 @ X1)
% 0.98/1.18          | ~ (v2_funct_1 @ X0))),
% 0.98/1.18      inference('sup-', [status(thm)], ['20', '21'])).
% 0.98/1.18  thf('23', plain,
% 0.98/1.18      (![X0 : $i, X1 : $i]:
% 0.98/1.18         ((zip_tseitin_0 @ (sk_D @ X1 @ X0) @ (sk_C @ X1 @ X0) @ X1 @ X0)
% 0.98/1.18          | ~ (v2_funct_1 @ X0)
% 0.98/1.18          | ~ (v1_relat_1 @ X1)
% 0.98/1.18          | ~ (v1_funct_1 @ X1)
% 0.98/1.18          | ((k1_relat_1 @ X1) != (k2_relat_1 @ X0))
% 0.98/1.18          | ((X1) = (k2_funct_1 @ X0))
% 0.98/1.18          | ~ (v1_funct_1 @ X0)
% 0.98/1.18          | ~ (v1_relat_1 @ X0)
% 0.98/1.18          | (zip_tseitin_2 @ (sk_D @ X1 @ X0) @ (sk_C @ X1 @ X0) @ X0))),
% 0.98/1.18      inference('sup-', [status(thm)], ['19', '22'])).
% 0.98/1.18  thf('24', plain,
% 0.98/1.18      (![X0 : $i]:
% 0.98/1.18         (((sk_B) != (k2_relat_1 @ X0))
% 0.98/1.18          | (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0) @ (sk_C @ sk_D_1 @ X0) @ X0)
% 0.98/1.18          | ~ (v1_relat_1 @ X0)
% 0.98/1.18          | ~ (v1_funct_1 @ X0)
% 0.98/1.18          | ((sk_D_1) = (k2_funct_1 @ X0))
% 0.98/1.18          | ~ (v1_funct_1 @ sk_D_1)
% 0.98/1.18          | ~ (v1_relat_1 @ sk_D_1)
% 0.98/1.18          | ~ (v2_funct_1 @ X0)
% 0.98/1.18          | (zip_tseitin_0 @ (sk_D @ sk_D_1 @ X0) @ (sk_C @ sk_D_1 @ X0) @ 
% 0.98/1.18             sk_D_1 @ X0))),
% 0.98/1.18      inference('sup-', [status(thm)], ['18', '23'])).
% 0.98/1.18  thf('25', plain, ((v1_funct_1 @ sk_D_1)),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('26', plain,
% 0.98/1.18      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf(cc1_relset_1, axiom,
% 0.98/1.18    (![A:$i,B:$i,C:$i]:
% 0.98/1.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.98/1.18       ( v1_relat_1 @ C ) ))).
% 0.98/1.18  thf('27', plain,
% 0.98/1.18      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.98/1.18         ((v1_relat_1 @ X24)
% 0.98/1.18          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.98/1.18      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.98/1.18  thf('28', plain, ((v1_relat_1 @ sk_D_1)),
% 0.98/1.18      inference('sup-', [status(thm)], ['26', '27'])).
% 0.98/1.18  thf('29', plain,
% 0.98/1.18      (![X0 : $i]:
% 0.98/1.18         (((sk_B) != (k2_relat_1 @ X0))
% 0.98/1.18          | (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0) @ (sk_C @ sk_D_1 @ X0) @ X0)
% 0.98/1.18          | ~ (v1_relat_1 @ X0)
% 0.98/1.18          | ~ (v1_funct_1 @ X0)
% 0.98/1.18          | ((sk_D_1) = (k2_funct_1 @ X0))
% 0.98/1.18          | ~ (v2_funct_1 @ X0)
% 0.98/1.18          | (zip_tseitin_0 @ (sk_D @ sk_D_1 @ X0) @ (sk_C @ sk_D_1 @ X0) @ 
% 0.98/1.18             sk_D_1 @ X0))),
% 0.98/1.18      inference('demod', [status(thm)], ['24', '25', '28'])).
% 0.98/1.18  thf('30', plain,
% 0.98/1.18      ((((sk_B) != (sk_B))
% 0.98/1.18        | (zip_tseitin_0 @ (sk_D @ sk_D_1 @ sk_C_1) @ 
% 0.98/1.18           (sk_C @ sk_D_1 @ sk_C_1) @ sk_D_1 @ sk_C_1)
% 0.98/1.18        | ~ (v2_funct_1 @ sk_C_1)
% 0.98/1.18        | ((sk_D_1) = (k2_funct_1 @ sk_C_1))
% 0.98/1.18        | ~ (v1_funct_1 @ sk_C_1)
% 0.98/1.18        | ~ (v1_relat_1 @ sk_C_1)
% 0.98/1.18        | (zip_tseitin_2 @ (sk_D @ sk_D_1 @ sk_C_1) @ 
% 0.98/1.18           (sk_C @ sk_D_1 @ sk_C_1) @ sk_C_1))),
% 0.98/1.18      inference('sup-', [status(thm)], ['4', '29'])).
% 0.98/1.18  thf('31', plain, ((v2_funct_1 @ sk_C_1)),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('32', plain, ((v1_funct_1 @ sk_C_1)),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('33', plain,
% 0.98/1.18      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('34', plain,
% 0.98/1.18      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.98/1.18         ((v1_relat_1 @ X24)
% 0.98/1.18          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.98/1.18      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.98/1.18  thf('35', plain, ((v1_relat_1 @ sk_C_1)),
% 0.98/1.18      inference('sup-', [status(thm)], ['33', '34'])).
% 0.98/1.18  thf('36', plain,
% 0.98/1.18      ((((sk_B) != (sk_B))
% 0.98/1.18        | (zip_tseitin_0 @ (sk_D @ sk_D_1 @ sk_C_1) @ 
% 0.98/1.18           (sk_C @ sk_D_1 @ sk_C_1) @ sk_D_1 @ sk_C_1)
% 0.98/1.18        | ((sk_D_1) = (k2_funct_1 @ sk_C_1))
% 0.98/1.18        | (zip_tseitin_2 @ (sk_D @ sk_D_1 @ sk_C_1) @ 
% 0.98/1.18           (sk_C @ sk_D_1 @ sk_C_1) @ sk_C_1))),
% 0.98/1.18      inference('demod', [status(thm)], ['30', '31', '32', '35'])).
% 0.98/1.18  thf('37', plain,
% 0.98/1.18      (((zip_tseitin_2 @ (sk_D @ sk_D_1 @ sk_C_1) @ (sk_C @ sk_D_1 @ sk_C_1) @ 
% 0.98/1.18         sk_C_1)
% 0.98/1.18        | ((sk_D_1) = (k2_funct_1 @ sk_C_1))
% 0.98/1.18        | (zip_tseitin_0 @ (sk_D @ sk_D_1 @ sk_C_1) @ 
% 0.98/1.18           (sk_C @ sk_D_1 @ sk_C_1) @ sk_D_1 @ sk_C_1))),
% 0.98/1.18      inference('simplify', [status(thm)], ['36'])).
% 0.98/1.18  thf('38', plain, (((sk_D_1) != (k2_funct_1 @ sk_C_1))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('39', plain,
% 0.98/1.18      (((zip_tseitin_2 @ (sk_D @ sk_D_1 @ sk_C_1) @ (sk_C @ sk_D_1 @ sk_C_1) @ 
% 0.98/1.18         sk_C_1)
% 0.98/1.18        | (zip_tseitin_0 @ (sk_D @ sk_D_1 @ sk_C_1) @ 
% 0.98/1.18           (sk_C @ sk_D_1 @ sk_C_1) @ sk_D_1 @ sk_C_1))),
% 0.98/1.18      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.98/1.18  thf('40', plain,
% 0.98/1.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.98/1.18         (((X2) = (k1_funct_1 @ X3 @ X0))
% 0.98/1.18          | ~ (zip_tseitin_0 @ X2 @ X0 @ X3 @ X1))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.98/1.18  thf('41', plain,
% 0.98/1.18      (((zip_tseitin_2 @ (sk_D @ sk_D_1 @ sk_C_1) @ (sk_C @ sk_D_1 @ sk_C_1) @ 
% 0.98/1.18         sk_C_1)
% 0.98/1.18        | ((sk_D @ sk_D_1 @ sk_C_1)
% 0.98/1.18            = (k1_funct_1 @ sk_D_1 @ (sk_C @ sk_D_1 @ sk_C_1))))),
% 0.98/1.18      inference('sup-', [status(thm)], ['39', '40'])).
% 0.98/1.18  thf('42', plain,
% 0.98/1.18      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.98/1.18         (((X12) = (k1_funct_1 @ X11 @ X10))
% 0.98/1.18          | ~ (zip_tseitin_2 @ X10 @ X12 @ X11))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_10])).
% 0.98/1.18  thf('43', plain,
% 0.98/1.18      ((((sk_D @ sk_D_1 @ sk_C_1)
% 0.98/1.18          = (k1_funct_1 @ sk_D_1 @ (sk_C @ sk_D_1 @ sk_C_1)))
% 0.98/1.18        | ((sk_C @ sk_D_1 @ sk_C_1)
% 0.98/1.18            = (k1_funct_1 @ sk_C_1 @ (sk_D @ sk_D_1 @ sk_C_1))))),
% 0.98/1.18      inference('sup-', [status(thm)], ['41', '42'])).
% 0.98/1.18  thf('44', plain,
% 0.98/1.18      (((zip_tseitin_2 @ (sk_D @ sk_D_1 @ sk_C_1) @ (sk_C @ sk_D_1 @ sk_C_1) @ 
% 0.98/1.18         sk_C_1)
% 0.98/1.18        | ((sk_D @ sk_D_1 @ sk_C_1)
% 0.98/1.18            = (k1_funct_1 @ sk_D_1 @ (sk_C @ sk_D_1 @ sk_C_1))))),
% 0.98/1.18      inference('sup-', [status(thm)], ['39', '40'])).
% 0.98/1.18  thf('45', plain,
% 0.98/1.18      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.98/1.18         ((r2_hidden @ X10 @ (k1_relat_1 @ X11))
% 0.98/1.18          | ~ (zip_tseitin_2 @ X10 @ X12 @ X11))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_10])).
% 0.98/1.18  thf('46', plain,
% 0.98/1.18      ((((sk_D @ sk_D_1 @ sk_C_1)
% 0.98/1.18          = (k1_funct_1 @ sk_D_1 @ (sk_C @ sk_D_1 @ sk_C_1)))
% 0.98/1.18        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1) @ (k1_relat_1 @ sk_C_1)))),
% 0.98/1.18      inference('sup-', [status(thm)], ['44', '45'])).
% 0.98/1.18  thf('47', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('48', plain,
% 0.98/1.18      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.98/1.18         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 0.98/1.18          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 0.98/1.18          | ~ (zip_tseitin_5 @ X37 @ X36 @ X35))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.98/1.18  thf('49', plain,
% 0.98/1.18      ((~ (zip_tseitin_5 @ sk_C_1 @ sk_B @ sk_A)
% 0.98/1.18        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.98/1.18      inference('sup-', [status(thm)], ['47', '48'])).
% 0.98/1.18  thf('50', plain,
% 0.98/1.18      (![X33 : $i, X34 : $i]:
% 0.98/1.18         ((zip_tseitin_4 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.98/1.18  thf('51', plain,
% 0.98/1.18      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('52', plain,
% 0.98/1.18      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.98/1.18         (~ (zip_tseitin_4 @ X38 @ X39)
% 0.98/1.18          | (zip_tseitin_5 @ X40 @ X38 @ X39)
% 0.98/1.18          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.98/1.18  thf('53', plain,
% 0.98/1.18      (((zip_tseitin_5 @ sk_C_1 @ sk_B @ sk_A)
% 0.98/1.18        | ~ (zip_tseitin_4 @ sk_B @ sk_A))),
% 0.98/1.18      inference('sup-', [status(thm)], ['51', '52'])).
% 0.98/1.18  thf('54', plain,
% 0.98/1.18      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_5 @ sk_C_1 @ sk_B @ sk_A))),
% 0.98/1.18      inference('sup-', [status(thm)], ['50', '53'])).
% 0.98/1.18  thf('55', plain, (((sk_B) != (k1_xboole_0))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('56', plain, ((zip_tseitin_5 @ sk_C_1 @ sk_B @ sk_A)),
% 0.98/1.18      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 0.98/1.18  thf('57', plain,
% 0.98/1.18      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('58', plain,
% 0.98/1.18      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.98/1.18         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 0.98/1.18          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.98/1.18      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.98/1.18  thf('59', plain,
% 0.98/1.18      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.98/1.18      inference('sup-', [status(thm)], ['57', '58'])).
% 0.98/1.18  thf('60', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.98/1.18      inference('demod', [status(thm)], ['49', '56', '59'])).
% 0.98/1.18  thf('61', plain,
% 0.98/1.18      ((((sk_D @ sk_D_1 @ sk_C_1)
% 0.98/1.18          = (k1_funct_1 @ sk_D_1 @ (sk_C @ sk_D_1 @ sk_C_1)))
% 0.98/1.18        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1) @ sk_A))),
% 0.98/1.18      inference('demod', [status(thm)], ['46', '60'])).
% 0.98/1.18  thf('62', plain,
% 0.98/1.18      (![X42 : $i, X43 : $i]:
% 0.98/1.18         (((k1_funct_1 @ sk_D_1 @ X42) = (X43))
% 0.98/1.18          | ((k1_funct_1 @ sk_C_1 @ X43) != (X42))
% 0.98/1.18          | ~ (r2_hidden @ X43 @ sk_A))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('63', plain,
% 0.98/1.18      (![X43 : $i]:
% 0.98/1.18         (~ (r2_hidden @ X43 @ sk_A)
% 0.98/1.18          | ((k1_funct_1 @ sk_D_1 @ (k1_funct_1 @ sk_C_1 @ X43)) = (X43)))),
% 0.98/1.18      inference('simplify', [status(thm)], ['62'])).
% 0.98/1.18  thf('64', plain,
% 0.98/1.18      ((((sk_D @ sk_D_1 @ sk_C_1)
% 0.98/1.18          = (k1_funct_1 @ sk_D_1 @ (sk_C @ sk_D_1 @ sk_C_1)))
% 0.98/1.18        | ((k1_funct_1 @ sk_D_1 @ 
% 0.98/1.18            (k1_funct_1 @ sk_C_1 @ (sk_D @ sk_D_1 @ sk_C_1)))
% 0.98/1.18            = (sk_D @ sk_D_1 @ sk_C_1)))),
% 0.98/1.18      inference('sup-', [status(thm)], ['61', '63'])).
% 0.98/1.18  thf('65', plain,
% 0.98/1.18      ((((k1_funct_1 @ sk_D_1 @ (sk_C @ sk_D_1 @ sk_C_1))
% 0.98/1.18          = (sk_D @ sk_D_1 @ sk_C_1))
% 0.98/1.18        | ((sk_D @ sk_D_1 @ sk_C_1)
% 0.98/1.18            = (k1_funct_1 @ sk_D_1 @ (sk_C @ sk_D_1 @ sk_C_1)))
% 0.98/1.18        | ((sk_D @ sk_D_1 @ sk_C_1)
% 0.98/1.18            = (k1_funct_1 @ sk_D_1 @ (sk_C @ sk_D_1 @ sk_C_1))))),
% 0.98/1.18      inference('sup+', [status(thm)], ['43', '64'])).
% 0.98/1.18  thf('66', plain,
% 0.98/1.18      (((k1_funct_1 @ sk_D_1 @ (sk_C @ sk_D_1 @ sk_C_1))
% 0.98/1.18         = (sk_D @ sk_D_1 @ sk_C_1))),
% 0.98/1.18      inference('simplify', [status(thm)], ['65'])).
% 0.98/1.18  thf('67', plain,
% 0.98/1.18      (((zip_tseitin_2 @ (sk_D @ sk_D_1 @ sk_C_1) @ (sk_C @ sk_D_1 @ sk_C_1) @ 
% 0.98/1.18         sk_C_1)
% 0.98/1.18        | (zip_tseitin_0 @ (sk_D @ sk_D_1 @ sk_C_1) @ 
% 0.98/1.18           (sk_C @ sk_D_1 @ sk_C_1) @ sk_D_1 @ sk_C_1))),
% 0.98/1.18      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.98/1.18  thf('68', plain,
% 0.98/1.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.98/1.18         ((r2_hidden @ X0 @ (k2_relat_1 @ X1))
% 0.98/1.18          | ~ (zip_tseitin_0 @ X2 @ X0 @ X3 @ X1))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.98/1.18  thf('69', plain,
% 0.98/1.18      (((zip_tseitin_2 @ (sk_D @ sk_D_1 @ sk_C_1) @ (sk_C @ sk_D_1 @ sk_C_1) @ 
% 0.98/1.18         sk_C_1)
% 0.98/1.18        | (r2_hidden @ (sk_C @ sk_D_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1)))),
% 0.98/1.18      inference('sup-', [status(thm)], ['67', '68'])).
% 0.98/1.18  thf('70', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 0.98/1.18      inference('sup+', [status(thm)], ['2', '3'])).
% 0.98/1.18  thf('71', plain,
% 0.98/1.18      (((zip_tseitin_2 @ (sk_D @ sk_D_1 @ sk_C_1) @ (sk_C @ sk_D_1 @ sk_C_1) @ 
% 0.98/1.18         sk_C_1)
% 0.98/1.18        | (r2_hidden @ (sk_C @ sk_D_1 @ sk_C_1) @ sk_B))),
% 0.98/1.18      inference('demod', [status(thm)], ['69', '70'])).
% 0.98/1.18  thf('72', plain,
% 0.98/1.18      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.98/1.18         (((X12) = (k1_funct_1 @ X11 @ X10))
% 0.98/1.18          | ~ (zip_tseitin_2 @ X10 @ X12 @ X11))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_10])).
% 0.98/1.18  thf('73', plain,
% 0.98/1.18      (((r2_hidden @ (sk_C @ sk_D_1 @ sk_C_1) @ sk_B)
% 0.98/1.18        | ((sk_C @ sk_D_1 @ sk_C_1)
% 0.98/1.18            = (k1_funct_1 @ sk_C_1 @ (sk_D @ sk_D_1 @ sk_C_1))))),
% 0.98/1.18      inference('sup-', [status(thm)], ['71', '72'])).
% 0.98/1.18  thf('74', plain,
% 0.98/1.18      (((zip_tseitin_2 @ (sk_D @ sk_D_1 @ sk_C_1) @ (sk_C @ sk_D_1 @ sk_C_1) @ 
% 0.98/1.18         sk_C_1)
% 0.98/1.18        | (r2_hidden @ (sk_C @ sk_D_1 @ sk_C_1) @ sk_B))),
% 0.98/1.18      inference('demod', [status(thm)], ['69', '70'])).
% 0.98/1.18  thf('75', plain,
% 0.98/1.18      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.98/1.18         ((r2_hidden @ X10 @ (k1_relat_1 @ X11))
% 0.98/1.18          | ~ (zip_tseitin_2 @ X10 @ X12 @ X11))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_10])).
% 0.98/1.18  thf('76', plain,
% 0.98/1.18      (((r2_hidden @ (sk_C @ sk_D_1 @ sk_C_1) @ sk_B)
% 0.98/1.18        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1) @ (k1_relat_1 @ sk_C_1)))),
% 0.98/1.18      inference('sup-', [status(thm)], ['74', '75'])).
% 0.98/1.18  thf('77', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.98/1.18      inference('demod', [status(thm)], ['49', '56', '59'])).
% 0.98/1.18  thf('78', plain,
% 0.98/1.18      (((r2_hidden @ (sk_C @ sk_D_1 @ sk_C_1) @ sk_B)
% 0.98/1.18        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1) @ sk_A))),
% 0.98/1.18      inference('demod', [status(thm)], ['76', '77'])).
% 0.98/1.18  thf('79', plain,
% 0.98/1.18      (![X41 : $i, X42 : $i]:
% 0.98/1.18         ((r2_hidden @ X41 @ sk_A)
% 0.98/1.18          | ((k1_funct_1 @ sk_D_1 @ X42) != (X41))
% 0.98/1.18          | ~ (r2_hidden @ X42 @ sk_B))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('80', plain,
% 0.98/1.18      (![X42 : $i]:
% 0.98/1.18         (~ (r2_hidden @ X42 @ sk_B)
% 0.98/1.18          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ X42) @ sk_A))),
% 0.98/1.18      inference('simplify', [status(thm)], ['79'])).
% 0.98/1.18  thf('81', plain,
% 0.98/1.18      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1) @ sk_A)
% 0.98/1.18        | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ (sk_C @ sk_D_1 @ sk_C_1)) @ sk_A))),
% 0.98/1.18      inference('sup-', [status(thm)], ['78', '80'])).
% 0.98/1.18  thf('82', plain,
% 0.98/1.18      (((k1_funct_1 @ sk_D_1 @ (sk_C @ sk_D_1 @ sk_C_1))
% 0.98/1.18         = (sk_D @ sk_D_1 @ sk_C_1))),
% 0.98/1.18      inference('simplify', [status(thm)], ['65'])).
% 0.98/1.18  thf('83', plain,
% 0.98/1.18      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1) @ sk_A)
% 0.98/1.18        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1) @ sk_A))),
% 0.98/1.18      inference('demod', [status(thm)], ['81', '82'])).
% 0.98/1.18  thf('84', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1) @ sk_A)),
% 0.98/1.18      inference('simplify', [status(thm)], ['83'])).
% 0.98/1.18  thf('85', plain,
% 0.98/1.18      (![X42 : $i, X43 : $i]:
% 0.98/1.18         ((r2_hidden @ X42 @ sk_B)
% 0.98/1.18          | ((k1_funct_1 @ sk_C_1 @ X43) != (X42))
% 0.98/1.18          | ~ (r2_hidden @ X43 @ sk_A))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('86', plain,
% 0.98/1.18      (![X43 : $i]:
% 0.98/1.18         (~ (r2_hidden @ X43 @ sk_A)
% 0.98/1.18          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ X43) @ sk_B))),
% 0.98/1.18      inference('simplify', [status(thm)], ['85'])).
% 0.98/1.18  thf('87', plain,
% 0.98/1.18      ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ (sk_D @ sk_D_1 @ sk_C_1)) @ sk_B)),
% 0.98/1.18      inference('sup-', [status(thm)], ['84', '86'])).
% 0.98/1.18  thf('88', plain,
% 0.98/1.18      (((r2_hidden @ (sk_C @ sk_D_1 @ sk_C_1) @ sk_B)
% 0.98/1.18        | (r2_hidden @ (sk_C @ sk_D_1 @ sk_C_1) @ sk_B))),
% 0.98/1.18      inference('sup+', [status(thm)], ['73', '87'])).
% 0.98/1.18  thf('89', plain, ((r2_hidden @ (sk_C @ sk_D_1 @ sk_C_1) @ sk_B)),
% 0.98/1.18      inference('simplify', [status(thm)], ['88'])).
% 0.98/1.18  thf('90', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 0.98/1.18      inference('sup+', [status(thm)], ['2', '3'])).
% 0.98/1.18  thf('91', plain,
% 0.98/1.18      (![X14 : $i, X15 : $i, X17 : $i, X18 : $i]:
% 0.98/1.18         ((zip_tseitin_3 @ X14 @ X15 @ X17 @ X18)
% 0.98/1.18          | ~ (r2_hidden @ X15 @ (k2_relat_1 @ X18))
% 0.98/1.18          | ((X14) != (k1_funct_1 @ X17 @ X15)))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.98/1.18  thf('92', plain,
% 0.98/1.18      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.98/1.18         (~ (r2_hidden @ X15 @ (k2_relat_1 @ X18))
% 0.98/1.18          | (zip_tseitin_3 @ (k1_funct_1 @ X17 @ X15) @ X15 @ X17 @ X18))),
% 0.98/1.18      inference('simplify', [status(thm)], ['91'])).
% 0.98/1.18  thf('93', plain,
% 0.98/1.18      (![X0 : $i, X1 : $i]:
% 0.98/1.18         (~ (r2_hidden @ X0 @ sk_B)
% 0.98/1.18          | (zip_tseitin_3 @ (k1_funct_1 @ X1 @ X0) @ X0 @ X1 @ sk_C_1))),
% 0.98/1.18      inference('sup-', [status(thm)], ['90', '92'])).
% 0.98/1.18  thf('94', plain,
% 0.98/1.18      (![X0 : $i]:
% 0.98/1.18         (zip_tseitin_3 @ (k1_funct_1 @ X0 @ (sk_C @ sk_D_1 @ sk_C_1)) @ 
% 0.98/1.18          (sk_C @ sk_D_1 @ sk_C_1) @ X0 @ sk_C_1)),
% 0.98/1.18      inference('sup-', [status(thm)], ['89', '93'])).
% 0.98/1.18  thf('95', plain,
% 0.98/1.18      ((zip_tseitin_3 @ (sk_D @ sk_D_1 @ sk_C_1) @ (sk_C @ sk_D_1 @ sk_C_1) @ 
% 0.98/1.18        sk_D_1 @ sk_C_1)),
% 0.98/1.18      inference('sup+', [status(thm)], ['66', '94'])).
% 0.98/1.18  thf('96', plain,
% 0.98/1.18      (![X19 : $i, X20 : $i]:
% 0.98/1.18         (~ (v2_funct_1 @ X19)
% 0.98/1.18          | ~ (v1_relat_1 @ X20)
% 0.98/1.18          | ~ (v1_funct_1 @ X20)
% 0.98/1.18          | ((k1_relat_1 @ X20) != (k2_relat_1 @ X19))
% 0.98/1.18          | ~ (zip_tseitin_3 @ (sk_D @ X20 @ X19) @ (sk_C @ X20 @ X19) @ X20 @ 
% 0.98/1.18               X19)
% 0.98/1.18          | ~ (zip_tseitin_1 @ (sk_D @ X20 @ X19) @ (sk_C @ X20 @ X19) @ X20 @ 
% 0.98/1.18               X19)
% 0.98/1.18          | ((X20) = (k2_funct_1 @ X19))
% 0.98/1.18          | ~ (v1_funct_1 @ X19)
% 0.98/1.18          | ~ (v1_relat_1 @ X19))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_14])).
% 0.98/1.18  thf('97', plain,
% 0.98/1.18      ((~ (v1_relat_1 @ sk_C_1)
% 0.98/1.18        | ~ (v1_funct_1 @ sk_C_1)
% 0.98/1.18        | ((sk_D_1) = (k2_funct_1 @ sk_C_1))
% 0.98/1.18        | ~ (zip_tseitin_1 @ (sk_D @ sk_D_1 @ sk_C_1) @ 
% 0.98/1.18             (sk_C @ sk_D_1 @ sk_C_1) @ sk_D_1 @ sk_C_1)
% 0.98/1.18        | ((k1_relat_1 @ sk_D_1) != (k2_relat_1 @ sk_C_1))
% 0.98/1.18        | ~ (v1_funct_1 @ sk_D_1)
% 0.98/1.18        | ~ (v1_relat_1 @ sk_D_1)
% 0.98/1.18        | ~ (v2_funct_1 @ sk_C_1))),
% 0.98/1.18      inference('sup-', [status(thm)], ['95', '96'])).
% 0.98/1.18  thf('98', plain, ((v1_relat_1 @ sk_C_1)),
% 0.98/1.18      inference('sup-', [status(thm)], ['33', '34'])).
% 0.98/1.18  thf('99', plain, ((v1_funct_1 @ sk_C_1)),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('100', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1) @ sk_A)),
% 0.98/1.18      inference('simplify', [status(thm)], ['83'])).
% 0.98/1.18  thf('101', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.98/1.18      inference('demod', [status(thm)], ['49', '56', '59'])).
% 0.98/1.18  thf('102', plain,
% 0.98/1.18      (![X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.98/1.18         ((zip_tseitin_1 @ X5 @ X6 @ X7 @ X9)
% 0.98/1.18          | ~ (r2_hidden @ X5 @ (k1_relat_1 @ X9))
% 0.98/1.18          | ((X6) != (k1_funct_1 @ X9 @ X5)))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.98/1.18  thf('103', plain,
% 0.98/1.18      (![X5 : $i, X7 : $i, X9 : $i]:
% 0.98/1.18         (~ (r2_hidden @ X5 @ (k1_relat_1 @ X9))
% 0.98/1.18          | (zip_tseitin_1 @ X5 @ (k1_funct_1 @ X9 @ X5) @ X7 @ X9))),
% 0.98/1.18      inference('simplify', [status(thm)], ['102'])).
% 0.98/1.18  thf('104', plain,
% 0.98/1.18      (![X0 : $i, X1 : $i]:
% 0.98/1.18         (~ (r2_hidden @ X0 @ sk_A)
% 0.98/1.18          | (zip_tseitin_1 @ X0 @ (k1_funct_1 @ sk_C_1 @ X0) @ X1 @ sk_C_1))),
% 0.98/1.18      inference('sup-', [status(thm)], ['101', '103'])).
% 0.98/1.18  thf('105', plain,
% 0.98/1.18      (![X0 : $i]:
% 0.98/1.18         (zip_tseitin_1 @ (sk_D @ sk_D_1 @ sk_C_1) @ 
% 0.98/1.18          (k1_funct_1 @ sk_C_1 @ (sk_D @ sk_D_1 @ sk_C_1)) @ X0 @ sk_C_1)),
% 0.98/1.18      inference('sup-', [status(thm)], ['100', '104'])).
% 0.98/1.18  thf('106', plain, ((r2_hidden @ (sk_C @ sk_D_1 @ sk_C_1) @ sk_B)),
% 0.98/1.18      inference('simplify', [status(thm)], ['88'])).
% 0.98/1.18  thf('107', plain,
% 0.98/1.18      (![X41 : $i, X42 : $i]:
% 0.98/1.18         (((k1_funct_1 @ sk_C_1 @ X41) = (X42))
% 0.98/1.18          | ((k1_funct_1 @ sk_D_1 @ X42) != (X41))
% 0.98/1.18          | ~ (r2_hidden @ X42 @ sk_B))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('108', plain,
% 0.98/1.18      (![X42 : $i]:
% 0.98/1.18         (~ (r2_hidden @ X42 @ sk_B)
% 0.98/1.18          | ((k1_funct_1 @ sk_C_1 @ (k1_funct_1 @ sk_D_1 @ X42)) = (X42)))),
% 0.98/1.18      inference('simplify', [status(thm)], ['107'])).
% 0.98/1.18  thf('109', plain,
% 0.98/1.18      (((k1_funct_1 @ sk_C_1 @ (k1_funct_1 @ sk_D_1 @ (sk_C @ sk_D_1 @ sk_C_1)))
% 0.98/1.18         = (sk_C @ sk_D_1 @ sk_C_1))),
% 0.98/1.18      inference('sup-', [status(thm)], ['106', '108'])).
% 0.98/1.18  thf('110', plain,
% 0.98/1.18      (((k1_funct_1 @ sk_D_1 @ (sk_C @ sk_D_1 @ sk_C_1))
% 0.98/1.18         = (sk_D @ sk_D_1 @ sk_C_1))),
% 0.98/1.18      inference('simplify', [status(thm)], ['65'])).
% 0.98/1.18  thf('111', plain,
% 0.98/1.18      (((k1_funct_1 @ sk_C_1 @ (sk_D @ sk_D_1 @ sk_C_1))
% 0.98/1.18         = (sk_C @ sk_D_1 @ sk_C_1))),
% 0.98/1.18      inference('demod', [status(thm)], ['109', '110'])).
% 0.98/1.18  thf('112', plain,
% 0.98/1.18      (![X0 : $i]:
% 0.98/1.18         (zip_tseitin_1 @ (sk_D @ sk_D_1 @ sk_C_1) @ 
% 0.98/1.18          (sk_C @ sk_D_1 @ sk_C_1) @ X0 @ sk_C_1)),
% 0.98/1.18      inference('demod', [status(thm)], ['105', '111'])).
% 0.98/1.18  thf('113', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 0.98/1.18      inference('demod', [status(thm)], ['7', '14', '17'])).
% 0.98/1.18  thf('114', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 0.98/1.18      inference('sup+', [status(thm)], ['2', '3'])).
% 0.98/1.18  thf('115', plain, ((v1_funct_1 @ sk_D_1)),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('116', plain, ((v1_relat_1 @ sk_D_1)),
% 0.98/1.18      inference('sup-', [status(thm)], ['26', '27'])).
% 0.98/1.18  thf('117', plain, ((v2_funct_1 @ sk_C_1)),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('118', plain,
% 0.98/1.18      ((((sk_D_1) = (k2_funct_1 @ sk_C_1)) | ((sk_B) != (sk_B)))),
% 0.98/1.18      inference('demod', [status(thm)],
% 0.98/1.18                ['97', '98', '99', '112', '113', '114', '115', '116', '117'])).
% 0.98/1.18  thf('119', plain, (((sk_D_1) = (k2_funct_1 @ sk_C_1))),
% 0.98/1.18      inference('simplify', [status(thm)], ['118'])).
% 0.98/1.18  thf('120', plain, (((sk_D_1) != (k2_funct_1 @ sk_C_1))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('121', plain, ($false),
% 0.98/1.18      inference('simplify_reflect-', [status(thm)], ['119', '120'])).
% 0.98/1.18  
% 0.98/1.18  % SZS output end Refutation
% 0.98/1.18  
% 0.98/1.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
