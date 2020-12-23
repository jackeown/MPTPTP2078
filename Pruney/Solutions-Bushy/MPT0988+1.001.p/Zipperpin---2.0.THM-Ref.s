%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0988+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BfTkZsMuPv

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:50 EST 2020

% Result     : Theorem 1.14s
% Output     : Refutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :  172 (1721 expanded)
%              Number of leaves         :   47 ( 518 expanded)
%              Depth                    :   30
%              Number of atoms          : 1686 (51043 expanded)
%              Number of equality atoms :  124 (4986 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
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
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('7',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
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
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_funct_2 @ X7 @ X5 @ X6 )
      | ( X5
        = ( k1_relset_1 @ X5 @ X6 @ X7 ) )
      | ~ ( zip_tseitin_1 @ X7 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('12',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
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

thf('13',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( zip_tseitin_0 @ X8 @ X9 )
      | ( zip_tseitin_1 @ X10 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('14',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf('18',plain,
    ( sk_B
    = ( k1_relset_1 @ sk_B @ sk_A @ sk_D_1 ) ),
    inference(demod,[status(thm)],['10','17'])).

thf('19',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['7','18'])).

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
      ( ( zip_tseitin_3 @ D @ C @ B @ A )
    <=> ( ( zip_tseitin_2 @ D @ C @ B @ A )
       => ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
          & ( C
            = ( k1_funct_1 @ A @ D ) ) ) ) ) )).

thf('20',plain,(
    ! [X22: $i,X23: $i,X24: $i,X26: $i] :
      ( ( zip_tseitin_3 @ X22 @ X23 @ X24 @ X26 )
      | ( zip_tseitin_2 @ X22 @ X23 @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf(zf_stmt_7,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_5 @ D @ C @ B @ A )
    <=> ( ( zip_tseitin_4 @ D @ C @ A )
       => ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) )
          & ( D
            = ( k1_funct_1 @ B @ C ) ) ) ) ) )).

thf('21',plain,(
    ! [X31: $i,X32: $i,X34: $i,X35: $i] :
      ( ( zip_tseitin_5 @ X31 @ X32 @ X34 @ X35 )
      | ( zip_tseitin_4 @ X31 @ X32 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf(zf_stmt_8,type,(
    zip_tseitin_5: $i > $i > $i > $i > $o )).

thf(zf_stmt_9,type,(
    zip_tseitin_4: $i > $i > $i > $o )).

thf(zf_stmt_10,axiom,(
    ! [D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_4 @ D @ C @ A )
    <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
        & ( C
          = ( k1_funct_1 @ A @ D ) ) ) ) )).

thf(zf_stmt_11,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(zf_stmt_12,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(zf_stmt_13,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ D @ C @ B @ A )
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
                    ( ( zip_tseitin_5 @ D @ C @ B @ A )
                    & ( zip_tseitin_3 @ D @ C @ B @ A ) ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v2_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X37 )
      | ~ ( v1_funct_1 @ X37 )
      | ( ( k1_relat_1 @ X37 )
       != ( k2_relat_1 @ X36 ) )
      | ~ ( zip_tseitin_5 @ ( sk_D @ X37 @ X36 ) @ ( sk_C @ X37 @ X36 ) @ X37 @ X36 )
      | ~ ( zip_tseitin_3 @ ( sk_D @ X37 @ X36 ) @ ( sk_C @ X37 @ X36 ) @ X37 @ X36 )
      | ( X37
        = ( k2_funct_1 @ X36 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_14])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_4 @ ( sk_D @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( zip_tseitin_3 @ ( sk_D @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ X1 @ X0 )
      | ( ( k1_relat_1 @ X1 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_2 @ ( sk_D @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ X1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != ( k2_relat_1 @ X0 ) )
      | ( X1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_4 @ ( sk_D @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( sk_B
       != ( k2_relat_1 @ X0 ) )
      | ( zip_tseitin_4 @ ( sk_D @ sk_D_1 @ X0 ) @ ( sk_C @ sk_D_1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( sk_D_1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 ) @ ( sk_C @ sk_D_1 @ X0 ) @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('29',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( sk_B
       != ( k2_relat_1 @ X0 ) )
      | ( zip_tseitin_4 @ ( sk_D @ sk_D_1 @ X0 ) @ ( sk_C @ sk_D_1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( sk_D_1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 ) @ ( sk_C @ sk_D_1 @ X0 ) @ sk_D_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26','29'])).

thf('31',plain,
    ( ( sk_B != sk_B )
    | ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_D_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( sk_D_1
      = ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( zip_tseitin_4 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','30'])).

thf('32',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('36',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_B != sk_B )
    | ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_D_1 @ sk_C_1 )
    | ( sk_D_1
      = ( k2_funct_1 @ sk_C_1 ) )
    | ( zip_tseitin_4 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['31','32','33','36'])).

thf('38',plain,
    ( ( zip_tseitin_4 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_C_1 )
    | ( sk_D_1
      = ( k2_funct_1 @ sk_C_1 ) )
    | ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_D_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    sk_D_1
 != ( k2_funct_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( zip_tseitin_4 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_C_1 )
    | ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_D_1 @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( X19
        = ( k1_funct_1 @ X20 @ X17 ) )
      | ~ ( zip_tseitin_2 @ X19 @ X17 @ X20 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('42',plain,
    ( ( zip_tseitin_4 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_C_1 )
    | ( ( sk_D @ sk_D_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X29
        = ( k1_funct_1 @ X28 @ X27 ) )
      | ~ ( zip_tseitin_4 @ X27 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('44',plain,
    ( ( ( sk_D @ sk_D_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) )
    | ( ( sk_C @ sk_D_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_C_1 @ ( sk_D @ sk_D_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( zip_tseitin_4 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_C_1 )
    | ( ( sk_D @ sk_D_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('46',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ X27 @ ( k1_relat_1 @ X28 ) )
      | ~ ( zip_tseitin_4 @ X27 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('47',plain,
    ( ( ( sk_D @ sk_D_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('50',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_funct_2 @ X7 @ X5 @ X6 )
      | ( X5
        = ( k1_relset_1 @ X5 @ X6 @ X7 ) )
      | ~ ( zip_tseitin_1 @ X7 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('53',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('55',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( zip_tseitin_0 @ X8 @ X9 )
      | ( zip_tseitin_1 @ X10 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('57',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

thf('61',plain,
    ( sk_A
    = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['53','60'])).

thf('62',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['50','61'])).

thf('63',plain,
    ( ( ( sk_D @ sk_D_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['47','62'])).

thf('64',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k1_funct_1 @ sk_D_1 @ X42 )
        = X43 )
      | ( ( k1_funct_1 @ sk_C_1 @ X43 )
       != X42 )
      | ~ ( r2_hidden @ X43 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X43: $i] :
      ( ~ ( r2_hidden @ X43 @ sk_A )
      | ( ( k1_funct_1 @ sk_D_1 @ ( k1_funct_1 @ sk_C_1 @ X43 ) )
        = X43 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( ( sk_D @ sk_D_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) )
    | ( ( k1_funct_1 @ sk_D_1 @ ( k1_funct_1 @ sk_C_1 @ ( sk_D @ sk_D_1 @ sk_C_1 ) ) )
      = ( sk_D @ sk_D_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,
    ( ( ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) )
      = ( sk_D @ sk_D_1 @ sk_C_1 ) )
    | ( ( sk_D @ sk_D_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) )
    | ( ( sk_D @ sk_D_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['44','66'])).

thf('68',plain,
    ( ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) )
    = ( sk_D @ sk_D_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( zip_tseitin_4 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_C_1 )
    | ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_D_1 @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

thf('70',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X17 @ ( k2_relat_1 @ X18 ) )
      | ~ ( zip_tseitin_2 @ X19 @ X17 @ X20 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('71',plain,
    ( ( zip_tseitin_4 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_C_1 )
    | ( r2_hidden @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['2','3'])).

thf('73',plain,
    ( ( zip_tseitin_4 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_C_1 )
    | ( r2_hidden @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_B ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X29
        = ( k1_funct_1 @ X28 @ X27 ) )
      | ~ ( zip_tseitin_4 @ X27 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('75',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_B )
    | ( ( sk_C @ sk_D_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_C_1 @ ( sk_D @ sk_D_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( zip_tseitin_4 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_C_1 )
    | ( r2_hidden @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_B ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('77',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ X27 @ ( k1_relat_1 @ X28 ) )
      | ~ ( zip_tseitin_4 @ X27 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('78',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['50','61'])).

thf('80',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r2_hidden @ X41 @ sk_A )
      | ( ( k1_funct_1 @ sk_D_1 @ X42 )
       != X41 )
      | ~ ( r2_hidden @ X42 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X42: $i] :
      ( ~ ( r2_hidden @ X42 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X42 ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ sk_A )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['80','82'])).

thf('84',plain,
    ( ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) )
    = ( sk_D @ sk_D_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('85',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ sk_A )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ sk_A ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X42: $i,X43: $i] :
      ( ( r2_hidden @ X42 @ sk_B )
      | ( ( k1_funct_1 @ sk_C_1 @ X43 )
       != X42 )
      | ~ ( r2_hidden @ X43 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X43: $i] :
      ( ~ ( r2_hidden @ X43 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X43 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_D @ sk_D_1 @ sk_C_1 ) ) @ sk_B ),
    inference('sup-',[status(thm)],['86','88'])).

thf('90',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_B )
    | ( r2_hidden @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_B ) ),
    inference('sup+',[status(thm)],['75','89'])).

thf('91',plain,(
    r2_hidden @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_B ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['2','3'])).

thf('93',plain,(
    ! [X31: $i,X32: $i,X34: $i,X35: $i] :
      ( ( zip_tseitin_5 @ X31 @ X32 @ X34 @ X35 )
      | ~ ( r2_hidden @ X32 @ ( k2_relat_1 @ X35 ) )
      | ( X31
       != ( k1_funct_1 @ X34 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('94',plain,(
    ! [X32: $i,X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X32 @ ( k2_relat_1 @ X35 ) )
      | ( zip_tseitin_5 @ ( k1_funct_1 @ X34 @ X32 ) @ X32 @ X34 @ X35 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( zip_tseitin_5 @ ( k1_funct_1 @ X1 @ X0 ) @ X0 @ X1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['92','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( zip_tseitin_5 @ ( k1_funct_1 @ X0 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ X0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['91','95'])).

thf('97',plain,(
    zip_tseitin_5 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_D_1 @ sk_C_1 ),
    inference('sup+',[status(thm)],['68','96'])).

thf('98',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v2_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X37 )
      | ~ ( v1_funct_1 @ X37 )
      | ( ( k1_relat_1 @ X37 )
       != ( k2_relat_1 @ X36 ) )
      | ~ ( zip_tseitin_5 @ ( sk_D @ X37 @ X36 ) @ ( sk_C @ X37 @ X36 ) @ X37 @ X36 )
      | ~ ( zip_tseitin_3 @ ( sk_D @ X37 @ X36 ) @ ( sk_C @ X37 @ X36 ) @ X37 @ X36 )
      | ( X37
        = ( k2_funct_1 @ X36 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_14])).

thf('99',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( sk_D_1
      = ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( zip_tseitin_3 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_D_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_D_1 )
     != ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['34','35'])).

thf('101',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ sk_A ),
    inference(simplify,[status(thm)],['85'])).

thf('103',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['50','61'])).

thf('104',plain,(
    ! [X22: $i,X23: $i,X24: $i,X26: $i] :
      ( ( zip_tseitin_3 @ X22 @ X23 @ X24 @ X26 )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X26 ) )
      | ( X23
       != ( k1_funct_1 @ X26 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('105',plain,(
    ! [X22: $i,X24: $i,X26: $i] :
      ( ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X26 ) )
      | ( zip_tseitin_3 @ X22 @ ( k1_funct_1 @ X26 @ X22 ) @ X24 @ X26 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( zip_tseitin_3 @ X0 @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ X1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['103','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( zip_tseitin_3 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( k1_funct_1 @ sk_C_1 @ ( sk_D @ sk_D_1 @ sk_C_1 ) ) @ X0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['102','106'])).

thf('108',plain,(
    r2_hidden @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ sk_B ),
    inference(simplify,[status(thm)],['90'])).

thf('109',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X41 )
        = X42 )
      | ( ( k1_funct_1 @ sk_D_1 @ X42 )
       != X41 )
      | ~ ( r2_hidden @ X42 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X42: $i] :
      ( ~ ( r2_hidden @ X42 @ sk_B )
      | ( ( k1_funct_1 @ sk_C_1 @ ( k1_funct_1 @ sk_D_1 @ X42 ) )
        = X42 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) ) )
    = ( sk_C @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['108','110'])).

thf('112',plain,
    ( ( k1_funct_1 @ sk_D_1 @ ( sk_C @ sk_D_1 @ sk_C_1 ) )
    = ( sk_D @ sk_D_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('113',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_D @ sk_D_1 @ sk_C_1 ) )
    = ( sk_C @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( zip_tseitin_3 @ ( sk_D @ sk_D_1 @ sk_C_1 ) @ ( sk_C @ sk_D_1 @ sk_C_1 ) @ X0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['107','113'])).

thf('115',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['7','18'])).

thf('116',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['2','3'])).

thf('117',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('119',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( sk_D_1
      = ( k2_funct_1 @ sk_C_1 ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['99','100','101','114','115','116','117','118','119'])).

thf('121',plain,
    ( sk_D_1
    = ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    sk_D_1
 != ( k2_funct_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['121','122'])).


%------------------------------------------------------------------------------
