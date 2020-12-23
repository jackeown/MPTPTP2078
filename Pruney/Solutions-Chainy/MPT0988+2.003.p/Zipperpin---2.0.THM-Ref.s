%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GNEI04gRPz

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:52 EST 2020

% Result     : Theorem 18.46s
% Output     : Refutation 18.46s
% Verified   : 
% Statistics : Number of formulae       :  214 (8059 expanded)
%              Number of leaves         :   39 (2352 expanded)
%              Depth                    :   33
%              Number of atoms          : 2106 (226750 expanded)
%              Number of equality atoms :  225 (22780 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    v1_funct_2 @ sk_D_3 @ sk_B @ sk_A ),
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

thf('1',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
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

thf('5',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_D_3 @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_3 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    zip_tseitin_1 @ sk_D_3 @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D_3 )
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('16',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k2_relat_1 @ sk_C_2 )
    = sk_B ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t60_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k1_relat_1 @ A )
                = ( k2_relat_1 @ B ) )
              & ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i,D: $i] :
                  ( ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                    & ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) )
                 => ( ( ( k1_funct_1 @ A @ C )
                      = D )
                  <=> ( ( k1_funct_1 @ B @ D )
                      = C ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11
        = ( k2_funct_1 @ X12 ) )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X12 ) @ ( k1_relat_1 @ X12 ) )
      | ( ( k2_relat_1 @ X12 )
       != ( k1_relat_1 @ X11 ) )
      | ( ( k1_relat_1 @ X12 )
       != ( k2_relat_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t60_funct_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( sk_B
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v2_funct_1 @ sk_C_2 )
      | ( ( k1_relat_1 @ sk_C_2 )
       != ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( X0
        = ( k2_funct_1 @ sk_C_2 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('25',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('30',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('32',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('34',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('40',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['30','37','40'])).

thf('42',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['30','37','40'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( sk_B
       != ( k1_relat_1 @ X0 ) )
      | ( sk_A
       != ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A )
      | ( X0
        = ( k2_funct_1 @ sk_C_2 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','25','26','27','41','42'])).

thf('44',plain,
    ( ( sk_B != sk_B )
    | ~ ( v1_relat_1 @ sk_D_3 )
    | ~ ( v1_funct_1 @ sk_D_3 )
    | ( sk_D_3
      = ( k2_funct_1 @ sk_C_2 ) )
    | ( r2_hidden @ ( sk_C_1 @ sk_D_3 @ sk_C_2 ) @ sk_A )
    | ( sk_A
     != ( k2_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['13','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('49',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('51',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ ( sk_C @ X4 @ X5 ) @ X4 )
      | ( ( sk_C @ X4 @ X5 )
        = ( k1_funct_1 @ X5 @ ( sk_D @ X4 @ X5 ) ) )
      | ( X4
        = ( k2_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('52',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('53',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ ( sk_C @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X4 @ X5 ) @ ( k1_relat_1 @ X5 ) )
      | ( X4
        = ( k2_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_D_3 ) @ sk_B )
      | ~ ( v1_relat_1 @ sk_D_3 )
      | ~ ( v1_funct_1 @ sk_D_3 )
      | ( X0
        = ( k2_relat_1 @ sk_D_3 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_D_3 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['47','48'])).

thf('56',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_D_3 ) @ sk_B )
      | ( X0
        = ( k2_relat_1 @ sk_D_3 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_D_3 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r2_hidden @ X27 @ sk_A )
      | ( ( k1_funct_1 @ sk_D_3 @ X28 )
       != X27 )
      | ~ ( r2_hidden @ X28 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X28: $i] :
      ( ~ ( r2_hidden @ X28 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_3 @ X28 ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_D_3 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_D_3 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_3 @ ( sk_D @ X0 @ sk_D_3 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_D_3 ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_D_3 )
      | ~ ( v1_funct_1 @ sk_D_3 )
      | ( X0
        = ( k2_relat_1 @ sk_D_3 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_D_3 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_D_3 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_D_3 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['47','48'])).

thf('63',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_D_3 ) @ sk_A )
      | ( X0
        = ( k2_relat_1 @ sk_D_3 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_D_3 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_D_3 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_D_3 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_D_3 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_D_3 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_D_3 ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( r2_hidden @ ( sk_C @ sk_A @ sk_D_3 ) @ sk_A )
    | ( sk_A
      = ( k2_relat_1 @ sk_D_3 ) ) ),
    inference(eq_fact,[status(thm)],['65'])).

thf('67',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k1_funct_1 @ sk_D_3 @ X28 )
        = X29 )
      | ( ( k1_funct_1 @ sk_C_2 @ X29 )
       != X28 )
      | ~ ( r2_hidden @ X29 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X29: $i] :
      ( ~ ( r2_hidden @ X29 @ sk_A )
      | ( ( k1_funct_1 @ sk_D_3 @ ( k1_funct_1 @ sk_C_2 @ X29 ) )
        = X29 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( sk_A
      = ( k2_relat_1 @ sk_D_3 ) )
    | ( ( k1_funct_1 @ sk_D_3 @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ sk_A @ sk_D_3 ) ) )
      = ( sk_C @ sk_A @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,
    ( ( r2_hidden @ ( sk_C @ sk_A @ sk_D_3 ) @ sk_A )
    | ( sk_A
      = ( k2_relat_1 @ sk_D_3 ) ) ),
    inference(eq_fact,[status(thm)],['65'])).

thf('71',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X4 @ X5 ) @ X4 )
      | ( ( sk_C @ X4 @ X5 )
       != ( k1_funct_1 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X5 ) )
      | ( X4
        = ( k2_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k2_relat_1 @ sk_D_3 ) )
      | ~ ( v1_relat_1 @ sk_D_3 )
      | ~ ( v1_funct_1 @ sk_D_3 )
      | ( sk_A
        = ( k2_relat_1 @ sk_D_3 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_3 ) )
      | ( ( sk_C @ sk_A @ sk_D_3 )
       != ( k1_funct_1 @ sk_D_3 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['47','48'])).

thf('74',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k2_relat_1 @ sk_D_3 ) )
      | ( sk_A
        = ( k2_relat_1 @ sk_D_3 ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( ( sk_C @ sk_A @ sk_D_3 )
       != ( k1_funct_1 @ sk_D_3 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_A @ sk_D_3 )
       != ( k1_funct_1 @ sk_D_3 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( sk_A
        = ( k2_relat_1 @ sk_D_3 ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( ( sk_C @ sk_A @ sk_D_3 )
     != ( sk_C @ sk_A @ sk_D_3 ) )
    | ( sk_A
      = ( k2_relat_1 @ sk_D_3 ) )
    | ( sk_A
      = ( k2_relat_1 @ sk_D_3 ) )
    | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ sk_A @ sk_D_3 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['69','77'])).

thf('79',plain,
    ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ sk_A @ sk_D_3 ) ) @ sk_B )
    | ( sk_A
      = ( k2_relat_1 @ sk_D_3 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( r2_hidden @ ( sk_C @ sk_A @ sk_D_3 ) @ sk_A )
    | ( sk_A
      = ( k2_relat_1 @ sk_D_3 ) ) ),
    inference(eq_fact,[status(thm)],['65'])).

thf('81',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r2_hidden @ X28 @ sk_B )
      | ( ( k1_funct_1 @ sk_C_2 @ X29 )
       != X28 )
      | ~ ( r2_hidden @ X29 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X29: $i] :
      ( ~ ( r2_hidden @ X29 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X29 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( sk_A
      = ( k2_relat_1 @ sk_D_3 ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ sk_A @ sk_D_3 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['80','82'])).

thf('84',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference(clc,[status(thm)],['79','83'])).

thf('85',plain,
    ( ( sk_B != sk_B )
    | ( sk_D_3
      = ( k2_funct_1 @ sk_C_2 ) )
    | ( r2_hidden @ ( sk_C_1 @ sk_D_3 @ sk_C_2 ) @ sk_A )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['44','49','50','84'])).

thf('86',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D_3 @ sk_C_2 ) @ sk_A )
    | ( sk_D_3
      = ( k2_funct_1 @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    sk_D_3
 != ( k2_funct_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    r2_hidden @ ( sk_C_1 @ sk_D_3 @ sk_C_2 ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['86','87'])).

thf('89',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference(clc,[status(thm)],['79','83'])).

thf('90',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( X7
       != ( k2_relat_1 @ X5 ) )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ ( k1_relat_1 @ X5 ) )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('91',plain,(
    ! [X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X5 ) )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ ( k1_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_D_3 ) @ ( k1_relat_1 @ sk_D_3 ) )
      | ~ ( v1_funct_1 @ sk_D_3 )
      | ~ ( v1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['89','91'])).

thf('93',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('94',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['47','48'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_D_3 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('97',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_D_3 @ sk_C_2 ) @ sk_D_3 ) @ sk_B ),
    inference('sup-',[status(thm)],['88','96'])).

thf('98',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X27 )
        = X28 )
      | ( ( k1_funct_1 @ sk_D_3 @ X28 )
       != X27 )
      | ~ ( r2_hidden @ X28 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X28: $i] :
      ( ~ ( r2_hidden @ X28 @ sk_B )
      | ( ( k1_funct_1 @ sk_C_2 @ ( k1_funct_1 @ sk_D_3 @ X28 ) )
        = X28 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( k1_funct_1 @ sk_D_3 @ ( sk_D_1 @ ( sk_C_1 @ sk_D_3 @ sk_C_2 ) @ sk_D_3 ) ) )
    = ( sk_D_1 @ ( sk_C_1 @ sk_D_3 @ sk_C_2 ) @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['97','99'])).

thf('101',plain,(
    r2_hidden @ ( sk_C_1 @ sk_D_3 @ sk_C_2 ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['86','87'])).

thf('102',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference(clc,[status(thm)],['79','83'])).

thf('103',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( X7
       != ( k2_relat_1 @ X5 ) )
      | ( X8
        = ( k1_funct_1 @ X5 @ ( sk_D_1 @ X8 @ X5 ) ) )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('104',plain,(
    ! [X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X5 ) )
      | ( X8
        = ( k1_funct_1 @ X5 @ ( sk_D_1 @ X8 @ X5 ) ) ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0
        = ( k1_funct_1 @ sk_D_3 @ ( sk_D_1 @ X0 @ sk_D_3 ) ) )
      | ~ ( v1_funct_1 @ sk_D_3 )
      | ~ ( v1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['102','104'])).

thf('106',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['47','48'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0
        = ( k1_funct_1 @ sk_D_3 @ ( sk_D_1 @ X0 @ sk_D_3 ) ) ) ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,
    ( ( sk_C_1 @ sk_D_3 @ sk_C_2 )
    = ( k1_funct_1 @ sk_D_3 @ ( sk_D_1 @ ( sk_C_1 @ sk_D_3 @ sk_C_2 ) @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['101','108'])).

thf('110',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D_3 @ sk_C_2 ) )
    = ( sk_D_1 @ ( sk_C_1 @ sk_D_3 @ sk_C_2 ) @ sk_D_3 ) ),
    inference(demod,[status(thm)],['100','109'])).

thf('111',plain,
    ( ( k2_relat_1 @ sk_C_2 )
    = sk_B ),
    inference('sup+',[status(thm)],['16','17'])).

thf('112',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('113',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11
        = ( k2_funct_1 @ X12 ) )
      | ( r2_hidden @ ( sk_D_2 @ X11 @ X12 ) @ ( k1_relat_1 @ X11 ) )
      | ( ( k2_relat_1 @ X12 )
       != ( k1_relat_1 @ X11 ) )
      | ( ( k1_relat_1 @ X12 )
       != ( k2_relat_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t60_funct_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
       != ( k2_relat_1 @ sk_D_3 ) )
      | ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ X0 ) @ ( k1_relat_1 @ sk_D_3 ) )
      | ( sk_D_3
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D_3 )
      | ~ ( v1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference(clc,[status(thm)],['79','83'])).

thf('116',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('117',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['47','48'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
       != sk_A )
      | ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ X0 ) @ sk_B )
      | ( sk_D_3
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['114','115','116','117','118'])).

thf('120',plain,
    ( ( sk_B != sk_B )
    | ( sk_D_3
      = ( k2_funct_1 @ sk_C_2 ) )
    | ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_C_2 ) @ sk_B )
    | ( ( k1_relat_1 @ sk_C_2 )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['111','119'])).

thf('121',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['30','37','40'])).

thf('122',plain,(
    v2_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['23','24'])).

thf('125',plain,
    ( ( sk_B != sk_B )
    | ( sk_D_3
      = ( k2_funct_1 @ sk_C_2 ) )
    | ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_C_2 ) @ sk_B )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['120','121','122','123','124'])).

thf('126',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_C_2 ) @ sk_B )
    | ( sk_D_3
      = ( k2_funct_1 @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    sk_D_3
 != ( k2_funct_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_C_2 ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X28: $i] :
      ( ~ ( r2_hidden @ X28 @ sk_B )
      | ( ( k1_funct_1 @ sk_C_2 @ ( k1_funct_1 @ sk_D_3 @ X28 ) )
        = X28 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('130',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ sk_C_2 ) ) )
    = ( sk_D_2 @ sk_D_3 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('132',plain,
    ( ( k2_relat_1 @ sk_C_2 )
    = sk_B ),
    inference('sup+',[status(thm)],['16','17'])).

thf('133',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11
        = ( k2_funct_1 @ X12 ) )
      | ( ( k1_funct_1 @ X12 @ ( sk_C_1 @ X11 @ X12 ) )
        = ( sk_D_2 @ X11 @ X12 ) )
      | ( ( k1_funct_1 @ X11 @ ( sk_D_2 @ X11 @ X12 ) )
        = ( sk_C_1 @ X11 @ X12 ) )
      | ( ( k2_relat_1 @ X12 )
       != ( k1_relat_1 @ X11 ) )
      | ( ( k1_relat_1 @ X12 )
       != ( k2_relat_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t60_funct_1])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( sk_B
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v2_funct_1 @ sk_C_2 )
      | ( ( k1_relat_1 @ sk_C_2 )
       != ( k2_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ ( sk_D_2 @ X0 @ sk_C_2 ) )
        = ( sk_C_1 @ X0 @ sk_C_2 ) )
      | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ X0 @ sk_C_2 ) )
        = ( sk_D_2 @ X0 @ sk_C_2 ) )
      | ( X0
        = ( k2_funct_1 @ sk_C_2 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['23','24'])).

thf('136',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v2_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['30','37','40'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( sk_B
       != ( k1_relat_1 @ X0 ) )
      | ( sk_A
       != ( k2_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ ( sk_D_2 @ X0 @ sk_C_2 ) )
        = ( sk_C_1 @ X0 @ sk_C_2 ) )
      | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ X0 @ sk_C_2 ) )
        = ( sk_D_2 @ X0 @ sk_C_2 ) )
      | ( X0
        = ( k2_funct_1 @ sk_C_2 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['134','135','136','137','138'])).

thf('140',plain,
    ( ( sk_B != sk_B )
    | ~ ( v1_relat_1 @ sk_D_3 )
    | ~ ( v1_funct_1 @ sk_D_3 )
    | ( sk_D_3
      = ( k2_funct_1 @ sk_C_2 ) )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D_3 @ sk_C_2 ) )
      = ( sk_D_2 @ sk_D_3 @ sk_C_2 ) )
    | ( ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ sk_C_2 ) )
      = ( sk_C_1 @ sk_D_3 @ sk_C_2 ) )
    | ( sk_A
     != ( k2_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['131','139'])).

thf('141',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['47','48'])).

thf('142',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D_3 @ sk_C_2 ) )
    = ( sk_D_1 @ ( sk_C_1 @ sk_D_3 @ sk_C_2 ) @ sk_D_3 ) ),
    inference(demod,[status(thm)],['100','109'])).

thf('144',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference(clc,[status(thm)],['79','83'])).

thf('145',plain,
    ( ( sk_B != sk_B )
    | ( sk_D_3
      = ( k2_funct_1 @ sk_C_2 ) )
    | ( ( sk_D_1 @ ( sk_C_1 @ sk_D_3 @ sk_C_2 ) @ sk_D_3 )
      = ( sk_D_2 @ sk_D_3 @ sk_C_2 ) )
    | ( ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ sk_C_2 ) )
      = ( sk_C_1 @ sk_D_3 @ sk_C_2 ) )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['140','141','142','143','144'])).

thf('146',plain,
    ( ( ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ sk_C_2 ) )
      = ( sk_C_1 @ sk_D_3 @ sk_C_2 ) )
    | ( ( sk_D_1 @ ( sk_C_1 @ sk_D_3 @ sk_C_2 ) @ sk_D_3 )
      = ( sk_D_2 @ sk_D_3 @ sk_C_2 ) )
    | ( sk_D_3
      = ( k2_funct_1 @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    sk_D_3
 != ( k2_funct_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ sk_C_2 ) )
      = ( sk_C_1 @ sk_D_3 @ sk_C_2 ) )
    | ( ( sk_D_1 @ ( sk_C_1 @ sk_D_3 @ sk_C_2 ) @ sk_D_3 )
      = ( sk_D_2 @ sk_D_3 @ sk_C_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['146','147'])).

thf('149',plain,
    ( ( sk_C_1 @ sk_D_3 @ sk_C_2 )
    = ( k1_funct_1 @ sk_D_3 @ ( sk_D_1 @ ( sk_C_1 @ sk_D_3 @ sk_C_2 ) @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['101','108'])).

thf('150',plain,
    ( ( ( sk_C_1 @ sk_D_3 @ sk_C_2 )
      = ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ sk_C_2 ) ) )
    | ( ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ sk_C_2 ) )
      = ( sk_C_1 @ sk_D_3 @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['148','149'])).

thf('151',plain,
    ( ( sk_C_1 @ sk_D_3 @ sk_C_2 )
    = ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D_3 @ sk_C_2 ) )
    = ( sk_D_2 @ sk_D_3 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['130','151'])).

thf('153',plain,
    ( ( sk_D_1 @ ( sk_C_1 @ sk_D_3 @ sk_C_2 ) @ sk_D_3 )
    = ( sk_D_2 @ sk_D_3 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['110','152'])).

thf('154',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D_3 @ sk_C_2 ) )
    = ( sk_D_1 @ ( sk_C_1 @ sk_D_3 @ sk_C_2 ) @ sk_D_3 ) ),
    inference(demod,[status(thm)],['100','109'])).

thf('155',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11
        = ( k2_funct_1 @ X12 ) )
      | ( ( k1_funct_1 @ X12 @ ( sk_C_1 @ X11 @ X12 ) )
       != ( sk_D_2 @ X11 @ X12 ) )
      | ( ( k1_funct_1 @ X11 @ ( sk_D_2 @ X11 @ X12 ) )
       != ( sk_C_1 @ X11 @ X12 ) )
      | ( ( k2_relat_1 @ X12 )
       != ( k1_relat_1 @ X11 ) )
      | ( ( k1_relat_1 @ X12 )
       != ( k2_relat_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t60_funct_1])).

thf('156',plain,
    ( ( ( sk_D_1 @ ( sk_C_1 @ sk_D_3 @ sk_C_2 ) @ sk_D_3 )
     != ( sk_D_2 @ sk_D_3 @ sk_C_2 ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v2_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k2_relat_1 @ sk_D_3 ) )
    | ( ( k2_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D_3 ) )
    | ( ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ sk_C_2 ) )
     != ( sk_C_1 @ sk_D_3 @ sk_C_2 ) )
    | ( sk_D_3
      = ( k2_funct_1 @ sk_C_2 ) )
    | ~ ( v1_funct_1 @ sk_D_3 )
    | ~ ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['23','24'])).

thf('158',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v2_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['30','37','40'])).

thf('161',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference(clc,[status(thm)],['79','83'])).

thf('162',plain,
    ( ( k2_relat_1 @ sk_C_2 )
    = sk_B ),
    inference('sup+',[status(thm)],['16','17'])).

thf('163',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('164',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['47','48'])).

thf('166',plain,
    ( ( ( sk_D_1 @ ( sk_C_1 @ sk_D_3 @ sk_C_2 ) @ sk_D_3 )
     != ( sk_D_2 @ sk_D_3 @ sk_C_2 ) )
    | ( sk_A != sk_A )
    | ( sk_B != sk_B )
    | ( ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ sk_C_2 ) )
     != ( sk_C_1 @ sk_D_3 @ sk_C_2 ) )
    | ( sk_D_3
      = ( k2_funct_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['156','157','158','159','160','161','162','163','164','165'])).

thf('167',plain,
    ( ( sk_D_3
      = ( k2_funct_1 @ sk_C_2 ) )
    | ( ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ sk_C_2 ) )
     != ( sk_C_1 @ sk_D_3 @ sk_C_2 ) )
    | ( ( sk_D_1 @ ( sk_C_1 @ sk_D_3 @ sk_C_2 ) @ sk_D_3 )
     != ( sk_D_2 @ sk_D_3 @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,(
    sk_D_3
 != ( k2_funct_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ sk_C_2 ) )
     != ( sk_C_1 @ sk_D_3 @ sk_C_2 ) )
    | ( ( sk_D_1 @ ( sk_C_1 @ sk_D_3 @ sk_C_2 ) @ sk_D_3 )
     != ( sk_D_2 @ sk_D_3 @ sk_C_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['167','168'])).

thf('170',plain,
    ( ( sk_C_1 @ sk_D_3 @ sk_C_2 )
    = ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('171',plain,
    ( ( ( sk_C_1 @ sk_D_3 @ sk_C_2 )
     != ( sk_C_1 @ sk_D_3 @ sk_C_2 ) )
    | ( ( sk_D_1 @ ( sk_C_1 @ sk_D_3 @ sk_C_2 ) @ sk_D_3 )
     != ( sk_D_2 @ sk_D_3 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,(
    ( sk_D_1 @ ( sk_C_1 @ sk_D_3 @ sk_C_2 ) @ sk_D_3 )
 != ( sk_D_2 @ sk_D_3 @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['153','172'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GNEI04gRPz
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:33:47 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 18.46/18.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 18.46/18.65  % Solved by: fo/fo7.sh
% 18.46/18.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 18.46/18.65  % done 6349 iterations in 18.181s
% 18.46/18.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 18.46/18.65  % SZS output start Refutation
% 18.46/18.65  thf(sk_D_3_type, type, sk_D_3: $i).
% 18.46/18.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 18.46/18.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 18.46/18.65  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 18.46/18.65  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 18.46/18.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 18.46/18.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 18.46/18.65  thf(sk_C_2_type, type, sk_C_2: $i).
% 18.46/18.65  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 18.46/18.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 18.46/18.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 18.46/18.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 18.46/18.65  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 18.46/18.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 18.46/18.65  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 18.46/18.65  thf(sk_B_type, type, sk_B: $i).
% 18.46/18.65  thf(sk_A_type, type, sk_A: $i).
% 18.46/18.65  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 18.46/18.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 18.46/18.65  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 18.46/18.65  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 18.46/18.65  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 18.46/18.65  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 18.46/18.65  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 18.46/18.65  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 18.46/18.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 18.46/18.65  thf(t34_funct_2, conjecture,
% 18.46/18.65    (![A:$i,B:$i,C:$i]:
% 18.46/18.65     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 18.46/18.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 18.46/18.65       ( ![D:$i]:
% 18.46/18.65         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 18.46/18.65             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 18.46/18.65           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) & 
% 18.46/18.65               ( ![E:$i,F:$i]:
% 18.46/18.65                 ( ( ( ( r2_hidden @ F @ A ) & 
% 18.46/18.65                       ( ( k1_funct_1 @ C @ F ) = ( E ) ) ) =>
% 18.46/18.65                     ( ( r2_hidden @ E @ B ) & 
% 18.46/18.65                       ( ( k1_funct_1 @ D @ E ) = ( F ) ) ) ) & 
% 18.46/18.65                   ( ( ( r2_hidden @ E @ B ) & 
% 18.46/18.65                       ( ( k1_funct_1 @ D @ E ) = ( F ) ) ) =>
% 18.46/18.65                     ( ( r2_hidden @ F @ A ) & 
% 18.46/18.65                       ( ( k1_funct_1 @ C @ F ) = ( E ) ) ) ) ) ) ) =>
% 18.46/18.65             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 18.46/18.65               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 18.46/18.65  thf(zf_stmt_0, negated_conjecture,
% 18.46/18.65    (~( ![A:$i,B:$i,C:$i]:
% 18.46/18.65        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 18.46/18.65            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 18.46/18.65          ( ![D:$i]:
% 18.46/18.65            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 18.46/18.65                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 18.46/18.65              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 18.46/18.65                  ( v2_funct_1 @ C ) & 
% 18.46/18.65                  ( ![E:$i,F:$i]:
% 18.46/18.65                    ( ( ( ( r2_hidden @ F @ A ) & 
% 18.46/18.65                          ( ( k1_funct_1 @ C @ F ) = ( E ) ) ) =>
% 18.46/18.65                        ( ( r2_hidden @ E @ B ) & 
% 18.46/18.65                          ( ( k1_funct_1 @ D @ E ) = ( F ) ) ) ) & 
% 18.46/18.65                      ( ( ( r2_hidden @ E @ B ) & 
% 18.46/18.65                          ( ( k1_funct_1 @ D @ E ) = ( F ) ) ) =>
% 18.46/18.65                        ( ( r2_hidden @ F @ A ) & 
% 18.46/18.65                          ( ( k1_funct_1 @ C @ F ) = ( E ) ) ) ) ) ) ) =>
% 18.46/18.65                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 18.46/18.65                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 18.46/18.65    inference('cnf.neg', [status(esa)], [t34_funct_2])).
% 18.46/18.65  thf('0', plain, ((v1_funct_2 @ sk_D_3 @ sk_B @ sk_A)),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf(d1_funct_2, axiom,
% 18.46/18.65    (![A:$i,B:$i,C:$i]:
% 18.46/18.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 18.46/18.65       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 18.46/18.65           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 18.46/18.65             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 18.46/18.65         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 18.46/18.65           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 18.46/18.65             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 18.46/18.65  thf(zf_stmt_1, axiom,
% 18.46/18.65    (![C:$i,B:$i,A:$i]:
% 18.46/18.65     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 18.46/18.65       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 18.46/18.65  thf('1', plain,
% 18.46/18.65      (![X21 : $i, X22 : $i, X23 : $i]:
% 18.46/18.65         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 18.46/18.65          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 18.46/18.65          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_1])).
% 18.46/18.65  thf('2', plain,
% 18.46/18.65      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_A @ sk_B)
% 18.46/18.65        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D_3)))),
% 18.46/18.65      inference('sup-', [status(thm)], ['0', '1'])).
% 18.46/18.65  thf(zf_stmt_2, axiom,
% 18.46/18.65    (![B:$i,A:$i]:
% 18.46/18.65     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 18.46/18.65       ( zip_tseitin_0 @ B @ A ) ))).
% 18.46/18.65  thf('3', plain,
% 18.46/18.65      (![X19 : $i, X20 : $i]:
% 18.46/18.65         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_2])).
% 18.46/18.65  thf('4', plain,
% 18.46/18.65      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 18.46/18.65  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 18.46/18.65  thf(zf_stmt_5, axiom,
% 18.46/18.65    (![A:$i,B:$i,C:$i]:
% 18.46/18.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 18.46/18.65       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 18.46/18.65         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 18.46/18.65           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 18.46/18.65             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 18.46/18.65  thf('5', plain,
% 18.46/18.65      (![X24 : $i, X25 : $i, X26 : $i]:
% 18.46/18.65         (~ (zip_tseitin_0 @ X24 @ X25)
% 18.46/18.65          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 18.46/18.65          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_5])).
% 18.46/18.65  thf('6', plain,
% 18.46/18.65      (((zip_tseitin_1 @ sk_D_3 @ sk_A @ sk_B)
% 18.46/18.65        | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 18.46/18.65      inference('sup-', [status(thm)], ['4', '5'])).
% 18.46/18.65  thf('7', plain,
% 18.46/18.65      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_3 @ sk_A @ sk_B))),
% 18.46/18.65      inference('sup-', [status(thm)], ['3', '6'])).
% 18.46/18.65  thf('8', plain, (((sk_A) != (k1_xboole_0))),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf('9', plain, ((zip_tseitin_1 @ sk_D_3 @ sk_A @ sk_B)),
% 18.46/18.65      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 18.46/18.65  thf('10', plain,
% 18.46/18.65      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf(redefinition_k1_relset_1, axiom,
% 18.46/18.65    (![A:$i,B:$i,C:$i]:
% 18.46/18.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 18.46/18.65       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 18.46/18.65  thf('11', plain,
% 18.46/18.65      (![X13 : $i, X14 : $i, X15 : $i]:
% 18.46/18.65         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 18.46/18.65          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 18.46/18.65      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 18.46/18.65  thf('12', plain,
% 18.46/18.65      (((k1_relset_1 @ sk_B @ sk_A @ sk_D_3) = (k1_relat_1 @ sk_D_3))),
% 18.46/18.65      inference('sup-', [status(thm)], ['10', '11'])).
% 18.46/18.65  thf('13', plain, (((sk_B) = (k1_relat_1 @ sk_D_3))),
% 18.46/18.65      inference('demod', [status(thm)], ['2', '9', '12'])).
% 18.46/18.65  thf('14', plain,
% 18.46/18.65      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf(redefinition_k2_relset_1, axiom,
% 18.46/18.65    (![A:$i,B:$i,C:$i]:
% 18.46/18.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 18.46/18.65       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 18.46/18.65  thf('15', plain,
% 18.46/18.65      (![X16 : $i, X17 : $i, X18 : $i]:
% 18.46/18.65         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 18.46/18.65          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 18.46/18.65      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 18.46/18.65  thf('16', plain,
% 18.46/18.65      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 18.46/18.65      inference('sup-', [status(thm)], ['14', '15'])).
% 18.46/18.65  thf('17', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf('18', plain, (((k2_relat_1 @ sk_C_2) = (sk_B))),
% 18.46/18.65      inference('sup+', [status(thm)], ['16', '17'])).
% 18.46/18.65  thf(t60_funct_1, axiom,
% 18.46/18.65    (![A:$i]:
% 18.46/18.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 18.46/18.65       ( ![B:$i]:
% 18.46/18.65         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 18.46/18.65           ( ( ( v2_funct_1 @ A ) & 
% 18.46/18.65               ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ B ) ) & 
% 18.46/18.65               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 18.46/18.65               ( ![C:$i,D:$i]:
% 18.46/18.65                 ( ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 18.46/18.65                     ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) ) =>
% 18.46/18.65                   ( ( ( k1_funct_1 @ A @ C ) = ( D ) ) <=>
% 18.46/18.65                     ( ( k1_funct_1 @ B @ D ) = ( C ) ) ) ) ) ) =>
% 18.46/18.65             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 18.46/18.65  thf('19', plain,
% 18.46/18.65      (![X11 : $i, X12 : $i]:
% 18.46/18.65         (~ (v1_relat_1 @ X11)
% 18.46/18.65          | ~ (v1_funct_1 @ X11)
% 18.46/18.65          | ((X11) = (k2_funct_1 @ X12))
% 18.46/18.65          | (r2_hidden @ (sk_C_1 @ X11 @ X12) @ (k1_relat_1 @ X12))
% 18.46/18.65          | ((k2_relat_1 @ X12) != (k1_relat_1 @ X11))
% 18.46/18.65          | ((k1_relat_1 @ X12) != (k2_relat_1 @ X11))
% 18.46/18.65          | ~ (v2_funct_1 @ X12)
% 18.46/18.65          | ~ (v1_funct_1 @ X12)
% 18.46/18.65          | ~ (v1_relat_1 @ X12))),
% 18.46/18.65      inference('cnf', [status(esa)], [t60_funct_1])).
% 18.46/18.65  thf('20', plain,
% 18.46/18.65      (![X0 : $i]:
% 18.46/18.65         (((sk_B) != (k1_relat_1 @ X0))
% 18.46/18.65          | ~ (v1_relat_1 @ sk_C_2)
% 18.46/18.65          | ~ (v1_funct_1 @ sk_C_2)
% 18.46/18.65          | ~ (v2_funct_1 @ sk_C_2)
% 18.46/18.65          | ((k1_relat_1 @ sk_C_2) != (k2_relat_1 @ X0))
% 18.46/18.65          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 18.46/18.65          | ((X0) = (k2_funct_1 @ sk_C_2))
% 18.46/18.65          | ~ (v1_funct_1 @ X0)
% 18.46/18.65          | ~ (v1_relat_1 @ X0))),
% 18.46/18.65      inference('sup-', [status(thm)], ['18', '19'])).
% 18.46/18.65  thf('21', plain,
% 18.46/18.65      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf(cc2_relat_1, axiom,
% 18.46/18.65    (![A:$i]:
% 18.46/18.65     ( ( v1_relat_1 @ A ) =>
% 18.46/18.65       ( ![B:$i]:
% 18.46/18.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 18.46/18.65  thf('22', plain,
% 18.46/18.65      (![X0 : $i, X1 : $i]:
% 18.46/18.65         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 18.46/18.65          | (v1_relat_1 @ X0)
% 18.46/18.65          | ~ (v1_relat_1 @ X1))),
% 18.46/18.65      inference('cnf', [status(esa)], [cc2_relat_1])).
% 18.46/18.65  thf('23', plain,
% 18.46/18.65      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_2))),
% 18.46/18.65      inference('sup-', [status(thm)], ['21', '22'])).
% 18.46/18.65  thf(fc6_relat_1, axiom,
% 18.46/18.65    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 18.46/18.65  thf('24', plain,
% 18.46/18.65      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 18.46/18.65      inference('cnf', [status(esa)], [fc6_relat_1])).
% 18.46/18.65  thf('25', plain, ((v1_relat_1 @ sk_C_2)),
% 18.46/18.65      inference('demod', [status(thm)], ['23', '24'])).
% 18.46/18.65  thf('26', plain, ((v1_funct_1 @ sk_C_2)),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf('27', plain, ((v2_funct_1 @ sk_C_2)),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf('28', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf('29', plain,
% 18.46/18.65      (![X21 : $i, X22 : $i, X23 : $i]:
% 18.46/18.65         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 18.46/18.65          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 18.46/18.65          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_1])).
% 18.46/18.65  thf('30', plain,
% 18.46/18.65      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 18.46/18.65        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 18.46/18.65      inference('sup-', [status(thm)], ['28', '29'])).
% 18.46/18.65  thf('31', plain,
% 18.46/18.65      (![X19 : $i, X20 : $i]:
% 18.46/18.65         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_2])).
% 18.46/18.65  thf('32', plain,
% 18.46/18.65      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf('33', plain,
% 18.46/18.65      (![X24 : $i, X25 : $i, X26 : $i]:
% 18.46/18.65         (~ (zip_tseitin_0 @ X24 @ X25)
% 18.46/18.65          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 18.46/18.65          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_5])).
% 18.46/18.65  thf('34', plain,
% 18.46/18.65      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 18.46/18.65        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 18.46/18.65      inference('sup-', [status(thm)], ['32', '33'])).
% 18.46/18.65  thf('35', plain,
% 18.46/18.65      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 18.46/18.65      inference('sup-', [status(thm)], ['31', '34'])).
% 18.46/18.65  thf('36', plain, (((sk_B) != (k1_xboole_0))),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf('37', plain, ((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)),
% 18.46/18.65      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 18.46/18.65  thf('38', plain,
% 18.46/18.65      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf('39', plain,
% 18.46/18.65      (![X13 : $i, X14 : $i, X15 : $i]:
% 18.46/18.65         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 18.46/18.65          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 18.46/18.65      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 18.46/18.65  thf('40', plain,
% 18.46/18.65      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 18.46/18.65      inference('sup-', [status(thm)], ['38', '39'])).
% 18.46/18.65  thf('41', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 18.46/18.65      inference('demod', [status(thm)], ['30', '37', '40'])).
% 18.46/18.65  thf('42', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 18.46/18.65      inference('demod', [status(thm)], ['30', '37', '40'])).
% 18.46/18.65  thf('43', plain,
% 18.46/18.65      (![X0 : $i]:
% 18.46/18.65         (((sk_B) != (k1_relat_1 @ X0))
% 18.46/18.65          | ((sk_A) != (k2_relat_1 @ X0))
% 18.46/18.65          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A)
% 18.46/18.65          | ((X0) = (k2_funct_1 @ sk_C_2))
% 18.46/18.65          | ~ (v1_funct_1 @ X0)
% 18.46/18.65          | ~ (v1_relat_1 @ X0))),
% 18.46/18.65      inference('demod', [status(thm)], ['20', '25', '26', '27', '41', '42'])).
% 18.46/18.65  thf('44', plain,
% 18.46/18.65      ((((sk_B) != (sk_B))
% 18.46/18.65        | ~ (v1_relat_1 @ sk_D_3)
% 18.46/18.65        | ~ (v1_funct_1 @ sk_D_3)
% 18.46/18.65        | ((sk_D_3) = (k2_funct_1 @ sk_C_2))
% 18.46/18.65        | (r2_hidden @ (sk_C_1 @ sk_D_3 @ sk_C_2) @ sk_A)
% 18.46/18.65        | ((sk_A) != (k2_relat_1 @ sk_D_3)))),
% 18.46/18.65      inference('sup-', [status(thm)], ['13', '43'])).
% 18.46/18.65  thf('45', plain,
% 18.46/18.65      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf('46', plain,
% 18.46/18.65      (![X0 : $i, X1 : $i]:
% 18.46/18.65         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 18.46/18.65          | (v1_relat_1 @ X0)
% 18.46/18.65          | ~ (v1_relat_1 @ X1))),
% 18.46/18.65      inference('cnf', [status(esa)], [cc2_relat_1])).
% 18.46/18.65  thf('47', plain,
% 18.46/18.65      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D_3))),
% 18.46/18.65      inference('sup-', [status(thm)], ['45', '46'])).
% 18.46/18.65  thf('48', plain,
% 18.46/18.65      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 18.46/18.65      inference('cnf', [status(esa)], [fc6_relat_1])).
% 18.46/18.65  thf('49', plain, ((v1_relat_1 @ sk_D_3)),
% 18.46/18.65      inference('demod', [status(thm)], ['47', '48'])).
% 18.46/18.65  thf('50', plain, ((v1_funct_1 @ sk_D_3)),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf(d5_funct_1, axiom,
% 18.46/18.65    (![A:$i]:
% 18.46/18.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 18.46/18.65       ( ![B:$i]:
% 18.46/18.65         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 18.46/18.65           ( ![C:$i]:
% 18.46/18.65             ( ( r2_hidden @ C @ B ) <=>
% 18.46/18.65               ( ?[D:$i]:
% 18.46/18.65                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 18.46/18.65                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 18.46/18.65  thf('51', plain,
% 18.46/18.65      (![X4 : $i, X5 : $i]:
% 18.46/18.65         ((r2_hidden @ (sk_C @ X4 @ X5) @ X4)
% 18.46/18.65          | ((sk_C @ X4 @ X5) = (k1_funct_1 @ X5 @ (sk_D @ X4 @ X5)))
% 18.46/18.65          | ((X4) = (k2_relat_1 @ X5))
% 18.46/18.65          | ~ (v1_funct_1 @ X5)
% 18.46/18.65          | ~ (v1_relat_1 @ X5))),
% 18.46/18.65      inference('cnf', [status(esa)], [d5_funct_1])).
% 18.46/18.65  thf('52', plain, (((sk_B) = (k1_relat_1 @ sk_D_3))),
% 18.46/18.65      inference('demod', [status(thm)], ['2', '9', '12'])).
% 18.46/18.65  thf('53', plain,
% 18.46/18.65      (![X4 : $i, X5 : $i]:
% 18.46/18.65         ((r2_hidden @ (sk_C @ X4 @ X5) @ X4)
% 18.46/18.65          | (r2_hidden @ (sk_D @ X4 @ X5) @ (k1_relat_1 @ X5))
% 18.46/18.65          | ((X4) = (k2_relat_1 @ X5))
% 18.46/18.65          | ~ (v1_funct_1 @ X5)
% 18.46/18.65          | ~ (v1_relat_1 @ X5))),
% 18.46/18.65      inference('cnf', [status(esa)], [d5_funct_1])).
% 18.46/18.65  thf('54', plain,
% 18.46/18.65      (![X0 : $i]:
% 18.46/18.65         ((r2_hidden @ (sk_D @ X0 @ sk_D_3) @ sk_B)
% 18.46/18.65          | ~ (v1_relat_1 @ sk_D_3)
% 18.46/18.65          | ~ (v1_funct_1 @ sk_D_3)
% 18.46/18.65          | ((X0) = (k2_relat_1 @ sk_D_3))
% 18.46/18.65          | (r2_hidden @ (sk_C @ X0 @ sk_D_3) @ X0))),
% 18.46/18.65      inference('sup+', [status(thm)], ['52', '53'])).
% 18.46/18.65  thf('55', plain, ((v1_relat_1 @ sk_D_3)),
% 18.46/18.65      inference('demod', [status(thm)], ['47', '48'])).
% 18.46/18.65  thf('56', plain, ((v1_funct_1 @ sk_D_3)),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf('57', plain,
% 18.46/18.65      (![X0 : $i]:
% 18.46/18.65         ((r2_hidden @ (sk_D @ X0 @ sk_D_3) @ sk_B)
% 18.46/18.65          | ((X0) = (k2_relat_1 @ sk_D_3))
% 18.46/18.65          | (r2_hidden @ (sk_C @ X0 @ sk_D_3) @ X0))),
% 18.46/18.65      inference('demod', [status(thm)], ['54', '55', '56'])).
% 18.46/18.65  thf('58', plain,
% 18.46/18.65      (![X27 : $i, X28 : $i]:
% 18.46/18.65         ((r2_hidden @ X27 @ sk_A)
% 18.46/18.65          | ((k1_funct_1 @ sk_D_3 @ X28) != (X27))
% 18.46/18.65          | ~ (r2_hidden @ X28 @ sk_B))),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf('59', plain,
% 18.46/18.65      (![X28 : $i]:
% 18.46/18.65         (~ (r2_hidden @ X28 @ sk_B)
% 18.46/18.65          | (r2_hidden @ (k1_funct_1 @ sk_D_3 @ X28) @ sk_A))),
% 18.46/18.65      inference('simplify', [status(thm)], ['58'])).
% 18.46/18.65  thf('60', plain,
% 18.46/18.65      (![X0 : $i]:
% 18.46/18.65         ((r2_hidden @ (sk_C @ X0 @ sk_D_3) @ X0)
% 18.46/18.65          | ((X0) = (k2_relat_1 @ sk_D_3))
% 18.46/18.65          | (r2_hidden @ (k1_funct_1 @ sk_D_3 @ (sk_D @ X0 @ sk_D_3)) @ sk_A))),
% 18.46/18.65      inference('sup-', [status(thm)], ['57', '59'])).
% 18.46/18.65  thf('61', plain,
% 18.46/18.65      (![X0 : $i]:
% 18.46/18.65         ((r2_hidden @ (sk_C @ X0 @ sk_D_3) @ sk_A)
% 18.46/18.65          | ~ (v1_relat_1 @ sk_D_3)
% 18.46/18.65          | ~ (v1_funct_1 @ sk_D_3)
% 18.46/18.65          | ((X0) = (k2_relat_1 @ sk_D_3))
% 18.46/18.65          | (r2_hidden @ (sk_C @ X0 @ sk_D_3) @ X0)
% 18.46/18.65          | ((X0) = (k2_relat_1 @ sk_D_3))
% 18.46/18.65          | (r2_hidden @ (sk_C @ X0 @ sk_D_3) @ X0))),
% 18.46/18.65      inference('sup+', [status(thm)], ['51', '60'])).
% 18.46/18.65  thf('62', plain, ((v1_relat_1 @ sk_D_3)),
% 18.46/18.65      inference('demod', [status(thm)], ['47', '48'])).
% 18.46/18.65  thf('63', plain, ((v1_funct_1 @ sk_D_3)),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf('64', plain,
% 18.46/18.65      (![X0 : $i]:
% 18.46/18.65         ((r2_hidden @ (sk_C @ X0 @ sk_D_3) @ sk_A)
% 18.46/18.65          | ((X0) = (k2_relat_1 @ sk_D_3))
% 18.46/18.65          | (r2_hidden @ (sk_C @ X0 @ sk_D_3) @ X0)
% 18.46/18.65          | ((X0) = (k2_relat_1 @ sk_D_3))
% 18.46/18.65          | (r2_hidden @ (sk_C @ X0 @ sk_D_3) @ X0))),
% 18.46/18.65      inference('demod', [status(thm)], ['61', '62', '63'])).
% 18.46/18.65  thf('65', plain,
% 18.46/18.65      (![X0 : $i]:
% 18.46/18.65         ((r2_hidden @ (sk_C @ X0 @ sk_D_3) @ X0)
% 18.46/18.65          | ((X0) = (k2_relat_1 @ sk_D_3))
% 18.46/18.65          | (r2_hidden @ (sk_C @ X0 @ sk_D_3) @ sk_A))),
% 18.46/18.65      inference('simplify', [status(thm)], ['64'])).
% 18.46/18.65  thf('66', plain,
% 18.46/18.65      (((r2_hidden @ (sk_C @ sk_A @ sk_D_3) @ sk_A)
% 18.46/18.65        | ((sk_A) = (k2_relat_1 @ sk_D_3)))),
% 18.46/18.65      inference('eq_fact', [status(thm)], ['65'])).
% 18.46/18.65  thf('67', plain,
% 18.46/18.65      (![X28 : $i, X29 : $i]:
% 18.46/18.65         (((k1_funct_1 @ sk_D_3 @ X28) = (X29))
% 18.46/18.65          | ((k1_funct_1 @ sk_C_2 @ X29) != (X28))
% 18.46/18.65          | ~ (r2_hidden @ X29 @ sk_A))),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf('68', plain,
% 18.46/18.65      (![X29 : $i]:
% 18.46/18.65         (~ (r2_hidden @ X29 @ sk_A)
% 18.46/18.65          | ((k1_funct_1 @ sk_D_3 @ (k1_funct_1 @ sk_C_2 @ X29)) = (X29)))),
% 18.46/18.65      inference('simplify', [status(thm)], ['67'])).
% 18.46/18.65  thf('69', plain,
% 18.46/18.65      ((((sk_A) = (k2_relat_1 @ sk_D_3))
% 18.46/18.65        | ((k1_funct_1 @ sk_D_3 @ 
% 18.46/18.65            (k1_funct_1 @ sk_C_2 @ (sk_C @ sk_A @ sk_D_3)))
% 18.46/18.65            = (sk_C @ sk_A @ sk_D_3)))),
% 18.46/18.65      inference('sup-', [status(thm)], ['66', '68'])).
% 18.46/18.65  thf('70', plain,
% 18.46/18.65      (((r2_hidden @ (sk_C @ sk_A @ sk_D_3) @ sk_A)
% 18.46/18.65        | ((sk_A) = (k2_relat_1 @ sk_D_3)))),
% 18.46/18.65      inference('eq_fact', [status(thm)], ['65'])).
% 18.46/18.65  thf('71', plain,
% 18.46/18.65      (![X4 : $i, X5 : $i, X6 : $i]:
% 18.46/18.65         (~ (r2_hidden @ (sk_C @ X4 @ X5) @ X4)
% 18.46/18.65          | ((sk_C @ X4 @ X5) != (k1_funct_1 @ X5 @ X6))
% 18.46/18.65          | ~ (r2_hidden @ X6 @ (k1_relat_1 @ X5))
% 18.46/18.65          | ((X4) = (k2_relat_1 @ X5))
% 18.46/18.65          | ~ (v1_funct_1 @ X5)
% 18.46/18.65          | ~ (v1_relat_1 @ X5))),
% 18.46/18.65      inference('cnf', [status(esa)], [d5_funct_1])).
% 18.46/18.65  thf('72', plain,
% 18.46/18.65      (![X0 : $i]:
% 18.46/18.65         (((sk_A) = (k2_relat_1 @ sk_D_3))
% 18.46/18.65          | ~ (v1_relat_1 @ sk_D_3)
% 18.46/18.65          | ~ (v1_funct_1 @ sk_D_3)
% 18.46/18.65          | ((sk_A) = (k2_relat_1 @ sk_D_3))
% 18.46/18.65          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_3))
% 18.46/18.65          | ((sk_C @ sk_A @ sk_D_3) != (k1_funct_1 @ sk_D_3 @ X0)))),
% 18.46/18.65      inference('sup-', [status(thm)], ['70', '71'])).
% 18.46/18.65  thf('73', plain, ((v1_relat_1 @ sk_D_3)),
% 18.46/18.65      inference('demod', [status(thm)], ['47', '48'])).
% 18.46/18.65  thf('74', plain, ((v1_funct_1 @ sk_D_3)),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf('75', plain, (((sk_B) = (k1_relat_1 @ sk_D_3))),
% 18.46/18.65      inference('demod', [status(thm)], ['2', '9', '12'])).
% 18.46/18.65  thf('76', plain,
% 18.46/18.65      (![X0 : $i]:
% 18.46/18.65         (((sk_A) = (k2_relat_1 @ sk_D_3))
% 18.46/18.65          | ((sk_A) = (k2_relat_1 @ sk_D_3))
% 18.46/18.65          | ~ (r2_hidden @ X0 @ sk_B)
% 18.46/18.65          | ((sk_C @ sk_A @ sk_D_3) != (k1_funct_1 @ sk_D_3 @ X0)))),
% 18.46/18.65      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 18.46/18.65  thf('77', plain,
% 18.46/18.65      (![X0 : $i]:
% 18.46/18.65         (((sk_C @ sk_A @ sk_D_3) != (k1_funct_1 @ sk_D_3 @ X0))
% 18.46/18.65          | ~ (r2_hidden @ X0 @ sk_B)
% 18.46/18.65          | ((sk_A) = (k2_relat_1 @ sk_D_3)))),
% 18.46/18.65      inference('simplify', [status(thm)], ['76'])).
% 18.46/18.65  thf('78', plain,
% 18.46/18.65      ((((sk_C @ sk_A @ sk_D_3) != (sk_C @ sk_A @ sk_D_3))
% 18.46/18.65        | ((sk_A) = (k2_relat_1 @ sk_D_3))
% 18.46/18.65        | ((sk_A) = (k2_relat_1 @ sk_D_3))
% 18.46/18.65        | ~ (r2_hidden @ (k1_funct_1 @ sk_C_2 @ (sk_C @ sk_A @ sk_D_3)) @ sk_B))),
% 18.46/18.65      inference('sup-', [status(thm)], ['69', '77'])).
% 18.46/18.65  thf('79', plain,
% 18.46/18.65      ((~ (r2_hidden @ (k1_funct_1 @ sk_C_2 @ (sk_C @ sk_A @ sk_D_3)) @ sk_B)
% 18.46/18.65        | ((sk_A) = (k2_relat_1 @ sk_D_3)))),
% 18.46/18.65      inference('simplify', [status(thm)], ['78'])).
% 18.46/18.65  thf('80', plain,
% 18.46/18.65      (((r2_hidden @ (sk_C @ sk_A @ sk_D_3) @ sk_A)
% 18.46/18.65        | ((sk_A) = (k2_relat_1 @ sk_D_3)))),
% 18.46/18.65      inference('eq_fact', [status(thm)], ['65'])).
% 18.46/18.65  thf('81', plain,
% 18.46/18.65      (![X28 : $i, X29 : $i]:
% 18.46/18.65         ((r2_hidden @ X28 @ sk_B)
% 18.46/18.65          | ((k1_funct_1 @ sk_C_2 @ X29) != (X28))
% 18.46/18.65          | ~ (r2_hidden @ X29 @ sk_A))),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf('82', plain,
% 18.46/18.65      (![X29 : $i]:
% 18.46/18.65         (~ (r2_hidden @ X29 @ sk_A)
% 18.46/18.65          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X29) @ sk_B))),
% 18.46/18.65      inference('simplify', [status(thm)], ['81'])).
% 18.46/18.65  thf('83', plain,
% 18.46/18.65      ((((sk_A) = (k2_relat_1 @ sk_D_3))
% 18.46/18.65        | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ (sk_C @ sk_A @ sk_D_3)) @ sk_B))),
% 18.46/18.65      inference('sup-', [status(thm)], ['80', '82'])).
% 18.46/18.65  thf('84', plain, (((sk_A) = (k2_relat_1 @ sk_D_3))),
% 18.46/18.65      inference('clc', [status(thm)], ['79', '83'])).
% 18.46/18.65  thf('85', plain,
% 18.46/18.65      ((((sk_B) != (sk_B))
% 18.46/18.65        | ((sk_D_3) = (k2_funct_1 @ sk_C_2))
% 18.46/18.65        | (r2_hidden @ (sk_C_1 @ sk_D_3 @ sk_C_2) @ sk_A)
% 18.46/18.65        | ((sk_A) != (sk_A)))),
% 18.46/18.65      inference('demod', [status(thm)], ['44', '49', '50', '84'])).
% 18.46/18.65  thf('86', plain,
% 18.46/18.65      (((r2_hidden @ (sk_C_1 @ sk_D_3 @ sk_C_2) @ sk_A)
% 18.46/18.65        | ((sk_D_3) = (k2_funct_1 @ sk_C_2)))),
% 18.46/18.65      inference('simplify', [status(thm)], ['85'])).
% 18.46/18.65  thf('87', plain, (((sk_D_3) != (k2_funct_1 @ sk_C_2))),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf('88', plain, ((r2_hidden @ (sk_C_1 @ sk_D_3 @ sk_C_2) @ sk_A)),
% 18.46/18.65      inference('simplify_reflect-', [status(thm)], ['86', '87'])).
% 18.46/18.65  thf('89', plain, (((sk_A) = (k2_relat_1 @ sk_D_3))),
% 18.46/18.65      inference('clc', [status(thm)], ['79', '83'])).
% 18.46/18.65  thf('90', plain,
% 18.46/18.65      (![X5 : $i, X7 : $i, X8 : $i]:
% 18.46/18.65         (((X7) != (k2_relat_1 @ X5))
% 18.46/18.65          | (r2_hidden @ (sk_D_1 @ X8 @ X5) @ (k1_relat_1 @ X5))
% 18.46/18.65          | ~ (r2_hidden @ X8 @ X7)
% 18.46/18.65          | ~ (v1_funct_1 @ X5)
% 18.46/18.65          | ~ (v1_relat_1 @ X5))),
% 18.46/18.65      inference('cnf', [status(esa)], [d5_funct_1])).
% 18.46/18.65  thf('91', plain,
% 18.46/18.65      (![X5 : $i, X8 : $i]:
% 18.46/18.65         (~ (v1_relat_1 @ X5)
% 18.46/18.65          | ~ (v1_funct_1 @ X5)
% 18.46/18.65          | ~ (r2_hidden @ X8 @ (k2_relat_1 @ X5))
% 18.46/18.65          | (r2_hidden @ (sk_D_1 @ X8 @ X5) @ (k1_relat_1 @ X5)))),
% 18.46/18.65      inference('simplify', [status(thm)], ['90'])).
% 18.46/18.65  thf('92', plain,
% 18.46/18.65      (![X0 : $i]:
% 18.46/18.65         (~ (r2_hidden @ X0 @ sk_A)
% 18.46/18.65          | (r2_hidden @ (sk_D_1 @ X0 @ sk_D_3) @ (k1_relat_1 @ sk_D_3))
% 18.46/18.65          | ~ (v1_funct_1 @ sk_D_3)
% 18.46/18.65          | ~ (v1_relat_1 @ sk_D_3))),
% 18.46/18.65      inference('sup-', [status(thm)], ['89', '91'])).
% 18.46/18.65  thf('93', plain, (((sk_B) = (k1_relat_1 @ sk_D_3))),
% 18.46/18.65      inference('demod', [status(thm)], ['2', '9', '12'])).
% 18.46/18.65  thf('94', plain, ((v1_funct_1 @ sk_D_3)),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf('95', plain, ((v1_relat_1 @ sk_D_3)),
% 18.46/18.65      inference('demod', [status(thm)], ['47', '48'])).
% 18.46/18.65  thf('96', plain,
% 18.46/18.65      (![X0 : $i]:
% 18.46/18.65         (~ (r2_hidden @ X0 @ sk_A)
% 18.46/18.65          | (r2_hidden @ (sk_D_1 @ X0 @ sk_D_3) @ sk_B))),
% 18.46/18.65      inference('demod', [status(thm)], ['92', '93', '94', '95'])).
% 18.46/18.65  thf('97', plain,
% 18.46/18.65      ((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_D_3 @ sk_C_2) @ sk_D_3) @ sk_B)),
% 18.46/18.65      inference('sup-', [status(thm)], ['88', '96'])).
% 18.46/18.65  thf('98', plain,
% 18.46/18.65      (![X27 : $i, X28 : $i]:
% 18.46/18.65         (((k1_funct_1 @ sk_C_2 @ X27) = (X28))
% 18.46/18.65          | ((k1_funct_1 @ sk_D_3 @ X28) != (X27))
% 18.46/18.65          | ~ (r2_hidden @ X28 @ sk_B))),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf('99', plain,
% 18.46/18.65      (![X28 : $i]:
% 18.46/18.65         (~ (r2_hidden @ X28 @ sk_B)
% 18.46/18.65          | ((k1_funct_1 @ sk_C_2 @ (k1_funct_1 @ sk_D_3 @ X28)) = (X28)))),
% 18.46/18.65      inference('simplify', [status(thm)], ['98'])).
% 18.46/18.65  thf('100', plain,
% 18.46/18.65      (((k1_funct_1 @ sk_C_2 @ 
% 18.46/18.65         (k1_funct_1 @ sk_D_3 @ (sk_D_1 @ (sk_C_1 @ sk_D_3 @ sk_C_2) @ sk_D_3)))
% 18.46/18.65         = (sk_D_1 @ (sk_C_1 @ sk_D_3 @ sk_C_2) @ sk_D_3))),
% 18.46/18.65      inference('sup-', [status(thm)], ['97', '99'])).
% 18.46/18.65  thf('101', plain, ((r2_hidden @ (sk_C_1 @ sk_D_3 @ sk_C_2) @ sk_A)),
% 18.46/18.65      inference('simplify_reflect-', [status(thm)], ['86', '87'])).
% 18.46/18.65  thf('102', plain, (((sk_A) = (k2_relat_1 @ sk_D_3))),
% 18.46/18.65      inference('clc', [status(thm)], ['79', '83'])).
% 18.46/18.65  thf('103', plain,
% 18.46/18.65      (![X5 : $i, X7 : $i, X8 : $i]:
% 18.46/18.65         (((X7) != (k2_relat_1 @ X5))
% 18.46/18.65          | ((X8) = (k1_funct_1 @ X5 @ (sk_D_1 @ X8 @ X5)))
% 18.46/18.65          | ~ (r2_hidden @ X8 @ X7)
% 18.46/18.65          | ~ (v1_funct_1 @ X5)
% 18.46/18.65          | ~ (v1_relat_1 @ X5))),
% 18.46/18.65      inference('cnf', [status(esa)], [d5_funct_1])).
% 18.46/18.65  thf('104', plain,
% 18.46/18.65      (![X5 : $i, X8 : $i]:
% 18.46/18.65         (~ (v1_relat_1 @ X5)
% 18.46/18.65          | ~ (v1_funct_1 @ X5)
% 18.46/18.65          | ~ (r2_hidden @ X8 @ (k2_relat_1 @ X5))
% 18.46/18.65          | ((X8) = (k1_funct_1 @ X5 @ (sk_D_1 @ X8 @ X5))))),
% 18.46/18.65      inference('simplify', [status(thm)], ['103'])).
% 18.46/18.65  thf('105', plain,
% 18.46/18.65      (![X0 : $i]:
% 18.46/18.65         (~ (r2_hidden @ X0 @ sk_A)
% 18.46/18.65          | ((X0) = (k1_funct_1 @ sk_D_3 @ (sk_D_1 @ X0 @ sk_D_3)))
% 18.46/18.65          | ~ (v1_funct_1 @ sk_D_3)
% 18.46/18.65          | ~ (v1_relat_1 @ sk_D_3))),
% 18.46/18.65      inference('sup-', [status(thm)], ['102', '104'])).
% 18.46/18.65  thf('106', plain, ((v1_funct_1 @ sk_D_3)),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf('107', plain, ((v1_relat_1 @ sk_D_3)),
% 18.46/18.65      inference('demod', [status(thm)], ['47', '48'])).
% 18.46/18.65  thf('108', plain,
% 18.46/18.65      (![X0 : $i]:
% 18.46/18.65         (~ (r2_hidden @ X0 @ sk_A)
% 18.46/18.65          | ((X0) = (k1_funct_1 @ sk_D_3 @ (sk_D_1 @ X0 @ sk_D_3))))),
% 18.46/18.65      inference('demod', [status(thm)], ['105', '106', '107'])).
% 18.46/18.65  thf('109', plain,
% 18.46/18.65      (((sk_C_1 @ sk_D_3 @ sk_C_2)
% 18.46/18.65         = (k1_funct_1 @ sk_D_3 @ 
% 18.46/18.65            (sk_D_1 @ (sk_C_1 @ sk_D_3 @ sk_C_2) @ sk_D_3)))),
% 18.46/18.65      inference('sup-', [status(thm)], ['101', '108'])).
% 18.46/18.65  thf('110', plain,
% 18.46/18.65      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D_3 @ sk_C_2))
% 18.46/18.65         = (sk_D_1 @ (sk_C_1 @ sk_D_3 @ sk_C_2) @ sk_D_3))),
% 18.46/18.65      inference('demod', [status(thm)], ['100', '109'])).
% 18.46/18.65  thf('111', plain, (((k2_relat_1 @ sk_C_2) = (sk_B))),
% 18.46/18.65      inference('sup+', [status(thm)], ['16', '17'])).
% 18.46/18.65  thf('112', plain, (((sk_B) = (k1_relat_1 @ sk_D_3))),
% 18.46/18.65      inference('demod', [status(thm)], ['2', '9', '12'])).
% 18.46/18.65  thf('113', plain,
% 18.46/18.65      (![X11 : $i, X12 : $i]:
% 18.46/18.65         (~ (v1_relat_1 @ X11)
% 18.46/18.65          | ~ (v1_funct_1 @ X11)
% 18.46/18.65          | ((X11) = (k2_funct_1 @ X12))
% 18.46/18.65          | (r2_hidden @ (sk_D_2 @ X11 @ X12) @ (k1_relat_1 @ X11))
% 18.46/18.65          | ((k2_relat_1 @ X12) != (k1_relat_1 @ X11))
% 18.46/18.65          | ((k1_relat_1 @ X12) != (k2_relat_1 @ X11))
% 18.46/18.65          | ~ (v2_funct_1 @ X12)
% 18.46/18.65          | ~ (v1_funct_1 @ X12)
% 18.46/18.65          | ~ (v1_relat_1 @ X12))),
% 18.46/18.65      inference('cnf', [status(esa)], [t60_funct_1])).
% 18.46/18.65  thf('114', plain,
% 18.46/18.65      (![X0 : $i]:
% 18.46/18.65         (((k2_relat_1 @ X0) != (sk_B))
% 18.46/18.65          | ~ (v1_relat_1 @ X0)
% 18.46/18.65          | ~ (v1_funct_1 @ X0)
% 18.46/18.65          | ~ (v2_funct_1 @ X0)
% 18.46/18.65          | ((k1_relat_1 @ X0) != (k2_relat_1 @ sk_D_3))
% 18.46/18.65          | (r2_hidden @ (sk_D_2 @ sk_D_3 @ X0) @ (k1_relat_1 @ sk_D_3))
% 18.46/18.65          | ((sk_D_3) = (k2_funct_1 @ X0))
% 18.46/18.65          | ~ (v1_funct_1 @ sk_D_3)
% 18.46/18.65          | ~ (v1_relat_1 @ sk_D_3))),
% 18.46/18.65      inference('sup-', [status(thm)], ['112', '113'])).
% 18.46/18.65  thf('115', plain, (((sk_A) = (k2_relat_1 @ sk_D_3))),
% 18.46/18.65      inference('clc', [status(thm)], ['79', '83'])).
% 18.46/18.65  thf('116', plain, (((sk_B) = (k1_relat_1 @ sk_D_3))),
% 18.46/18.65      inference('demod', [status(thm)], ['2', '9', '12'])).
% 18.46/18.65  thf('117', plain, ((v1_funct_1 @ sk_D_3)),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf('118', plain, ((v1_relat_1 @ sk_D_3)),
% 18.46/18.65      inference('demod', [status(thm)], ['47', '48'])).
% 18.46/18.65  thf('119', plain,
% 18.46/18.65      (![X0 : $i]:
% 18.46/18.65         (((k2_relat_1 @ X0) != (sk_B))
% 18.46/18.65          | ~ (v1_relat_1 @ X0)
% 18.46/18.65          | ~ (v1_funct_1 @ X0)
% 18.46/18.65          | ~ (v2_funct_1 @ X0)
% 18.46/18.65          | ((k1_relat_1 @ X0) != (sk_A))
% 18.46/18.65          | (r2_hidden @ (sk_D_2 @ sk_D_3 @ X0) @ sk_B)
% 18.46/18.65          | ((sk_D_3) = (k2_funct_1 @ X0)))),
% 18.46/18.65      inference('demod', [status(thm)], ['114', '115', '116', '117', '118'])).
% 18.46/18.65  thf('120', plain,
% 18.46/18.65      ((((sk_B) != (sk_B))
% 18.46/18.65        | ((sk_D_3) = (k2_funct_1 @ sk_C_2))
% 18.46/18.65        | (r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_C_2) @ sk_B)
% 18.46/18.65        | ((k1_relat_1 @ sk_C_2) != (sk_A))
% 18.46/18.65        | ~ (v2_funct_1 @ sk_C_2)
% 18.46/18.65        | ~ (v1_funct_1 @ sk_C_2)
% 18.46/18.65        | ~ (v1_relat_1 @ sk_C_2))),
% 18.46/18.65      inference('sup-', [status(thm)], ['111', '119'])).
% 18.46/18.65  thf('121', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 18.46/18.65      inference('demod', [status(thm)], ['30', '37', '40'])).
% 18.46/18.65  thf('122', plain, ((v2_funct_1 @ sk_C_2)),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf('123', plain, ((v1_funct_1 @ sk_C_2)),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf('124', plain, ((v1_relat_1 @ sk_C_2)),
% 18.46/18.65      inference('demod', [status(thm)], ['23', '24'])).
% 18.46/18.65  thf('125', plain,
% 18.46/18.65      ((((sk_B) != (sk_B))
% 18.46/18.65        | ((sk_D_3) = (k2_funct_1 @ sk_C_2))
% 18.46/18.65        | (r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_C_2) @ sk_B)
% 18.46/18.65        | ((sk_A) != (sk_A)))),
% 18.46/18.65      inference('demod', [status(thm)], ['120', '121', '122', '123', '124'])).
% 18.46/18.65  thf('126', plain,
% 18.46/18.65      (((r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_C_2) @ sk_B)
% 18.46/18.65        | ((sk_D_3) = (k2_funct_1 @ sk_C_2)))),
% 18.46/18.65      inference('simplify', [status(thm)], ['125'])).
% 18.46/18.65  thf('127', plain, (((sk_D_3) != (k2_funct_1 @ sk_C_2))),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf('128', plain, ((r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_C_2) @ sk_B)),
% 18.46/18.65      inference('simplify_reflect-', [status(thm)], ['126', '127'])).
% 18.46/18.65  thf('129', plain,
% 18.46/18.65      (![X28 : $i]:
% 18.46/18.65         (~ (r2_hidden @ X28 @ sk_B)
% 18.46/18.65          | ((k1_funct_1 @ sk_C_2 @ (k1_funct_1 @ sk_D_3 @ X28)) = (X28)))),
% 18.46/18.65      inference('simplify', [status(thm)], ['98'])).
% 18.46/18.65  thf('130', plain,
% 18.46/18.65      (((k1_funct_1 @ sk_C_2 @ 
% 18.46/18.65         (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ sk_C_2)))
% 18.46/18.65         = (sk_D_2 @ sk_D_3 @ sk_C_2))),
% 18.46/18.65      inference('sup-', [status(thm)], ['128', '129'])).
% 18.46/18.65  thf('131', plain, (((sk_B) = (k1_relat_1 @ sk_D_3))),
% 18.46/18.65      inference('demod', [status(thm)], ['2', '9', '12'])).
% 18.46/18.65  thf('132', plain, (((k2_relat_1 @ sk_C_2) = (sk_B))),
% 18.46/18.65      inference('sup+', [status(thm)], ['16', '17'])).
% 18.46/18.65  thf('133', plain,
% 18.46/18.65      (![X11 : $i, X12 : $i]:
% 18.46/18.65         (~ (v1_relat_1 @ X11)
% 18.46/18.65          | ~ (v1_funct_1 @ X11)
% 18.46/18.65          | ((X11) = (k2_funct_1 @ X12))
% 18.46/18.65          | ((k1_funct_1 @ X12 @ (sk_C_1 @ X11 @ X12)) = (sk_D_2 @ X11 @ X12))
% 18.46/18.65          | ((k1_funct_1 @ X11 @ (sk_D_2 @ X11 @ X12)) = (sk_C_1 @ X11 @ X12))
% 18.46/18.65          | ((k2_relat_1 @ X12) != (k1_relat_1 @ X11))
% 18.46/18.65          | ((k1_relat_1 @ X12) != (k2_relat_1 @ X11))
% 18.46/18.65          | ~ (v2_funct_1 @ X12)
% 18.46/18.65          | ~ (v1_funct_1 @ X12)
% 18.46/18.65          | ~ (v1_relat_1 @ X12))),
% 18.46/18.65      inference('cnf', [status(esa)], [t60_funct_1])).
% 18.46/18.65  thf('134', plain,
% 18.46/18.65      (![X0 : $i]:
% 18.46/18.65         (((sk_B) != (k1_relat_1 @ X0))
% 18.46/18.65          | ~ (v1_relat_1 @ sk_C_2)
% 18.46/18.65          | ~ (v1_funct_1 @ sk_C_2)
% 18.46/18.65          | ~ (v2_funct_1 @ sk_C_2)
% 18.46/18.65          | ((k1_relat_1 @ sk_C_2) != (k2_relat_1 @ X0))
% 18.46/18.65          | ((k1_funct_1 @ X0 @ (sk_D_2 @ X0 @ sk_C_2))
% 18.46/18.65              = (sk_C_1 @ X0 @ sk_C_2))
% 18.46/18.65          | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ X0 @ sk_C_2))
% 18.46/18.65              = (sk_D_2 @ X0 @ sk_C_2))
% 18.46/18.65          | ((X0) = (k2_funct_1 @ sk_C_2))
% 18.46/18.65          | ~ (v1_funct_1 @ X0)
% 18.46/18.65          | ~ (v1_relat_1 @ X0))),
% 18.46/18.65      inference('sup-', [status(thm)], ['132', '133'])).
% 18.46/18.65  thf('135', plain, ((v1_relat_1 @ sk_C_2)),
% 18.46/18.65      inference('demod', [status(thm)], ['23', '24'])).
% 18.46/18.65  thf('136', plain, ((v1_funct_1 @ sk_C_2)),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf('137', plain, ((v2_funct_1 @ sk_C_2)),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf('138', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 18.46/18.65      inference('demod', [status(thm)], ['30', '37', '40'])).
% 18.46/18.65  thf('139', plain,
% 18.46/18.65      (![X0 : $i]:
% 18.46/18.65         (((sk_B) != (k1_relat_1 @ X0))
% 18.46/18.65          | ((sk_A) != (k2_relat_1 @ X0))
% 18.46/18.65          | ((k1_funct_1 @ X0 @ (sk_D_2 @ X0 @ sk_C_2))
% 18.46/18.65              = (sk_C_1 @ X0 @ sk_C_2))
% 18.46/18.65          | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ X0 @ sk_C_2))
% 18.46/18.65              = (sk_D_2 @ X0 @ sk_C_2))
% 18.46/18.65          | ((X0) = (k2_funct_1 @ sk_C_2))
% 18.46/18.65          | ~ (v1_funct_1 @ X0)
% 18.46/18.65          | ~ (v1_relat_1 @ X0))),
% 18.46/18.65      inference('demod', [status(thm)], ['134', '135', '136', '137', '138'])).
% 18.46/18.65  thf('140', plain,
% 18.46/18.65      ((((sk_B) != (sk_B))
% 18.46/18.65        | ~ (v1_relat_1 @ sk_D_3)
% 18.46/18.65        | ~ (v1_funct_1 @ sk_D_3)
% 18.46/18.65        | ((sk_D_3) = (k2_funct_1 @ sk_C_2))
% 18.46/18.65        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D_3 @ sk_C_2))
% 18.46/18.65            = (sk_D_2 @ sk_D_3 @ sk_C_2))
% 18.46/18.65        | ((k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ sk_C_2))
% 18.46/18.65            = (sk_C_1 @ sk_D_3 @ sk_C_2))
% 18.46/18.65        | ((sk_A) != (k2_relat_1 @ sk_D_3)))),
% 18.46/18.65      inference('sup-', [status(thm)], ['131', '139'])).
% 18.46/18.65  thf('141', plain, ((v1_relat_1 @ sk_D_3)),
% 18.46/18.65      inference('demod', [status(thm)], ['47', '48'])).
% 18.46/18.65  thf('142', plain, ((v1_funct_1 @ sk_D_3)),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf('143', plain,
% 18.46/18.65      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D_3 @ sk_C_2))
% 18.46/18.65         = (sk_D_1 @ (sk_C_1 @ sk_D_3 @ sk_C_2) @ sk_D_3))),
% 18.46/18.65      inference('demod', [status(thm)], ['100', '109'])).
% 18.46/18.65  thf('144', plain, (((sk_A) = (k2_relat_1 @ sk_D_3))),
% 18.46/18.65      inference('clc', [status(thm)], ['79', '83'])).
% 18.46/18.65  thf('145', plain,
% 18.46/18.65      ((((sk_B) != (sk_B))
% 18.46/18.65        | ((sk_D_3) = (k2_funct_1 @ sk_C_2))
% 18.46/18.65        | ((sk_D_1 @ (sk_C_1 @ sk_D_3 @ sk_C_2) @ sk_D_3)
% 18.46/18.65            = (sk_D_2 @ sk_D_3 @ sk_C_2))
% 18.46/18.65        | ((k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ sk_C_2))
% 18.46/18.65            = (sk_C_1 @ sk_D_3 @ sk_C_2))
% 18.46/18.65        | ((sk_A) != (sk_A)))),
% 18.46/18.65      inference('demod', [status(thm)], ['140', '141', '142', '143', '144'])).
% 18.46/18.65  thf('146', plain,
% 18.46/18.65      ((((k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ sk_C_2))
% 18.46/18.65          = (sk_C_1 @ sk_D_3 @ sk_C_2))
% 18.46/18.65        | ((sk_D_1 @ (sk_C_1 @ sk_D_3 @ sk_C_2) @ sk_D_3)
% 18.46/18.65            = (sk_D_2 @ sk_D_3 @ sk_C_2))
% 18.46/18.65        | ((sk_D_3) = (k2_funct_1 @ sk_C_2)))),
% 18.46/18.65      inference('simplify', [status(thm)], ['145'])).
% 18.46/18.65  thf('147', plain, (((sk_D_3) != (k2_funct_1 @ sk_C_2))),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf('148', plain,
% 18.46/18.65      ((((k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ sk_C_2))
% 18.46/18.65          = (sk_C_1 @ sk_D_3 @ sk_C_2))
% 18.46/18.65        | ((sk_D_1 @ (sk_C_1 @ sk_D_3 @ sk_C_2) @ sk_D_3)
% 18.46/18.65            = (sk_D_2 @ sk_D_3 @ sk_C_2)))),
% 18.46/18.65      inference('simplify_reflect-', [status(thm)], ['146', '147'])).
% 18.46/18.65  thf('149', plain,
% 18.46/18.65      (((sk_C_1 @ sk_D_3 @ sk_C_2)
% 18.46/18.65         = (k1_funct_1 @ sk_D_3 @ 
% 18.46/18.65            (sk_D_1 @ (sk_C_1 @ sk_D_3 @ sk_C_2) @ sk_D_3)))),
% 18.46/18.65      inference('sup-', [status(thm)], ['101', '108'])).
% 18.46/18.65  thf('150', plain,
% 18.46/18.65      ((((sk_C_1 @ sk_D_3 @ sk_C_2)
% 18.46/18.65          = (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ sk_C_2)))
% 18.46/18.65        | ((k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ sk_C_2))
% 18.46/18.65            = (sk_C_1 @ sk_D_3 @ sk_C_2)))),
% 18.46/18.65      inference('sup+', [status(thm)], ['148', '149'])).
% 18.46/18.65  thf('151', plain,
% 18.46/18.65      (((sk_C_1 @ sk_D_3 @ sk_C_2)
% 18.46/18.65         = (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ sk_C_2)))),
% 18.46/18.65      inference('simplify', [status(thm)], ['150'])).
% 18.46/18.65  thf('152', plain,
% 18.46/18.65      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D_3 @ sk_C_2))
% 18.46/18.65         = (sk_D_2 @ sk_D_3 @ sk_C_2))),
% 18.46/18.65      inference('demod', [status(thm)], ['130', '151'])).
% 18.46/18.65  thf('153', plain,
% 18.46/18.65      (((sk_D_1 @ (sk_C_1 @ sk_D_3 @ sk_C_2) @ sk_D_3)
% 18.46/18.65         = (sk_D_2 @ sk_D_3 @ sk_C_2))),
% 18.46/18.65      inference('sup+', [status(thm)], ['110', '152'])).
% 18.46/18.65  thf('154', plain,
% 18.46/18.65      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D_3 @ sk_C_2))
% 18.46/18.65         = (sk_D_1 @ (sk_C_1 @ sk_D_3 @ sk_C_2) @ sk_D_3))),
% 18.46/18.65      inference('demod', [status(thm)], ['100', '109'])).
% 18.46/18.65  thf('155', plain,
% 18.46/18.65      (![X11 : $i, X12 : $i]:
% 18.46/18.65         (~ (v1_relat_1 @ X11)
% 18.46/18.65          | ~ (v1_funct_1 @ X11)
% 18.46/18.65          | ((X11) = (k2_funct_1 @ X12))
% 18.46/18.65          | ((k1_funct_1 @ X12 @ (sk_C_1 @ X11 @ X12)) != (sk_D_2 @ X11 @ X12))
% 18.46/18.65          | ((k1_funct_1 @ X11 @ (sk_D_2 @ X11 @ X12)) != (sk_C_1 @ X11 @ X12))
% 18.46/18.65          | ((k2_relat_1 @ X12) != (k1_relat_1 @ X11))
% 18.46/18.65          | ((k1_relat_1 @ X12) != (k2_relat_1 @ X11))
% 18.46/18.65          | ~ (v2_funct_1 @ X12)
% 18.46/18.65          | ~ (v1_funct_1 @ X12)
% 18.46/18.65          | ~ (v1_relat_1 @ X12))),
% 18.46/18.65      inference('cnf', [status(esa)], [t60_funct_1])).
% 18.46/18.65  thf('156', plain,
% 18.46/18.65      ((((sk_D_1 @ (sk_C_1 @ sk_D_3 @ sk_C_2) @ sk_D_3)
% 18.46/18.65          != (sk_D_2 @ sk_D_3 @ sk_C_2))
% 18.46/18.65        | ~ (v1_relat_1 @ sk_C_2)
% 18.46/18.65        | ~ (v1_funct_1 @ sk_C_2)
% 18.46/18.65        | ~ (v2_funct_1 @ sk_C_2)
% 18.46/18.65        | ((k1_relat_1 @ sk_C_2) != (k2_relat_1 @ sk_D_3))
% 18.46/18.65        | ((k2_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D_3))
% 18.46/18.65        | ((k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ sk_C_2))
% 18.46/18.65            != (sk_C_1 @ sk_D_3 @ sk_C_2))
% 18.46/18.65        | ((sk_D_3) = (k2_funct_1 @ sk_C_2))
% 18.46/18.65        | ~ (v1_funct_1 @ sk_D_3)
% 18.46/18.65        | ~ (v1_relat_1 @ sk_D_3))),
% 18.46/18.65      inference('sup-', [status(thm)], ['154', '155'])).
% 18.46/18.65  thf('157', plain, ((v1_relat_1 @ sk_C_2)),
% 18.46/18.65      inference('demod', [status(thm)], ['23', '24'])).
% 18.46/18.65  thf('158', plain, ((v1_funct_1 @ sk_C_2)),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf('159', plain, ((v2_funct_1 @ sk_C_2)),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf('160', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 18.46/18.65      inference('demod', [status(thm)], ['30', '37', '40'])).
% 18.46/18.65  thf('161', plain, (((sk_A) = (k2_relat_1 @ sk_D_3))),
% 18.46/18.65      inference('clc', [status(thm)], ['79', '83'])).
% 18.46/18.65  thf('162', plain, (((k2_relat_1 @ sk_C_2) = (sk_B))),
% 18.46/18.65      inference('sup+', [status(thm)], ['16', '17'])).
% 18.46/18.65  thf('163', plain, (((sk_B) = (k1_relat_1 @ sk_D_3))),
% 18.46/18.65      inference('demod', [status(thm)], ['2', '9', '12'])).
% 18.46/18.65  thf('164', plain, ((v1_funct_1 @ sk_D_3)),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf('165', plain, ((v1_relat_1 @ sk_D_3)),
% 18.46/18.65      inference('demod', [status(thm)], ['47', '48'])).
% 18.46/18.65  thf('166', plain,
% 18.46/18.65      ((((sk_D_1 @ (sk_C_1 @ sk_D_3 @ sk_C_2) @ sk_D_3)
% 18.46/18.65          != (sk_D_2 @ sk_D_3 @ sk_C_2))
% 18.46/18.65        | ((sk_A) != (sk_A))
% 18.46/18.65        | ((sk_B) != (sk_B))
% 18.46/18.65        | ((k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ sk_C_2))
% 18.46/18.65            != (sk_C_1 @ sk_D_3 @ sk_C_2))
% 18.46/18.65        | ((sk_D_3) = (k2_funct_1 @ sk_C_2)))),
% 18.46/18.65      inference('demod', [status(thm)],
% 18.46/18.65                ['156', '157', '158', '159', '160', '161', '162', '163', 
% 18.46/18.65                 '164', '165'])).
% 18.46/18.65  thf('167', plain,
% 18.46/18.65      ((((sk_D_3) = (k2_funct_1 @ sk_C_2))
% 18.46/18.65        | ((k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ sk_C_2))
% 18.46/18.65            != (sk_C_1 @ sk_D_3 @ sk_C_2))
% 18.46/18.65        | ((sk_D_1 @ (sk_C_1 @ sk_D_3 @ sk_C_2) @ sk_D_3)
% 18.46/18.65            != (sk_D_2 @ sk_D_3 @ sk_C_2)))),
% 18.46/18.65      inference('simplify', [status(thm)], ['166'])).
% 18.46/18.65  thf('168', plain, (((sk_D_3) != (k2_funct_1 @ sk_C_2))),
% 18.46/18.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.46/18.65  thf('169', plain,
% 18.46/18.65      ((((k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ sk_C_2))
% 18.46/18.65          != (sk_C_1 @ sk_D_3 @ sk_C_2))
% 18.46/18.65        | ((sk_D_1 @ (sk_C_1 @ sk_D_3 @ sk_C_2) @ sk_D_3)
% 18.46/18.65            != (sk_D_2 @ sk_D_3 @ sk_C_2)))),
% 18.46/18.65      inference('simplify_reflect-', [status(thm)], ['167', '168'])).
% 18.46/18.65  thf('170', plain,
% 18.46/18.65      (((sk_C_1 @ sk_D_3 @ sk_C_2)
% 18.46/18.65         = (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ sk_C_2)))),
% 18.46/18.65      inference('simplify', [status(thm)], ['150'])).
% 18.46/18.65  thf('171', plain,
% 18.46/18.65      ((((sk_C_1 @ sk_D_3 @ sk_C_2) != (sk_C_1 @ sk_D_3 @ sk_C_2))
% 18.46/18.65        | ((sk_D_1 @ (sk_C_1 @ sk_D_3 @ sk_C_2) @ sk_D_3)
% 18.46/18.65            != (sk_D_2 @ sk_D_3 @ sk_C_2)))),
% 18.46/18.65      inference('demod', [status(thm)], ['169', '170'])).
% 18.46/18.65  thf('172', plain,
% 18.46/18.65      (((sk_D_1 @ (sk_C_1 @ sk_D_3 @ sk_C_2) @ sk_D_3)
% 18.46/18.65         != (sk_D_2 @ sk_D_3 @ sk_C_2))),
% 18.46/18.65      inference('simplify', [status(thm)], ['171'])).
% 18.46/18.65  thf('173', plain, ($false),
% 18.46/18.65      inference('simplify_reflect-', [status(thm)], ['153', '172'])).
% 18.46/18.65  
% 18.46/18.65  % SZS output end Refutation
% 18.46/18.65  
% 18.46/18.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
