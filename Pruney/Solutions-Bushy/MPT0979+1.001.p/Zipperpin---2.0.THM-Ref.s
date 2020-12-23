%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0979+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MBOwOfRIEa

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:49 EST 2020

% Result     : Theorem 1.80s
% Output     : Refutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :  207 (2458 expanded)
%              Number of leaves         :   35 ( 643 expanded)
%              Depth                    :   25
%              Number of atoms          : 1980 (39222 expanded)
%              Number of equality atoms :  217 (4131 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t25_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ C @ A @ B )
        & ( v1_funct_1 @ C ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( v2_funct_1 @ C )
        <=> ! [D: $i,E: $i] :
              ( ( ( ( k1_funct_1 @ C @ D )
                  = ( k1_funct_1 @ C @ E ) )
                & ( r2_hidden @ E @ A )
                & ( r2_hidden @ D @ A ) )
             => ( D = E ) ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_2 @ E @ D @ C @ A )
    <=> ( ( r2_hidden @ D @ A )
        & ( r2_hidden @ E @ A )
        & ( ( k1_funct_1 @ C @ D )
          = ( k1_funct_1 @ C @ E ) ) ) ) )).

thf(zf_stmt_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( v2_funct_1 @ C )
        <=> ! [D: $i,E: $i] :
              ( ( zip_tseitin_2 @ E @ D @ C @ A )
             => ( D = E ) ) ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v2_funct_1 @ C )
          <=> ! [D: $i,E: $i] :
                ( ( zip_tseitin_2 @ E @ D @ C @ A )
               => ( D = E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[zf_stmt_2])).

thf('0',plain,
    ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('1',plain,
    ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
   <= ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_funct_1 @ X20 @ X17 )
        = ( k1_funct_1 @ X20 @ X19 ) )
      | ~ ( zip_tseitin_2 @ X19 @ X17 @ X20 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_D )
      = ( k1_funct_1 @ sk_C_1 @ sk_E ) )
   <= ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_D != sk_E )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,
    ( ( sk_D != sk_E )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('7',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

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

thf(zf_stmt_4,axiom,(
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
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('10',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('13',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('17',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('18',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(zf_stmt_5,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( zip_tseitin_0 @ X8 @ X9 )
      | ( zip_tseitin_1 @ X10 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('20',plain,
    ( ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('22',plain,(
    ! [X3: $i] :
      ( zip_tseitin_0 @ X3 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','22'])).

thf('24',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('25',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','23','24'])).

thf(d8_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
      <=> ! [B: $i,C: $i] :
            ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
              & ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
              & ( ( k1_funct_1 @ A @ B )
                = ( k1_funct_1 @ A @ C ) ) )
           => ( B = C ) ) ) ) )).

thf('26',plain,(
    ! [X11: $i] :
      ( ( r2_hidden @ ( sk_C @ X11 ) @ ( k1_relat_1 @ X11 ) )
      | ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('27',plain,(
    ! [X11: $i] :
      ( ( r2_hidden @ ( sk_B @ X11 ) @ ( k1_relat_1 @ X11 ) )
      | ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('28',plain,(
    ! [X11: $i] :
      ( ( ( k1_funct_1 @ X11 @ ( sk_B @ X11 ) )
        = ( k1_funct_1 @ X11 @ ( sk_C @ X11 ) ) )
      | ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('29',plain,(
    ! [X17: $i,X19: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_2 @ X19 @ X17 @ X20 @ X21 )
      | ( ( k1_funct_1 @ X20 @ X17 )
       != ( k1_funct_1 @ X20 @ X19 ) )
      | ~ ( r2_hidden @ X19 @ X21 )
      | ~ ( r2_hidden @ X17 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) )
       != ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ( zip_tseitin_2 @ X1 @ ( sk_C @ X0 ) @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_2 @ ( sk_B @ X1 ) @ ( sk_C @ X1 ) @ X1 @ X0 )
      | ~ ( r2_hidden @ ( sk_B @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X1 ) @ X0 )
      | ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(eq_res,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( zip_tseitin_2 @ ( sk_B @ X0 ) @ ( sk_C @ X0 ) @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ ( sk_B @ X0 ) @ ( sk_C @ X0 ) @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ( zip_tseitin_2 @ ( sk_B @ X0 ) @ ( sk_C @ X0 ) @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ ( sk_B @ X0 ) @ ( sk_C @ X0 ) @ X0 @ ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( ( zip_tseitin_2 @ ( sk_B @ sk_C_1 ) @ ( sk_C @ sk_C_1 ) @ sk_C_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( v2_funct_1 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('39',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,
    ( ( ( zip_tseitin_2 @ ( sk_B @ sk_C_1 ) @ ( sk_C @ sk_C_1 ) @ sk_C_1 @ k1_xboole_0 )
      | ( v2_funct_1 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','39','40'])).

thf('42',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('43',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A )
      | ( X23 = X22 )
      | ( v2_funct_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('44',plain,
    ( ! [X22: $i,X23: $i] :
        ( ( X23 = X22 )
        | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) )
   <= ! [X22: $i,X23: $i] :
        ( ( X23 = X22 )
        | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['43'])).

thf('45',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_2 @ X1 @ X0 @ sk_C_1 @ k1_xboole_0 )
        | ( X0 = X1 ) )
   <= ( ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,
    ( ( ( v2_funct_1 @ sk_C_1 )
      | ( ( sk_C @ sk_C_1 )
        = ( sk_B @ sk_C_1 ) ) )
   <= ( ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','45'])).

thf('47',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('48',plain,
    ( ( ( sk_C @ sk_C_1 )
      = ( sk_B @ sk_C_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_C_1 )
      & ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X11: $i] :
      ( ( ( sk_B @ X11 )
       != ( sk_C @ X11 ) )
      | ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('50',plain,
    ( ( ( ( sk_B @ sk_C_1 )
       != ( sk_B @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( v2_funct_1 @ sk_C_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_C_1 )
      & ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('52',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('53',plain,
    ( ( ( ( sk_B @ sk_C_1 )
       != ( sk_B @ sk_C_1 ) )
      | ( v2_funct_1 @ sk_C_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_C_1 )
      & ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( v2_funct_1 @ sk_C_1 )
   <= ( ~ ( v2_funct_1 @ sk_C_1 )
      & ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('56',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( v2_funct_1 @ sk_C_1 )
    | ~ ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
   <= ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,
    ( ! [X22: $i,X23: $i] :
        ( ( X23 = X22 )
        | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) )
   <= ! [X22: $i,X23: $i] :
        ( ( X23 = X22 )
        | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['43'])).

thf('59',plain,
    ( ( sk_D = sk_E )
   <= ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( sk_D != sk_E )
   <= ( sk_D != sk_E ) ),
    inference(split,[status(esa)],['4'])).

thf('61',plain,
    ( ( sk_D != sk_D )
   <= ( ( sk_D != sk_E )
      & ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) )
    | ( sk_D = sk_E )
    | ~ ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_D )
      = ( k1_funct_1 @ sk_C_1 @ sk_E ) )
   <= ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('64',plain,
    ( ( v2_funct_1 @ sk_C_1 )
   <= ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['43'])).

thf('65',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','23','24'])).

thf('66',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X11 ) )
      | ( ( k1_funct_1 @ X11 @ X12 )
       != ( k1_funct_1 @ X11 @ X13 ) )
      | ( X12 = X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('67',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
        | ~ ( v1_relat_1 @ sk_C_1 )
        | ~ ( v1_funct_1 @ sk_C_1 )
        | ( X0 = X1 )
        | ( ( k1_funct_1 @ sk_C_1 @ X0 )
         != ( k1_funct_1 @ sk_C_1 @ X1 ) )
        | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_1 ) )
        | ~ ( v2_funct_1 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('69',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('70',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','23','24'])).

thf('71',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
        | ( X0 = X1 )
        | ( ( k1_funct_1 @ sk_C_1 @ X0 )
         != ( k1_funct_1 @ sk_C_1 @ X1 ) )
        | ~ ( r2_hidden @ X1 @ k1_xboole_0 )
        | ~ ( v2_funct_1 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('72',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
        | ( ( k1_funct_1 @ sk_C_1 @ X1 )
         != ( k1_funct_1 @ sk_C_1 @ X0 ) )
        | ( X1 = X0 )
        | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) )
   <= ( ( v2_funct_1 @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','71'])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_C_1 @ sk_D )
         != ( k1_funct_1 @ sk_C_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_E @ k1_xboole_0 )
        | ( sk_E = X0 )
        | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) )
   <= ( ( v2_funct_1 @ sk_C_1 )
      & ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','72'])).

thf('74',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('75',plain,
    ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
   <= ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('76',plain,
    ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ k1_xboole_0 )
   <= ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ X18 )
      | ~ ( zip_tseitin_2 @ X19 @ X17 @ X20 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('78',plain,
    ( ( r2_hidden @ sk_E @ k1_xboole_0 )
   <= ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_C_1 @ sk_D )
         != ( k1_funct_1 @ sk_C_1 @ X0 ) )
        | ( sk_E = X0 )
        | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) )
   <= ( ( v2_funct_1 @ sk_C_1 )
      & ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['73','78'])).

thf('80',plain,
    ( ( ~ ( r2_hidden @ sk_D @ k1_xboole_0 )
      | ( sk_E = sk_D ) )
   <= ( ( v2_funct_1 @ sk_C_1 )
      & ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(eq_res,[status(thm)],['79'])).

thf('81',plain,
    ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ k1_xboole_0 )
   <= ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('82',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ~ ( zip_tseitin_2 @ X19 @ X17 @ X20 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('83',plain,
    ( ( r2_hidden @ sk_D @ k1_xboole_0 )
   <= ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( sk_E = sk_D )
   <= ( ( v2_funct_1 @ sk_C_1 )
      & ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['80','83'])).

thf('85',plain,
    ( ( sk_D != sk_E )
   <= ( sk_D != sk_E ) ),
    inference(split,[status(esa)],['4'])).

thf('86',plain,
    ( ( sk_D != sk_D )
   <= ( ( sk_D != sk_E )
      & ( v2_funct_1 @ sk_C_1 )
      & ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
    | ( sk_D = sk_E ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('89',plain,
    ( ( v2_funct_1 @ sk_C_1 )
    | ! [X22: $i,X23: $i] :
        ( ( X23 = X22 )
        | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['43'])).

thf('90',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('91',plain,(
    ! [X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('92',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('93',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( zip_tseitin_0 @ X8 @ X9 )
      | ( zip_tseitin_1 @ X10 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('94',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('97',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['90','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ ( sk_B @ X0 ) @ ( sk_C @ X0 ) @ X0 @ ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('100',plain,
    ( ( zip_tseitin_2 @ ( sk_B @ sk_C_1 ) @ ( sk_C @ sk_C_1 ) @ sk_C_1 @ sk_A )
    | ( sk_B_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('102',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('103',plain,
    ( ( zip_tseitin_2 @ ( sk_B @ sk_C_1 ) @ ( sk_C @ sk_C_1 ) @ sk_C_1 @ sk_A )
    | ( sk_B_1 = k1_xboole_0 )
    | ( v2_funct_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,
    ( ! [X22: $i,X23: $i] :
        ( ( X23 = X22 )
        | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) )
   <= ! [X22: $i,X23: $i] :
        ( ( X23 = X22 )
        | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['43'])).

thf('105',plain,
    ( ( ( v2_funct_1 @ sk_C_1 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( ( sk_C @ sk_C_1 )
        = ( sk_B @ sk_C_1 ) ) )
   <= ! [X22: $i,X23: $i] :
        ( ( X23 = X22 )
        | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('107',plain,
    ( ( ( ( sk_C @ sk_C_1 )
        = ( sk_B @ sk_C_1 ) )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( ~ ( v2_funct_1 @ sk_C_1 )
      & ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X11: $i] :
      ( ( ( sk_B @ X11 )
       != ( sk_C @ X11 ) )
      | ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('109',plain,
    ( ( ( ( sk_B @ sk_C_1 )
       != ( sk_B @ sk_C_1 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( v2_funct_1 @ sk_C_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_C_1 )
      & ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('111',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('112',plain,
    ( ( ( ( sk_B @ sk_C_1 )
       != ( sk_B @ sk_C_1 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( v2_funct_1 @ sk_C_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_C_1 )
      & ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,
    ( ( ( v2_funct_1 @ sk_C_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( ~ ( v2_funct_1 @ sk_C_1 )
      & ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('115',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( ~ ( v2_funct_1 @ sk_C_1 )
      & ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('117',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ~ ( v2_funct_1 @ sk_C_1 )
      & ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ~ ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('120',plain,(
    zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['5','56','62','87','88','89','118','119'])).

thf('121',plain,
    ( ( k1_funct_1 @ sk_C_1 @ sk_D )
    = ( k1_funct_1 @ sk_C_1 @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['3','120'])).

thf('122',plain,(
    ! [X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('123',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('124',plain,(
    ! [X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('125',plain,(
    ! [X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = X0 )
      | ( zip_tseitin_0 @ X0 @ X3 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( sk_B_1 = X1 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('130',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
        | ( zip_tseitin_0 @ X0 @ X1 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ! [X1: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X1 )
        | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('133',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X0 )
        | ( sk_A
          = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ! [X0: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_C_1 ) )
        | ( zip_tseitin_0 @ k1_xboole_0 @ X0 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['123','133'])).

thf('135',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_0 @ X0 @ X1 )
        | ( zip_tseitin_0 @ X0 @ X2 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['122','134'])).

thf('136',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_C_1 ) )
        | ( zip_tseitin_0 @ X1 @ X0 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['135'])).

thf('137',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('138',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('140',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( v2_funct_1 @ sk_C_1 )
    | ( sk_A != k1_xboole_0 )
    | ~ ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ~ ( zip_tseitin_2 @ X22 @ X23 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('142',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['89','5','119','141','62','87','88'])).

thf('143',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['140','142'])).

thf('144',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X11 ) )
      | ( ( k1_funct_1 @ X11 @ X12 )
       != ( k1_funct_1 @ X11 @ X13 ) )
      | ( X12 = X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_C_1 @ X0 )
       != ( k1_funct_1 @ sk_C_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('147',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('148',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['140','142'])).

thf('149',plain,
    ( ( v2_funct_1 @ sk_C_1 )
   <= ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['43'])).

thf('150',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['5','119','56','62','87','88','89','118'])).

thf('151',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(simpl_trail,[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_C_1 @ X0 )
       != ( k1_funct_1 @ sk_C_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['145','146','147','148','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ sk_D )
       != ( k1_funct_1 @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_E = X0 )
      | ~ ( r2_hidden @ sk_E @ sk_A ) ) ),
    inference('sup-',[status(thm)],['121','152'])).

thf('154',plain,
    ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
   <= ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('155',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ X18 )
      | ~ ( zip_tseitin_2 @ X19 @ X17 @ X20 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('156',plain,
    ( ( r2_hidden @ sk_E @ sk_A )
   <= ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['5','56','62','87','88','89','118','119'])).

thf('158',plain,(
    r2_hidden @ sk_E @ sk_A ),
    inference(simpl_trail,[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ sk_D )
       != ( k1_funct_1 @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_E = X0 ) ) ),
    inference(demod,[status(thm)],['153','158'])).

thf('160',plain,
    ( ( sk_E = sk_D )
    | ~ ( r2_hidden @ sk_D @ sk_A ) ),
    inference(eq_res,[status(thm)],['159'])).

thf('161',plain,
    ( ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A )
   <= ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('162',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ~ ( zip_tseitin_2 @ X19 @ X17 @ X20 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('163',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
   <= ( zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    zip_tseitin_2 @ sk_E @ sk_D @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['5','56','62','87','88','89','118','119'])).

thf('165',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['163','164'])).

thf('166',plain,(
    sk_E = sk_D ),
    inference(demod,[status(thm)],['160','165'])).

thf('167',plain,
    ( ( sk_D != sk_E )
   <= ( sk_D != sk_E ) ),
    inference(split,[status(esa)],['4'])).

thf('168',plain,(
    sk_D != sk_E ),
    inference('sat_resolution*',[status(thm)],['119','56','62','87','88','89','118','5'])).

thf('169',plain,(
    sk_D != sk_E ),
    inference(simpl_trail,[status(thm)],['167','168'])).

thf('170',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['166','169'])).


%------------------------------------------------------------------------------
