%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XF7Is0skUB

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 850 expanded)
%              Number of leaves         :   31 ( 253 expanded)
%              Depth                    :   25
%              Number of atoms          : 1068 (12752 expanded)
%              Number of equality atoms :  100 ( 933 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t77_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v2_funct_1 @ B )
      <=> ! [C: $i,D: $i] :
            ( ( ( r2_hidden @ C @ A )
              & ( r2_hidden @ D @ A )
              & ( ( k1_funct_1 @ B @ C )
                = ( k1_funct_1 @ B @ D ) ) )
           => ( C = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( v2_funct_1 @ B )
        <=> ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A )
                & ( ( k1_funct_1 @ B @ C )
                  = ( k1_funct_1 @ B @ D ) ) )
             => ( C = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_funct_2])).

thf('0',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D_1 ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D_1 ) )
   <= ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X43: $i,X44: $i] :
      ( ( X44 = X43 )
      | ( ( k1_funct_1 @ sk_B_1 @ X44 )
       != ( k1_funct_1 @ sk_B_1 @ X43 ) )
      | ~ ( r2_hidden @ X43 @ sk_A )
      | ~ ( r2_hidden @ X44 @ sk_A )
      | ( v2_funct_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ! [X43: $i,X44: $i] :
        ( ( X44 = X43 )
        | ( ( k1_funct_1 @ sk_B_1 @ X44 )
         != ( k1_funct_1 @ sk_B_1 @ X43 ) )
        | ~ ( r2_hidden @ X43 @ sk_A )
        | ~ ( r2_hidden @ X44 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
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

thf('5',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ( X37
        = ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ~ ( zip_tseitin_5 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,
    ( ~ ( zip_tseitin_5 @ sk_B_1 @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_5: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_4 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_4 @ B @ A )
         => ( zip_tseitin_5 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_4 @ X40 @ X41 )
      | ( zip_tseitin_5 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,
    ( ( zip_tseitin_5 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( zip_tseitin_4 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_4 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('11',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_4 @ X35 @ X36 )
      | ( X36 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('12',plain,(
    ! [X35: $i] :
      ( zip_tseitin_4 @ X35 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_4 @ X1 @ X0 )
      | ( zip_tseitin_4 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( zip_tseitin_4 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['13'])).

thf('15',plain,(
    zip_tseitin_5 @ sk_B_1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k1_relset_1 @ X33 @ X34 @ X32 )
        = ( k1_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('18',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','15','18'])).

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

thf('20',plain,(
    ! [X4: $i] :
      ( ( r2_hidden @ ( sk_C @ X4 ) @ ( k1_relat_1 @ X4 ) )
      | ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('21',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('26',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['21','26','27'])).

thf('29',plain,(
    ! [X4: $i] :
      ( ( ( k1_funct_1 @ X4 @ ( sk_B @ X4 ) )
        = ( k1_funct_1 @ X4 @ ( sk_C @ X4 ) ) )
      | ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('30',plain,
    ( ! [X43: $i,X44: $i] :
        ( ( X44 = X43 )
        | ( ( k1_funct_1 @ sk_B_1 @ X44 )
         != ( k1_funct_1 @ sk_B_1 @ X43 ) )
        | ~ ( r2_hidden @ X43 @ sk_A )
        | ~ ( r2_hidden @ X44 @ sk_A ) )
   <= ! [X43: $i,X44: $i] :
        ( ( X44 = X43 )
        | ( ( k1_funct_1 @ sk_B_1 @ X44 )
         != ( k1_funct_1 @ sk_B_1 @ X43 ) )
        | ~ ( r2_hidden @ X43 @ sk_A )
        | ~ ( r2_hidden @ X44 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ~ ( v1_relat_1 @ sk_B_1 )
        | ~ ( v1_funct_1 @ sk_B_1 )
        | ( v2_funct_1 @ sk_B_1 )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A )
        | ( X0
          = ( sk_C @ sk_B_1 ) ) )
   <= ! [X43: $i,X44: $i] :
        ( ( X44 = X43 )
        | ( ( k1_funct_1 @ sk_B_1 @ X44 )
         != ( k1_funct_1 @ sk_B_1 @ X43 ) )
        | ~ ( r2_hidden @ X43 @ sk_A )
        | ~ ( r2_hidden @ X44 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('33',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ( v2_funct_1 @ sk_B_1 )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A )
        | ( X0
          = ( sk_C @ sk_B_1 ) ) )
   <= ! [X43: $i,X44: $i] :
        ( ( X44 = X43 )
        | ( ( k1_funct_1 @ sk_B_1 @ X44 )
         != ( k1_funct_1 @ sk_B_1 @ X43 ) )
        | ~ ( r2_hidden @ X43 @ sk_A )
        | ~ ( r2_hidden @ X44 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( v2_funct_1 @ sk_B_1 )
        | ( X0
          = ( sk_C @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( v2_funct_1 @ sk_B_1 )
        | ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) )
   <= ! [X43: $i,X44: $i] :
        ( ( X44 = X43 )
        | ( ( k1_funct_1 @ sk_B_1 @ X44 )
         != ( k1_funct_1 @ sk_B_1 @ X43 ) )
        | ~ ( r2_hidden @ X43 @ sk_A )
        | ~ ( r2_hidden @ X44 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( X0
          = ( sk_C @ sk_B_1 ) )
        | ( v2_funct_1 @ sk_B_1 ) )
   <= ! [X43: $i,X44: $i] :
        ( ( X44 = X43 )
        | ( ( k1_funct_1 @ sk_B_1 @ X44 )
         != ( k1_funct_1 @ sk_B_1 @ X43 ) )
        | ~ ( r2_hidden @ X43 @ sk_A )
        | ~ ( r2_hidden @ X44 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( ( v2_funct_1 @ sk_B_1 )
      | ( ( sk_B @ sk_B_1 )
        = ( sk_C @ sk_B_1 ) )
      | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) )
   <= ! [X43: $i,X44: $i] :
        ( ( X44 = X43 )
        | ( ( k1_funct_1 @ sk_B_1 @ X44 )
         != ( k1_funct_1 @ sk_B_1 @ X43 ) )
        | ~ ( r2_hidden @ X43 @ sk_A )
        | ~ ( r2_hidden @ X44 @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['36'])).

thf('38',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','15','18'])).

thf('39',plain,(
    ! [X4: $i] :
      ( ( r2_hidden @ ( sk_B @ X4 ) @ ( k1_relat_1 @ X4 ) )
      | ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('40',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('42',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( ( ( sk_B @ sk_B_1 )
        = ( sk_C @ sk_B_1 ) )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ! [X43: $i,X44: $i] :
        ( ( X44 = X43 )
        | ( ( k1_funct_1 @ sk_B_1 @ X44 )
         != ( k1_funct_1 @ sk_B_1 @ X43 ) )
        | ~ ( r2_hidden @ X43 @ sk_A )
        | ~ ( r2_hidden @ X44 @ sk_A ) ) ),
    inference(clc,[status(thm)],['37','43'])).

thf('45',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['45'])).

thf('47',plain,
    ( ( ( sk_B @ sk_B_1 )
      = ( sk_C @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X43: $i,X44: $i] :
          ( ( X44 = X43 )
          | ( ( k1_funct_1 @ sk_B_1 @ X44 )
           != ( k1_funct_1 @ sk_B_1 @ X43 ) )
          | ~ ( r2_hidden @ X43 @ sk_A )
          | ~ ( r2_hidden @ X44 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    ! [X4: $i] :
      ( ( ( sk_B @ X4 )
       != ( sk_C @ X4 ) )
      | ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('49',plain,
    ( ( ( ( sk_B @ sk_B_1 )
       != ( sk_B @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X43: $i,X44: $i] :
          ( ( X44 = X43 )
          | ( ( k1_funct_1 @ sk_B_1 @ X44 )
           != ( k1_funct_1 @ sk_B_1 @ X43 ) )
          | ~ ( r2_hidden @ X43 @ sk_A )
          | ~ ( r2_hidden @ X44 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('51',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( ( sk_B @ sk_B_1 )
       != ( sk_B @ sk_B_1 ) )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X43: $i,X44: $i] :
          ( ( X44 = X43 )
          | ( ( k1_funct_1 @ sk_B_1 @ X44 )
           != ( k1_funct_1 @ sk_B_1 @ X43 ) )
          | ~ ( r2_hidden @ X43 @ sk_A )
          | ~ ( r2_hidden @ X44 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( v2_funct_1 @ sk_B_1 )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X43: $i,X44: $i] :
          ( ( X44 = X43 )
          | ( ( k1_funct_1 @ sk_B_1 @ X44 )
           != ( k1_funct_1 @ sk_B_1 @ X43 ) )
          | ~ ( r2_hidden @ X43 @ sk_A )
          | ~ ( r2_hidden @ X44 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['45'])).

thf('55',plain,
    ( ~ ! [X43: $i,X44: $i] :
          ( ( X44 = X43 )
          | ( ( k1_funct_1 @ sk_B_1 @ X44 )
           != ( k1_funct_1 @ sk_B_1 @ X43 ) )
          | ~ ( r2_hidden @ X43 @ sk_A )
          | ~ ( r2_hidden @ X44 @ sk_A ) )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D_1 ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('57',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D_1 ) ),
    inference('sat_resolution*',[status(thm)],['3','55','56'])).

thf('58',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D_1 ) ),
    inference(simpl_trail,[status(thm)],['1','57'])).

thf('59',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','15','18'])).

thf('60',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X4 ) )
      | ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X4 ) )
      | ( ( k1_funct_1 @ X4 @ X5 )
       != ( k1_funct_1 @ X4 @ X6 ) )
      | ( X5 = X6 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('63',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','15','18'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,
    ( ( v2_funct_1 @ sk_B_1 )
   <= ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('67',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['3','55'])).

thf('68',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_D_1 = X0 )
      | ~ ( r2_hidden @ sk_D_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','69'])).

thf('71',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_A )
   <= ( r2_hidden @ sk_D_1 @ sk_A ) ),
    inference(split,[status(esa)],['71'])).

thf('73',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['71'])).

thf('74',plain,(
    r2_hidden @ sk_D_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','55','73'])).

thf('75',plain,(
    r2_hidden @ sk_D_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['72','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_D_1 = X0 ) ) ),
    inference(demod,[status(thm)],['70','75'])).

thf('77',plain,
    ( ( sk_D_1 = sk_C_2 )
    | ~ ( r2_hidden @ sk_C_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['76'])).

thf('78',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
   <= ( r2_hidden @ sk_C_2 @ sk_A ) ),
    inference(split,[status(esa)],['45'])).

thf('79',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['45'])).

thf('80',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','55','79'])).

thf('81',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference(simpl_trail,[status(thm)],['78','80'])).

thf('82',plain,(
    sk_D_1 = sk_C_2 ),
    inference(demod,[status(thm)],['77','81'])).

thf('83',plain,
    ( ( sk_C_2 != sk_D_1 )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( sk_C_2 != sk_D_1 )
   <= ( sk_C_2 != sk_D_1 ) ),
    inference(split,[status(esa)],['83'])).

thf('85',plain,
    ( ( sk_C_2 != sk_D_1 )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['83'])).

thf('86',plain,(
    sk_C_2 != sk_D_1 ),
    inference('sat_resolution*',[status(thm)],['3','55','85'])).

thf('87',plain,(
    sk_C_2 != sk_D_1 ),
    inference(simpl_trail,[status(thm)],['84','86'])).

thf('88',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['82','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XF7Is0skUB
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 115 iterations in 0.091s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.54  thf(sk_C_type, type, sk_C: $i > $i).
% 0.21/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.54  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.54  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $i > $o).
% 0.21/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.54  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.21/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.54  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.54  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(t77_funct_2, conjecture,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.54       ( ( v2_funct_1 @ B ) <=>
% 0.21/0.54         ( ![C:$i,D:$i]:
% 0.21/0.54           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.21/0.54               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.21/0.54             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i,B:$i]:
% 0.21/0.54        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.54            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.54          ( ( v2_funct_1 @ B ) <=>
% 0.21/0.54            ( ![C:$i,D:$i]:
% 0.21/0.54              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.21/0.54                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.21/0.54                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t77_funct_2])).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D_1))
% 0.21/0.54        | ~ (v2_funct_1 @ sk_B_1))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D_1)))
% 0.21/0.54         <= ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D_1))))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (![X43 : $i, X44 : $i]:
% 0.21/0.54         (((X44) = (X43))
% 0.21/0.54          | ((k1_funct_1 @ sk_B_1 @ X44) != (k1_funct_1 @ sk_B_1 @ X43))
% 0.21/0.54          | ~ (r2_hidden @ X43 @ sk_A)
% 0.21/0.54          | ~ (r2_hidden @ X44 @ sk_A)
% 0.21/0.54          | (v2_funct_1 @ sk_B_1))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (((v2_funct_1 @ sk_B_1)) | 
% 0.21/0.54       (![X43 : $i, X44 : $i]:
% 0.21/0.54          (((X44) = (X43))
% 0.21/0.54           | ((k1_funct_1 @ sk_B_1 @ X44) != (k1_funct_1 @ sk_B_1 @ X43))
% 0.21/0.54           | ~ (r2_hidden @ X43 @ sk_A)
% 0.21/0.54           | ~ (r2_hidden @ X44 @ sk_A)))),
% 0.21/0.54      inference('split', [status(esa)], ['2'])).
% 0.21/0.54  thf('4', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(d1_funct_2, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.54           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.21/0.54             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.54         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.54           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.21/0.54             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_1, axiom,
% 0.21/0.54    (![C:$i,B:$i,A:$i]:
% 0.21/0.54     ( ( zip_tseitin_5 @ C @ B @ A ) =>
% 0.21/0.54       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.21/0.54         (~ (v1_funct_2 @ X39 @ X37 @ X38)
% 0.21/0.54          | ((X37) = (k1_relset_1 @ X37 @ X38 @ X39))
% 0.21/0.54          | ~ (zip_tseitin_5 @ X39 @ X38 @ X37))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      ((~ (zip_tseitin_5 @ sk_B_1 @ sk_A @ sk_A)
% 0.21/0.54        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(zf_stmt_2, type, zip_tseitin_5 : $i > $i > $i > $o).
% 0.21/0.54  thf(zf_stmt_3, type, zip_tseitin_4 : $i > $i > $o).
% 0.21/0.54  thf(zf_stmt_4, axiom,
% 0.21/0.54    (![B:$i,A:$i]:
% 0.21/0.54     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.54       ( zip_tseitin_4 @ B @ A ) ))).
% 0.21/0.54  thf(zf_stmt_5, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( ( ( zip_tseitin_4 @ B @ A ) => ( zip_tseitin_5 @ C @ B @ A ) ) & 
% 0.21/0.54         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.54           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.54             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.21/0.54         (~ (zip_tseitin_4 @ X40 @ X41)
% 0.21/0.54          | (zip_tseitin_5 @ X42 @ X40 @ X41)
% 0.21/0.54          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      (((zip_tseitin_5 @ sk_B_1 @ sk_A @ sk_A)
% 0.21/0.54        | ~ (zip_tseitin_4 @ sk_A @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (![X35 : $i, X36 : $i]:
% 0.21/0.54         ((zip_tseitin_4 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (![X35 : $i, X36 : $i]:
% 0.21/0.54         ((zip_tseitin_4 @ X35 @ X36) | ((X36) != (k1_xboole_0)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.54  thf('12', plain, (![X35 : $i]: (zip_tseitin_4 @ X35 @ k1_xboole_0)),
% 0.21/0.54      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         ((zip_tseitin_4 @ X1 @ X0) | (zip_tseitin_4 @ X0 @ X2))),
% 0.21/0.54      inference('sup+', [status(thm)], ['10', '12'])).
% 0.21/0.54  thf('14', plain, (![X0 : $i]: (zip_tseitin_4 @ X0 @ X0)),
% 0.21/0.54      inference('eq_fact', [status(thm)], ['13'])).
% 0.21/0.54  thf('15', plain, ((zip_tseitin_5 @ sk_B_1 @ sk_A @ sk_A)),
% 0.21/0.54      inference('demod', [status(thm)], ['9', '14'])).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.21/0.54         (((k1_relset_1 @ X33 @ X34 @ X32) = (k1_relat_1 @ X32))
% 0.21/0.54          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      (((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k1_relat_1 @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.54  thf('19', plain, (((sk_A) = (k1_relat_1 @ sk_B_1))),
% 0.21/0.54      inference('demod', [status(thm)], ['6', '15', '18'])).
% 0.21/0.54  thf(d8_funct_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.54       ( ( v2_funct_1 @ A ) <=>
% 0.21/0.54         ( ![B:$i,C:$i]:
% 0.21/0.54           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.54               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.54               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.21/0.54             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      (![X4 : $i]:
% 0.21/0.54         ((r2_hidden @ (sk_C @ X4) @ (k1_relat_1 @ X4))
% 0.21/0.54          | (v2_funct_1 @ X4)
% 0.21/0.54          | ~ (v1_funct_1 @ X4)
% 0.21/0.54          | ~ (v1_relat_1 @ X4))),
% 0.21/0.54      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      (((r2_hidden @ (sk_C @ sk_B_1) @ sk_A)
% 0.21/0.54        | ~ (v1_relat_1 @ sk_B_1)
% 0.21/0.54        | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.54        | (v2_funct_1 @ sk_B_1))),
% 0.21/0.54      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(cc2_relat_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.21/0.54          | (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X1))),
% 0.21/0.54      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.54  thf(fc6_relat_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.21/0.54      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.54  thf('26', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.54      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.54  thf('27', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (((r2_hidden @ (sk_C @ sk_B_1) @ sk_A) | (v2_funct_1 @ sk_B_1))),
% 0.21/0.54      inference('demod', [status(thm)], ['21', '26', '27'])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (![X4 : $i]:
% 0.21/0.54         (((k1_funct_1 @ X4 @ (sk_B @ X4)) = (k1_funct_1 @ X4 @ (sk_C @ X4)))
% 0.21/0.54          | (v2_funct_1 @ X4)
% 0.21/0.54          | ~ (v1_funct_1 @ X4)
% 0.21/0.54          | ~ (v1_relat_1 @ X4))),
% 0.21/0.54      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      ((![X43 : $i, X44 : $i]:
% 0.21/0.54          (((X44) = (X43))
% 0.21/0.54           | ((k1_funct_1 @ sk_B_1 @ X44) != (k1_funct_1 @ sk_B_1 @ X43))
% 0.21/0.54           | ~ (r2_hidden @ X43 @ sk_A)
% 0.21/0.54           | ~ (r2_hidden @ X44 @ sk_A)))
% 0.21/0.54         <= ((![X43 : $i, X44 : $i]:
% 0.21/0.54                (((X44) = (X43))
% 0.21/0.54                 | ((k1_funct_1 @ sk_B_1 @ X44) != (k1_funct_1 @ sk_B_1 @ X43))
% 0.21/0.54                 | ~ (r2_hidden @ X43 @ sk_A)
% 0.21/0.54                 | ~ (r2_hidden @ X44 @ sk_A))))),
% 0.21/0.54      inference('split', [status(esa)], ['2'])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      ((![X0 : $i]:
% 0.21/0.54          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.21/0.54             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.21/0.54           | ~ (v1_relat_1 @ sk_B_1)
% 0.21/0.54           | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.54           | (v2_funct_1 @ sk_B_1)
% 0.21/0.54           | ~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.54           | ~ (r2_hidden @ (sk_C @ sk_B_1) @ sk_A)
% 0.21/0.54           | ((X0) = (sk_C @ sk_B_1))))
% 0.21/0.54         <= ((![X43 : $i, X44 : $i]:
% 0.21/0.54                (((X44) = (X43))
% 0.21/0.54                 | ((k1_funct_1 @ sk_B_1 @ X44) != (k1_funct_1 @ sk_B_1 @ X43))
% 0.21/0.54                 | ~ (r2_hidden @ X43 @ sk_A)
% 0.21/0.54                 | ~ (r2_hidden @ X44 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.54  thf('32', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.54      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.54  thf('33', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('34', plain,
% 0.21/0.54      ((![X0 : $i]:
% 0.21/0.54          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.21/0.54             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.21/0.54           | (v2_funct_1 @ sk_B_1)
% 0.21/0.54           | ~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.54           | ~ (r2_hidden @ (sk_C @ sk_B_1) @ sk_A)
% 0.21/0.54           | ((X0) = (sk_C @ sk_B_1))))
% 0.21/0.54         <= ((![X43 : $i, X44 : $i]:
% 0.21/0.54                (((X44) = (X43))
% 0.21/0.54                 | ((k1_funct_1 @ sk_B_1 @ X44) != (k1_funct_1 @ sk_B_1 @ X43))
% 0.21/0.54                 | ~ (r2_hidden @ X43 @ sk_A)
% 0.21/0.54                 | ~ (r2_hidden @ X44 @ sk_A))))),
% 0.21/0.54      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      ((![X0 : $i]:
% 0.21/0.54          ((v2_funct_1 @ sk_B_1)
% 0.21/0.54           | ((X0) = (sk_C @ sk_B_1))
% 0.21/0.54           | ~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.54           | (v2_funct_1 @ sk_B_1)
% 0.21/0.54           | ((k1_funct_1 @ sk_B_1 @ X0)
% 0.21/0.54               != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))))
% 0.21/0.54         <= ((![X43 : $i, X44 : $i]:
% 0.21/0.54                (((X44) = (X43))
% 0.21/0.54                 | ((k1_funct_1 @ sk_B_1 @ X44) != (k1_funct_1 @ sk_B_1 @ X43))
% 0.21/0.54                 | ~ (r2_hidden @ X43 @ sk_A)
% 0.21/0.54                 | ~ (r2_hidden @ X44 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['28', '34'])).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      ((![X0 : $i]:
% 0.21/0.54          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.21/0.54             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.21/0.54           | ~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.54           | ((X0) = (sk_C @ sk_B_1))
% 0.21/0.54           | (v2_funct_1 @ sk_B_1)))
% 0.21/0.54         <= ((![X43 : $i, X44 : $i]:
% 0.21/0.54                (((X44) = (X43))
% 0.21/0.54                 | ((k1_funct_1 @ sk_B_1 @ X44) != (k1_funct_1 @ sk_B_1 @ X43))
% 0.21/0.54                 | ~ (r2_hidden @ X43 @ sk_A)
% 0.21/0.54                 | ~ (r2_hidden @ X44 @ sk_A))))),
% 0.21/0.54      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.54  thf('37', plain,
% 0.21/0.54      ((((v2_funct_1 @ sk_B_1)
% 0.21/0.54         | ((sk_B @ sk_B_1) = (sk_C @ sk_B_1))
% 0.21/0.54         | ~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_A)))
% 0.21/0.54         <= ((![X43 : $i, X44 : $i]:
% 0.21/0.54                (((X44) = (X43))
% 0.21/0.54                 | ((k1_funct_1 @ sk_B_1 @ X44) != (k1_funct_1 @ sk_B_1 @ X43))
% 0.21/0.54                 | ~ (r2_hidden @ X43 @ sk_A)
% 0.21/0.54                 | ~ (r2_hidden @ X44 @ sk_A))))),
% 0.21/0.54      inference('eq_res', [status(thm)], ['36'])).
% 0.21/0.54  thf('38', plain, (((sk_A) = (k1_relat_1 @ sk_B_1))),
% 0.21/0.54      inference('demod', [status(thm)], ['6', '15', '18'])).
% 0.21/0.54  thf('39', plain,
% 0.21/0.54      (![X4 : $i]:
% 0.21/0.54         ((r2_hidden @ (sk_B @ X4) @ (k1_relat_1 @ X4))
% 0.21/0.54          | (v2_funct_1 @ X4)
% 0.21/0.54          | ~ (v1_funct_1 @ X4)
% 0.21/0.54          | ~ (v1_relat_1 @ X4))),
% 0.21/0.54      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      (((r2_hidden @ (sk_B @ sk_B_1) @ sk_A)
% 0.21/0.54        | ~ (v1_relat_1 @ sk_B_1)
% 0.21/0.54        | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.54        | (v2_funct_1 @ sk_B_1))),
% 0.21/0.54      inference('sup+', [status(thm)], ['38', '39'])).
% 0.21/0.54  thf('41', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.54      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.54  thf('42', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      (((r2_hidden @ (sk_B @ sk_B_1) @ sk_A) | (v2_funct_1 @ sk_B_1))),
% 0.21/0.54      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.21/0.54  thf('44', plain,
% 0.21/0.54      (((((sk_B @ sk_B_1) = (sk_C @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.21/0.54         <= ((![X43 : $i, X44 : $i]:
% 0.21/0.54                (((X44) = (X43))
% 0.21/0.54                 | ((k1_funct_1 @ sk_B_1 @ X44) != (k1_funct_1 @ sk_B_1 @ X43))
% 0.21/0.54                 | ~ (r2_hidden @ X43 @ sk_A)
% 0.21/0.54                 | ~ (r2_hidden @ X44 @ sk_A))))),
% 0.21/0.54      inference('clc', [status(thm)], ['37', '43'])).
% 0.21/0.54  thf('45', plain, (((r2_hidden @ sk_C_2 @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('46', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.21/0.54      inference('split', [status(esa)], ['45'])).
% 0.21/0.54  thf('47', plain,
% 0.21/0.54      ((((sk_B @ sk_B_1) = (sk_C @ sk_B_1)))
% 0.21/0.54         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.21/0.54             (![X43 : $i, X44 : $i]:
% 0.21/0.54                (((X44) = (X43))
% 0.21/0.54                 | ((k1_funct_1 @ sk_B_1 @ X44) != (k1_funct_1 @ sk_B_1 @ X43))
% 0.21/0.54                 | ~ (r2_hidden @ X43 @ sk_A)
% 0.21/0.54                 | ~ (r2_hidden @ X44 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['44', '46'])).
% 0.21/0.54  thf('48', plain,
% 0.21/0.54      (![X4 : $i]:
% 0.21/0.54         (((sk_B @ X4) != (sk_C @ X4))
% 0.21/0.54          | (v2_funct_1 @ X4)
% 0.21/0.54          | ~ (v1_funct_1 @ X4)
% 0.21/0.54          | ~ (v1_relat_1 @ X4))),
% 0.21/0.54      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.54  thf('49', plain,
% 0.21/0.54      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1))
% 0.21/0.54         | ~ (v1_relat_1 @ sk_B_1)
% 0.21/0.54         | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.54         | (v2_funct_1 @ sk_B_1)))
% 0.21/0.54         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.21/0.54             (![X43 : $i, X44 : $i]:
% 0.21/0.54                (((X44) = (X43))
% 0.21/0.54                 | ((k1_funct_1 @ sk_B_1 @ X44) != (k1_funct_1 @ sk_B_1 @ X43))
% 0.21/0.54                 | ~ (r2_hidden @ X43 @ sk_A)
% 0.21/0.54                 | ~ (r2_hidden @ X44 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.54  thf('50', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.54      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.54  thf('51', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('52', plain,
% 0.21/0.54      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.21/0.54         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.21/0.54             (![X43 : $i, X44 : $i]:
% 0.21/0.54                (((X44) = (X43))
% 0.21/0.54                 | ((k1_funct_1 @ sk_B_1 @ X44) != (k1_funct_1 @ sk_B_1 @ X43))
% 0.21/0.54                 | ~ (r2_hidden @ X43 @ sk_A)
% 0.21/0.54                 | ~ (r2_hidden @ X44 @ sk_A))))),
% 0.21/0.54      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.21/0.54  thf('53', plain,
% 0.21/0.54      (((v2_funct_1 @ sk_B_1))
% 0.21/0.54         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.21/0.54             (![X43 : $i, X44 : $i]:
% 0.21/0.54                (((X44) = (X43))
% 0.21/0.54                 | ((k1_funct_1 @ sk_B_1 @ X44) != (k1_funct_1 @ sk_B_1 @ X43))
% 0.21/0.54                 | ~ (r2_hidden @ X43 @ sk_A)
% 0.21/0.54                 | ~ (r2_hidden @ X44 @ sk_A))))),
% 0.21/0.54      inference('simplify', [status(thm)], ['52'])).
% 0.21/0.54  thf('54', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.21/0.54      inference('split', [status(esa)], ['45'])).
% 0.21/0.54  thf('55', plain,
% 0.21/0.54      (~
% 0.21/0.54       (![X43 : $i, X44 : $i]:
% 0.21/0.54          (((X44) = (X43))
% 0.21/0.54           | ((k1_funct_1 @ sk_B_1 @ X44) != (k1_funct_1 @ sk_B_1 @ X43))
% 0.21/0.54           | ~ (r2_hidden @ X43 @ sk_A)
% 0.21/0.54           | ~ (r2_hidden @ X44 @ sk_A))) | 
% 0.21/0.54       ((v2_funct_1 @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.54  thf('56', plain,
% 0.21/0.54      ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D_1))) | 
% 0.21/0.54       ~ ((v2_funct_1 @ sk_B_1))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('57', plain,
% 0.21/0.54      ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D_1)))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['3', '55', '56'])).
% 0.21/0.54  thf('58', plain,
% 0.21/0.54      (((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D_1))),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['1', '57'])).
% 0.21/0.54  thf('59', plain, (((sk_A) = (k1_relat_1 @ sk_B_1))),
% 0.21/0.54      inference('demod', [status(thm)], ['6', '15', '18'])).
% 0.21/0.54  thf('60', plain,
% 0.21/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.54         (~ (v2_funct_1 @ X4)
% 0.21/0.54          | ~ (r2_hidden @ X5 @ (k1_relat_1 @ X4))
% 0.21/0.54          | ~ (r2_hidden @ X6 @ (k1_relat_1 @ X4))
% 0.21/0.54          | ((k1_funct_1 @ X4 @ X5) != (k1_funct_1 @ X4 @ X6))
% 0.21/0.54          | ((X5) = (X6))
% 0.21/0.54          | ~ (v1_funct_1 @ X4)
% 0.21/0.54          | ~ (v1_relat_1 @ X4))),
% 0.21/0.54      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.54  thf('61', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.54          | ~ (v1_relat_1 @ sk_B_1)
% 0.21/0.54          | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.54          | ((X0) = (X1))
% 0.21/0.54          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.21/0.54          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1))
% 0.21/0.54          | ~ (v2_funct_1 @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.54  thf('62', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.54      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.54  thf('63', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('64', plain, (((sk_A) = (k1_relat_1 @ sk_B_1))),
% 0.21/0.54      inference('demod', [status(thm)], ['6', '15', '18'])).
% 0.21/0.54  thf('65', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.54          | ((X0) = (X1))
% 0.21/0.54          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.21/0.54          | ~ (r2_hidden @ X1 @ sk_A)
% 0.21/0.54          | ~ (v2_funct_1 @ sk_B_1))),
% 0.21/0.54      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 0.21/0.54  thf('66', plain, (((v2_funct_1 @ sk_B_1)) <= (((v2_funct_1 @ sk_B_1)))),
% 0.21/0.54      inference('split', [status(esa)], ['2'])).
% 0.21/0.54  thf('67', plain, (((v2_funct_1 @ sk_B_1))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['3', '55'])).
% 0.21/0.54  thf('68', plain, ((v2_funct_1 @ sk_B_1)),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['66', '67'])).
% 0.21/0.54  thf('69', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.54          | ((X0) = (X1))
% 0.21/0.54          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.21/0.54          | ~ (r2_hidden @ X1 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['65', '68'])).
% 0.21/0.54  thf('70', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k1_funct_1 @ sk_B_1 @ sk_C_2) != (k1_funct_1 @ sk_B_1 @ X0))
% 0.21/0.54          | ~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.54          | ((sk_D_1) = (X0))
% 0.21/0.54          | ~ (r2_hidden @ sk_D_1 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['58', '69'])).
% 0.21/0.54  thf('71', plain, (((r2_hidden @ sk_D_1 @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('72', plain,
% 0.21/0.54      (((r2_hidden @ sk_D_1 @ sk_A)) <= (((r2_hidden @ sk_D_1 @ sk_A)))),
% 0.21/0.54      inference('split', [status(esa)], ['71'])).
% 0.21/0.54  thf('73', plain, (((r2_hidden @ sk_D_1 @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.21/0.54      inference('split', [status(esa)], ['71'])).
% 0.21/0.54  thf('74', plain, (((r2_hidden @ sk_D_1 @ sk_A))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['3', '55', '73'])).
% 0.21/0.54  thf('75', plain, ((r2_hidden @ sk_D_1 @ sk_A)),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['72', '74'])).
% 0.21/0.54  thf('76', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k1_funct_1 @ sk_B_1 @ sk_C_2) != (k1_funct_1 @ sk_B_1 @ X0))
% 0.21/0.54          | ~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.54          | ((sk_D_1) = (X0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['70', '75'])).
% 0.21/0.54  thf('77', plain, ((((sk_D_1) = (sk_C_2)) | ~ (r2_hidden @ sk_C_2 @ sk_A))),
% 0.21/0.54      inference('eq_res', [status(thm)], ['76'])).
% 0.21/0.54  thf('78', plain,
% 0.21/0.54      (((r2_hidden @ sk_C_2 @ sk_A)) <= (((r2_hidden @ sk_C_2 @ sk_A)))),
% 0.21/0.54      inference('split', [status(esa)], ['45'])).
% 0.21/0.54  thf('79', plain, (((r2_hidden @ sk_C_2 @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.21/0.54      inference('split', [status(esa)], ['45'])).
% 0.21/0.54  thf('80', plain, (((r2_hidden @ sk_C_2 @ sk_A))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['3', '55', '79'])).
% 0.21/0.54  thf('81', plain, ((r2_hidden @ sk_C_2 @ sk_A)),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['78', '80'])).
% 0.21/0.54  thf('82', plain, (((sk_D_1) = (sk_C_2))),
% 0.21/0.54      inference('demod', [status(thm)], ['77', '81'])).
% 0.21/0.54  thf('83', plain, ((((sk_C_2) != (sk_D_1)) | ~ (v2_funct_1 @ sk_B_1))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('84', plain, ((((sk_C_2) != (sk_D_1))) <= (~ (((sk_C_2) = (sk_D_1))))),
% 0.21/0.54      inference('split', [status(esa)], ['83'])).
% 0.21/0.54  thf('85', plain, (~ (((sk_C_2) = (sk_D_1))) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.21/0.54      inference('split', [status(esa)], ['83'])).
% 0.21/0.54  thf('86', plain, (~ (((sk_C_2) = (sk_D_1)))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['3', '55', '85'])).
% 0.21/0.54  thf('87', plain, (((sk_C_2) != (sk_D_1))),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['84', '86'])).
% 0.21/0.54  thf('88', plain, ($false),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)], ['82', '87'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
