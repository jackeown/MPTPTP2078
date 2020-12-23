%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KwQQwiwtQK

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:54 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 862 expanded)
%              Number of leaves         :   31 ( 253 expanded)
%              Depth                    :   25
%              Number of atoms          : 1076 (12848 expanded)
%              Number of equality atoms :  101 ( 945 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ( ( ( k1_funct_1 @ sk_B_2 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_2 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k1_funct_1 @ sk_B_2 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_2 @ sk_D ) )
   <= ( ( k1_funct_1 @ sk_B_2 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_2 @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X35 = X34 )
      | ( ( k1_funct_1 @ sk_B_2 @ X35 )
       != ( k1_funct_1 @ sk_B_2 @ X34 ) )
      | ~ ( r2_hidden @ X34 @ sk_A )
      | ~ ( r2_hidden @ X35 @ sk_A )
      | ( v2_funct_1 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v2_funct_1 @ sk_B_2 )
    | ! [X34: $i,X35: $i] :
        ( ( X35 = X34 )
        | ( ( k1_funct_1 @ sk_B_2 @ X35 )
         != ( k1_funct_1 @ sk_B_2 @ X34 ) )
        | ~ ( r2_hidden @ X34 @ sk_A )
        | ~ ( r2_hidden @ X35 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    v1_funct_2 @ sk_B_2 @ sk_A @ sk_A ),
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

thf('5',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,
    ( ~ ( zip_tseitin_1 @ sk_B_2 @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('9',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_2 )
    = ( k1_relat_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( zip_tseitin_1 @ sk_B_2 @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('13',plain,
    ( ( zip_tseitin_1 @ sk_B_2 @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('15',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X27 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('16',plain,(
    ! [X26: $i] :
      ( zip_tseitin_0 @ X26 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['17'])).

thf('19',plain,(
    zip_tseitin_1 @ sk_B_2 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['13','18'])).

thf('20',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['10','19'])).

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

thf('21',plain,(
    ! [X17: $i] :
      ( ( r2_hidden @ ( sk_C @ X17 ) @ ( k1_relat_1 @ X17 ) )
      | ( v2_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('22',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B_2 ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_2 )
    | ~ ( v1_funct_1 @ sk_B_2 )
    | ( v2_funct_1 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('24',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('26',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('27',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B_2 ) @ sk_A )
    | ( v2_funct_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['22','27','28'])).

thf('30',plain,(
    ! [X17: $i] :
      ( ( ( k1_funct_1 @ X17 @ ( sk_B_1 @ X17 ) )
        = ( k1_funct_1 @ X17 @ ( sk_C @ X17 ) ) )
      | ( v2_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('31',plain,
    ( ! [X34: $i,X35: $i] :
        ( ( X35 = X34 )
        | ( ( k1_funct_1 @ sk_B_2 @ X35 )
         != ( k1_funct_1 @ sk_B_2 @ X34 ) )
        | ~ ( r2_hidden @ X34 @ sk_A )
        | ~ ( r2_hidden @ X35 @ sk_A ) )
   <= ! [X34: $i,X35: $i] :
        ( ( X35 = X34 )
        | ( ( k1_funct_1 @ sk_B_2 @ X35 )
         != ( k1_funct_1 @ sk_B_2 @ X34 ) )
        | ~ ( r2_hidden @ X34 @ sk_A )
        | ~ ( r2_hidden @ X35 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_2 @ X0 )
         != ( k1_funct_1 @ sk_B_2 @ ( sk_B_1 @ sk_B_2 ) ) )
        | ~ ( v1_relat_1 @ sk_B_2 )
        | ~ ( v1_funct_1 @ sk_B_2 )
        | ( v2_funct_1 @ sk_B_2 )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ ( sk_C @ sk_B_2 ) @ sk_A )
        | ( X0
          = ( sk_C @ sk_B_2 ) ) )
   <= ! [X34: $i,X35: $i] :
        ( ( X35 = X34 )
        | ( ( k1_funct_1 @ sk_B_2 @ X35 )
         != ( k1_funct_1 @ sk_B_2 @ X34 ) )
        | ~ ( r2_hidden @ X34 @ sk_A )
        | ~ ( r2_hidden @ X35 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(demod,[status(thm)],['25','26'])).

thf('34',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_2 @ X0 )
         != ( k1_funct_1 @ sk_B_2 @ ( sk_B_1 @ sk_B_2 ) ) )
        | ( v2_funct_1 @ sk_B_2 )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ ( sk_C @ sk_B_2 ) @ sk_A )
        | ( X0
          = ( sk_C @ sk_B_2 ) ) )
   <= ! [X34: $i,X35: $i] :
        ( ( X35 = X34 )
        | ( ( k1_funct_1 @ sk_B_2 @ X35 )
         != ( k1_funct_1 @ sk_B_2 @ X34 ) )
        | ~ ( r2_hidden @ X34 @ sk_A )
        | ~ ( r2_hidden @ X35 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( v2_funct_1 @ sk_B_2 )
        | ( X0
          = ( sk_C @ sk_B_2 ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( v2_funct_1 @ sk_B_2 )
        | ( ( k1_funct_1 @ sk_B_2 @ X0 )
         != ( k1_funct_1 @ sk_B_2 @ ( sk_B_1 @ sk_B_2 ) ) ) )
   <= ! [X34: $i,X35: $i] :
        ( ( X35 = X34 )
        | ( ( k1_funct_1 @ sk_B_2 @ X35 )
         != ( k1_funct_1 @ sk_B_2 @ X34 ) )
        | ~ ( r2_hidden @ X34 @ sk_A )
        | ~ ( r2_hidden @ X35 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_2 @ X0 )
         != ( k1_funct_1 @ sk_B_2 @ ( sk_B_1 @ sk_B_2 ) ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( X0
          = ( sk_C @ sk_B_2 ) )
        | ( v2_funct_1 @ sk_B_2 ) )
   <= ! [X34: $i,X35: $i] :
        ( ( X35 = X34 )
        | ( ( k1_funct_1 @ sk_B_2 @ X35 )
         != ( k1_funct_1 @ sk_B_2 @ X34 ) )
        | ~ ( r2_hidden @ X34 @ sk_A )
        | ~ ( r2_hidden @ X35 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( ( v2_funct_1 @ sk_B_2 )
      | ( ( sk_B_1 @ sk_B_2 )
        = ( sk_C @ sk_B_2 ) )
      | ~ ( r2_hidden @ ( sk_B_1 @ sk_B_2 ) @ sk_A ) )
   <= ! [X34: $i,X35: $i] :
        ( ( X35 = X34 )
        | ( ( k1_funct_1 @ sk_B_2 @ X35 )
         != ( k1_funct_1 @ sk_B_2 @ X34 ) )
        | ~ ( r2_hidden @ X34 @ sk_A )
        | ~ ( r2_hidden @ X35 @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['37'])).

thf('39',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['10','19'])).

thf('40',plain,(
    ! [X17: $i] :
      ( ( r2_hidden @ ( sk_B_1 @ X17 ) @ ( k1_relat_1 @ X17 ) )
      | ( v2_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('41',plain,
    ( ( r2_hidden @ ( sk_B_1 @ sk_B_2 ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_2 )
    | ~ ( v1_funct_1 @ sk_B_2 )
    | ( v2_funct_1 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(demod,[status(thm)],['25','26'])).

thf('43',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( r2_hidden @ ( sk_B_1 @ sk_B_2 ) @ sk_A )
    | ( v2_funct_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ( ( ( sk_B_1 @ sk_B_2 )
        = ( sk_C @ sk_B_2 ) )
      | ( v2_funct_1 @ sk_B_2 ) )
   <= ! [X34: $i,X35: $i] :
        ( ( X35 = X34 )
        | ( ( k1_funct_1 @ sk_B_2 @ X35 )
         != ( k1_funct_1 @ sk_B_2 @ X34 ) )
        | ~ ( r2_hidden @ X34 @ sk_A )
        | ~ ( r2_hidden @ X35 @ sk_A ) ) ),
    inference(clc,[status(thm)],['38','44'])).

thf('46',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ~ ( v2_funct_1 @ sk_B_2 )
   <= ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,
    ( ( ( sk_B_1 @ sk_B_2 )
      = ( sk_C @ sk_B_2 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_2 )
      & ! [X34: $i,X35: $i] :
          ( ( X35 = X34 )
          | ( ( k1_funct_1 @ sk_B_2 @ X35 )
           != ( k1_funct_1 @ sk_B_2 @ X34 ) )
          | ~ ( r2_hidden @ X34 @ sk_A )
          | ~ ( r2_hidden @ X35 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X17: $i] :
      ( ( ( sk_B_1 @ X17 )
       != ( sk_C @ X17 ) )
      | ( v2_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('50',plain,
    ( ( ( ( sk_B_1 @ sk_B_2 )
       != ( sk_B_1 @ sk_B_2 ) )
      | ~ ( v1_relat_1 @ sk_B_2 )
      | ~ ( v1_funct_1 @ sk_B_2 )
      | ( v2_funct_1 @ sk_B_2 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_2 )
      & ! [X34: $i,X35: $i] :
          ( ( X35 = X34 )
          | ( ( k1_funct_1 @ sk_B_2 @ X35 )
           != ( k1_funct_1 @ sk_B_2 @ X34 ) )
          | ~ ( r2_hidden @ X34 @ sk_A )
          | ~ ( r2_hidden @ X35 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(demod,[status(thm)],['25','26'])).

thf('52',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( ( sk_B_1 @ sk_B_2 )
       != ( sk_B_1 @ sk_B_2 ) )
      | ( v2_funct_1 @ sk_B_2 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_2 )
      & ! [X34: $i,X35: $i] :
          ( ( X35 = X34 )
          | ( ( k1_funct_1 @ sk_B_2 @ X35 )
           != ( k1_funct_1 @ sk_B_2 @ X34 ) )
          | ~ ( r2_hidden @ X34 @ sk_A )
          | ~ ( r2_hidden @ X35 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( v2_funct_1 @ sk_B_2 )
   <= ( ~ ( v2_funct_1 @ sk_B_2 )
      & ! [X34: $i,X35: $i] :
          ( ( X35 = X34 )
          | ( ( k1_funct_1 @ sk_B_2 @ X35 )
           != ( k1_funct_1 @ sk_B_2 @ X34 ) )
          | ~ ( r2_hidden @ X34 @ sk_A )
          | ~ ( r2_hidden @ X35 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ~ ( v2_funct_1 @ sk_B_2 )
   <= ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['46'])).

thf('56',plain,
    ( ~ ! [X34: $i,X35: $i] :
          ( ( X35 = X34 )
          | ( ( k1_funct_1 @ sk_B_2 @ X35 )
           != ( k1_funct_1 @ sk_B_2 @ X34 ) )
          | ~ ( r2_hidden @ X34 @ sk_A )
          | ~ ( r2_hidden @ X35 @ sk_A ) )
    | ( v2_funct_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k1_funct_1 @ sk_B_2 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_2 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,
    ( ( k1_funct_1 @ sk_B_2 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_2 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['3','56','57'])).

thf('59',plain,
    ( ( k1_funct_1 @ sk_B_2 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_2 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['1','58'])).

thf('60',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['10','19'])).

thf('61',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ X17 ) )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X17 ) )
      | ( ( k1_funct_1 @ X17 @ X18 )
       != ( k1_funct_1 @ X17 @ X19 ) )
      | ( X18 = X19 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_2 )
      | ~ ( v1_funct_1 @ sk_B_2 )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_2 @ X0 )
       != ( k1_funct_1 @ sk_B_2 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_2 ) )
      | ~ ( v2_funct_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(demod,[status(thm)],['25','26'])).

thf('64',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['10','19'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_2 @ X0 )
       != ( k1_funct_1 @ sk_B_2 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('67',plain,
    ( ( v2_funct_1 @ sk_B_2 )
   <= ( v2_funct_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['2'])).

thf('68',plain,(
    v2_funct_1 @ sk_B_2 ),
    inference('sat_resolution*',[status(thm)],['3','56'])).

thf('69',plain,(
    v2_funct_1 @ sk_B_2 ),
    inference(simpl_trail,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_2 @ X0 )
       != ( k1_funct_1 @ sk_B_2 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_2 @ sk_C_1 )
       != ( k1_funct_1 @ sk_B_2 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_D = X0 )
      | ~ ( r2_hidden @ sk_D @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','70'])).

thf('72',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
   <= ( r2_hidden @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['72'])).

thf('74',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['72'])).

thf('75',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','56','74'])).

thf('76',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['73','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_2 @ sk_C_1 )
       != ( k1_funct_1 @ sk_B_2 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_D = X0 ) ) ),
    inference(demod,[status(thm)],['71','76'])).

thf('78',plain,
    ( ( sk_D = sk_C_1 )
    | ~ ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference(eq_res,[status(thm)],['77'])).

thf('79',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
   <= ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['46'])).

thf('80',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['46'])).

thf('81',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','56','80'])).

thf('82',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['79','81'])).

thf('83',plain,(
    sk_D = sk_C_1 ),
    inference(demod,[status(thm)],['78','82'])).

thf('84',plain,
    ( ( sk_C_1 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( sk_C_1 != sk_D )
   <= ( sk_C_1 != sk_D ) ),
    inference(split,[status(esa)],['84'])).

thf('86',plain,
    ( ( sk_C_1 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['84'])).

thf('87',plain,(
    sk_C_1 != sk_D ),
    inference('sat_resolution*',[status(thm)],['3','56','86'])).

thf('88',plain,(
    sk_C_1 != sk_D ),
    inference(simpl_trail,[status(thm)],['85','87'])).

thf('89',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['83','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KwQQwiwtQK
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:13:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.50/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.72  % Solved by: fo/fo7.sh
% 0.50/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.72  % done 403 iterations in 0.262s
% 0.50/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.72  % SZS output start Refutation
% 0.50/0.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.50/0.72  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.50/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.72  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.50/0.72  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.50/0.72  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.50/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.72  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.50/0.72  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.50/0.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.50/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.72  thf(sk_C_type, type, sk_C: $i > $i).
% 0.50/0.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.50/0.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.50/0.72  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.50/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.72  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.50/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.50/0.72  thf(sk_D_type, type, sk_D: $i).
% 0.50/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.72  thf(t77_funct_2, conjecture,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.50/0.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.50/0.72       ( ( v2_funct_1 @ B ) <=>
% 0.50/0.72         ( ![C:$i,D:$i]:
% 0.50/0.72           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.50/0.72               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.50/0.72             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.50/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.72    (~( ![A:$i,B:$i]:
% 0.50/0.72        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.50/0.72            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.50/0.72          ( ( v2_funct_1 @ B ) <=>
% 0.50/0.72            ( ![C:$i,D:$i]:
% 0.50/0.72              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.50/0.72                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.50/0.72                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.50/0.72    inference('cnf.neg', [status(esa)], [t77_funct_2])).
% 0.50/0.72  thf('0', plain,
% 0.50/0.72      ((((k1_funct_1 @ sk_B_2 @ sk_C_1) = (k1_funct_1 @ sk_B_2 @ sk_D))
% 0.50/0.72        | ~ (v2_funct_1 @ sk_B_2))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('1', plain,
% 0.50/0.72      ((((k1_funct_1 @ sk_B_2 @ sk_C_1) = (k1_funct_1 @ sk_B_2 @ sk_D)))
% 0.50/0.72         <= ((((k1_funct_1 @ sk_B_2 @ sk_C_1) = (k1_funct_1 @ sk_B_2 @ sk_D))))),
% 0.50/0.72      inference('split', [status(esa)], ['0'])).
% 0.50/0.72  thf('2', plain,
% 0.50/0.72      (![X34 : $i, X35 : $i]:
% 0.50/0.72         (((X35) = (X34))
% 0.50/0.72          | ((k1_funct_1 @ sk_B_2 @ X35) != (k1_funct_1 @ sk_B_2 @ X34))
% 0.50/0.72          | ~ (r2_hidden @ X34 @ sk_A)
% 0.50/0.72          | ~ (r2_hidden @ X35 @ sk_A)
% 0.50/0.72          | (v2_funct_1 @ sk_B_2))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('3', plain,
% 0.50/0.72      (((v2_funct_1 @ sk_B_2)) | 
% 0.50/0.72       (![X34 : $i, X35 : $i]:
% 0.50/0.72          (((X35) = (X34))
% 0.50/0.72           | ((k1_funct_1 @ sk_B_2 @ X35) != (k1_funct_1 @ sk_B_2 @ X34))
% 0.50/0.72           | ~ (r2_hidden @ X34 @ sk_A)
% 0.50/0.72           | ~ (r2_hidden @ X35 @ sk_A)))),
% 0.50/0.72      inference('split', [status(esa)], ['2'])).
% 0.50/0.72  thf('4', plain, ((v1_funct_2 @ sk_B_2 @ sk_A @ sk_A)),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf(d1_funct_2, axiom,
% 0.50/0.72    (![A:$i,B:$i,C:$i]:
% 0.50/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.72       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.50/0.72           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.50/0.72             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.50/0.72         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.50/0.72           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.50/0.72             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.50/0.72  thf(zf_stmt_1, axiom,
% 0.50/0.72    (![C:$i,B:$i,A:$i]:
% 0.50/0.72     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.50/0.72       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.50/0.72  thf('5', plain,
% 0.50/0.72      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.50/0.72         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 0.50/0.72          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 0.50/0.72          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.50/0.72  thf('6', plain,
% 0.50/0.72      ((~ (zip_tseitin_1 @ sk_B_2 @ sk_A @ sk_A)
% 0.50/0.72        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_B_2)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['4', '5'])).
% 0.50/0.72  thf('7', plain,
% 0.50/0.72      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf(redefinition_k1_relset_1, axiom,
% 0.50/0.72    (![A:$i,B:$i,C:$i]:
% 0.50/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.72       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.50/0.72  thf('8', plain,
% 0.50/0.72      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.50/0.72         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 0.50/0.72          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.50/0.72      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.50/0.72  thf('9', plain,
% 0.50/0.72      (((k1_relset_1 @ sk_A @ sk_A @ sk_B_2) = (k1_relat_1 @ sk_B_2))),
% 0.50/0.72      inference('sup-', [status(thm)], ['7', '8'])).
% 0.50/0.72  thf('10', plain,
% 0.50/0.72      ((~ (zip_tseitin_1 @ sk_B_2 @ sk_A @ sk_A)
% 0.50/0.72        | ((sk_A) = (k1_relat_1 @ sk_B_2)))),
% 0.50/0.72      inference('demod', [status(thm)], ['6', '9'])).
% 0.50/0.72  thf('11', plain,
% 0.50/0.72      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.50/0.72  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.50/0.72  thf(zf_stmt_4, axiom,
% 0.50/0.72    (![B:$i,A:$i]:
% 0.50/0.72     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.50/0.72       ( zip_tseitin_0 @ B @ A ) ))).
% 0.50/0.72  thf(zf_stmt_5, axiom,
% 0.50/0.72    (![A:$i,B:$i,C:$i]:
% 0.50/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.72       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.50/0.72         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.50/0.72           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.50/0.72             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.50/0.72  thf('12', plain,
% 0.50/0.72      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.50/0.72         (~ (zip_tseitin_0 @ X31 @ X32)
% 0.50/0.72          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 0.50/0.72          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.50/0.72  thf('13', plain,
% 0.50/0.72      (((zip_tseitin_1 @ sk_B_2 @ sk_A @ sk_A)
% 0.50/0.72        | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 0.50/0.72      inference('sup-', [status(thm)], ['11', '12'])).
% 0.50/0.72  thf('14', plain,
% 0.50/0.72      (![X26 : $i, X27 : $i]:
% 0.50/0.72         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.50/0.72  thf('15', plain,
% 0.50/0.72      (![X26 : $i, X27 : $i]:
% 0.50/0.72         ((zip_tseitin_0 @ X26 @ X27) | ((X27) != (k1_xboole_0)))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.50/0.72  thf('16', plain, (![X26 : $i]: (zip_tseitin_0 @ X26 @ k1_xboole_0)),
% 0.50/0.72      inference('simplify', [status(thm)], ['15'])).
% 0.50/0.72  thf('17', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.72         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.50/0.72      inference('sup+', [status(thm)], ['14', '16'])).
% 0.50/0.72  thf('18', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.50/0.72      inference('eq_fact', [status(thm)], ['17'])).
% 0.50/0.72  thf('19', plain, ((zip_tseitin_1 @ sk_B_2 @ sk_A @ sk_A)),
% 0.50/0.72      inference('demod', [status(thm)], ['13', '18'])).
% 0.50/0.72  thf('20', plain, (((sk_A) = (k1_relat_1 @ sk_B_2))),
% 0.50/0.72      inference('demod', [status(thm)], ['10', '19'])).
% 0.50/0.72  thf(d8_funct_1, axiom,
% 0.50/0.72    (![A:$i]:
% 0.50/0.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.50/0.72       ( ( v2_funct_1 @ A ) <=>
% 0.50/0.72         ( ![B:$i,C:$i]:
% 0.50/0.72           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.50/0.72               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.50/0.72               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.50/0.72             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.50/0.72  thf('21', plain,
% 0.50/0.72      (![X17 : $i]:
% 0.50/0.72         ((r2_hidden @ (sk_C @ X17) @ (k1_relat_1 @ X17))
% 0.50/0.72          | (v2_funct_1 @ X17)
% 0.50/0.72          | ~ (v1_funct_1 @ X17)
% 0.50/0.72          | ~ (v1_relat_1 @ X17))),
% 0.50/0.72      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.50/0.72  thf('22', plain,
% 0.50/0.72      (((r2_hidden @ (sk_C @ sk_B_2) @ sk_A)
% 0.50/0.72        | ~ (v1_relat_1 @ sk_B_2)
% 0.50/0.72        | ~ (v1_funct_1 @ sk_B_2)
% 0.50/0.72        | (v2_funct_1 @ sk_B_2))),
% 0.50/0.72      inference('sup+', [status(thm)], ['20', '21'])).
% 0.50/0.72  thf('23', plain,
% 0.50/0.72      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf(cc2_relat_1, axiom,
% 0.50/0.72    (![A:$i]:
% 0.50/0.72     ( ( v1_relat_1 @ A ) =>
% 0.50/0.72       ( ![B:$i]:
% 0.50/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.50/0.72  thf('24', plain,
% 0.50/0.72      (![X13 : $i, X14 : $i]:
% 0.50/0.72         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.50/0.72          | (v1_relat_1 @ X13)
% 0.50/0.72          | ~ (v1_relat_1 @ X14))),
% 0.50/0.72      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.50/0.72  thf('25', plain,
% 0.50/0.72      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B_2))),
% 0.50/0.72      inference('sup-', [status(thm)], ['23', '24'])).
% 0.50/0.72  thf(fc6_relat_1, axiom,
% 0.50/0.72    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.50/0.72  thf('26', plain,
% 0.50/0.72      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 0.50/0.72      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.50/0.72  thf('27', plain, ((v1_relat_1 @ sk_B_2)),
% 0.50/0.72      inference('demod', [status(thm)], ['25', '26'])).
% 0.50/0.72  thf('28', plain, ((v1_funct_1 @ sk_B_2)),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('29', plain,
% 0.50/0.72      (((r2_hidden @ (sk_C @ sk_B_2) @ sk_A) | (v2_funct_1 @ sk_B_2))),
% 0.50/0.72      inference('demod', [status(thm)], ['22', '27', '28'])).
% 0.50/0.72  thf('30', plain,
% 0.50/0.72      (![X17 : $i]:
% 0.50/0.72         (((k1_funct_1 @ X17 @ (sk_B_1 @ X17))
% 0.50/0.72            = (k1_funct_1 @ X17 @ (sk_C @ X17)))
% 0.50/0.72          | (v2_funct_1 @ X17)
% 0.50/0.72          | ~ (v1_funct_1 @ X17)
% 0.50/0.72          | ~ (v1_relat_1 @ X17))),
% 0.50/0.72      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.50/0.72  thf('31', plain,
% 0.50/0.72      ((![X34 : $i, X35 : $i]:
% 0.50/0.72          (((X35) = (X34))
% 0.50/0.72           | ((k1_funct_1 @ sk_B_2 @ X35) != (k1_funct_1 @ sk_B_2 @ X34))
% 0.50/0.72           | ~ (r2_hidden @ X34 @ sk_A)
% 0.50/0.72           | ~ (r2_hidden @ X35 @ sk_A)))
% 0.50/0.72         <= ((![X34 : $i, X35 : $i]:
% 0.50/0.72                (((X35) = (X34))
% 0.50/0.72                 | ((k1_funct_1 @ sk_B_2 @ X35) != (k1_funct_1 @ sk_B_2 @ X34))
% 0.50/0.72                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.50/0.72                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.50/0.72      inference('split', [status(esa)], ['2'])).
% 0.50/0.72  thf('32', plain,
% 0.50/0.72      ((![X0 : $i]:
% 0.50/0.72          (((k1_funct_1 @ sk_B_2 @ X0)
% 0.50/0.72             != (k1_funct_1 @ sk_B_2 @ (sk_B_1 @ sk_B_2)))
% 0.50/0.72           | ~ (v1_relat_1 @ sk_B_2)
% 0.50/0.72           | ~ (v1_funct_1 @ sk_B_2)
% 0.50/0.72           | (v2_funct_1 @ sk_B_2)
% 0.50/0.72           | ~ (r2_hidden @ X0 @ sk_A)
% 0.50/0.72           | ~ (r2_hidden @ (sk_C @ sk_B_2) @ sk_A)
% 0.50/0.72           | ((X0) = (sk_C @ sk_B_2))))
% 0.50/0.72         <= ((![X34 : $i, X35 : $i]:
% 0.50/0.72                (((X35) = (X34))
% 0.50/0.72                 | ((k1_funct_1 @ sk_B_2 @ X35) != (k1_funct_1 @ sk_B_2 @ X34))
% 0.50/0.72                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.50/0.72                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.50/0.72      inference('sup-', [status(thm)], ['30', '31'])).
% 0.50/0.72  thf('33', plain, ((v1_relat_1 @ sk_B_2)),
% 0.50/0.72      inference('demod', [status(thm)], ['25', '26'])).
% 0.50/0.72  thf('34', plain, ((v1_funct_1 @ sk_B_2)),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('35', plain,
% 0.50/0.72      ((![X0 : $i]:
% 0.50/0.72          (((k1_funct_1 @ sk_B_2 @ X0)
% 0.50/0.72             != (k1_funct_1 @ sk_B_2 @ (sk_B_1 @ sk_B_2)))
% 0.50/0.72           | (v2_funct_1 @ sk_B_2)
% 0.50/0.72           | ~ (r2_hidden @ X0 @ sk_A)
% 0.50/0.72           | ~ (r2_hidden @ (sk_C @ sk_B_2) @ sk_A)
% 0.50/0.72           | ((X0) = (sk_C @ sk_B_2))))
% 0.50/0.72         <= ((![X34 : $i, X35 : $i]:
% 0.50/0.72                (((X35) = (X34))
% 0.50/0.72                 | ((k1_funct_1 @ sk_B_2 @ X35) != (k1_funct_1 @ sk_B_2 @ X34))
% 0.50/0.72                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.50/0.72                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.50/0.72      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.50/0.72  thf('36', plain,
% 0.50/0.72      ((![X0 : $i]:
% 0.50/0.72          ((v2_funct_1 @ sk_B_2)
% 0.50/0.72           | ((X0) = (sk_C @ sk_B_2))
% 0.50/0.72           | ~ (r2_hidden @ X0 @ sk_A)
% 0.50/0.72           | (v2_funct_1 @ sk_B_2)
% 0.50/0.72           | ((k1_funct_1 @ sk_B_2 @ X0)
% 0.50/0.72               != (k1_funct_1 @ sk_B_2 @ (sk_B_1 @ sk_B_2)))))
% 0.50/0.72         <= ((![X34 : $i, X35 : $i]:
% 0.50/0.72                (((X35) = (X34))
% 0.50/0.72                 | ((k1_funct_1 @ sk_B_2 @ X35) != (k1_funct_1 @ sk_B_2 @ X34))
% 0.50/0.72                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.50/0.72                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.50/0.72      inference('sup-', [status(thm)], ['29', '35'])).
% 0.50/0.72  thf('37', plain,
% 0.50/0.72      ((![X0 : $i]:
% 0.50/0.72          (((k1_funct_1 @ sk_B_2 @ X0)
% 0.50/0.72             != (k1_funct_1 @ sk_B_2 @ (sk_B_1 @ sk_B_2)))
% 0.50/0.72           | ~ (r2_hidden @ X0 @ sk_A)
% 0.50/0.72           | ((X0) = (sk_C @ sk_B_2))
% 0.50/0.72           | (v2_funct_1 @ sk_B_2)))
% 0.50/0.72         <= ((![X34 : $i, X35 : $i]:
% 0.50/0.72                (((X35) = (X34))
% 0.50/0.72                 | ((k1_funct_1 @ sk_B_2 @ X35) != (k1_funct_1 @ sk_B_2 @ X34))
% 0.50/0.72                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.50/0.72                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.50/0.72      inference('simplify', [status(thm)], ['36'])).
% 0.50/0.72  thf('38', plain,
% 0.50/0.72      ((((v2_funct_1 @ sk_B_2)
% 0.50/0.72         | ((sk_B_1 @ sk_B_2) = (sk_C @ sk_B_2))
% 0.50/0.72         | ~ (r2_hidden @ (sk_B_1 @ sk_B_2) @ sk_A)))
% 0.50/0.72         <= ((![X34 : $i, X35 : $i]:
% 0.50/0.72                (((X35) = (X34))
% 0.50/0.72                 | ((k1_funct_1 @ sk_B_2 @ X35) != (k1_funct_1 @ sk_B_2 @ X34))
% 0.50/0.72                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.50/0.72                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.50/0.72      inference('eq_res', [status(thm)], ['37'])).
% 0.50/0.72  thf('39', plain, (((sk_A) = (k1_relat_1 @ sk_B_2))),
% 0.50/0.72      inference('demod', [status(thm)], ['10', '19'])).
% 0.50/0.72  thf('40', plain,
% 0.50/0.72      (![X17 : $i]:
% 0.50/0.72         ((r2_hidden @ (sk_B_1 @ X17) @ (k1_relat_1 @ X17))
% 0.50/0.72          | (v2_funct_1 @ X17)
% 0.50/0.72          | ~ (v1_funct_1 @ X17)
% 0.50/0.72          | ~ (v1_relat_1 @ X17))),
% 0.50/0.72      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.50/0.72  thf('41', plain,
% 0.50/0.72      (((r2_hidden @ (sk_B_1 @ sk_B_2) @ sk_A)
% 0.50/0.72        | ~ (v1_relat_1 @ sk_B_2)
% 0.50/0.72        | ~ (v1_funct_1 @ sk_B_2)
% 0.50/0.72        | (v2_funct_1 @ sk_B_2))),
% 0.50/0.72      inference('sup+', [status(thm)], ['39', '40'])).
% 0.50/0.72  thf('42', plain, ((v1_relat_1 @ sk_B_2)),
% 0.50/0.72      inference('demod', [status(thm)], ['25', '26'])).
% 0.50/0.72  thf('43', plain, ((v1_funct_1 @ sk_B_2)),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('44', plain,
% 0.50/0.72      (((r2_hidden @ (sk_B_1 @ sk_B_2) @ sk_A) | (v2_funct_1 @ sk_B_2))),
% 0.50/0.72      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.50/0.72  thf('45', plain,
% 0.50/0.72      (((((sk_B_1 @ sk_B_2) = (sk_C @ sk_B_2)) | (v2_funct_1 @ sk_B_2)))
% 0.50/0.72         <= ((![X34 : $i, X35 : $i]:
% 0.50/0.72                (((X35) = (X34))
% 0.50/0.72                 | ((k1_funct_1 @ sk_B_2 @ X35) != (k1_funct_1 @ sk_B_2 @ X34))
% 0.50/0.72                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.50/0.72                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.50/0.72      inference('clc', [status(thm)], ['38', '44'])).
% 0.50/0.72  thf('46', plain, (((r2_hidden @ sk_C_1 @ sk_A) | ~ (v2_funct_1 @ sk_B_2))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('47', plain, ((~ (v2_funct_1 @ sk_B_2)) <= (~ ((v2_funct_1 @ sk_B_2)))),
% 0.50/0.72      inference('split', [status(esa)], ['46'])).
% 0.50/0.72  thf('48', plain,
% 0.50/0.72      ((((sk_B_1 @ sk_B_2) = (sk_C @ sk_B_2)))
% 0.50/0.72         <= (~ ((v2_funct_1 @ sk_B_2)) & 
% 0.50/0.72             (![X34 : $i, X35 : $i]:
% 0.50/0.72                (((X35) = (X34))
% 0.50/0.72                 | ((k1_funct_1 @ sk_B_2 @ X35) != (k1_funct_1 @ sk_B_2 @ X34))
% 0.50/0.72                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.50/0.72                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.50/0.72      inference('sup-', [status(thm)], ['45', '47'])).
% 0.50/0.72  thf('49', plain,
% 0.50/0.72      (![X17 : $i]:
% 0.50/0.72         (((sk_B_1 @ X17) != (sk_C @ X17))
% 0.50/0.72          | (v2_funct_1 @ X17)
% 0.50/0.72          | ~ (v1_funct_1 @ X17)
% 0.50/0.72          | ~ (v1_relat_1 @ X17))),
% 0.50/0.72      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.50/0.72  thf('50', plain,
% 0.50/0.72      (((((sk_B_1 @ sk_B_2) != (sk_B_1 @ sk_B_2))
% 0.50/0.72         | ~ (v1_relat_1 @ sk_B_2)
% 0.50/0.72         | ~ (v1_funct_1 @ sk_B_2)
% 0.50/0.72         | (v2_funct_1 @ sk_B_2)))
% 0.50/0.72         <= (~ ((v2_funct_1 @ sk_B_2)) & 
% 0.50/0.72             (![X34 : $i, X35 : $i]:
% 0.50/0.72                (((X35) = (X34))
% 0.50/0.72                 | ((k1_funct_1 @ sk_B_2 @ X35) != (k1_funct_1 @ sk_B_2 @ X34))
% 0.50/0.72                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.50/0.72                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.50/0.72      inference('sup-', [status(thm)], ['48', '49'])).
% 0.50/0.72  thf('51', plain, ((v1_relat_1 @ sk_B_2)),
% 0.50/0.72      inference('demod', [status(thm)], ['25', '26'])).
% 0.50/0.72  thf('52', plain, ((v1_funct_1 @ sk_B_2)),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('53', plain,
% 0.50/0.72      (((((sk_B_1 @ sk_B_2) != (sk_B_1 @ sk_B_2)) | (v2_funct_1 @ sk_B_2)))
% 0.50/0.72         <= (~ ((v2_funct_1 @ sk_B_2)) & 
% 0.50/0.72             (![X34 : $i, X35 : $i]:
% 0.50/0.72                (((X35) = (X34))
% 0.50/0.72                 | ((k1_funct_1 @ sk_B_2 @ X35) != (k1_funct_1 @ sk_B_2 @ X34))
% 0.50/0.72                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.50/0.72                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.50/0.72      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.50/0.72  thf('54', plain,
% 0.50/0.72      (((v2_funct_1 @ sk_B_2))
% 0.50/0.72         <= (~ ((v2_funct_1 @ sk_B_2)) & 
% 0.50/0.72             (![X34 : $i, X35 : $i]:
% 0.50/0.72                (((X35) = (X34))
% 0.50/0.72                 | ((k1_funct_1 @ sk_B_2 @ X35) != (k1_funct_1 @ sk_B_2 @ X34))
% 0.50/0.72                 | ~ (r2_hidden @ X34 @ sk_A)
% 0.50/0.72                 | ~ (r2_hidden @ X35 @ sk_A))))),
% 0.50/0.72      inference('simplify', [status(thm)], ['53'])).
% 0.50/0.72  thf('55', plain, ((~ (v2_funct_1 @ sk_B_2)) <= (~ ((v2_funct_1 @ sk_B_2)))),
% 0.50/0.72      inference('split', [status(esa)], ['46'])).
% 0.50/0.72  thf('56', plain,
% 0.50/0.72      (~
% 0.50/0.72       (![X34 : $i, X35 : $i]:
% 0.50/0.72          (((X35) = (X34))
% 0.50/0.72           | ((k1_funct_1 @ sk_B_2 @ X35) != (k1_funct_1 @ sk_B_2 @ X34))
% 0.50/0.72           | ~ (r2_hidden @ X34 @ sk_A)
% 0.50/0.72           | ~ (r2_hidden @ X35 @ sk_A))) | 
% 0.50/0.72       ((v2_funct_1 @ sk_B_2))),
% 0.50/0.72      inference('sup-', [status(thm)], ['54', '55'])).
% 0.50/0.72  thf('57', plain,
% 0.50/0.72      ((((k1_funct_1 @ sk_B_2 @ sk_C_1) = (k1_funct_1 @ sk_B_2 @ sk_D))) | 
% 0.50/0.72       ~ ((v2_funct_1 @ sk_B_2))),
% 0.50/0.72      inference('split', [status(esa)], ['0'])).
% 0.50/0.72  thf('58', plain,
% 0.50/0.72      ((((k1_funct_1 @ sk_B_2 @ sk_C_1) = (k1_funct_1 @ sk_B_2 @ sk_D)))),
% 0.50/0.72      inference('sat_resolution*', [status(thm)], ['3', '56', '57'])).
% 0.50/0.72  thf('59', plain,
% 0.50/0.72      (((k1_funct_1 @ sk_B_2 @ sk_C_1) = (k1_funct_1 @ sk_B_2 @ sk_D))),
% 0.50/0.72      inference('simpl_trail', [status(thm)], ['1', '58'])).
% 0.50/0.72  thf('60', plain, (((sk_A) = (k1_relat_1 @ sk_B_2))),
% 0.50/0.72      inference('demod', [status(thm)], ['10', '19'])).
% 0.50/0.72  thf('61', plain,
% 0.50/0.72      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.50/0.72         (~ (v2_funct_1 @ X17)
% 0.50/0.72          | ~ (r2_hidden @ X18 @ (k1_relat_1 @ X17))
% 0.50/0.72          | ~ (r2_hidden @ X19 @ (k1_relat_1 @ X17))
% 0.50/0.72          | ((k1_funct_1 @ X17 @ X18) != (k1_funct_1 @ X17 @ X19))
% 0.50/0.72          | ((X18) = (X19))
% 0.50/0.72          | ~ (v1_funct_1 @ X17)
% 0.50/0.72          | ~ (v1_relat_1 @ X17))),
% 0.50/0.72      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.50/0.72  thf('62', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]:
% 0.50/0.72         (~ (r2_hidden @ X0 @ sk_A)
% 0.50/0.72          | ~ (v1_relat_1 @ sk_B_2)
% 0.50/0.72          | ~ (v1_funct_1 @ sk_B_2)
% 0.50/0.72          | ((X0) = (X1))
% 0.50/0.72          | ((k1_funct_1 @ sk_B_2 @ X0) != (k1_funct_1 @ sk_B_2 @ X1))
% 0.50/0.72          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_2))
% 0.50/0.72          | ~ (v2_funct_1 @ sk_B_2))),
% 0.50/0.72      inference('sup-', [status(thm)], ['60', '61'])).
% 0.50/0.72  thf('63', plain, ((v1_relat_1 @ sk_B_2)),
% 0.50/0.72      inference('demod', [status(thm)], ['25', '26'])).
% 0.50/0.72  thf('64', plain, ((v1_funct_1 @ sk_B_2)),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('65', plain, (((sk_A) = (k1_relat_1 @ sk_B_2))),
% 0.50/0.72      inference('demod', [status(thm)], ['10', '19'])).
% 0.50/0.72  thf('66', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]:
% 0.50/0.72         (~ (r2_hidden @ X0 @ sk_A)
% 0.50/0.72          | ((X0) = (X1))
% 0.50/0.72          | ((k1_funct_1 @ sk_B_2 @ X0) != (k1_funct_1 @ sk_B_2 @ X1))
% 0.50/0.72          | ~ (r2_hidden @ X1 @ sk_A)
% 0.50/0.72          | ~ (v2_funct_1 @ sk_B_2))),
% 0.50/0.72      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 0.50/0.72  thf('67', plain, (((v2_funct_1 @ sk_B_2)) <= (((v2_funct_1 @ sk_B_2)))),
% 0.50/0.72      inference('split', [status(esa)], ['2'])).
% 0.50/0.72  thf('68', plain, (((v2_funct_1 @ sk_B_2))),
% 0.50/0.72      inference('sat_resolution*', [status(thm)], ['3', '56'])).
% 0.50/0.72  thf('69', plain, ((v2_funct_1 @ sk_B_2)),
% 0.50/0.72      inference('simpl_trail', [status(thm)], ['67', '68'])).
% 0.50/0.72  thf('70', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]:
% 0.50/0.72         (~ (r2_hidden @ X0 @ sk_A)
% 0.50/0.72          | ((X0) = (X1))
% 0.50/0.72          | ((k1_funct_1 @ sk_B_2 @ X0) != (k1_funct_1 @ sk_B_2 @ X1))
% 0.50/0.72          | ~ (r2_hidden @ X1 @ sk_A))),
% 0.50/0.72      inference('demod', [status(thm)], ['66', '69'])).
% 0.50/0.72  thf('71', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         (((k1_funct_1 @ sk_B_2 @ sk_C_1) != (k1_funct_1 @ sk_B_2 @ X0))
% 0.50/0.72          | ~ (r2_hidden @ X0 @ sk_A)
% 0.50/0.72          | ((sk_D) = (X0))
% 0.50/0.72          | ~ (r2_hidden @ sk_D @ sk_A))),
% 0.50/0.72      inference('sup-', [status(thm)], ['59', '70'])).
% 0.50/0.72  thf('72', plain, (((r2_hidden @ sk_D @ sk_A) | ~ (v2_funct_1 @ sk_B_2))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('73', plain,
% 0.50/0.72      (((r2_hidden @ sk_D @ sk_A)) <= (((r2_hidden @ sk_D @ sk_A)))),
% 0.50/0.72      inference('split', [status(esa)], ['72'])).
% 0.50/0.72  thf('74', plain, (((r2_hidden @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_B_2))),
% 0.50/0.72      inference('split', [status(esa)], ['72'])).
% 0.50/0.72  thf('75', plain, (((r2_hidden @ sk_D @ sk_A))),
% 0.50/0.72      inference('sat_resolution*', [status(thm)], ['3', '56', '74'])).
% 0.50/0.72  thf('76', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.50/0.72      inference('simpl_trail', [status(thm)], ['73', '75'])).
% 0.50/0.72  thf('77', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         (((k1_funct_1 @ sk_B_2 @ sk_C_1) != (k1_funct_1 @ sk_B_2 @ X0))
% 0.50/0.72          | ~ (r2_hidden @ X0 @ sk_A)
% 0.50/0.72          | ((sk_D) = (X0)))),
% 0.50/0.72      inference('demod', [status(thm)], ['71', '76'])).
% 0.50/0.72  thf('78', plain, ((((sk_D) = (sk_C_1)) | ~ (r2_hidden @ sk_C_1 @ sk_A))),
% 0.50/0.72      inference('eq_res', [status(thm)], ['77'])).
% 0.50/0.72  thf('79', plain,
% 0.50/0.72      (((r2_hidden @ sk_C_1 @ sk_A)) <= (((r2_hidden @ sk_C_1 @ sk_A)))),
% 0.50/0.72      inference('split', [status(esa)], ['46'])).
% 0.50/0.72  thf('80', plain, (((r2_hidden @ sk_C_1 @ sk_A)) | ~ ((v2_funct_1 @ sk_B_2))),
% 0.50/0.72      inference('split', [status(esa)], ['46'])).
% 0.50/0.72  thf('81', plain, (((r2_hidden @ sk_C_1 @ sk_A))),
% 0.50/0.72      inference('sat_resolution*', [status(thm)], ['3', '56', '80'])).
% 0.50/0.72  thf('82', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.50/0.72      inference('simpl_trail', [status(thm)], ['79', '81'])).
% 0.50/0.72  thf('83', plain, (((sk_D) = (sk_C_1))),
% 0.50/0.72      inference('demod', [status(thm)], ['78', '82'])).
% 0.50/0.72  thf('84', plain, ((((sk_C_1) != (sk_D)) | ~ (v2_funct_1 @ sk_B_2))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('85', plain, ((((sk_C_1) != (sk_D))) <= (~ (((sk_C_1) = (sk_D))))),
% 0.50/0.72      inference('split', [status(esa)], ['84'])).
% 0.50/0.72  thf('86', plain, (~ (((sk_C_1) = (sk_D))) | ~ ((v2_funct_1 @ sk_B_2))),
% 0.50/0.72      inference('split', [status(esa)], ['84'])).
% 0.50/0.72  thf('87', plain, (~ (((sk_C_1) = (sk_D)))),
% 0.50/0.72      inference('sat_resolution*', [status(thm)], ['3', '56', '86'])).
% 0.50/0.72  thf('88', plain, (((sk_C_1) != (sk_D))),
% 0.50/0.72      inference('simpl_trail', [status(thm)], ['85', '87'])).
% 0.50/0.72  thf('89', plain, ($false),
% 0.50/0.72      inference('simplify_reflect-', [status(thm)], ['83', '88'])).
% 0.50/0.72  
% 0.50/0.72  % SZS output end Refutation
% 0.50/0.72  
% 0.50/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
