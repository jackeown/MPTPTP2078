%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Gwr7DmVSgg

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:27 EST 2020

% Result     : Theorem 3.17s
% Output     : Refutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :  210 (1692 expanded)
%              Number of leaves         :   49 ( 530 expanded)
%              Depth                    :   22
%              Number of atoms          : 1413 (25439 expanded)
%              Number of equality atoms :   90 ( 981 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t31_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v2_funct_1 @ C )
            & ( ( k2_relset_1 @ A @ B @ C )
              = B ) )
         => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
            & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
            & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('3',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v1_relat_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('4',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X30: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k2_funct_1 @ X30 )
        = ( k4_relat_1 @ X30 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k2_funct_1 @ sk_C_1 )
      = ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X31: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X31 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('20',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X11 ) @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('21',plain,(
    ! [X10: $i] :
      ( ( k2_subset_1 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('22',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('23',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('27',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( ( k1_relset_1 @ X42 @ X43 @ X41 )
        = ( k1_relat_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('31',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31'])).

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

thf('33',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( X49
       != ( k1_relset_1 @ X49 @ X50 @ X51 ) )
      | ( v1_funct_2 @ X51 @ X49 @ X50 )
      | ~ ( zip_tseitin_1 @ X51 @ X50 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('36',plain,(
    ! [X47: $i,X48: $i] :
      ( ( zip_tseitin_0 @ X47 @ X48 )
      | ( X48 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('37',plain,(
    ! [X47: $i] :
      ( zip_tseitin_0 @ X47 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

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

thf('39',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( zip_tseitin_0 @ X52 @ X53 )
      | ( zip_tseitin_1 @ X54 @ X52 @ X53 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['35','41'])).

thf('43',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('45',plain,(
    ! [X47: $i,X48: $i] :
      ( ( zip_tseitin_0 @ X47 @ X48 )
      | ( X47 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('46',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( zip_tseitin_0 @ X52 @ X53 )
      | ( zip_tseitin_1 @ X54 @ X52 @ X53 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('48',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( v1_funct_2 @ X51 @ X49 @ X50 )
      | ( X49
        = ( k1_relset_1 @ X49 @ X50 @ X51 ) )
      | ~ ( zip_tseitin_1 @ X51 @ X50 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('52',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( ( k1_relset_1 @ X42 @ X43 @ X41 )
        = ( k1_relat_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('55',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('57',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['49','56'])).

thf('58',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('59',plain,(
    ! [X34: $i] :
      ( ~ ( v2_funct_1 @ X34 )
      | ( ( k2_relat_1 @ X34 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('60',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('62',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('66',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( ( k2_relset_1 @ X45 @ X46 @ X44 )
        = ( k2_relat_1 @ X44 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('67',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['64','69'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('71',plain,(
    ! [X55: $i] :
      ( ( v1_funct_2 @ X55 @ ( k1_relat_1 @ X55 ) @ ( k2_relat_1 @ X55 ) )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('72',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ sk_B @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('74',plain,(
    ! [X34: $i] :
      ( ~ ( v2_funct_1 @ X34 )
      | ( ( k1_relat_1 @ X34 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('75',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('77',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('80',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('81',plain,(
    ! [X31: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X31 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('82',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('84',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('87',plain,(
    ! [X31: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X31 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('88',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('90',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['72','79','85','91'])).

thf('93',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','92'])).

thf('94',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('95',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('96',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['43','44','97'])).

thf('99',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('100',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('102',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('103',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('104',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C_1 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) @ sk_C_1 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = sk_C_1 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['99','104'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('106',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('107',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('109',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('110',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['106'])).

thf('111',plain,
    ( ( k1_xboole_0 = sk_C_1 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['105','107','108','109','110'])).

thf('112',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(fc14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( ( v1_xboole_0 @ ( k4_relat_1 @ A ) )
        & ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) ) )).

thf('113',plain,(
    ! [X22: $i] :
      ( ( v1_xboole_0 @ ( k4_relat_1 @ X22 ) )
      | ~ ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc14_relat_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('115',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('116',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['114','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['113','118'])).

thf('120',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['112','119'])).

thf('121',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['98','111','120'])).

thf('122',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['42','121'])).

thf('123',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('124',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['17','122','123'])).

thf('125',plain,(
    ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['10','124'])).

thf('126',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('127',plain,(
    ! [X47: $i,X48: $i] :
      ( ( zip_tseitin_0 @ X47 @ X48 )
      | ( X47 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('128',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['106'])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('131',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_xboole_0 @ X12 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('132',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['129','132'])).

thf('134',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X22: $i] :
      ( ( v1_xboole_0 @ ( k4_relat_1 @ X22 ) )
      | ~ ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc14_relat_1])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('138',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('141',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('142',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ~ ( v1_xboole_0 @ ( k4_relat_1 @ sk_C_1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['139','142'])).

thf('144',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['136','143'])).

thf('145',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B @ X0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['135','144'])).

thf('146',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('147',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('149',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['17','122','123'])).

thf('151',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['149','150'])).

thf('152',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['126','151'])).

thf('153',plain,(
    ! [X55: $i] :
      ( ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X55 ) @ ( k2_relat_1 @ X55 ) ) ) )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('154',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['152','153'])).

thf('155',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['64','69'])).

thf('156',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('157',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('158',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['154','155','156','157'])).

thf('159',plain,(
    $false ),
    inference(demod,[status(thm)],['125','158'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Gwr7DmVSgg
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.17/3.37  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.17/3.37  % Solved by: fo/fo7.sh
% 3.17/3.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.17/3.37  % done 2986 iterations in 2.906s
% 3.17/3.37  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.17/3.37  % SZS output start Refutation
% 3.17/3.37  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.17/3.37  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.17/3.37  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.17/3.37  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.17/3.37  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 3.17/3.37  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.17/3.37  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.17/3.37  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 3.17/3.37  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.17/3.37  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.17/3.37  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.17/3.37  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.17/3.37  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.17/3.37  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.17/3.37  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.17/3.37  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.17/3.37  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.17/3.37  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 3.17/3.37  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.17/3.37  thf(sk_B_type, type, sk_B: $i).
% 3.17/3.37  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.17/3.37  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.17/3.37  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.17/3.37  thf(sk_A_type, type, sk_A: $i).
% 3.17/3.37  thf(t31_funct_2, conjecture,
% 3.17/3.37    (![A:$i,B:$i,C:$i]:
% 3.17/3.37     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.17/3.37         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.17/3.37       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 3.17/3.37         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 3.17/3.37           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 3.17/3.37           ( m1_subset_1 @
% 3.17/3.37             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 3.17/3.37  thf(zf_stmt_0, negated_conjecture,
% 3.17/3.37    (~( ![A:$i,B:$i,C:$i]:
% 3.17/3.37        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.17/3.37            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.17/3.37          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 3.17/3.37            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 3.17/3.37              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 3.17/3.37              ( m1_subset_1 @
% 3.17/3.37                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 3.17/3.37    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 3.17/3.37  thf('0', plain,
% 3.17/3.37      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 3.17/3.37        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)
% 3.17/3.37        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.17/3.37             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 3.17/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.17/3.37  thf('1', plain,
% 3.17/3.37      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.17/3.37           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 3.17/3.37         <= (~
% 3.17/3.37             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.17/3.37               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.17/3.37      inference('split', [status(esa)], ['0'])).
% 3.17/3.37  thf('2', plain,
% 3.17/3.37      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.17/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.17/3.37  thf(cc1_relset_1, axiom,
% 3.17/3.37    (![A:$i,B:$i,C:$i]:
% 3.17/3.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.17/3.37       ( v1_relat_1 @ C ) ))).
% 3.17/3.37  thf('3', plain,
% 3.17/3.37      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.17/3.37         ((v1_relat_1 @ X35)
% 3.17/3.37          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 3.17/3.37      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.17/3.37  thf('4', plain, ((v1_relat_1 @ sk_C_1)),
% 3.17/3.37      inference('sup-', [status(thm)], ['2', '3'])).
% 3.17/3.37  thf(d9_funct_1, axiom,
% 3.17/3.37    (![A:$i]:
% 3.17/3.37     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.17/3.37       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 3.17/3.37  thf('5', plain,
% 3.17/3.37      (![X30 : $i]:
% 3.17/3.37         (~ (v2_funct_1 @ X30)
% 3.17/3.37          | ((k2_funct_1 @ X30) = (k4_relat_1 @ X30))
% 3.17/3.37          | ~ (v1_funct_1 @ X30)
% 3.17/3.37          | ~ (v1_relat_1 @ X30))),
% 3.17/3.37      inference('cnf', [status(esa)], [d9_funct_1])).
% 3.17/3.37  thf('6', plain,
% 3.17/3.37      ((~ (v1_funct_1 @ sk_C_1)
% 3.17/3.37        | ((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))
% 3.17/3.37        | ~ (v2_funct_1 @ sk_C_1))),
% 3.17/3.37      inference('sup-', [status(thm)], ['4', '5'])).
% 3.17/3.37  thf('7', plain, ((v1_funct_1 @ sk_C_1)),
% 3.17/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.17/3.37  thf('8', plain, ((v2_funct_1 @ sk_C_1)),
% 3.17/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.17/3.37  thf('9', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 3.17/3.37      inference('demod', [status(thm)], ['6', '7', '8'])).
% 3.17/3.37  thf('10', plain,
% 3.17/3.37      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 3.17/3.37           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 3.17/3.37         <= (~
% 3.17/3.37             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.17/3.37               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.17/3.37      inference('demod', [status(thm)], ['1', '9'])).
% 3.17/3.37  thf('11', plain, ((v1_relat_1 @ sk_C_1)),
% 3.17/3.37      inference('sup-', [status(thm)], ['2', '3'])).
% 3.17/3.37  thf(dt_k2_funct_1, axiom,
% 3.17/3.37    (![A:$i]:
% 3.17/3.37     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.17/3.37       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 3.17/3.37         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 3.17/3.37  thf('12', plain,
% 3.17/3.37      (![X31 : $i]:
% 3.17/3.37         ((v1_funct_1 @ (k2_funct_1 @ X31))
% 3.17/3.37          | ~ (v1_funct_1 @ X31)
% 3.17/3.37          | ~ (v1_relat_1 @ X31))),
% 3.17/3.37      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.17/3.37  thf('13', plain,
% 3.17/3.37      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 3.17/3.37         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 3.17/3.37      inference('split', [status(esa)], ['0'])).
% 3.17/3.37  thf('14', plain,
% 3.17/3.37      (((~ (v1_relat_1 @ sk_C_1) | ~ (v1_funct_1 @ sk_C_1)))
% 3.17/3.37         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 3.17/3.37      inference('sup-', [status(thm)], ['12', '13'])).
% 3.17/3.37  thf('15', plain, ((v1_funct_1 @ sk_C_1)),
% 3.17/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.17/3.37  thf('16', plain,
% 3.17/3.37      ((~ (v1_relat_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 3.17/3.37      inference('demod', [status(thm)], ['14', '15'])).
% 3.17/3.37  thf('17', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 3.17/3.37      inference('sup-', [status(thm)], ['11', '16'])).
% 3.17/3.37  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.17/3.37  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.17/3.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.17/3.37  thf(d3_tarski, axiom,
% 3.17/3.37    (![A:$i,B:$i]:
% 3.17/3.37     ( ( r1_tarski @ A @ B ) <=>
% 3.17/3.37       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.17/3.37  thf('19', plain,
% 3.17/3.37      (![X1 : $i, X3 : $i]:
% 3.17/3.37         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.17/3.37      inference('cnf', [status(esa)], [d3_tarski])).
% 3.17/3.37  thf(dt_k2_subset_1, axiom,
% 3.17/3.37    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 3.17/3.37  thf('20', plain,
% 3.17/3.37      (![X11 : $i]: (m1_subset_1 @ (k2_subset_1 @ X11) @ (k1_zfmisc_1 @ X11))),
% 3.17/3.37      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 3.17/3.37  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 3.17/3.37  thf('21', plain, (![X10 : $i]: ((k2_subset_1 @ X10) = (X10))),
% 3.17/3.37      inference('cnf', [status(esa)], [d4_subset_1])).
% 3.17/3.37  thf('22', plain, (![X11 : $i]: (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X11))),
% 3.17/3.37      inference('demod', [status(thm)], ['20', '21'])).
% 3.17/3.37  thf(t5_subset, axiom,
% 3.17/3.37    (![A:$i,B:$i,C:$i]:
% 3.17/3.37     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 3.17/3.37          ( v1_xboole_0 @ C ) ) ))).
% 3.17/3.37  thf('23', plain,
% 3.17/3.37      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.17/3.37         (~ (r2_hidden @ X17 @ X18)
% 3.17/3.37          | ~ (v1_xboole_0 @ X19)
% 3.17/3.37          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 3.17/3.37      inference('cnf', [status(esa)], [t5_subset])).
% 3.17/3.37  thf('24', plain,
% 3.17/3.37      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 3.17/3.37      inference('sup-', [status(thm)], ['22', '23'])).
% 3.17/3.37  thf('25', plain,
% 3.17/3.37      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.17/3.37      inference('sup-', [status(thm)], ['19', '24'])).
% 3.17/3.37  thf('26', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 3.17/3.37      inference('sup-', [status(thm)], ['18', '25'])).
% 3.17/3.37  thf(t3_subset, axiom,
% 3.17/3.37    (![A:$i,B:$i]:
% 3.17/3.37     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.17/3.37  thf('27', plain,
% 3.17/3.37      (![X14 : $i, X16 : $i]:
% 3.17/3.37         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 3.17/3.37      inference('cnf', [status(esa)], [t3_subset])).
% 3.17/3.37  thf('28', plain,
% 3.17/3.37      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.17/3.37      inference('sup-', [status(thm)], ['26', '27'])).
% 3.17/3.37  thf(redefinition_k1_relset_1, axiom,
% 3.17/3.37    (![A:$i,B:$i,C:$i]:
% 3.17/3.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.17/3.37       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.17/3.37  thf('29', plain,
% 3.17/3.37      (![X41 : $i, X42 : $i, X43 : $i]:
% 3.17/3.37         (((k1_relset_1 @ X42 @ X43 @ X41) = (k1_relat_1 @ X41))
% 3.17/3.37          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43))))),
% 3.17/3.37      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.17/3.37  thf('30', plain,
% 3.17/3.37      (![X0 : $i, X1 : $i]:
% 3.17/3.37         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 3.17/3.37      inference('sup-', [status(thm)], ['28', '29'])).
% 3.17/3.37  thf(t60_relat_1, axiom,
% 3.17/3.37    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 3.17/3.37     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 3.17/3.37  thf('31', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.17/3.37      inference('cnf', [status(esa)], [t60_relat_1])).
% 3.17/3.37  thf('32', plain,
% 3.17/3.37      (![X0 : $i, X1 : $i]:
% 3.17/3.37         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.17/3.37      inference('demod', [status(thm)], ['30', '31'])).
% 3.17/3.37  thf(d1_funct_2, axiom,
% 3.17/3.37    (![A:$i,B:$i,C:$i]:
% 3.17/3.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.17/3.37       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.17/3.37           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.17/3.37             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.17/3.37         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.17/3.37           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.17/3.37             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.17/3.37  thf(zf_stmt_1, axiom,
% 3.17/3.37    (![C:$i,B:$i,A:$i]:
% 3.17/3.37     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.17/3.37       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.17/3.37  thf('33', plain,
% 3.17/3.37      (![X49 : $i, X50 : $i, X51 : $i]:
% 3.17/3.37         (((X49) != (k1_relset_1 @ X49 @ X50 @ X51))
% 3.17/3.37          | (v1_funct_2 @ X51 @ X49 @ X50)
% 3.17/3.37          | ~ (zip_tseitin_1 @ X51 @ X50 @ X49))),
% 3.17/3.37      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.17/3.37  thf('34', plain,
% 3.17/3.37      (![X0 : $i, X1 : $i]:
% 3.17/3.37         (((X1) != (k1_xboole_0))
% 3.17/3.37          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 3.17/3.37          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 3.17/3.37      inference('sup-', [status(thm)], ['32', '33'])).
% 3.17/3.37  thf('35', plain,
% 3.17/3.37      (![X0 : $i]:
% 3.17/3.37         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 3.17/3.37          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 3.17/3.37      inference('simplify', [status(thm)], ['34'])).
% 3.17/3.37  thf(zf_stmt_2, axiom,
% 3.17/3.37    (![B:$i,A:$i]:
% 3.17/3.37     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.17/3.37       ( zip_tseitin_0 @ B @ A ) ))).
% 3.17/3.37  thf('36', plain,
% 3.17/3.37      (![X47 : $i, X48 : $i]:
% 3.17/3.37         ((zip_tseitin_0 @ X47 @ X48) | ((X48) != (k1_xboole_0)))),
% 3.17/3.37      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.17/3.37  thf('37', plain, (![X47 : $i]: (zip_tseitin_0 @ X47 @ k1_xboole_0)),
% 3.17/3.37      inference('simplify', [status(thm)], ['36'])).
% 3.17/3.37  thf('38', plain,
% 3.17/3.37      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.17/3.37      inference('sup-', [status(thm)], ['26', '27'])).
% 3.17/3.37  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.17/3.37  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.17/3.37  thf(zf_stmt_5, axiom,
% 3.17/3.37    (![A:$i,B:$i,C:$i]:
% 3.17/3.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.17/3.37       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.17/3.37         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.17/3.37           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.17/3.37             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.17/3.37  thf('39', plain,
% 3.17/3.37      (![X52 : $i, X53 : $i, X54 : $i]:
% 3.17/3.37         (~ (zip_tseitin_0 @ X52 @ X53)
% 3.17/3.37          | (zip_tseitin_1 @ X54 @ X52 @ X53)
% 3.17/3.37          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X52))))),
% 3.17/3.37      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.17/3.37  thf('40', plain,
% 3.17/3.37      (![X0 : $i, X1 : $i]:
% 3.17/3.37         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 3.17/3.37      inference('sup-', [status(thm)], ['38', '39'])).
% 3.17/3.37  thf('41', plain,
% 3.17/3.37      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 3.17/3.37      inference('sup-', [status(thm)], ['37', '40'])).
% 3.17/3.37  thf('42', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 3.17/3.37      inference('demod', [status(thm)], ['35', '41'])).
% 3.17/3.37  thf('43', plain,
% 3.17/3.37      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))
% 3.17/3.37         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 3.17/3.37      inference('split', [status(esa)], ['0'])).
% 3.17/3.37  thf('44', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 3.17/3.37      inference('demod', [status(thm)], ['6', '7', '8'])).
% 3.17/3.37  thf('45', plain,
% 3.17/3.37      (![X47 : $i, X48 : $i]:
% 3.17/3.37         ((zip_tseitin_0 @ X47 @ X48) | ((X47) = (k1_xboole_0)))),
% 3.17/3.37      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.17/3.37  thf('46', plain,
% 3.17/3.37      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.17/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.17/3.37  thf('47', plain,
% 3.17/3.37      (![X52 : $i, X53 : $i, X54 : $i]:
% 3.17/3.37         (~ (zip_tseitin_0 @ X52 @ X53)
% 3.17/3.37          | (zip_tseitin_1 @ X54 @ X52 @ X53)
% 3.17/3.37          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X52))))),
% 3.17/3.37      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.17/3.37  thf('48', plain,
% 3.17/3.37      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 3.17/3.37        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 3.17/3.37      inference('sup-', [status(thm)], ['46', '47'])).
% 3.17/3.37  thf('49', plain,
% 3.17/3.37      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 3.17/3.37      inference('sup-', [status(thm)], ['45', '48'])).
% 3.17/3.37  thf('50', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 3.17/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.17/3.37  thf('51', plain,
% 3.17/3.37      (![X49 : $i, X50 : $i, X51 : $i]:
% 3.17/3.37         (~ (v1_funct_2 @ X51 @ X49 @ X50)
% 3.17/3.37          | ((X49) = (k1_relset_1 @ X49 @ X50 @ X51))
% 3.17/3.37          | ~ (zip_tseitin_1 @ X51 @ X50 @ X49))),
% 3.17/3.37      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.17/3.37  thf('52', plain,
% 3.17/3.37      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 3.17/3.37        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 3.17/3.37      inference('sup-', [status(thm)], ['50', '51'])).
% 3.17/3.37  thf('53', plain,
% 3.17/3.37      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.17/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.17/3.37  thf('54', plain,
% 3.17/3.37      (![X41 : $i, X42 : $i, X43 : $i]:
% 3.17/3.37         (((k1_relset_1 @ X42 @ X43 @ X41) = (k1_relat_1 @ X41))
% 3.17/3.37          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43))))),
% 3.17/3.37      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.17/3.37  thf('55', plain,
% 3.17/3.37      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 3.17/3.37      inference('sup-', [status(thm)], ['53', '54'])).
% 3.17/3.37  thf('56', plain,
% 3.17/3.37      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 3.17/3.37        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 3.17/3.37      inference('demod', [status(thm)], ['52', '55'])).
% 3.17/3.37  thf('57', plain,
% 3.17/3.37      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 3.17/3.37      inference('sup-', [status(thm)], ['49', '56'])).
% 3.17/3.37  thf('58', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 3.17/3.37      inference('demod', [status(thm)], ['6', '7', '8'])).
% 3.17/3.37  thf(t55_funct_1, axiom,
% 3.17/3.37    (![A:$i]:
% 3.17/3.37     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.17/3.37       ( ( v2_funct_1 @ A ) =>
% 3.17/3.37         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 3.17/3.37           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 3.17/3.37  thf('59', plain,
% 3.17/3.37      (![X34 : $i]:
% 3.17/3.37         (~ (v2_funct_1 @ X34)
% 3.17/3.37          | ((k2_relat_1 @ X34) = (k1_relat_1 @ (k2_funct_1 @ X34)))
% 3.17/3.37          | ~ (v1_funct_1 @ X34)
% 3.17/3.37          | ~ (v1_relat_1 @ X34))),
% 3.17/3.37      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.17/3.37  thf('60', plain,
% 3.17/3.37      ((((k2_relat_1 @ sk_C_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 3.17/3.37        | ~ (v1_relat_1 @ sk_C_1)
% 3.17/3.37        | ~ (v1_funct_1 @ sk_C_1)
% 3.17/3.37        | ~ (v2_funct_1 @ sk_C_1))),
% 3.17/3.37      inference('sup+', [status(thm)], ['58', '59'])).
% 3.17/3.37  thf('61', plain, ((v1_relat_1 @ sk_C_1)),
% 3.17/3.37      inference('sup-', [status(thm)], ['2', '3'])).
% 3.17/3.37  thf('62', plain, ((v1_funct_1 @ sk_C_1)),
% 3.17/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.17/3.37  thf('63', plain, ((v2_funct_1 @ sk_C_1)),
% 3.17/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.17/3.37  thf('64', plain,
% 3.17/3.37      (((k2_relat_1 @ sk_C_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 3.17/3.37      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 3.17/3.37  thf('65', plain,
% 3.17/3.37      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.17/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.17/3.37  thf(redefinition_k2_relset_1, axiom,
% 3.17/3.37    (![A:$i,B:$i,C:$i]:
% 3.17/3.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.17/3.37       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.17/3.37  thf('66', plain,
% 3.17/3.37      (![X44 : $i, X45 : $i, X46 : $i]:
% 3.17/3.37         (((k2_relset_1 @ X45 @ X46 @ X44) = (k2_relat_1 @ X44))
% 3.17/3.37          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46))))),
% 3.17/3.37      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.17/3.37  thf('67', plain,
% 3.17/3.37      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 3.17/3.37      inference('sup-', [status(thm)], ['65', '66'])).
% 3.17/3.37  thf('68', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))),
% 3.17/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.17/3.37  thf('69', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 3.17/3.37      inference('sup+', [status(thm)], ['67', '68'])).
% 3.17/3.37  thf('70', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 3.17/3.37      inference('demod', [status(thm)], ['64', '69'])).
% 3.17/3.37  thf(t3_funct_2, axiom,
% 3.17/3.37    (![A:$i]:
% 3.17/3.37     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.17/3.37       ( ( v1_funct_1 @ A ) & 
% 3.17/3.37         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 3.17/3.37         ( m1_subset_1 @
% 3.17/3.37           A @ 
% 3.17/3.37           ( k1_zfmisc_1 @
% 3.17/3.37             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 3.17/3.37  thf('71', plain,
% 3.17/3.37      (![X55 : $i]:
% 3.17/3.37         ((v1_funct_2 @ X55 @ (k1_relat_1 @ X55) @ (k2_relat_1 @ X55))
% 3.17/3.37          | ~ (v1_funct_1 @ X55)
% 3.17/3.37          | ~ (v1_relat_1 @ X55))),
% 3.17/3.37      inference('cnf', [status(esa)], [t3_funct_2])).
% 3.17/3.37  thf('72', plain,
% 3.17/3.37      (((v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ sk_B @ 
% 3.17/3.37         (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 3.17/3.37        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 3.17/3.37        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C_1)))),
% 3.17/3.37      inference('sup+', [status(thm)], ['70', '71'])).
% 3.17/3.37  thf('73', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 3.17/3.37      inference('demod', [status(thm)], ['6', '7', '8'])).
% 3.17/3.37  thf('74', plain,
% 3.17/3.37      (![X34 : $i]:
% 3.17/3.37         (~ (v2_funct_1 @ X34)
% 3.17/3.37          | ((k1_relat_1 @ X34) = (k2_relat_1 @ (k2_funct_1 @ X34)))
% 3.17/3.37          | ~ (v1_funct_1 @ X34)
% 3.17/3.37          | ~ (v1_relat_1 @ X34))),
% 3.17/3.37      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.17/3.37  thf('75', plain,
% 3.17/3.37      ((((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 3.17/3.37        | ~ (v1_relat_1 @ sk_C_1)
% 3.17/3.37        | ~ (v1_funct_1 @ sk_C_1)
% 3.17/3.37        | ~ (v2_funct_1 @ sk_C_1))),
% 3.17/3.37      inference('sup+', [status(thm)], ['73', '74'])).
% 3.17/3.37  thf('76', plain, ((v1_relat_1 @ sk_C_1)),
% 3.17/3.37      inference('sup-', [status(thm)], ['2', '3'])).
% 3.17/3.37  thf('77', plain, ((v1_funct_1 @ sk_C_1)),
% 3.17/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.17/3.37  thf('78', plain, ((v2_funct_1 @ sk_C_1)),
% 3.17/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.17/3.37  thf('79', plain,
% 3.17/3.37      (((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 3.17/3.37      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 3.17/3.37  thf('80', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 3.17/3.37      inference('demod', [status(thm)], ['6', '7', '8'])).
% 3.17/3.37  thf('81', plain,
% 3.17/3.37      (![X31 : $i]:
% 3.17/3.37         ((v1_relat_1 @ (k2_funct_1 @ X31))
% 3.17/3.37          | ~ (v1_funct_1 @ X31)
% 3.17/3.37          | ~ (v1_relat_1 @ X31))),
% 3.17/3.37      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.17/3.37  thf('82', plain,
% 3.17/3.37      (((v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 3.17/3.37        | ~ (v1_relat_1 @ sk_C_1)
% 3.17/3.37        | ~ (v1_funct_1 @ sk_C_1))),
% 3.17/3.37      inference('sup+', [status(thm)], ['80', '81'])).
% 3.17/3.37  thf('83', plain, ((v1_relat_1 @ sk_C_1)),
% 3.17/3.37      inference('sup-', [status(thm)], ['2', '3'])).
% 3.17/3.37  thf('84', plain, ((v1_funct_1 @ sk_C_1)),
% 3.17/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.17/3.37  thf('85', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 3.17/3.37      inference('demod', [status(thm)], ['82', '83', '84'])).
% 3.17/3.37  thf('86', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 3.17/3.37      inference('demod', [status(thm)], ['6', '7', '8'])).
% 3.17/3.37  thf('87', plain,
% 3.17/3.37      (![X31 : $i]:
% 3.17/3.37         ((v1_funct_1 @ (k2_funct_1 @ X31))
% 3.17/3.37          | ~ (v1_funct_1 @ X31)
% 3.17/3.37          | ~ (v1_relat_1 @ X31))),
% 3.17/3.37      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.17/3.37  thf('88', plain,
% 3.17/3.37      (((v1_funct_1 @ (k4_relat_1 @ sk_C_1))
% 3.17/3.37        | ~ (v1_relat_1 @ sk_C_1)
% 3.17/3.37        | ~ (v1_funct_1 @ sk_C_1))),
% 3.17/3.37      inference('sup+', [status(thm)], ['86', '87'])).
% 3.17/3.37  thf('89', plain, ((v1_relat_1 @ sk_C_1)),
% 3.17/3.37      inference('sup-', [status(thm)], ['2', '3'])).
% 3.17/3.37  thf('90', plain, ((v1_funct_1 @ sk_C_1)),
% 3.17/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.17/3.37  thf('91', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C_1))),
% 3.17/3.37      inference('demod', [status(thm)], ['88', '89', '90'])).
% 3.17/3.37  thf('92', plain,
% 3.17/3.37      ((v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ sk_B @ (k1_relat_1 @ sk_C_1))),
% 3.17/3.37      inference('demod', [status(thm)], ['72', '79', '85', '91'])).
% 3.17/3.37  thf('93', plain,
% 3.17/3.37      (((v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ sk_B @ sk_A)
% 3.17/3.37        | ((sk_B) = (k1_xboole_0)))),
% 3.17/3.37      inference('sup+', [status(thm)], ['57', '92'])).
% 3.17/3.37  thf('94', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 3.17/3.37      inference('demod', [status(thm)], ['6', '7', '8'])).
% 3.17/3.37  thf('95', plain,
% 3.17/3.37      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))
% 3.17/3.37         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 3.17/3.37      inference('split', [status(esa)], ['0'])).
% 3.17/3.37  thf('96', plain,
% 3.17/3.37      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ sk_B @ sk_A))
% 3.17/3.37         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 3.17/3.37      inference('sup-', [status(thm)], ['94', '95'])).
% 3.17/3.37  thf('97', plain,
% 3.17/3.37      ((((sk_B) = (k1_xboole_0)))
% 3.17/3.37         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 3.17/3.37      inference('sup-', [status(thm)], ['93', '96'])).
% 3.17/3.37  thf('98', plain,
% 3.17/3.37      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ k1_xboole_0 @ sk_A))
% 3.17/3.37         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 3.17/3.37      inference('demod', [status(thm)], ['43', '44', '97'])).
% 3.17/3.37  thf('99', plain,
% 3.17/3.37      ((((sk_B) = (k1_xboole_0)))
% 3.17/3.37         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 3.17/3.37      inference('sup-', [status(thm)], ['93', '96'])).
% 3.17/3.37  thf('100', plain,
% 3.17/3.37      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.17/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.17/3.37  thf('101', plain,
% 3.17/3.37      (![X14 : $i, X15 : $i]:
% 3.17/3.37         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 3.17/3.37      inference('cnf', [status(esa)], [t3_subset])).
% 3.17/3.37  thf('102', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 3.17/3.37      inference('sup-', [status(thm)], ['100', '101'])).
% 3.17/3.37  thf(d10_xboole_0, axiom,
% 3.17/3.37    (![A:$i,B:$i]:
% 3.17/3.37     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.17/3.37  thf('103', plain,
% 3.17/3.37      (![X4 : $i, X6 : $i]:
% 3.17/3.37         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 3.17/3.37      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.17/3.37  thf('104', plain,
% 3.17/3.37      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C_1)
% 3.17/3.37        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 3.17/3.37      inference('sup-', [status(thm)], ['102', '103'])).
% 3.17/3.37  thf('105', plain,
% 3.17/3.37      (((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0) @ sk_C_1)
% 3.17/3.37         | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1))))
% 3.17/3.37         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 3.17/3.37      inference('sup-', [status(thm)], ['99', '104'])).
% 3.17/3.37  thf(t113_zfmisc_1, axiom,
% 3.17/3.37    (![A:$i,B:$i]:
% 3.17/3.37     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.17/3.37       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.17/3.37  thf('106', plain,
% 3.17/3.37      (![X8 : $i, X9 : $i]:
% 3.17/3.37         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 3.17/3.37      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.17/3.37  thf('107', plain,
% 3.17/3.37      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 3.17/3.37      inference('simplify', [status(thm)], ['106'])).
% 3.17/3.37  thf('108', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 3.17/3.37      inference('sup-', [status(thm)], ['18', '25'])).
% 3.17/3.37  thf('109', plain,
% 3.17/3.37      ((((sk_B) = (k1_xboole_0)))
% 3.17/3.37         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 3.17/3.37      inference('sup-', [status(thm)], ['93', '96'])).
% 3.17/3.37  thf('110', plain,
% 3.17/3.37      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 3.17/3.37      inference('simplify', [status(thm)], ['106'])).
% 3.17/3.37  thf('111', plain,
% 3.17/3.37      ((((k1_xboole_0) = (sk_C_1)))
% 3.17/3.37         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 3.17/3.37      inference('demod', [status(thm)], ['105', '107', '108', '109', '110'])).
% 3.17/3.37  thf('112', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.17/3.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.17/3.37  thf(fc14_relat_1, axiom,
% 3.17/3.37    (![A:$i]:
% 3.17/3.37     ( ( v1_xboole_0 @ A ) =>
% 3.17/3.37       ( ( v1_xboole_0 @ ( k4_relat_1 @ A ) ) & 
% 3.17/3.37         ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) ))).
% 3.17/3.37  thf('113', plain,
% 3.17/3.37      (![X22 : $i]:
% 3.17/3.37         ((v1_xboole_0 @ (k4_relat_1 @ X22)) | ~ (v1_xboole_0 @ X22))),
% 3.17/3.37      inference('cnf', [status(esa)], [fc14_relat_1])).
% 3.17/3.37  thf('114', plain,
% 3.17/3.37      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.17/3.37      inference('sup-', [status(thm)], ['19', '24'])).
% 3.17/3.37  thf('115', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 3.17/3.37      inference('sup-', [status(thm)], ['18', '25'])).
% 3.17/3.37  thf('116', plain,
% 3.17/3.37      (![X4 : $i, X6 : $i]:
% 3.17/3.37         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 3.17/3.37      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.17/3.37  thf('117', plain,
% 3.17/3.37      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 3.17/3.37      inference('sup-', [status(thm)], ['115', '116'])).
% 3.17/3.37  thf('118', plain,
% 3.17/3.37      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 3.17/3.37      inference('sup-', [status(thm)], ['114', '117'])).
% 3.17/3.37  thf('119', plain,
% 3.17/3.37      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k4_relat_1 @ X0) = (k1_xboole_0)))),
% 3.17/3.37      inference('sup-', [status(thm)], ['113', '118'])).
% 3.17/3.37  thf('120', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.17/3.37      inference('sup-', [status(thm)], ['112', '119'])).
% 3.17/3.37  thf('121', plain,
% 3.17/3.37      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A))
% 3.17/3.37         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 3.17/3.37      inference('demod', [status(thm)], ['98', '111', '120'])).
% 3.17/3.37  thf('122', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))),
% 3.17/3.37      inference('sup-', [status(thm)], ['42', '121'])).
% 3.17/3.37  thf('123', plain,
% 3.17/3.37      (~
% 3.17/3.37       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.17/3.37         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 3.17/3.37       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)) | 
% 3.17/3.37       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 3.17/3.37      inference('split', [status(esa)], ['0'])).
% 3.17/3.37  thf('124', plain,
% 3.17/3.37      (~
% 3.17/3.37       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.17/3.37         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 3.17/3.37      inference('sat_resolution*', [status(thm)], ['17', '122', '123'])).
% 3.17/3.37  thf('125', plain,
% 3.17/3.37      (~ (m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 3.17/3.37          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.17/3.37      inference('simpl_trail', [status(thm)], ['10', '124'])).
% 3.17/3.37  thf('126', plain,
% 3.17/3.37      (((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 3.17/3.37      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 3.17/3.37  thf('127', plain,
% 3.17/3.37      (![X47 : $i, X48 : $i]:
% 3.17/3.37         ((zip_tseitin_0 @ X47 @ X48) | ((X47) = (k1_xboole_0)))),
% 3.17/3.37      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.17/3.37  thf('128', plain,
% 3.17/3.37      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 3.17/3.37      inference('simplify', [status(thm)], ['106'])).
% 3.17/3.37  thf('129', plain,
% 3.17/3.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.17/3.37         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 3.17/3.37      inference('sup+', [status(thm)], ['127', '128'])).
% 3.17/3.37  thf('130', plain,
% 3.17/3.37      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.17/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.17/3.37  thf(cc1_subset_1, axiom,
% 3.17/3.37    (![A:$i]:
% 3.17/3.37     ( ( v1_xboole_0 @ A ) =>
% 3.17/3.37       ( ![B:$i]:
% 3.17/3.37         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 3.17/3.37  thf('131', plain,
% 3.17/3.37      (![X12 : $i, X13 : $i]:
% 3.17/3.37         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 3.17/3.37          | (v1_xboole_0 @ X12)
% 3.17/3.37          | ~ (v1_xboole_0 @ X13))),
% 3.17/3.37      inference('cnf', [status(esa)], [cc1_subset_1])).
% 3.17/3.37  thf('132', plain,
% 3.17/3.37      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C_1))),
% 3.17/3.37      inference('sup-', [status(thm)], ['130', '131'])).
% 3.17/3.37  thf('133', plain,
% 3.17/3.37      (![X0 : $i]:
% 3.17/3.37         (~ (v1_xboole_0 @ k1_xboole_0)
% 3.17/3.37          | (zip_tseitin_0 @ sk_B @ X0)
% 3.17/3.37          | (v1_xboole_0 @ sk_C_1))),
% 3.17/3.37      inference('sup-', [status(thm)], ['129', '132'])).
% 3.17/3.37  thf('134', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.17/3.37      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.17/3.37  thf('135', plain,
% 3.17/3.37      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ sk_C_1))),
% 3.17/3.37      inference('demod', [status(thm)], ['133', '134'])).
% 3.17/3.37  thf('136', plain,
% 3.17/3.37      (![X22 : $i]:
% 3.17/3.37         ((v1_xboole_0 @ (k4_relat_1 @ X22)) | ~ (v1_xboole_0 @ X22))),
% 3.17/3.37      inference('cnf', [status(esa)], [fc14_relat_1])).
% 3.17/3.37  thf('137', plain,
% 3.17/3.37      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.17/3.37      inference('sup-', [status(thm)], ['19', '24'])).
% 3.17/3.37  thf('138', plain,
% 3.17/3.37      (![X14 : $i, X16 : $i]:
% 3.17/3.37         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 3.17/3.37      inference('cnf', [status(esa)], [t3_subset])).
% 3.17/3.37  thf('139', plain,
% 3.17/3.37      (![X0 : $i, X1 : $i]:
% 3.17/3.37         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 3.17/3.37      inference('sup-', [status(thm)], ['137', '138'])).
% 3.17/3.37  thf('140', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 3.17/3.37      inference('demod', [status(thm)], ['6', '7', '8'])).
% 3.17/3.37  thf('141', plain,
% 3.17/3.37      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.17/3.37           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 3.17/3.37         <= (~
% 3.17/3.37             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.17/3.37               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.17/3.37      inference('split', [status(esa)], ['0'])).
% 3.17/3.37  thf('142', plain,
% 3.17/3.37      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 3.17/3.37           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 3.17/3.37         <= (~
% 3.17/3.37             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.17/3.37               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.17/3.37      inference('sup-', [status(thm)], ['140', '141'])).
% 3.17/3.37  thf('143', plain,
% 3.17/3.37      ((~ (v1_xboole_0 @ (k4_relat_1 @ sk_C_1)))
% 3.17/3.37         <= (~
% 3.17/3.37             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.17/3.37               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.17/3.37      inference('sup-', [status(thm)], ['139', '142'])).
% 3.17/3.37  thf('144', plain,
% 3.17/3.37      ((~ (v1_xboole_0 @ sk_C_1))
% 3.17/3.37         <= (~
% 3.17/3.37             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.17/3.37               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.17/3.37      inference('sup-', [status(thm)], ['136', '143'])).
% 3.17/3.37  thf('145', plain,
% 3.17/3.37      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 3.17/3.37         <= (~
% 3.17/3.37             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.17/3.37               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.17/3.37      inference('sup-', [status(thm)], ['135', '144'])).
% 3.17/3.37  thf('146', plain,
% 3.17/3.37      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 3.17/3.37        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 3.17/3.37      inference('sup-', [status(thm)], ['46', '47'])).
% 3.17/3.37  thf('147', plain,
% 3.17/3.37      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))
% 3.17/3.37         <= (~
% 3.17/3.37             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.17/3.37               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.17/3.37      inference('sup-', [status(thm)], ['145', '146'])).
% 3.17/3.37  thf('148', plain,
% 3.17/3.37      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 3.17/3.37        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 3.17/3.37      inference('demod', [status(thm)], ['52', '55'])).
% 3.17/3.37  thf('149', plain,
% 3.17/3.37      ((((sk_A) = (k1_relat_1 @ sk_C_1)))
% 3.17/3.37         <= (~
% 3.17/3.37             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.17/3.37               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 3.17/3.37      inference('sup-', [status(thm)], ['147', '148'])).
% 3.17/3.37  thf('150', plain,
% 3.17/3.37      (~
% 3.17/3.37       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 3.17/3.37         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 3.17/3.37      inference('sat_resolution*', [status(thm)], ['17', '122', '123'])).
% 3.17/3.37  thf('151', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 3.17/3.37      inference('simpl_trail', [status(thm)], ['149', '150'])).
% 3.17/3.37  thf('152', plain, (((sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 3.17/3.37      inference('demod', [status(thm)], ['126', '151'])).
% 3.17/3.37  thf('153', plain,
% 3.17/3.37      (![X55 : $i]:
% 3.17/3.37         ((m1_subset_1 @ X55 @ 
% 3.17/3.37           (k1_zfmisc_1 @ 
% 3.17/3.37            (k2_zfmisc_1 @ (k1_relat_1 @ X55) @ (k2_relat_1 @ X55))))
% 3.17/3.37          | ~ (v1_funct_1 @ X55)
% 3.17/3.37          | ~ (v1_relat_1 @ X55))),
% 3.17/3.37      inference('cnf', [status(esa)], [t3_funct_2])).
% 3.17/3.37  thf('154', plain,
% 3.17/3.37      (((m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 3.17/3.37         (k1_zfmisc_1 @ 
% 3.17/3.37          (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_C_1)) @ sk_A)))
% 3.17/3.37        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 3.17/3.37        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C_1)))),
% 3.17/3.37      inference('sup+', [status(thm)], ['152', '153'])).
% 3.17/3.37  thf('155', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 3.17/3.37      inference('demod', [status(thm)], ['64', '69'])).
% 3.17/3.37  thf('156', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 3.17/3.37      inference('demod', [status(thm)], ['82', '83', '84'])).
% 3.17/3.37  thf('157', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C_1))),
% 3.17/3.37      inference('demod', [status(thm)], ['88', '89', '90'])).
% 3.17/3.37  thf('158', plain,
% 3.17/3.37      ((m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 3.17/3.37        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.17/3.37      inference('demod', [status(thm)], ['154', '155', '156', '157'])).
% 3.17/3.37  thf('159', plain, ($false), inference('demod', [status(thm)], ['125', '158'])).
% 3.17/3.37  
% 3.17/3.37  % SZS output end Refutation
% 3.17/3.37  
% 3.17/3.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
