%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XKa0sKbHmO

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:53 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  100 (1382 expanded)
%              Number of leaves         :   29 ( 382 expanded)
%              Depth                    :   17
%              Number of atoms          :  670 (17005 expanded)
%              Number of equality atoms :   50 ( 385 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $i > $o )).

thf(t4_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
         => ( ( v1_funct_1 @ B )
            & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t4_funct_2])).

thf('0',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X32 ) @ X33 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X32 ) @ X34 )
      | ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

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

thf(zf_stmt_1,type,(
    zip_tseitin_5: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_5 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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
    ( ( zip_tseitin_5 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_4 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( X37
       != ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ~ ( zip_tseitin_5 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('14',plain,
    ( ( ( k1_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_5 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_5 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_B )
   <= ~ ( v1_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('20',plain,(
    v1_funct_1 @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('22',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('25',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['20','23','24'])).

thf('26',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['17','25'])).

thf('27',plain,(
    ~ ( zip_tseitin_5 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['15','26'])).

thf('28',plain,(
    ~ ( zip_tseitin_4 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['9','27'])).

thf('29',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_4 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('30',plain,(
    ~ ( zip_tseitin_4 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['9','27'])).

thf('31',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( zip_tseitin_4 @ k1_xboole_0 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( sk_A
      = ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('37',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('38',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('39',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('40',plain,(
    ! [X17: $i] :
      ( ( r1_tarski @ X17 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X17 ) @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('41',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) @ X0 )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ k1_xboole_0 ) @ sk_B )
    | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_B ) )
      = sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('44',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('45',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('47',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('48',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('49',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['43','45','46','47','48','49'])).

thf('51',plain,(
    ~ ( zip_tseitin_4 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['32','50'])).

thf('52',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( X40 != k1_xboole_0 )
      | ( X41 = k1_xboole_0 )
      | ( v1_funct_2 @ X42 @ X41 @ X40 )
      | ( X42 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('53',plain,(
    ! [X41: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X41 @ k1_xboole_0 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('55',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('56',plain,(
    ! [X41: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X41 @ k1_xboole_0 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['17','25'])).

thf('58',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('59',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['43','45','46','47','48','49'])).

thf('61',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['43','45','46','47','48','49'])).

thf('62',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_4 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('65',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_4 @ X35 @ X36 )
      | ( X36 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('66',plain,(
    ! [X35: $i] :
      ( zip_tseitin_4 @ X35 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_4 @ X1 @ X0 )
      | ( zip_tseitin_4 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['64','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( zip_tseitin_4 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['51','63','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XKa0sKbHmO
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:17:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.40/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.61  % Solved by: fo/fo7.sh
% 0.40/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.61  % done 209 iterations in 0.148s
% 0.40/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.61  % SZS output start Refutation
% 0.40/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.61  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.40/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.40/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.40/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.61  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $i > $o).
% 0.40/0.61  thf(t4_funct_2, conjecture,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.40/0.61       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.40/0.61         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.40/0.61           ( m1_subset_1 @
% 0.40/0.61             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.40/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.61    (~( ![A:$i,B:$i]:
% 0.40/0.61        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.40/0.61          ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.40/0.61            ( ( v1_funct_1 @ B ) & 
% 0.40/0.61              ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.40/0.61              ( m1_subset_1 @
% 0.40/0.61                B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )),
% 0.40/0.61    inference('cnf.neg', [status(esa)], [t4_funct_2])).
% 0.40/0.61  thf('0', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(d10_xboole_0, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.61  thf('1', plain,
% 0.40/0.61      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.61  thf('2', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.40/0.61      inference('simplify', [status(thm)], ['1'])).
% 0.40/0.61  thf(t11_relset_1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( v1_relat_1 @ C ) =>
% 0.40/0.61       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.40/0.61           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.40/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.40/0.61  thf('3', plain,
% 0.40/0.61      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.40/0.61         (~ (r1_tarski @ (k1_relat_1 @ X32) @ X33)
% 0.40/0.61          | ~ (r1_tarski @ (k2_relat_1 @ X32) @ X34)
% 0.40/0.61          | (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.40/0.61          | ~ (v1_relat_1 @ X32))),
% 0.40/0.61      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.40/0.61  thf('4', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (~ (v1_relat_1 @ X0)
% 0.40/0.61          | (m1_subset_1 @ X0 @ 
% 0.40/0.61             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.40/0.61          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.40/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.40/0.61  thf('5', plain,
% 0.40/0.61      (((m1_subset_1 @ sk_B @ 
% 0.40/0.61         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.40/0.61        | ~ (v1_relat_1 @ sk_B))),
% 0.40/0.61      inference('sup-', [status(thm)], ['0', '4'])).
% 0.40/0.61  thf('6', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('7', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_B @ 
% 0.40/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.40/0.61      inference('demod', [status(thm)], ['5', '6'])).
% 0.40/0.61  thf(d1_funct_2, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.61       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.40/0.61           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.40/0.61             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.40/0.61         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.40/0.61           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.40/0.61             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.40/0.61  thf(zf_stmt_1, type, zip_tseitin_5 : $i > $i > $i > $o).
% 0.40/0.61  thf(zf_stmt_2, axiom,
% 0.40/0.61    (![C:$i,B:$i,A:$i]:
% 0.40/0.61     ( ( zip_tseitin_5 @ C @ B @ A ) =>
% 0.40/0.61       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.40/0.61  thf(zf_stmt_3, type, zip_tseitin_4 : $i > $i > $o).
% 0.40/0.61  thf(zf_stmt_4, axiom,
% 0.40/0.61    (![B:$i,A:$i]:
% 0.40/0.61     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.40/0.61       ( zip_tseitin_4 @ B @ A ) ))).
% 0.40/0.61  thf(zf_stmt_5, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.61       ( ( ( zip_tseitin_4 @ B @ A ) => ( zip_tseitin_5 @ C @ B @ A ) ) & 
% 0.40/0.61         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.40/0.61           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.40/0.61             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.40/0.61  thf('8', plain,
% 0.40/0.61      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.40/0.61         (~ (zip_tseitin_4 @ X40 @ X41)
% 0.40/0.61          | (zip_tseitin_5 @ X42 @ X40 @ X41)
% 0.40/0.61          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.40/0.61  thf('9', plain,
% 0.40/0.61      (((zip_tseitin_5 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 0.40/0.61        | ~ (zip_tseitin_4 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.40/0.61  thf('10', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_B @ 
% 0.40/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.40/0.61      inference('demod', [status(thm)], ['5', '6'])).
% 0.40/0.61  thf(redefinition_k1_relset_1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.40/0.61  thf('11', plain,
% 0.40/0.61      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.40/0.61         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 0.40/0.61          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.40/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.40/0.61  thf('12', plain,
% 0.40/0.61      (((k1_relset_1 @ (k1_relat_1 @ sk_B) @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.40/0.61      inference('sup-', [status(thm)], ['10', '11'])).
% 0.40/0.61  thf('13', plain,
% 0.40/0.61      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.40/0.61         (((X37) != (k1_relset_1 @ X37 @ X38 @ X39))
% 0.40/0.61          | (v1_funct_2 @ X39 @ X37 @ X38)
% 0.40/0.61          | ~ (zip_tseitin_5 @ X39 @ X38 @ X37))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.40/0.61  thf('14', plain,
% 0.40/0.61      ((((k1_relat_1 @ sk_B) != (k1_relat_1 @ sk_B))
% 0.40/0.61        | ~ (zip_tseitin_5 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 0.40/0.61        | (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.40/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.40/0.61  thf('15', plain,
% 0.40/0.61      (((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.40/0.61        | ~ (zip_tseitin_5 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.40/0.61      inference('simplify', [status(thm)], ['14'])).
% 0.40/0.61  thf('16', plain,
% 0.40/0.61      ((~ (v1_funct_1 @ sk_B)
% 0.40/0.61        | ~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.40/0.61        | ~ (m1_subset_1 @ sk_B @ 
% 0.40/0.61             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('17', plain,
% 0.40/0.61      ((~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.40/0.61         <= (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.40/0.61      inference('split', [status(esa)], ['16'])).
% 0.40/0.61  thf('18', plain, ((v1_funct_1 @ sk_B)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('19', plain, ((~ (v1_funct_1 @ sk_B)) <= (~ ((v1_funct_1 @ sk_B)))),
% 0.40/0.61      inference('split', [status(esa)], ['16'])).
% 0.40/0.61  thf('20', plain, (((v1_funct_1 @ sk_B))),
% 0.40/0.61      inference('sup-', [status(thm)], ['18', '19'])).
% 0.40/0.61  thf('21', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_B @ 
% 0.40/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.40/0.61      inference('demod', [status(thm)], ['5', '6'])).
% 0.40/0.61  thf('22', plain,
% 0.40/0.61      ((~ (m1_subset_1 @ sk_B @ 
% 0.40/0.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))
% 0.40/0.61         <= (~
% 0.40/0.61             ((m1_subset_1 @ sk_B @ 
% 0.40/0.61               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))))),
% 0.40/0.61      inference('split', [status(esa)], ['16'])).
% 0.40/0.61  thf('23', plain,
% 0.40/0.61      (((m1_subset_1 @ sk_B @ 
% 0.40/0.61         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['21', '22'])).
% 0.40/0.61  thf('24', plain,
% 0.40/0.61      (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.40/0.61       ~
% 0.40/0.61       ((m1_subset_1 @ sk_B @ 
% 0.40/0.61         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))) | 
% 0.40/0.61       ~ ((v1_funct_1 @ sk_B))),
% 0.40/0.61      inference('split', [status(esa)], ['16'])).
% 0.40/0.61  thf('25', plain, (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.40/0.61      inference('sat_resolution*', [status(thm)], ['20', '23', '24'])).
% 0.40/0.61  thf('26', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.40/0.61      inference('simpl_trail', [status(thm)], ['17', '25'])).
% 0.40/0.61  thf('27', plain, (~ (zip_tseitin_5 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.40/0.61      inference('clc', [status(thm)], ['15', '26'])).
% 0.40/0.61  thf('28', plain, (~ (zip_tseitin_4 @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.40/0.61      inference('clc', [status(thm)], ['9', '27'])).
% 0.40/0.61  thf('29', plain,
% 0.40/0.61      (![X35 : $i, X36 : $i]:
% 0.40/0.61         ((zip_tseitin_4 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.40/0.61  thf('30', plain, (~ (zip_tseitin_4 @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.40/0.61      inference('clc', [status(thm)], ['9', '27'])).
% 0.40/0.61  thf('31', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['29', '30'])).
% 0.40/0.61  thf('32', plain, (~ (zip_tseitin_4 @ k1_xboole_0 @ (k1_relat_1 @ sk_B))),
% 0.40/0.61      inference('demod', [status(thm)], ['28', '31'])).
% 0.40/0.61  thf('33', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('34', plain,
% 0.40/0.61      (![X4 : $i, X6 : $i]:
% 0.40/0.61         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.40/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.61  thf('35', plain,
% 0.40/0.61      ((~ (r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))
% 0.40/0.61        | ((sk_A) = (k2_relat_1 @ sk_B)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['33', '34'])).
% 0.40/0.61  thf('36', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['29', '30'])).
% 0.40/0.61  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.40/0.61  thf('37', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.40/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.40/0.61  thf('38', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['29', '30'])).
% 0.40/0.61  thf('39', plain, (((k1_xboole_0) = (k2_relat_1 @ sk_B))),
% 0.40/0.61      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 0.40/0.61  thf(t21_relat_1, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( v1_relat_1 @ A ) =>
% 0.40/0.61       ( r1_tarski @
% 0.40/0.61         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.40/0.61  thf('40', plain,
% 0.40/0.61      (![X17 : $i]:
% 0.40/0.61         ((r1_tarski @ X17 @ 
% 0.40/0.61           (k2_zfmisc_1 @ (k1_relat_1 @ X17) @ (k2_relat_1 @ X17)))
% 0.40/0.61          | ~ (v1_relat_1 @ X17))),
% 0.40/0.61      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.40/0.61  thf('41', plain,
% 0.40/0.61      (![X4 : $i, X6 : $i]:
% 0.40/0.61         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.40/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.61  thf('42', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (v1_relat_1 @ X0)
% 0.40/0.61          | ~ (r1_tarski @ 
% 0.40/0.61               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ X0)
% 0.40/0.61          | ((k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) = (X0)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['40', '41'])).
% 0.40/0.61  thf('43', plain,
% 0.40/0.61      ((~ (r1_tarski @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ k1_xboole_0) @ sk_B)
% 0.40/0.61        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ (k2_relat_1 @ sk_B)) = (sk_B))
% 0.40/0.61        | ~ (v1_relat_1 @ sk_B))),
% 0.40/0.61      inference('sup-', [status(thm)], ['39', '42'])).
% 0.40/0.61  thf(t113_zfmisc_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.40/0.61       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.40/0.61  thf('44', plain,
% 0.40/0.61      (![X9 : $i, X10 : $i]:
% 0.40/0.61         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X10) != (k1_xboole_0)))),
% 0.40/0.61      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.40/0.61  thf('45', plain,
% 0.40/0.61      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.61      inference('simplify', [status(thm)], ['44'])).
% 0.40/0.61  thf('46', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.40/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.40/0.61  thf('47', plain, (((k1_xboole_0) = (k2_relat_1 @ sk_B))),
% 0.40/0.61      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 0.40/0.61  thf('48', plain,
% 0.40/0.61      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.61      inference('simplify', [status(thm)], ['44'])).
% 0.40/0.61  thf('49', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('50', plain, (((k1_xboole_0) = (sk_B))),
% 0.40/0.61      inference('demod', [status(thm)], ['43', '45', '46', '47', '48', '49'])).
% 0.40/0.61  thf('51', plain,
% 0.40/0.61      (~ (zip_tseitin_4 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))),
% 0.40/0.61      inference('demod', [status(thm)], ['32', '50'])).
% 0.40/0.61  thf('52', plain,
% 0.40/0.61      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.40/0.61         (((X40) != (k1_xboole_0))
% 0.40/0.61          | ((X41) = (k1_xboole_0))
% 0.40/0.61          | (v1_funct_2 @ X42 @ X41 @ X40)
% 0.40/0.61          | ((X42) != (k1_xboole_0))
% 0.40/0.61          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.40/0.61  thf('53', plain,
% 0.40/0.61      (![X41 : $i]:
% 0.40/0.61         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.40/0.61             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ k1_xboole_0)))
% 0.40/0.61          | (v1_funct_2 @ k1_xboole_0 @ X41 @ k1_xboole_0)
% 0.40/0.61          | ((X41) = (k1_xboole_0)))),
% 0.40/0.61      inference('simplify', [status(thm)], ['52'])).
% 0.40/0.61  thf('54', plain,
% 0.40/0.61      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.61      inference('simplify', [status(thm)], ['44'])).
% 0.40/0.61  thf(t4_subset_1, axiom,
% 0.40/0.61    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.40/0.61  thf('55', plain,
% 0.40/0.61      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.40/0.61      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.40/0.61  thf('56', plain,
% 0.40/0.61      (![X41 : $i]:
% 0.40/0.61         ((v1_funct_2 @ k1_xboole_0 @ X41 @ k1_xboole_0)
% 0.40/0.61          | ((X41) = (k1_xboole_0)))),
% 0.40/0.61      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.40/0.61  thf('57', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.40/0.61      inference('simpl_trail', [status(thm)], ['17', '25'])).
% 0.40/0.61  thf('58', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['29', '30'])).
% 0.40/0.61  thf('59', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ k1_xboole_0)),
% 0.40/0.61      inference('demod', [status(thm)], ['57', '58'])).
% 0.40/0.61  thf('60', plain, (((k1_xboole_0) = (sk_B))),
% 0.40/0.61      inference('demod', [status(thm)], ['43', '45', '46', '47', '48', '49'])).
% 0.40/0.61  thf('61', plain, (((k1_xboole_0) = (sk_B))),
% 0.40/0.61      inference('demod', [status(thm)], ['43', '45', '46', '47', '48', '49'])).
% 0.40/0.61  thf('62', plain,
% 0.40/0.61      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.40/0.61      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.40/0.61  thf('63', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['56', '62'])).
% 0.40/0.61  thf('64', plain,
% 0.40/0.61      (![X35 : $i, X36 : $i]:
% 0.40/0.61         ((zip_tseitin_4 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.40/0.61  thf('65', plain,
% 0.40/0.61      (![X35 : $i, X36 : $i]:
% 0.40/0.61         ((zip_tseitin_4 @ X35 @ X36) | ((X36) != (k1_xboole_0)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.40/0.61  thf('66', plain, (![X35 : $i]: (zip_tseitin_4 @ X35 @ k1_xboole_0)),
% 0.40/0.61      inference('simplify', [status(thm)], ['65'])).
% 0.40/0.61  thf('67', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.61         ((zip_tseitin_4 @ X1 @ X0) | (zip_tseitin_4 @ X0 @ X2))),
% 0.40/0.61      inference('sup+', [status(thm)], ['64', '66'])).
% 0.40/0.61  thf('68', plain, (![X0 : $i]: (zip_tseitin_4 @ X0 @ X0)),
% 0.40/0.61      inference('eq_fact', [status(thm)], ['67'])).
% 0.40/0.61  thf('69', plain, ($false),
% 0.40/0.61      inference('demod', [status(thm)], ['51', '63', '68'])).
% 0.40/0.61  
% 0.40/0.61  % SZS output end Refutation
% 0.40/0.61  
% 0.40/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
