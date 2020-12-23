%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1029+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QGHaAwWKel

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:05 EST 2020

% Result     : Theorem 55.42s
% Output     : Refutation 55.42s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 123 expanded)
%              Number of leaves         :   26 (  49 expanded)
%              Depth                    :   16
%              Number of atoms          :  386 (1004 expanded)
%              Number of equality atoms :   54 ( 122 expanded)
%              Maximal formula depth    :   14 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_C_110_type,type,(
    sk_C_110: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_16_type,type,(
    sk_A_16: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_99_type,type,(
    sk_B_99: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t132_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ ( C @ ( A @ B ) ) )
          & ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) ) )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( v1_partfun1 @ ( C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) ) )
       => ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ ( C @ ( A @ B ) ) )
            & ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) ) )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( v1_partfun1 @ ( C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t132_funct_2])).

thf('0',plain,(
    ~ ( v1_partfun1 @ ( sk_C_110 @ sk_A_16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_B_99 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ ( C @ ( A @ B ) ) ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ ( C @ A ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X4650: $i,X4651: $i,X4652: $i] :
      ( ~ ( m1_subset_1 @ ( X4650 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X4651 @ X4652 ) ) ) ) )
      | ( v1_partfun1 @ ( X4650 @ X4651 ) )
      | ~ ( v1_funct_2 @ ( X4650 @ ( X4651 @ X4652 ) ) )
      | ~ ( v1_funct_1 @ X4650 )
      | ( v1_xboole_0 @ X4652 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('3',plain,
    ( ( v1_xboole_0 @ sk_B_99 )
    | ~ ( v1_funct_1 @ sk_C_110 )
    | ~ ( v1_funct_2 @ ( sk_C_110 @ ( sk_A_16 @ sk_B_99 ) ) )
    | ( v1_partfun1 @ ( sk_C_110 @ sk_A_16 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_C_110 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ ( sk_C_110 @ ( sk_A_16 @ sk_B_99 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v1_xboole_0 @ sk_B_99 )
    | ( v1_partfun1 @ ( sk_C_110 @ sk_A_16 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('7',plain,(
    ! [X392: $i,X393: $i] :
      ( ~ ( v1_xboole_0 @ X392 )
      | ~ ( v1_xboole_0 @ X393 )
      | ( X392 = X393 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('8',plain,
    ( ( sk_B_99 != k1_xboole_0 )
    | ( sk_A_16 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('9',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('10',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('11',plain,
    ( ( sk_B_99 != o_0_0_xboole_0 )
    | ( sk_A_16 = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,
    ( ( sk_B_99 != o_0_0_xboole_0 )
   <= ( sk_B_99 != o_0_0_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ( sk_A_16 = o_0_0_xboole_0 )
   <= ( sk_A_16 = o_0_0_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('14',plain,(
    ~ ( v1_partfun1 @ ( sk_C_110 @ sk_A_16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ~ ( v1_partfun1 @ ( sk_C_110 @ o_0_0_xboole_0 ) )
   <= ( sk_A_16 = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_A_16 = o_0_0_xboole_0 )
   <= ( sk_A_16 = o_0_0_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('17',plain,(
    m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_B_99 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( o_0_0_xboole_0 @ sk_B_99 ) ) ) ) )
   <= ( sk_A_16 = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( A @ ( k1_zfmisc_1 @ B ) ) )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('19',plain,(
    ! [X1964: $i,X1965: $i] :
      ( ( r1_tarski @ ( X1964 @ X1965 ) )
      | ~ ( m1_subset_1 @ ( X1964 @ ( k1_zfmisc_1 @ X1965 ) ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,
    ( ( r1_tarski @ ( sk_C_110 @ ( k2_zfmisc_1 @ ( o_0_0_xboole_0 @ sk_B_99 ) ) ) )
   <= ( sk_A_16 = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('21',plain,(
    ! [X1104: $i,X1105: $i] :
      ( ( ( k2_zfmisc_1 @ ( X1104 @ X1105 ) )
        = k1_xboole_0 )
      | ( X1104 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('22',plain,(
    ! [X1105: $i] :
      ( ( k2_zfmisc_1 @ ( k1_xboole_0 @ X1105 ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('24',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('25',plain,(
    ! [X1105: $i] :
      ( ( k2_zfmisc_1 @ ( o_0_0_xboole_0 @ X1105 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ( r1_tarski @ ( sk_C_110 @ o_0_0_xboole_0 ) )
   <= ( sk_A_16 = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['20','25'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ ( A @ k1_xboole_0 ) )
     => ( A = k1_xboole_0 ) ) )).

thf('27',plain,(
    ! [X245: $i] :
      ( ( X245 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X245 @ k1_xboole_0 ) ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('28',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('29',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('30',plain,(
    ! [X245: $i] :
      ( ( X245 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X245 @ o_0_0_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( sk_C_110 = o_0_0_xboole_0 )
   <= ( sk_A_16 = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('32',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('33',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('34',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('35',plain,
    ( ( k6_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['32','33','34'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('36',plain,(
    ! [X4755: $i] :
      ( ( k6_partfun1 @ X4755 )
      = ( k6_relat_1 @ X4755 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('37',plain,
    ( ( k6_partfun1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['35','36'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ A ) ) ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A @ A ) ) ) )).

thf('38',plain,(
    ! [X4688: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X4688 @ X4688 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('39',plain,(
    v1_partfun1 @ ( o_0_0_xboole_0 @ o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    sk_A_16 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['15','31','39'])).

thf('41',plain,
    ( ( sk_B_99 != o_0_0_xboole_0 )
    | ( sk_A_16 = o_0_0_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('42',plain,(
    sk_B_99 != o_0_0_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['40','41'])).

thf('43',plain,(
    sk_B_99 != o_0_0_xboole_0 ),
    inference(simpl_trail,[status(thm)],['12','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0 != o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_B_99 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','43'])).

thf('45',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_99 ) ),
    inference(simplify,[status(thm)],['44'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('46',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('47',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('48',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ sk_B_99 ) ),
    inference('simplify_reflect+',[status(thm)],['45','48'])).

thf('50',plain,(
    v1_partfun1 @ ( sk_C_110 @ sk_A_16 ) ),
    inference(clc,[status(thm)],['6','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['0','50'])).

%------------------------------------------------------------------------------
