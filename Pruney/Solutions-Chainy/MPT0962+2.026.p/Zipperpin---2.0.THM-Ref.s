%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qOb4l3Ydm8

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:52 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 378 expanded)
%              Number of leaves         :   33 ( 116 expanded)
%              Depth                    :   16
%              Number of atoms          :  647 (4479 expanded)
%              Number of equality atoms :   35 (  95 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('40',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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

thf('41',plain,(
    ! [X10: $i,X12: $i,X14: $i,X15: $i] :
      ( ( X12
       != ( k2_relat_1 @ X10 ) )
      | ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X10 ) )
      | ( X14
       != ( k1_funct_1 @ X10 @ X15 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('42',plain,(
    ! [X10: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X10 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X10 @ X15 ) @ ( k2_relat_1 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('44',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( r1_tarski @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_funct_1 @ X0 @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_funct_1 @ sk_B @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_B ) ) ) )
      | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('48',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('51',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('52',plain,
    ( ( k1_relat_1 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_4 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('54',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_4 @ X35 @ X36 )
      | ( X36 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('55',plain,(
    ! [X35: $i] :
      ( zip_tseitin_4 @ X35 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_4 @ X1 @ X0 )
      | ( zip_tseitin_4 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['53','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( zip_tseitin_4 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['32','52','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qOb4l3Ydm8
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:24:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.29/1.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.29/1.48  % Solved by: fo/fo7.sh
% 1.29/1.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.29/1.48  % done 514 iterations in 1.018s
% 1.29/1.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.29/1.48  % SZS output start Refutation
% 1.29/1.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.29/1.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.29/1.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.29/1.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.29/1.48  thf(sk_A_type, type, sk_A: $i).
% 1.29/1.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.29/1.48  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 1.29/1.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.29/1.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.29/1.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.29/1.48  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.29/1.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.29/1.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.29/1.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.29/1.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.29/1.48  thf(sk_B_type, type, sk_B: $i).
% 1.29/1.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.29/1.48  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $i > $o).
% 1.29/1.48  thf(t4_funct_2, conjecture,
% 1.29/1.48    (![A:$i,B:$i]:
% 1.29/1.48     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.29/1.48       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.29/1.48         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 1.29/1.48           ( m1_subset_1 @
% 1.29/1.48             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 1.29/1.48  thf(zf_stmt_0, negated_conjecture,
% 1.29/1.48    (~( ![A:$i,B:$i]:
% 1.29/1.48        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.29/1.48          ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.29/1.48            ( ( v1_funct_1 @ B ) & 
% 1.29/1.48              ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 1.29/1.48              ( m1_subset_1 @
% 1.29/1.48                B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )),
% 1.29/1.48    inference('cnf.neg', [status(esa)], [t4_funct_2])).
% 1.29/1.48  thf('0', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf(d10_xboole_0, axiom,
% 1.29/1.48    (![A:$i,B:$i]:
% 1.29/1.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.29/1.48  thf('1', plain,
% 1.29/1.48      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 1.29/1.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.29/1.48  thf('2', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.29/1.48      inference('simplify', [status(thm)], ['1'])).
% 1.29/1.48  thf(t11_relset_1, axiom,
% 1.29/1.48    (![A:$i,B:$i,C:$i]:
% 1.29/1.48     ( ( v1_relat_1 @ C ) =>
% 1.29/1.48       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 1.29/1.48           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 1.29/1.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.29/1.48  thf('3', plain,
% 1.29/1.48      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.29/1.48         (~ (r1_tarski @ (k1_relat_1 @ X32) @ X33)
% 1.29/1.48          | ~ (r1_tarski @ (k2_relat_1 @ X32) @ X34)
% 1.29/1.48          | (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.29/1.48          | ~ (v1_relat_1 @ X32))),
% 1.29/1.48      inference('cnf', [status(esa)], [t11_relset_1])).
% 1.29/1.48  thf('4', plain,
% 1.29/1.48      (![X0 : $i, X1 : $i]:
% 1.29/1.48         (~ (v1_relat_1 @ X0)
% 1.29/1.48          | (m1_subset_1 @ X0 @ 
% 1.29/1.48             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 1.29/1.48          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 1.29/1.48      inference('sup-', [status(thm)], ['2', '3'])).
% 1.29/1.48  thf('5', plain,
% 1.29/1.48      (((m1_subset_1 @ sk_B @ 
% 1.29/1.48         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 1.29/1.48        | ~ (v1_relat_1 @ sk_B))),
% 1.29/1.48      inference('sup-', [status(thm)], ['0', '4'])).
% 1.29/1.48  thf('6', plain, ((v1_relat_1 @ sk_B)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('7', plain,
% 1.29/1.48      ((m1_subset_1 @ sk_B @ 
% 1.29/1.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.29/1.48      inference('demod', [status(thm)], ['5', '6'])).
% 1.29/1.48  thf(d1_funct_2, axiom,
% 1.29/1.48    (![A:$i,B:$i,C:$i]:
% 1.29/1.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.29/1.48       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.29/1.48           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.29/1.48             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.29/1.48         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.29/1.48           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.29/1.48             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.29/1.48  thf(zf_stmt_1, type, zip_tseitin_5 : $i > $i > $i > $o).
% 1.29/1.48  thf(zf_stmt_2, axiom,
% 1.29/1.48    (![C:$i,B:$i,A:$i]:
% 1.29/1.48     ( ( zip_tseitin_5 @ C @ B @ A ) =>
% 1.29/1.48       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.29/1.48  thf(zf_stmt_3, type, zip_tseitin_4 : $i > $i > $o).
% 1.29/1.48  thf(zf_stmt_4, axiom,
% 1.29/1.48    (![B:$i,A:$i]:
% 1.29/1.48     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.29/1.48       ( zip_tseitin_4 @ B @ A ) ))).
% 1.29/1.48  thf(zf_stmt_5, axiom,
% 1.29/1.48    (![A:$i,B:$i,C:$i]:
% 1.29/1.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.29/1.48       ( ( ( zip_tseitin_4 @ B @ A ) => ( zip_tseitin_5 @ C @ B @ A ) ) & 
% 1.29/1.48         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.29/1.48           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.29/1.48             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.29/1.48  thf('8', plain,
% 1.29/1.48      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.29/1.48         (~ (zip_tseitin_4 @ X40 @ X41)
% 1.29/1.48          | (zip_tseitin_5 @ X42 @ X40 @ X41)
% 1.29/1.48          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.29/1.48  thf('9', plain,
% 1.29/1.48      (((zip_tseitin_5 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 1.29/1.48        | ~ (zip_tseitin_4 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 1.29/1.48      inference('sup-', [status(thm)], ['7', '8'])).
% 1.29/1.48  thf('10', plain,
% 1.29/1.48      ((m1_subset_1 @ sk_B @ 
% 1.29/1.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.29/1.48      inference('demod', [status(thm)], ['5', '6'])).
% 1.29/1.48  thf(redefinition_k1_relset_1, axiom,
% 1.29/1.48    (![A:$i,B:$i,C:$i]:
% 1.29/1.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.29/1.48       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.29/1.48  thf('11', plain,
% 1.29/1.48      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.29/1.48         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 1.29/1.48          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 1.29/1.48      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.29/1.48  thf('12', plain,
% 1.29/1.48      (((k1_relset_1 @ (k1_relat_1 @ sk_B) @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 1.29/1.48      inference('sup-', [status(thm)], ['10', '11'])).
% 1.29/1.48  thf('13', plain,
% 1.29/1.48      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.29/1.48         (((X37) != (k1_relset_1 @ X37 @ X38 @ X39))
% 1.29/1.48          | (v1_funct_2 @ X39 @ X37 @ X38)
% 1.29/1.48          | ~ (zip_tseitin_5 @ X39 @ X38 @ X37))),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.29/1.48  thf('14', plain,
% 1.29/1.48      ((((k1_relat_1 @ sk_B) != (k1_relat_1 @ sk_B))
% 1.29/1.48        | ~ (zip_tseitin_5 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 1.29/1.48        | (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 1.29/1.48      inference('sup-', [status(thm)], ['12', '13'])).
% 1.29/1.48  thf('15', plain,
% 1.29/1.48      (((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 1.29/1.48        | ~ (zip_tseitin_5 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B)))),
% 1.29/1.48      inference('simplify', [status(thm)], ['14'])).
% 1.29/1.48  thf('16', plain,
% 1.29/1.48      ((~ (v1_funct_1 @ sk_B)
% 1.29/1.48        | ~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 1.29/1.48        | ~ (m1_subset_1 @ sk_B @ 
% 1.29/1.48             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('17', plain,
% 1.29/1.48      ((~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))
% 1.29/1.48         <= (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.29/1.48      inference('split', [status(esa)], ['16'])).
% 1.29/1.48  thf('18', plain, ((v1_funct_1 @ sk_B)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('19', plain, ((~ (v1_funct_1 @ sk_B)) <= (~ ((v1_funct_1 @ sk_B)))),
% 1.29/1.48      inference('split', [status(esa)], ['16'])).
% 1.29/1.48  thf('20', plain, (((v1_funct_1 @ sk_B))),
% 1.29/1.48      inference('sup-', [status(thm)], ['18', '19'])).
% 1.29/1.48  thf('21', plain,
% 1.29/1.48      ((m1_subset_1 @ sk_B @ 
% 1.29/1.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.29/1.48      inference('demod', [status(thm)], ['5', '6'])).
% 1.29/1.48  thf('22', plain,
% 1.29/1.48      ((~ (m1_subset_1 @ sk_B @ 
% 1.29/1.48           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))
% 1.29/1.48         <= (~
% 1.29/1.48             ((m1_subset_1 @ sk_B @ 
% 1.29/1.48               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))))),
% 1.29/1.48      inference('split', [status(esa)], ['16'])).
% 1.29/1.48  thf('23', plain,
% 1.29/1.48      (((m1_subset_1 @ sk_B @ 
% 1.29/1.48         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 1.29/1.48      inference('sup-', [status(thm)], ['21', '22'])).
% 1.29/1.48  thf('24', plain,
% 1.29/1.48      (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 1.29/1.48       ~
% 1.29/1.48       ((m1_subset_1 @ sk_B @ 
% 1.29/1.48         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))) | 
% 1.29/1.48       ~ ((v1_funct_1 @ sk_B))),
% 1.29/1.48      inference('split', [status(esa)], ['16'])).
% 1.29/1.48  thf('25', plain, (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 1.29/1.48      inference('sat_resolution*', [status(thm)], ['20', '23', '24'])).
% 1.29/1.48  thf('26', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)),
% 1.29/1.48      inference('simpl_trail', [status(thm)], ['17', '25'])).
% 1.29/1.48  thf('27', plain, (~ (zip_tseitin_5 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.29/1.48      inference('clc', [status(thm)], ['15', '26'])).
% 1.29/1.48  thf('28', plain, (~ (zip_tseitin_4 @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.29/1.48      inference('clc', [status(thm)], ['9', '27'])).
% 1.29/1.48  thf('29', plain,
% 1.29/1.48      (![X35 : $i, X36 : $i]:
% 1.29/1.48         ((zip_tseitin_4 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.29/1.48  thf('30', plain, (~ (zip_tseitin_4 @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.29/1.48      inference('clc', [status(thm)], ['9', '27'])).
% 1.29/1.48  thf('31', plain, (((sk_A) = (k1_xboole_0))),
% 1.29/1.48      inference('sup-', [status(thm)], ['29', '30'])).
% 1.29/1.48  thf('32', plain, (~ (zip_tseitin_4 @ k1_xboole_0 @ (k1_relat_1 @ sk_B))),
% 1.29/1.48      inference('demod', [status(thm)], ['28', '31'])).
% 1.29/1.48  thf('33', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('34', plain,
% 1.29/1.48      (![X4 : $i, X6 : $i]:
% 1.29/1.48         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.29/1.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.29/1.48  thf('35', plain,
% 1.29/1.48      ((~ (r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))
% 1.29/1.48        | ((sk_A) = (k2_relat_1 @ sk_B)))),
% 1.29/1.48      inference('sup-', [status(thm)], ['33', '34'])).
% 1.29/1.48  thf('36', plain, (((sk_A) = (k1_xboole_0))),
% 1.29/1.48      inference('sup-', [status(thm)], ['29', '30'])).
% 1.29/1.48  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.29/1.48  thf('37', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 1.29/1.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.29/1.48  thf('38', plain, (((sk_A) = (k1_xboole_0))),
% 1.29/1.48      inference('sup-', [status(thm)], ['29', '30'])).
% 1.29/1.48  thf('39', plain, (((k1_xboole_0) = (k2_relat_1 @ sk_B))),
% 1.29/1.48      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 1.29/1.48  thf(d3_tarski, axiom,
% 1.29/1.48    (![A:$i,B:$i]:
% 1.29/1.48     ( ( r1_tarski @ A @ B ) <=>
% 1.29/1.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.29/1.48  thf('40', plain,
% 1.29/1.48      (![X1 : $i, X3 : $i]:
% 1.29/1.48         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.29/1.48      inference('cnf', [status(esa)], [d3_tarski])).
% 1.29/1.48  thf(d5_funct_1, axiom,
% 1.29/1.48    (![A:$i]:
% 1.29/1.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.29/1.48       ( ![B:$i]:
% 1.29/1.48         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 1.29/1.48           ( ![C:$i]:
% 1.29/1.48             ( ( r2_hidden @ C @ B ) <=>
% 1.29/1.48               ( ?[D:$i]:
% 1.29/1.48                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 1.29/1.48                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 1.29/1.48  thf('41', plain,
% 1.29/1.48      (![X10 : $i, X12 : $i, X14 : $i, X15 : $i]:
% 1.29/1.48         (((X12) != (k2_relat_1 @ X10))
% 1.29/1.48          | (r2_hidden @ X14 @ X12)
% 1.29/1.48          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X10))
% 1.29/1.48          | ((X14) != (k1_funct_1 @ X10 @ X15))
% 1.29/1.48          | ~ (v1_funct_1 @ X10)
% 1.29/1.48          | ~ (v1_relat_1 @ X10))),
% 1.29/1.48      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.29/1.48  thf('42', plain,
% 1.29/1.48      (![X10 : $i, X15 : $i]:
% 1.29/1.48         (~ (v1_relat_1 @ X10)
% 1.29/1.48          | ~ (v1_funct_1 @ X10)
% 1.29/1.48          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X10))
% 1.29/1.48          | (r2_hidden @ (k1_funct_1 @ X10 @ X15) @ (k2_relat_1 @ X10)))),
% 1.29/1.48      inference('simplify', [status(thm)], ['41'])).
% 1.29/1.48  thf('43', plain,
% 1.29/1.48      (![X0 : $i, X1 : $i]:
% 1.29/1.48         ((r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 1.29/1.48          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_C @ X1 @ (k1_relat_1 @ X0))) @ 
% 1.29/1.48             (k2_relat_1 @ X0))
% 1.29/1.48          | ~ (v1_funct_1 @ X0)
% 1.29/1.48          | ~ (v1_relat_1 @ X0))),
% 1.29/1.48      inference('sup-', [status(thm)], ['40', '42'])).
% 1.29/1.48  thf(t7_ordinal1, axiom,
% 1.29/1.48    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.29/1.48  thf('44', plain,
% 1.29/1.48      (![X27 : $i, X28 : $i]:
% 1.29/1.48         (~ (r2_hidden @ X27 @ X28) | ~ (r1_tarski @ X28 @ X27))),
% 1.29/1.48      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.29/1.48  thf('45', plain,
% 1.29/1.48      (![X0 : $i, X1 : $i]:
% 1.29/1.48         (~ (v1_relat_1 @ X0)
% 1.29/1.48          | ~ (v1_funct_1 @ X0)
% 1.29/1.48          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 1.29/1.48          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 1.29/1.48               (k1_funct_1 @ X0 @ (sk_C @ X1 @ (k1_relat_1 @ X0)))))),
% 1.29/1.48      inference('sup-', [status(thm)], ['43', '44'])).
% 1.29/1.48  thf('46', plain,
% 1.29/1.48      (![X0 : $i]:
% 1.29/1.48         (~ (r1_tarski @ k1_xboole_0 @ 
% 1.29/1.48             (k1_funct_1 @ sk_B @ (sk_C @ X0 @ (k1_relat_1 @ sk_B))))
% 1.29/1.48          | (r1_tarski @ (k1_relat_1 @ sk_B) @ X0)
% 1.29/1.48          | ~ (v1_funct_1 @ sk_B)
% 1.29/1.48          | ~ (v1_relat_1 @ sk_B))),
% 1.29/1.48      inference('sup-', [status(thm)], ['39', '45'])).
% 1.29/1.48  thf('47', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 1.29/1.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.29/1.48  thf('48', plain, ((v1_funct_1 @ sk_B)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('49', plain, ((v1_relat_1 @ sk_B)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('50', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ sk_B) @ X0)),
% 1.29/1.48      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 1.29/1.48  thf(t3_xboole_1, axiom,
% 1.29/1.48    (![A:$i]:
% 1.29/1.48     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.29/1.48  thf('51', plain,
% 1.29/1.48      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ k1_xboole_0))),
% 1.29/1.48      inference('cnf', [status(esa)], [t3_xboole_1])).
% 1.29/1.48  thf('52', plain, (((k1_relat_1 @ sk_B) = (k1_xboole_0))),
% 1.29/1.48      inference('sup-', [status(thm)], ['50', '51'])).
% 1.29/1.48  thf('53', plain,
% 1.29/1.48      (![X35 : $i, X36 : $i]:
% 1.29/1.48         ((zip_tseitin_4 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.29/1.48  thf('54', plain,
% 1.29/1.48      (![X35 : $i, X36 : $i]:
% 1.29/1.48         ((zip_tseitin_4 @ X35 @ X36) | ((X36) != (k1_xboole_0)))),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.29/1.48  thf('55', plain, (![X35 : $i]: (zip_tseitin_4 @ X35 @ k1_xboole_0)),
% 1.29/1.48      inference('simplify', [status(thm)], ['54'])).
% 1.29/1.48  thf('56', plain,
% 1.29/1.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.48         ((zip_tseitin_4 @ X1 @ X0) | (zip_tseitin_4 @ X0 @ X2))),
% 1.29/1.48      inference('sup+', [status(thm)], ['53', '55'])).
% 1.29/1.48  thf('57', plain, (![X0 : $i]: (zip_tseitin_4 @ X0 @ X0)),
% 1.29/1.48      inference('eq_fact', [status(thm)], ['56'])).
% 1.29/1.48  thf('58', plain, ($false),
% 1.29/1.48      inference('demod', [status(thm)], ['32', '52', '57'])).
% 1.29/1.48  
% 1.29/1.48  % SZS output end Refutation
% 1.29/1.48  
% 1.29/1.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
