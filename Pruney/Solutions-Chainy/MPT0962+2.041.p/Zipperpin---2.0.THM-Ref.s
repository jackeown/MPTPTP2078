%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OcKWVZya5s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:54 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   92 (1054 expanded)
%              Number of leaves         :   27 ( 292 expanded)
%              Depth                    :   17
%              Number of atoms          :  625 (13011 expanded)
%              Number of equality atoms :   42 ( 296 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X13 )
      | ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('9',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

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

thf('10',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X16
       != ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ~ ( zip_tseitin_1 @ X18 @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,
    ( ( ( k1_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( v1_funct_1 @ sk_B )
   <= ~ ( v1_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['13'])).

thf('17',plain,(
    v1_funct_1 @ sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('19',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['13'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['13'])).

thf('22',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['17','20','21'])).

thf('23',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['14','22'])).

thf('24',plain,(
    ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['12','23'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

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

thf('27',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X19 @ X20 )
      | ( zip_tseitin_1 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('28',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['12','23'])).

thf('31',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( zip_tseitin_1 @ sk_B @ k1_xboole_0 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','31'])).

thf('33',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
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
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('38',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('39',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('40',plain,(
    ! [X7: $i] :
      ( ( ( k2_relat_1 @ X7 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X7 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('41',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k1_relat_1 @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ~ ( zip_tseitin_1 @ sk_B @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','44'])).

thf('46',plain,
    ( ( k1_relat_1 @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['43'])).

thf('47',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X19 @ X20 )
      | ( zip_tseitin_1 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( zip_tseitin_0 @ ( k2_relat_1 @ sk_B ) @ k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_B @ ( k2_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('54',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('55',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( X15 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('56',plain,(
    ! [X14: $i] :
      ( zip_tseitin_0 @ X14 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['54','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['57'])).

thf('59',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('60',plain,
    ( ( k1_relat_1 @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['43'])).

thf('61',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    zip_tseitin_1 @ sk_B @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['52','53','58','59','60','61'])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['45','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OcKWVZya5s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:16:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.39/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.59  % Solved by: fo/fo7.sh
% 0.39/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.59  % done 116 iterations in 0.122s
% 0.39/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.59  % SZS output start Refutation
% 0.39/0.59  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.39/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.39/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.39/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.59  thf(t4_funct_2, conjecture,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.59       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.39/0.59         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.39/0.59           ( m1_subset_1 @
% 0.39/0.59             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.39/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.59    (~( ![A:$i,B:$i]:
% 0.39/0.59        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.59          ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.39/0.59            ( ( v1_funct_1 @ B ) & 
% 0.39/0.59              ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.39/0.59              ( m1_subset_1 @
% 0.39/0.59                B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )),
% 0.39/0.59    inference('cnf.neg', [status(esa)], [t4_funct_2])).
% 0.39/0.59  thf('0', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(d10_xboole_0, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.59  thf('1', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.39/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.59  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.39/0.59      inference('simplify', [status(thm)], ['1'])).
% 0.39/0.59  thf(t11_relset_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( v1_relat_1 @ C ) =>
% 0.39/0.59       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.39/0.59           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.39/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.39/0.59  thf('3', plain,
% 0.39/0.59      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.59         (~ (r1_tarski @ (k1_relat_1 @ X11) @ X12)
% 0.39/0.59          | ~ (r1_tarski @ (k2_relat_1 @ X11) @ X13)
% 0.39/0.59          | (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.39/0.59          | ~ (v1_relat_1 @ X11))),
% 0.39/0.59      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.39/0.59  thf('4', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (~ (v1_relat_1 @ X0)
% 0.39/0.59          | (m1_subset_1 @ X0 @ 
% 0.39/0.59             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.39/0.59          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.39/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.59  thf('5', plain,
% 0.39/0.59      (((m1_subset_1 @ sk_B @ 
% 0.39/0.59         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.39/0.59        | ~ (v1_relat_1 @ sk_B))),
% 0.39/0.59      inference('sup-', [status(thm)], ['0', '4'])).
% 0.39/0.59  thf('6', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('7', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_B @ 
% 0.39/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.39/0.59      inference('demod', [status(thm)], ['5', '6'])).
% 0.39/0.59  thf(redefinition_k1_relset_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.59       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.39/0.59  thf('8', plain,
% 0.39/0.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.59         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.39/0.59          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.39/0.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.39/0.59  thf('9', plain,
% 0.39/0.59      (((k1_relset_1 @ (k1_relat_1 @ sk_B) @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.39/0.59      inference('sup-', [status(thm)], ['7', '8'])).
% 0.39/0.59  thf(d1_funct_2, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.59       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.59           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.39/0.59             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.39/0.59         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.59           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.39/0.59             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.39/0.59  thf(zf_stmt_1, axiom,
% 0.39/0.59    (![C:$i,B:$i,A:$i]:
% 0.39/0.59     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.39/0.59       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.39/0.59  thf('10', plain,
% 0.39/0.59      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.59         (((X16) != (k1_relset_1 @ X16 @ X17 @ X18))
% 0.39/0.59          | (v1_funct_2 @ X18 @ X16 @ X17)
% 0.39/0.59          | ~ (zip_tseitin_1 @ X18 @ X17 @ X16))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.59  thf('11', plain,
% 0.39/0.59      ((((k1_relat_1 @ sk_B) != (k1_relat_1 @ sk_B))
% 0.39/0.59        | ~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 0.39/0.59        | (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['9', '10'])).
% 0.39/0.59  thf('12', plain,
% 0.39/0.59      (((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.39/0.59        | ~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.39/0.59      inference('simplify', [status(thm)], ['11'])).
% 0.39/0.59  thf('13', plain,
% 0.39/0.59      ((~ (v1_funct_1 @ sk_B)
% 0.39/0.59        | ~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.39/0.59        | ~ (m1_subset_1 @ sk_B @ 
% 0.39/0.59             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('14', plain,
% 0.39/0.59      ((~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.39/0.59         <= (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.39/0.59      inference('split', [status(esa)], ['13'])).
% 0.39/0.59  thf('15', plain, ((v1_funct_1 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('16', plain, ((~ (v1_funct_1 @ sk_B)) <= (~ ((v1_funct_1 @ sk_B)))),
% 0.39/0.59      inference('split', [status(esa)], ['13'])).
% 0.39/0.59  thf('17', plain, (((v1_funct_1 @ sk_B))),
% 0.39/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.39/0.59  thf('18', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_B @ 
% 0.39/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.39/0.59      inference('demod', [status(thm)], ['5', '6'])).
% 0.39/0.59  thf('19', plain,
% 0.39/0.59      ((~ (m1_subset_1 @ sk_B @ 
% 0.39/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))
% 0.39/0.59         <= (~
% 0.39/0.59             ((m1_subset_1 @ sk_B @ 
% 0.39/0.59               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))))),
% 0.39/0.59      inference('split', [status(esa)], ['13'])).
% 0.39/0.59  thf('20', plain,
% 0.39/0.59      (((m1_subset_1 @ sk_B @ 
% 0.39/0.59         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.59  thf('21', plain,
% 0.39/0.59      (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.39/0.59       ~
% 0.39/0.59       ((m1_subset_1 @ sk_B @ 
% 0.39/0.59         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))) | 
% 0.39/0.59       ~ ((v1_funct_1 @ sk_B))),
% 0.39/0.59      inference('split', [status(esa)], ['13'])).
% 0.39/0.59  thf('22', plain, (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.39/0.59      inference('sat_resolution*', [status(thm)], ['17', '20', '21'])).
% 0.39/0.59  thf('23', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.39/0.59      inference('simpl_trail', [status(thm)], ['14', '22'])).
% 0.39/0.59  thf('24', plain, (~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.39/0.59      inference('clc', [status(thm)], ['12', '23'])).
% 0.39/0.59  thf(zf_stmt_2, axiom,
% 0.39/0.59    (![B:$i,A:$i]:
% 0.39/0.59     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.59       ( zip_tseitin_0 @ B @ A ) ))).
% 0.39/0.59  thf('25', plain,
% 0.39/0.59      (![X14 : $i, X15 : $i]:
% 0.39/0.59         ((zip_tseitin_0 @ X14 @ X15) | ((X14) = (k1_xboole_0)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.39/0.59  thf('26', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_B @ 
% 0.39/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.39/0.59      inference('demod', [status(thm)], ['5', '6'])).
% 0.39/0.59  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.39/0.59  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.39/0.59  thf(zf_stmt_5, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.59       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.39/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.59           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.39/0.59             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.39/0.59  thf('27', plain,
% 0.39/0.59      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.39/0.59         (~ (zip_tseitin_0 @ X19 @ X20)
% 0.39/0.59          | (zip_tseitin_1 @ X21 @ X19 @ X20)
% 0.39/0.59          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19))))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.39/0.59  thf('28', plain,
% 0.39/0.59      (((zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 0.39/0.59        | ~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.39/0.59  thf('29', plain,
% 0.39/0.59      ((((sk_A) = (k1_xboole_0))
% 0.39/0.59        | (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['25', '28'])).
% 0.39/0.59  thf('30', plain, (~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.39/0.59      inference('clc', [status(thm)], ['12', '23'])).
% 0.39/0.59  thf('31', plain, (((sk_A) = (k1_xboole_0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['29', '30'])).
% 0.39/0.59  thf('32', plain,
% 0.39/0.59      (~ (zip_tseitin_1 @ sk_B @ k1_xboole_0 @ (k1_relat_1 @ sk_B))),
% 0.39/0.59      inference('demod', [status(thm)], ['24', '31'])).
% 0.39/0.59  thf('33', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('34', plain,
% 0.39/0.59      (![X0 : $i, X2 : $i]:
% 0.39/0.59         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.39/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.59  thf('35', plain,
% 0.39/0.59      ((~ (r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))
% 0.39/0.59        | ((sk_A) = (k2_relat_1 @ sk_B)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['33', '34'])).
% 0.39/0.59  thf('36', plain, (((sk_A) = (k1_xboole_0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['29', '30'])).
% 0.39/0.59  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.39/0.59  thf('37', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.39/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.39/0.59  thf('38', plain, (((sk_A) = (k1_xboole_0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['29', '30'])).
% 0.39/0.59  thf('39', plain, (((k1_xboole_0) = (k2_relat_1 @ sk_B))),
% 0.39/0.59      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 0.39/0.59  thf(t65_relat_1, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( v1_relat_1 @ A ) =>
% 0.39/0.59       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.39/0.59         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.39/0.59  thf('40', plain,
% 0.39/0.59      (![X7 : $i]:
% 0.39/0.59         (((k2_relat_1 @ X7) != (k1_xboole_0))
% 0.39/0.59          | ((k1_relat_1 @ X7) = (k1_xboole_0))
% 0.39/0.59          | ~ (v1_relat_1 @ X7))),
% 0.39/0.59      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.39/0.59  thf('41', plain,
% 0.39/0.59      ((((k1_xboole_0) != (k1_xboole_0))
% 0.39/0.59        | ~ (v1_relat_1 @ sk_B)
% 0.39/0.59        | ((k1_relat_1 @ sk_B) = (k1_xboole_0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['39', '40'])).
% 0.39/0.59  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('43', plain,
% 0.39/0.59      ((((k1_xboole_0) != (k1_xboole_0))
% 0.39/0.59        | ((k1_relat_1 @ sk_B) = (k1_xboole_0)))),
% 0.39/0.59      inference('demod', [status(thm)], ['41', '42'])).
% 0.39/0.59  thf('44', plain, (((k1_relat_1 @ sk_B) = (k1_xboole_0))),
% 0.39/0.59      inference('simplify', [status(thm)], ['43'])).
% 0.39/0.59  thf('45', plain, (~ (zip_tseitin_1 @ sk_B @ k1_xboole_0 @ k1_xboole_0)),
% 0.39/0.59      inference('demod', [status(thm)], ['32', '44'])).
% 0.39/0.59  thf('46', plain, (((k1_relat_1 @ sk_B) = (k1_xboole_0))),
% 0.39/0.59      inference('simplify', [status(thm)], ['43'])).
% 0.39/0.59  thf('47', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.39/0.59      inference('simplify', [status(thm)], ['1'])).
% 0.39/0.59  thf('48', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (~ (v1_relat_1 @ X0)
% 0.39/0.59          | (m1_subset_1 @ X0 @ 
% 0.39/0.59             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.39/0.59          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.39/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.59  thf('49', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((m1_subset_1 @ X0 @ 
% 0.39/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.39/0.59          | ~ (v1_relat_1 @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['47', '48'])).
% 0.39/0.59  thf('50', plain,
% 0.39/0.59      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.39/0.59         (~ (zip_tseitin_0 @ X19 @ X20)
% 0.39/0.59          | (zip_tseitin_1 @ X21 @ X19 @ X20)
% 0.39/0.59          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19))))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.39/0.59  thf('51', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (v1_relat_1 @ X0)
% 0.39/0.59          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.39/0.59          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['49', '50'])).
% 0.39/0.59  thf('52', plain,
% 0.39/0.59      ((~ (zip_tseitin_0 @ (k2_relat_1 @ sk_B) @ k1_xboole_0)
% 0.39/0.59        | (zip_tseitin_1 @ sk_B @ (k2_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.39/0.59        | ~ (v1_relat_1 @ sk_B))),
% 0.39/0.59      inference('sup-', [status(thm)], ['46', '51'])).
% 0.39/0.59  thf('53', plain, (((k1_xboole_0) = (k2_relat_1 @ sk_B))),
% 0.39/0.59      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 0.39/0.59  thf('54', plain,
% 0.39/0.59      (![X14 : $i, X15 : $i]:
% 0.39/0.59         ((zip_tseitin_0 @ X14 @ X15) | ((X14) = (k1_xboole_0)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.39/0.59  thf('55', plain,
% 0.39/0.59      (![X14 : $i, X15 : $i]:
% 0.39/0.59         ((zip_tseitin_0 @ X14 @ X15) | ((X15) != (k1_xboole_0)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.39/0.59  thf('56', plain, (![X14 : $i]: (zip_tseitin_0 @ X14 @ k1_xboole_0)),
% 0.39/0.59      inference('simplify', [status(thm)], ['55'])).
% 0.39/0.59  thf('57', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.59         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.39/0.59      inference('sup+', [status(thm)], ['54', '56'])).
% 0.39/0.59  thf('58', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.39/0.59      inference('eq_fact', [status(thm)], ['57'])).
% 0.39/0.59  thf('59', plain, (((k1_xboole_0) = (k2_relat_1 @ sk_B))),
% 0.39/0.59      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 0.39/0.59  thf('60', plain, (((k1_relat_1 @ sk_B) = (k1_xboole_0))),
% 0.39/0.59      inference('simplify', [status(thm)], ['43'])).
% 0.39/0.59  thf('61', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('62', plain, ((zip_tseitin_1 @ sk_B @ k1_xboole_0 @ k1_xboole_0)),
% 0.39/0.59      inference('demod', [status(thm)], ['52', '53', '58', '59', '60', '61'])).
% 0.39/0.59  thf('63', plain, ($false), inference('demod', [status(thm)], ['45', '62'])).
% 0.39/0.59  
% 0.39/0.59  % SZS output end Refutation
% 0.39/0.59  
% 0.42/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
