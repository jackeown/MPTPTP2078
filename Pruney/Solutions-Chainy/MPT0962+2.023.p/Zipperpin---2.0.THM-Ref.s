%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A6Sg0Hez50

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:52 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 344 expanded)
%              Number of leaves         :   32 ( 108 expanded)
%              Depth                    :   15
%              Number of atoms          :  592 (3979 expanded)
%              Number of equality atoms :   31 (  75 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X24: $i] :
      ( ( v1_funct_2 @ X24 @ ( k1_relat_1 @ X24 ) @ ( k2_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('1',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

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

thf('10',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
   <= ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['10'])).

thf('14',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X15 )
      | ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf('24',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['10'])).

thf('26',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['14','24','25'])).

thf('27',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['11','26'])).

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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('28',plain,(
    ! [X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('29',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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

thf('30',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X22 )
      | ( zip_tseitin_1 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('31',plain,
    ( ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('33',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('34',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X18
       != ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ~ ( zip_tseitin_1 @ X20 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('36',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
     != ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['11','26'])).

thf('39',plain,(
    ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['31','39'])).

thf('41',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','40'])).

thf('42',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','42'])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('48',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B_1 ) )
    | ( sk_A
      = ( k2_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k2_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','40'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('54',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','40'])).

thf('55',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['44','45','46','55','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A6Sg0Hez50
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:21:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.44/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.61  % Solved by: fo/fo7.sh
% 0.44/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.61  % done 135 iterations in 0.168s
% 0.44/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.61  % SZS output start Refutation
% 0.44/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.44/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.44/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.44/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.44/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.61  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.44/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.44/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.44/0.61  thf(t3_funct_2, axiom,
% 0.44/0.61    (![A:$i]:
% 0.44/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.44/0.61       ( ( v1_funct_1 @ A ) & 
% 0.44/0.61         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.44/0.61         ( m1_subset_1 @
% 0.44/0.61           A @ 
% 0.44/0.61           ( k1_zfmisc_1 @
% 0.44/0.61             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.44/0.61  thf('0', plain,
% 0.44/0.61      (![X24 : $i]:
% 0.44/0.61         ((v1_funct_2 @ X24 @ (k1_relat_1 @ X24) @ (k2_relat_1 @ X24))
% 0.44/0.61          | ~ (v1_funct_1 @ X24)
% 0.44/0.61          | ~ (v1_relat_1 @ X24))),
% 0.44/0.61      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.44/0.61  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.44/0.61  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.44/0.61  thf(d3_tarski, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( r1_tarski @ A @ B ) <=>
% 0.44/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.44/0.61  thf('2', plain,
% 0.44/0.61      (![X4 : $i, X6 : $i]:
% 0.44/0.61         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.44/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.61  thf(d1_xboole_0, axiom,
% 0.44/0.61    (![A:$i]:
% 0.44/0.61     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.44/0.61  thf('3', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.44/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.44/0.61  thf('4', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.44/0.61  thf('5', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.44/0.61  thf(d10_xboole_0, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.44/0.61  thf('6', plain,
% 0.44/0.61      (![X7 : $i, X9 : $i]:
% 0.44/0.61         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.44/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.44/0.61  thf('7', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.44/0.61  thf('8', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['4', '7'])).
% 0.44/0.61  thf('9', plain,
% 0.44/0.61      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['1', '8'])).
% 0.44/0.61  thf(t4_funct_2, conjecture,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.44/0.61       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.44/0.61         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.44/0.61           ( m1_subset_1 @
% 0.44/0.61             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.44/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.61    (~( ![A:$i,B:$i]:
% 0.44/0.61        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.44/0.61          ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.44/0.61            ( ( v1_funct_1 @ B ) & 
% 0.44/0.61              ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.44/0.61              ( m1_subset_1 @
% 0.44/0.61                B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )),
% 0.44/0.61    inference('cnf.neg', [status(esa)], [t4_funct_2])).
% 0.44/0.61  thf('10', plain,
% 0.44/0.61      ((~ (v1_funct_1 @ sk_B_1)
% 0.44/0.61        | ~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.44/0.61        | ~ (m1_subset_1 @ sk_B_1 @ 
% 0.44/0.61             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('11', plain,
% 0.44/0.61      ((~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.44/0.61         <= (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.44/0.61      inference('split', [status(esa)], ['10'])).
% 0.44/0.61  thf('12', plain, ((v1_funct_1 @ sk_B_1)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('13', plain, ((~ (v1_funct_1 @ sk_B_1)) <= (~ ((v1_funct_1 @ sk_B_1)))),
% 0.44/0.61      inference('split', [status(esa)], ['10'])).
% 0.44/0.61  thf('14', plain, (((v1_funct_1 @ sk_B_1))),
% 0.44/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.44/0.61  thf('15', plain, ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ sk_A)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('16', plain,
% 0.44/0.61      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 0.44/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.44/0.61  thf('17', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.44/0.61      inference('simplify', [status(thm)], ['16'])).
% 0.44/0.61  thf(t11_relset_1, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( v1_relat_1 @ C ) =>
% 0.44/0.61       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.44/0.61           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.44/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.44/0.61  thf('18', plain,
% 0.44/0.61      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.44/0.61         (~ (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 0.44/0.61          | ~ (r1_tarski @ (k2_relat_1 @ X13) @ X15)
% 0.44/0.61          | (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.44/0.61          | ~ (v1_relat_1 @ X13))),
% 0.44/0.61      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.44/0.61  thf('19', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (~ (v1_relat_1 @ X0)
% 0.44/0.61          | (m1_subset_1 @ X0 @ 
% 0.44/0.61             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.44/0.61          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.44/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.44/0.61  thf('20', plain,
% 0.44/0.61      (((m1_subset_1 @ sk_B_1 @ 
% 0.44/0.61         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))
% 0.44/0.61        | ~ (v1_relat_1 @ sk_B_1))),
% 0.44/0.61      inference('sup-', [status(thm)], ['15', '19'])).
% 0.44/0.61  thf('21', plain, ((v1_relat_1 @ sk_B_1)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('22', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_B_1 @ 
% 0.44/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.44/0.61      inference('demod', [status(thm)], ['20', '21'])).
% 0.44/0.61  thf('23', plain,
% 0.44/0.61      ((~ (m1_subset_1 @ sk_B_1 @ 
% 0.44/0.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))
% 0.44/0.61         <= (~
% 0.44/0.61             ((m1_subset_1 @ sk_B_1 @ 
% 0.44/0.61               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))))),
% 0.44/0.61      inference('split', [status(esa)], ['10'])).
% 0.44/0.61  thf('24', plain,
% 0.44/0.61      (((m1_subset_1 @ sk_B_1 @ 
% 0.44/0.61         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))),
% 0.44/0.61      inference('sup-', [status(thm)], ['22', '23'])).
% 0.44/0.61  thf('25', plain,
% 0.44/0.61      (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)) | 
% 0.44/0.61       ~
% 0.44/0.61       ((m1_subset_1 @ sk_B_1 @ 
% 0.44/0.61         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))) | 
% 0.44/0.61       ~ ((v1_funct_1 @ sk_B_1))),
% 0.44/0.61      inference('split', [status(esa)], ['10'])).
% 0.44/0.61  thf('26', plain, (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.44/0.61      inference('sat_resolution*', [status(thm)], ['14', '24', '25'])).
% 0.44/0.61  thf('27', plain, (~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.44/0.61      inference('simpl_trail', [status(thm)], ['11', '26'])).
% 0.44/0.61  thf(d1_funct_2, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.61       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.44/0.61           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.44/0.61             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.44/0.61         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.61           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.44/0.61             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.44/0.61  thf(zf_stmt_1, axiom,
% 0.44/0.61    (![B:$i,A:$i]:
% 0.44/0.61     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.61       ( zip_tseitin_0 @ B @ A ) ))).
% 0.44/0.61  thf('28', plain,
% 0.44/0.61      (![X16 : $i, X17 : $i]:
% 0.44/0.61         ((zip_tseitin_0 @ X16 @ X17) | ((X16) = (k1_xboole_0)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.61  thf('29', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_B_1 @ 
% 0.44/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.44/0.61      inference('demod', [status(thm)], ['20', '21'])).
% 0.44/0.61  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.44/0.61  thf(zf_stmt_3, axiom,
% 0.44/0.61    (![C:$i,B:$i,A:$i]:
% 0.44/0.61     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.44/0.61       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.44/0.61  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.44/0.61  thf(zf_stmt_5, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.61       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.44/0.61         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.44/0.61           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.44/0.61             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.44/0.61  thf('30', plain,
% 0.44/0.61      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.44/0.61         (~ (zip_tseitin_0 @ X21 @ X22)
% 0.44/0.61          | (zip_tseitin_1 @ X23 @ X21 @ X22)
% 0.44/0.61          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21))))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.44/0.61  thf('31', plain,
% 0.44/0.61      (((zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))
% 0.44/0.61        | ~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['29', '30'])).
% 0.44/0.61  thf('32', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_B_1 @ 
% 0.44/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.44/0.61      inference('demod', [status(thm)], ['20', '21'])).
% 0.44/0.61  thf(redefinition_k1_relset_1, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.44/0.61  thf('33', plain,
% 0.44/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.44/0.61         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 0.44/0.61          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.44/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.44/0.61  thf('34', plain,
% 0.44/0.61      (((k1_relset_1 @ (k1_relat_1 @ sk_B_1) @ sk_A @ sk_B_1)
% 0.44/0.61         = (k1_relat_1 @ sk_B_1))),
% 0.44/0.61      inference('sup-', [status(thm)], ['32', '33'])).
% 0.44/0.61  thf('35', plain,
% 0.44/0.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.44/0.61         (((X18) != (k1_relset_1 @ X18 @ X19 @ X20))
% 0.44/0.61          | (v1_funct_2 @ X20 @ X18 @ X19)
% 0.44/0.61          | ~ (zip_tseitin_1 @ X20 @ X19 @ X18))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.44/0.61  thf('36', plain,
% 0.44/0.61      ((((k1_relat_1 @ sk_B_1) != (k1_relat_1 @ sk_B_1))
% 0.44/0.61        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))
% 0.44/0.61        | (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.44/0.61      inference('sup-', [status(thm)], ['34', '35'])).
% 0.44/0.61  thf('37', plain,
% 0.44/0.61      (((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.44/0.61        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.44/0.61      inference('simplify', [status(thm)], ['36'])).
% 0.44/0.61  thf('38', plain, (~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.44/0.61      inference('simpl_trail', [status(thm)], ['11', '26'])).
% 0.44/0.61  thf('39', plain, (~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.44/0.61      inference('clc', [status(thm)], ['37', '38'])).
% 0.44/0.61  thf('40', plain, (~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.44/0.61      inference('clc', [status(thm)], ['31', '39'])).
% 0.44/0.61  thf('41', plain, (((sk_A) = (k1_xboole_0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['28', '40'])).
% 0.44/0.61  thf('42', plain,
% 0.44/0.61      (~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ k1_xboole_0)),
% 0.44/0.61      inference('demod', [status(thm)], ['27', '41'])).
% 0.44/0.61  thf('43', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ X0)
% 0.44/0.61          | ~ (v1_xboole_0 @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['9', '42'])).
% 0.44/0.61  thf('44', plain,
% 0.44/0.61      ((~ (v1_relat_1 @ sk_B_1)
% 0.44/0.61        | ~ (v1_funct_1 @ sk_B_1)
% 0.44/0.61        | ~ (v1_xboole_0 @ (k2_relat_1 @ sk_B_1)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['0', '43'])).
% 0.44/0.61  thf('45', plain, ((v1_relat_1 @ sk_B_1)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('46', plain, ((v1_funct_1 @ sk_B_1)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('47', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.44/0.61  thf('48', plain, ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ sk_A)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('49', plain,
% 0.44/0.61      (![X7 : $i, X9 : $i]:
% 0.44/0.61         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.44/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.44/0.61  thf('50', plain,
% 0.44/0.61      ((~ (r1_tarski @ sk_A @ (k2_relat_1 @ sk_B_1))
% 0.44/0.61        | ((sk_A) = (k2_relat_1 @ sk_B_1)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['48', '49'])).
% 0.44/0.61  thf('51', plain,
% 0.44/0.61      ((~ (v1_xboole_0 @ sk_A) | ((sk_A) = (k2_relat_1 @ sk_B_1)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['47', '50'])).
% 0.44/0.61  thf('52', plain, (((sk_A) = (k1_xboole_0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['28', '40'])).
% 0.44/0.61  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.44/0.61  thf('54', plain, (((sk_A) = (k1_xboole_0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['28', '40'])).
% 0.44/0.61  thf('55', plain, (((k1_xboole_0) = (k2_relat_1 @ sk_B_1))),
% 0.44/0.61      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.44/0.61  thf('56', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.44/0.61  thf('57', plain, ($false),
% 0.44/0.61      inference('demod', [status(thm)], ['44', '45', '46', '55', '56'])).
% 0.44/0.61  
% 0.44/0.61  % SZS output end Refutation
% 0.44/0.61  
% 0.44/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
