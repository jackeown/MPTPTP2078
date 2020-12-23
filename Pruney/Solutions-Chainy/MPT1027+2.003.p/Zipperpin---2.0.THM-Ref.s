%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3lBZwiMX6e

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:55 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 861 expanded)
%              Number of leaves         :   30 ( 249 expanded)
%              Depth                    :   17
%              Number of atoms          :  646 (9888 expanded)
%              Number of equality atoms :   48 ( 443 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('3',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

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

thf(zf_stmt_0,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X22 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X21: $i] :
      ( zip_tseitin_0 @ X21 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf(t130_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( k1_relset_1 @ A @ B @ C )
          = A )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( k1_relset_1 @ A @ B @ C )
            = A )
         => ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ B )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t130_funct_2])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

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

thf('11',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('12',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('14',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X23
       != ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
   <= ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('20',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
   <= ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['17'])).

thf('21',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['17'])).

thf('24',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['17'])).

thf('26',plain,(
    ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['21','24','25'])).

thf('27',plain,(
    ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['18','26'])).

thf('28',plain,(
    ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['16','27'])).

thf('29',plain,(
    ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['12','28'])).

thf('30',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','29'])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('31',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X11 @ X12 ) )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X26 != k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( v1_funct_2 @ X28 @ X27 @ X26 )
      | ( X28 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('35',plain,(
    ! [X27: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X27 @ k1_xboole_0 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('37',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( X0 = k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('40',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('41',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('45',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X11 @ X12 ) )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf('46',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('47',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_xboole_0 @ X13 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('48',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X0 = sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X0 @ X2 )
      | ( X0 = sk_C_1 )
      | ( zip_tseitin_0 @ sk_B_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( sk_B_1 = sk_C_1 ) ) ),
    inference(eq_fact,[status(thm)],['55'])).

thf('57',plain,(
    ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['12','28'])).

thf('58',plain,(
    sk_B_1 = sk_C_1 ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['40','58'])).

thf('60',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['12','28'])).

thf('62',plain,(
    sk_B_1 = sk_C_1 ),
    inference('sup-',[status(thm)],['56','57'])).

thf('63',plain,(
    ~ ( zip_tseitin_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['60','63'])).

thf('66',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['59','64','65'])).

thf('67',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','66'])).

thf('68',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('69',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','69'])).

thf('71',plain,(
    ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['18','26'])).

thf('72',plain,(
    sk_B_1 = sk_C_1 ),
    inference('sup-',[status(thm)],['56','57'])).

thf('73',plain,(
    ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['60','63'])).

thf('75',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['60','63'])).

thf('76',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['70','76'])).

thf('78',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['30','77','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3lBZwiMX6e
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:39:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.44/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.69  % Solved by: fo/fo7.sh
% 0.44/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.69  % done 190 iterations in 0.234s
% 0.44/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.69  % SZS output start Refutation
% 0.44/0.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.69  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.44/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.44/0.69  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.44/0.69  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.44/0.69  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.44/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.69  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.44/0.69  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.44/0.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.69  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.69  thf(d3_tarski, axiom,
% 0.44/0.69    (![A:$i,B:$i]:
% 0.44/0.69     ( ( r1_tarski @ A @ B ) <=>
% 0.44/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.44/0.69  thf('0', plain,
% 0.44/0.69      (![X4 : $i, X6 : $i]:
% 0.44/0.69         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.44/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.69  thf(d1_xboole_0, axiom,
% 0.44/0.69    (![A:$i]:
% 0.44/0.69     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.44/0.69  thf('1', plain,
% 0.44/0.69      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.44/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.44/0.69  thf('2', plain,
% 0.44/0.69      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.69      inference('sup-', [status(thm)], ['0', '1'])).
% 0.44/0.69  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.44/0.69  thf('3', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.44/0.69      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.44/0.69  thf(d10_xboole_0, axiom,
% 0.44/0.69    (![A:$i,B:$i]:
% 0.44/0.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.44/0.69  thf('4', plain,
% 0.44/0.69      (![X7 : $i, X9 : $i]:
% 0.44/0.69         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.44/0.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.44/0.69  thf('5', plain,
% 0.44/0.69      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['3', '4'])).
% 0.44/0.69  thf('6', plain,
% 0.44/0.69      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['2', '5'])).
% 0.44/0.69  thf(d1_funct_2, axiom,
% 0.44/0.69    (![A:$i,B:$i,C:$i]:
% 0.44/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.69       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.44/0.69           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.44/0.69             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.44/0.69         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.69           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.44/0.69             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.44/0.69  thf(zf_stmt_0, axiom,
% 0.44/0.69    (![B:$i,A:$i]:
% 0.44/0.69     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.69       ( zip_tseitin_0 @ B @ A ) ))).
% 0.44/0.69  thf('7', plain,
% 0.44/0.69      (![X21 : $i, X22 : $i]:
% 0.44/0.69         ((zip_tseitin_0 @ X21 @ X22) | ((X22) != (k1_xboole_0)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('8', plain, (![X21 : $i]: (zip_tseitin_0 @ X21 @ k1_xboole_0)),
% 0.44/0.69      inference('simplify', [status(thm)], ['7'])).
% 0.44/0.69  thf('9', plain,
% 0.44/0.69      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.69      inference('sup+', [status(thm)], ['6', '8'])).
% 0.44/0.69  thf(t130_funct_2, conjecture,
% 0.44/0.69    (![A:$i,B:$i,C:$i]:
% 0.44/0.69     ( ( ( v1_funct_1 @ C ) & 
% 0.44/0.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.69       ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.44/0.69         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.44/0.69           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ))).
% 0.44/0.69  thf(zf_stmt_1, negated_conjecture,
% 0.44/0.69    (~( ![A:$i,B:$i,C:$i]:
% 0.44/0.69        ( ( ( v1_funct_1 @ C ) & 
% 0.44/0.69            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.69          ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.44/0.69            ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.44/0.69              ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )),
% 0.44/0.69    inference('cnf.neg', [status(esa)], [t130_funct_2])).
% 0.44/0.69  thf('10', plain,
% 0.44/0.69      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.69  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.44/0.69  thf(zf_stmt_3, axiom,
% 0.44/0.69    (![C:$i,B:$i,A:$i]:
% 0.44/0.69     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.44/0.69       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.44/0.69  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.44/0.69  thf(zf_stmt_5, axiom,
% 0.44/0.69    (![A:$i,B:$i,C:$i]:
% 0.44/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.69       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.44/0.69         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.44/0.69           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.44/0.69             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.44/0.69  thf('11', plain,
% 0.44/0.69      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.44/0.69         (~ (zip_tseitin_0 @ X26 @ X27)
% 0.44/0.69          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 0.44/0.69          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.44/0.69  thf('12', plain,
% 0.44/0.69      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 0.44/0.69        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.44/0.69      inference('sup-', [status(thm)], ['10', '11'])).
% 0.44/0.69  thf('13', plain, (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (sk_A))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.69  thf('14', plain,
% 0.44/0.69      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.44/0.69         (((X23) != (k1_relset_1 @ X23 @ X24 @ X25))
% 0.44/0.69          | (v1_funct_2 @ X25 @ X23 @ X24)
% 0.44/0.69          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.44/0.69  thf('15', plain,
% 0.44/0.69      ((((sk_A) != (sk_A))
% 0.44/0.69        | ~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 0.44/0.69        | (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1))),
% 0.44/0.69      inference('sup-', [status(thm)], ['13', '14'])).
% 0.44/0.69  thf('16', plain,
% 0.44/0.69      (((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 0.44/0.69        | ~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A))),
% 0.44/0.69      inference('simplify', [status(thm)], ['15'])).
% 0.44/0.69  thf('17', plain,
% 0.44/0.69      ((~ (v1_funct_1 @ sk_C_1)
% 0.44/0.69        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 0.44/0.69        | ~ (m1_subset_1 @ sk_C_1 @ 
% 0.44/0.69             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.69  thf('18', plain,
% 0.44/0.69      ((~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1))
% 0.44/0.69         <= (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 0.44/0.69      inference('split', [status(esa)], ['17'])).
% 0.44/0.69  thf('19', plain, ((v1_funct_1 @ sk_C_1)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.69  thf('20', plain, ((~ (v1_funct_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ sk_C_1)))),
% 0.44/0.69      inference('split', [status(esa)], ['17'])).
% 0.44/0.69  thf('21', plain, (((v1_funct_1 @ sk_C_1))),
% 0.44/0.69      inference('sup-', [status(thm)], ['19', '20'])).
% 0.44/0.69  thf('22', plain,
% 0.44/0.69      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.69  thf('23', plain,
% 0.44/0.69      ((~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))
% 0.44/0.69         <= (~
% 0.44/0.69             ((m1_subset_1 @ sk_C_1 @ 
% 0.44/0.69               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))))),
% 0.44/0.69      inference('split', [status(esa)], ['17'])).
% 0.44/0.69  thf('24', plain,
% 0.44/0.69      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))),
% 0.44/0.69      inference('sup-', [status(thm)], ['22', '23'])).
% 0.44/0.69  thf('25', plain,
% 0.44/0.69      (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)) | 
% 0.44/0.69       ~
% 0.44/0.69       ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))) | 
% 0.44/0.69       ~ ((v1_funct_1 @ sk_C_1))),
% 0.44/0.69      inference('split', [status(esa)], ['17'])).
% 0.44/0.69  thf('26', plain, (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1))),
% 0.44/0.69      inference('sat_resolution*', [status(thm)], ['21', '24', '25'])).
% 0.44/0.69  thf('27', plain, (~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 0.44/0.69      inference('simpl_trail', [status(thm)], ['18', '26'])).
% 0.44/0.69  thf('28', plain, (~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)),
% 0.44/0.69      inference('clc', [status(thm)], ['16', '27'])).
% 0.44/0.69  thf('29', plain, (~ (zip_tseitin_0 @ sk_B_1 @ sk_A)),
% 0.44/0.69      inference('clc', [status(thm)], ['12', '28'])).
% 0.44/0.69  thf('30', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.44/0.69      inference('sup-', [status(thm)], ['9', '29'])).
% 0.44/0.69  thf(fc3_zfmisc_1, axiom,
% 0.44/0.69    (![A:$i,B:$i]:
% 0.44/0.69     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.44/0.69  thf('31', plain,
% 0.44/0.69      (![X11 : $i, X12 : $i]:
% 0.44/0.69         ((v1_xboole_0 @ (k2_zfmisc_1 @ X11 @ X12)) | ~ (v1_xboole_0 @ X12))),
% 0.44/0.69      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.44/0.69  thf('32', plain,
% 0.44/0.69      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['2', '5'])).
% 0.44/0.69  thf('33', plain,
% 0.44/0.69      (![X0 : $i, X1 : $i]:
% 0.44/0.69         (~ (v1_xboole_0 @ X0) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['31', '32'])).
% 0.44/0.69  thf('34', plain,
% 0.44/0.69      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.44/0.69         (((X26) != (k1_xboole_0))
% 0.44/0.69          | ((X27) = (k1_xboole_0))
% 0.44/0.69          | (v1_funct_2 @ X28 @ X27 @ X26)
% 0.44/0.69          | ((X28) != (k1_xboole_0))
% 0.44/0.69          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.44/0.69  thf('35', plain,
% 0.44/0.69      (![X27 : $i]:
% 0.44/0.69         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.44/0.69             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ k1_xboole_0)))
% 0.44/0.69          | (v1_funct_2 @ k1_xboole_0 @ X27 @ k1_xboole_0)
% 0.44/0.69          | ((X27) = (k1_xboole_0)))),
% 0.44/0.69      inference('simplify', [status(thm)], ['34'])).
% 0.44/0.69  thf('36', plain,
% 0.44/0.69      (![X0 : $i]:
% 0.44/0.69         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.44/0.69          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.44/0.69          | ((X0) = (k1_xboole_0))
% 0.44/0.69          | (v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.69      inference('sup-', [status(thm)], ['33', '35'])).
% 0.44/0.69  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.44/0.69  thf('37', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.44/0.69  thf('38', plain,
% 0.44/0.69      (![X0 : $i]:
% 0.44/0.69         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.44/0.69          | ((X0) = (k1_xboole_0))
% 0.44/0.69          | (v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.69      inference('demod', [status(thm)], ['36', '37'])).
% 0.44/0.69  thf('39', plain,
% 0.44/0.69      (![X0 : $i, X1 : $i]:
% 0.44/0.69         (~ (v1_xboole_0 @ X0) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['31', '32'])).
% 0.44/0.69  thf('40', plain,
% 0.44/0.69      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.69  thf('41', plain,
% 0.44/0.69      (![X21 : $i, X22 : $i]:
% 0.44/0.69         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.44/0.69  thf('43', plain,
% 0.44/0.69      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.44/0.69      inference('sup+', [status(thm)], ['41', '42'])).
% 0.44/0.69  thf('44', plain,
% 0.44/0.69      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.44/0.69      inference('sup+', [status(thm)], ['41', '42'])).
% 0.44/0.69  thf('45', plain,
% 0.44/0.69      (![X11 : $i, X12 : $i]:
% 0.44/0.69         ((v1_xboole_0 @ (k2_zfmisc_1 @ X11 @ X12)) | ~ (v1_xboole_0 @ X12))),
% 0.44/0.69      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.44/0.69  thf('46', plain,
% 0.44/0.69      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.69  thf(cc1_subset_1, axiom,
% 0.44/0.69    (![A:$i]:
% 0.44/0.69     ( ( v1_xboole_0 @ A ) =>
% 0.44/0.69       ( ![B:$i]:
% 0.44/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.44/0.69  thf('47', plain,
% 0.44/0.69      (![X13 : $i, X14 : $i]:
% 0.44/0.69         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.44/0.69          | (v1_xboole_0 @ X13)
% 0.44/0.69          | ~ (v1_xboole_0 @ X14))),
% 0.44/0.69      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.44/0.69  thf('48', plain,
% 0.44/0.69      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.44/0.69        | (v1_xboole_0 @ sk_C_1))),
% 0.44/0.69      inference('sup-', [status(thm)], ['46', '47'])).
% 0.44/0.69  thf('49', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_C_1))),
% 0.44/0.69      inference('sup-', [status(thm)], ['45', '48'])).
% 0.44/0.69  thf('50', plain,
% 0.44/0.69      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_C_1))),
% 0.44/0.69      inference('sup-', [status(thm)], ['44', '49'])).
% 0.44/0.69  thf('51', plain,
% 0.44/0.69      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['2', '5'])).
% 0.44/0.69  thf('52', plain,
% 0.44/0.69      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['2', '5'])).
% 0.44/0.69  thf('53', plain,
% 0.44/0.69      (![X0 : $i, X1 : $i]:
% 0.44/0.69         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.44/0.69      inference('sup+', [status(thm)], ['51', '52'])).
% 0.44/0.69  thf('54', plain,
% 0.44/0.69      (![X0 : $i, X1 : $i]:
% 0.44/0.69         ((zip_tseitin_0 @ sk_B_1 @ X1)
% 0.44/0.69          | ~ (v1_xboole_0 @ X0)
% 0.44/0.69          | ((X0) = (sk_C_1)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['50', '53'])).
% 0.44/0.69  thf('55', plain,
% 0.44/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.69         ((zip_tseitin_0 @ X0 @ X2)
% 0.44/0.69          | ((X0) = (sk_C_1))
% 0.44/0.69          | (zip_tseitin_0 @ sk_B_1 @ X1))),
% 0.44/0.69      inference('sup-', [status(thm)], ['43', '54'])).
% 0.44/0.69  thf('56', plain,
% 0.44/0.69      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | ((sk_B_1) = (sk_C_1)))),
% 0.44/0.69      inference('eq_fact', [status(thm)], ['55'])).
% 0.44/0.69  thf('57', plain, (~ (zip_tseitin_0 @ sk_B_1 @ sk_A)),
% 0.44/0.69      inference('clc', [status(thm)], ['12', '28'])).
% 0.44/0.69  thf('58', plain, (((sk_B_1) = (sk_C_1))),
% 0.44/0.69      inference('sup-', [status(thm)], ['56', '57'])).
% 0.44/0.69  thf('59', plain,
% 0.44/0.69      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.44/0.69      inference('demod', [status(thm)], ['40', '58'])).
% 0.44/0.69  thf('60', plain,
% 0.44/0.69      (![X21 : $i, X22 : $i]:
% 0.44/0.69         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('61', plain, (~ (zip_tseitin_0 @ sk_B_1 @ sk_A)),
% 0.44/0.69      inference('clc', [status(thm)], ['12', '28'])).
% 0.44/0.69  thf('62', plain, (((sk_B_1) = (sk_C_1))),
% 0.44/0.69      inference('sup-', [status(thm)], ['56', '57'])).
% 0.44/0.69  thf('63', plain, (~ (zip_tseitin_0 @ sk_C_1 @ sk_A)),
% 0.44/0.69      inference('demod', [status(thm)], ['61', '62'])).
% 0.44/0.69  thf('64', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.44/0.69      inference('sup-', [status(thm)], ['60', '63'])).
% 0.44/0.69  thf('65', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.44/0.69      inference('sup-', [status(thm)], ['60', '63'])).
% 0.44/0.69  thf('66', plain,
% 0.44/0.69      ((m1_subset_1 @ k1_xboole_0 @ 
% 0.44/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.44/0.69      inference('demod', [status(thm)], ['59', '64', '65'])).
% 0.44/0.69  thf('67', plain,
% 0.44/0.69      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.44/0.69        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.44/0.69      inference('sup+', [status(thm)], ['39', '66'])).
% 0.44/0.69  thf('68', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.44/0.69  thf('69', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.44/0.69      inference('demod', [status(thm)], ['67', '68'])).
% 0.44/0.69  thf('70', plain,
% 0.44/0.69      (![X0 : $i]:
% 0.44/0.69         (((X0) = (k1_xboole_0))
% 0.44/0.69          | (v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.69      inference('demod', [status(thm)], ['38', '69'])).
% 0.44/0.69  thf('71', plain, (~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 0.44/0.69      inference('simpl_trail', [status(thm)], ['18', '26'])).
% 0.44/0.69  thf('72', plain, (((sk_B_1) = (sk_C_1))),
% 0.44/0.69      inference('sup-', [status(thm)], ['56', '57'])).
% 0.44/0.69  thf('73', plain, (~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_C_1)),
% 0.44/0.69      inference('demod', [status(thm)], ['71', '72'])).
% 0.44/0.69  thf('74', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.44/0.69      inference('sup-', [status(thm)], ['60', '63'])).
% 0.44/0.69  thf('75', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.44/0.69      inference('sup-', [status(thm)], ['60', '63'])).
% 0.44/0.69  thf('76', plain, (~ (v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0)),
% 0.44/0.69      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.44/0.69  thf('77', plain, (((sk_A) = (k1_xboole_0))),
% 0.44/0.69      inference('sup-', [status(thm)], ['70', '76'])).
% 0.44/0.69  thf('78', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.44/0.69  thf('79', plain, ($false),
% 0.44/0.69      inference('demod', [status(thm)], ['30', '77', '78'])).
% 0.44/0.69  
% 0.44/0.69  % SZS output end Refutation
% 0.44/0.69  
% 0.44/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
