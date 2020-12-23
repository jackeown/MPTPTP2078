%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1UVtUkY25z

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:46 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 346 expanded)
%              Number of leaves         :   35 ( 115 expanded)
%              Depth                    :   17
%              Number of atoms          :  811 (3590 expanded)
%              Number of equality atoms :   49 ( 108 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t3_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v1_funct_1 @ A )
          & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
          & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_A )
   <= ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_1 @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X18: $i] :
      ( ( r1_tarski @ X18 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X18 ) @ ( k2_relat_1 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['4','11','12'])).

thf('14',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

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

thf('15',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

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

thf('17',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X26
       != ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','31'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('33',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf('35',plain,(
    ! [X18: $i] :
      ( ( r1_tarski @ X18 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X18 ) @ ( k2_relat_1 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('36',plain,
    ( ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('37',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('38',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r1_tarski @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['36','38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','42'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('44',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ ( sk_C @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('46',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('49',plain,(
    ! [X13: $i,X16: $i] :
      ( ( X16
        = ( k1_relat_1 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X16 @ X13 ) @ ( sk_D @ X16 @ X13 ) ) @ X13 )
      | ( r2_hidden @ ( sk_C_1 @ X16 @ X13 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('50',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ~ ( r1_tarski @ X0 @ ( k4_tarski @ ( sk_C_1 @ X1 @ X0 ) @ ( sk_D @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('53',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( sk_C_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','56'])).

thf('58',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','56'])).

thf('59',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('60',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('61',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('62',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X26
       != ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X25 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('71',plain,(
    ! [X24: $i] :
      ( zip_tseitin_0 @ X24 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('73',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('simplify_reflect+',[status(thm)],['69','75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['32','57','58','59','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1UVtUkY25z
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:14:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.33/1.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.33/1.50  % Solved by: fo/fo7.sh
% 1.33/1.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.33/1.50  % done 1216 iterations in 1.057s
% 1.33/1.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.33/1.50  % SZS output start Refutation
% 1.33/1.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.33/1.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.33/1.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.33/1.50  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.33/1.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.33/1.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.33/1.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.33/1.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.33/1.50  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.33/1.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.33/1.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.33/1.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.33/1.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.33/1.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.33/1.50  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.33/1.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.33/1.50  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 1.33/1.50  thf(sk_A_type, type, sk_A: $i).
% 1.33/1.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.33/1.50  thf(t3_funct_2, conjecture,
% 1.33/1.50    (![A:$i]:
% 1.33/1.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.33/1.50       ( ( v1_funct_1 @ A ) & 
% 1.33/1.50         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.33/1.50         ( m1_subset_1 @
% 1.33/1.50           A @ 
% 1.33/1.50           ( k1_zfmisc_1 @
% 1.33/1.50             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.33/1.50  thf(zf_stmt_0, negated_conjecture,
% 1.33/1.50    (~( ![A:$i]:
% 1.33/1.50        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.33/1.50          ( ( v1_funct_1 @ A ) & 
% 1.33/1.50            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.33/1.50            ( m1_subset_1 @
% 1.33/1.50              A @ 
% 1.33/1.50              ( k1_zfmisc_1 @
% 1.33/1.50                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 1.33/1.50    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 1.33/1.50  thf('0', plain,
% 1.33/1.50      ((~ (v1_funct_1 @ sk_A)
% 1.33/1.50        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 1.33/1.50        | ~ (m1_subset_1 @ sk_A @ 
% 1.33/1.50             (k1_zfmisc_1 @ 
% 1.33/1.50              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 1.33/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.50  thf('1', plain,
% 1.33/1.50      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 1.33/1.50         <= (~
% 1.33/1.50             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 1.33/1.50      inference('split', [status(esa)], ['0'])).
% 1.33/1.50  thf('2', plain, ((v1_funct_1 @ sk_A)),
% 1.33/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.50  thf('3', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 1.33/1.50      inference('split', [status(esa)], ['0'])).
% 1.33/1.50  thf('4', plain, (((v1_funct_1 @ sk_A))),
% 1.33/1.50      inference('sup-', [status(thm)], ['2', '3'])).
% 1.33/1.50  thf(t21_relat_1, axiom,
% 1.33/1.50    (![A:$i]:
% 1.33/1.50     ( ( v1_relat_1 @ A ) =>
% 1.33/1.50       ( r1_tarski @
% 1.33/1.50         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 1.33/1.50  thf('5', plain,
% 1.33/1.50      (![X18 : $i]:
% 1.33/1.50         ((r1_tarski @ X18 @ 
% 1.33/1.50           (k2_zfmisc_1 @ (k1_relat_1 @ X18) @ (k2_relat_1 @ X18)))
% 1.33/1.50          | ~ (v1_relat_1 @ X18))),
% 1.33/1.50      inference('cnf', [status(esa)], [t21_relat_1])).
% 1.33/1.50  thf(t3_subset, axiom,
% 1.33/1.50    (![A:$i,B:$i]:
% 1.33/1.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.33/1.50  thf('6', plain,
% 1.33/1.50      (![X8 : $i, X10 : $i]:
% 1.33/1.50         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 1.33/1.50      inference('cnf', [status(esa)], [t3_subset])).
% 1.33/1.50  thf('7', plain,
% 1.33/1.50      (![X0 : $i]:
% 1.33/1.50         (~ (v1_relat_1 @ X0)
% 1.33/1.50          | (m1_subset_1 @ X0 @ 
% 1.33/1.50             (k1_zfmisc_1 @ 
% 1.33/1.50              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 1.33/1.50      inference('sup-', [status(thm)], ['5', '6'])).
% 1.33/1.50  thf('8', plain,
% 1.33/1.50      ((~ (m1_subset_1 @ sk_A @ 
% 1.33/1.50           (k1_zfmisc_1 @ 
% 1.33/1.50            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 1.33/1.50         <= (~
% 1.33/1.50             ((m1_subset_1 @ sk_A @ 
% 1.33/1.50               (k1_zfmisc_1 @ 
% 1.33/1.50                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 1.33/1.50      inference('split', [status(esa)], ['0'])).
% 1.33/1.50  thf('9', plain,
% 1.33/1.50      ((~ (v1_relat_1 @ sk_A))
% 1.33/1.50         <= (~
% 1.33/1.50             ((m1_subset_1 @ sk_A @ 
% 1.33/1.50               (k1_zfmisc_1 @ 
% 1.33/1.50                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 1.33/1.50      inference('sup-', [status(thm)], ['7', '8'])).
% 1.33/1.50  thf('10', plain, ((v1_relat_1 @ sk_A)),
% 1.33/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.50  thf('11', plain,
% 1.33/1.50      (((m1_subset_1 @ sk_A @ 
% 1.33/1.50         (k1_zfmisc_1 @ 
% 1.33/1.50          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 1.33/1.50      inference('demod', [status(thm)], ['9', '10'])).
% 1.33/1.50  thf('12', plain,
% 1.33/1.50      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 1.33/1.50       ~
% 1.33/1.50       ((m1_subset_1 @ sk_A @ 
% 1.33/1.50         (k1_zfmisc_1 @ 
% 1.33/1.50          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 1.33/1.50       ~ ((v1_funct_1 @ sk_A))),
% 1.33/1.50      inference('split', [status(esa)], ['0'])).
% 1.33/1.50  thf('13', plain,
% 1.33/1.50      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 1.33/1.50      inference('sat_resolution*', [status(thm)], ['4', '11', '12'])).
% 1.33/1.50  thf('14', plain,
% 1.33/1.50      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 1.33/1.50      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 1.33/1.50  thf(d1_funct_2, axiom,
% 1.33/1.50    (![A:$i,B:$i,C:$i]:
% 1.33/1.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.33/1.50       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.33/1.50           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.33/1.50             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.33/1.50         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.33/1.50           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.33/1.50             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.33/1.50  thf(zf_stmt_1, axiom,
% 1.33/1.50    (![B:$i,A:$i]:
% 1.33/1.50     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.33/1.50       ( zip_tseitin_0 @ B @ A ) ))).
% 1.33/1.50  thf('15', plain,
% 1.33/1.50      (![X24 : $i, X25 : $i]:
% 1.33/1.50         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 1.33/1.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.33/1.50  thf('16', plain,
% 1.33/1.50      (![X0 : $i]:
% 1.33/1.50         (~ (v1_relat_1 @ X0)
% 1.33/1.50          | (m1_subset_1 @ X0 @ 
% 1.33/1.50             (k1_zfmisc_1 @ 
% 1.33/1.50              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 1.33/1.50      inference('sup-', [status(thm)], ['5', '6'])).
% 1.33/1.50  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.33/1.50  thf(zf_stmt_3, axiom,
% 1.33/1.50    (![C:$i,B:$i,A:$i]:
% 1.33/1.50     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.33/1.50       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.33/1.50  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.33/1.50  thf(zf_stmt_5, axiom,
% 1.33/1.50    (![A:$i,B:$i,C:$i]:
% 1.33/1.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.33/1.50       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.33/1.50         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.33/1.50           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.33/1.50             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.33/1.50  thf('17', plain,
% 1.33/1.50      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.33/1.50         (~ (zip_tseitin_0 @ X29 @ X30)
% 1.33/1.50          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 1.33/1.50          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 1.33/1.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.33/1.50  thf('18', plain,
% 1.33/1.50      (![X0 : $i]:
% 1.33/1.50         (~ (v1_relat_1 @ X0)
% 1.33/1.50          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 1.33/1.50          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 1.33/1.50      inference('sup-', [status(thm)], ['16', '17'])).
% 1.33/1.50  thf('19', plain,
% 1.33/1.50      (![X0 : $i]:
% 1.33/1.50         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.33/1.50          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 1.33/1.50          | ~ (v1_relat_1 @ X0))),
% 1.33/1.50      inference('sup-', [status(thm)], ['15', '18'])).
% 1.33/1.50  thf('20', plain,
% 1.33/1.50      (![X0 : $i]:
% 1.33/1.50         (~ (v1_relat_1 @ X0)
% 1.33/1.50          | (m1_subset_1 @ X0 @ 
% 1.33/1.50             (k1_zfmisc_1 @ 
% 1.33/1.50              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 1.33/1.50      inference('sup-', [status(thm)], ['5', '6'])).
% 1.33/1.50  thf(redefinition_k1_relset_1, axiom,
% 1.33/1.50    (![A:$i,B:$i,C:$i]:
% 1.33/1.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.33/1.50       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.33/1.50  thf('21', plain,
% 1.33/1.50      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.33/1.50         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 1.33/1.50          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.33/1.50      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.33/1.50  thf('22', plain,
% 1.33/1.50      (![X0 : $i]:
% 1.33/1.50         (~ (v1_relat_1 @ X0)
% 1.33/1.50          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.33/1.50              = (k1_relat_1 @ X0)))),
% 1.33/1.50      inference('sup-', [status(thm)], ['20', '21'])).
% 1.33/1.50  thf('23', plain,
% 1.33/1.50      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.33/1.50         (((X26) != (k1_relset_1 @ X26 @ X27 @ X28))
% 1.33/1.50          | (v1_funct_2 @ X28 @ X26 @ X27)
% 1.33/1.50          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 1.33/1.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.33/1.50  thf('24', plain,
% 1.33/1.50      (![X0 : $i]:
% 1.33/1.50         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 1.33/1.50          | ~ (v1_relat_1 @ X0)
% 1.33/1.50          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 1.33/1.50          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.33/1.50      inference('sup-', [status(thm)], ['22', '23'])).
% 1.33/1.50  thf('25', plain,
% 1.33/1.50      (![X0 : $i]:
% 1.33/1.50         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 1.33/1.50          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 1.33/1.50          | ~ (v1_relat_1 @ X0))),
% 1.33/1.50      inference('simplify', [status(thm)], ['24'])).
% 1.33/1.50  thf('26', plain,
% 1.33/1.50      (![X0 : $i]:
% 1.33/1.50         (~ (v1_relat_1 @ X0)
% 1.33/1.50          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.33/1.50          | ~ (v1_relat_1 @ X0)
% 1.33/1.50          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.33/1.50      inference('sup-', [status(thm)], ['19', '25'])).
% 1.33/1.50  thf('27', plain,
% 1.33/1.50      (![X0 : $i]:
% 1.33/1.50         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 1.33/1.50          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.33/1.50          | ~ (v1_relat_1 @ X0))),
% 1.33/1.50      inference('simplify', [status(thm)], ['26'])).
% 1.33/1.50  thf('28', plain,
% 1.33/1.50      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 1.33/1.50      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 1.33/1.50  thf('29', plain,
% 1.33/1.50      ((~ (v1_relat_1 @ sk_A) | ((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 1.33/1.50      inference('sup-', [status(thm)], ['27', '28'])).
% 1.33/1.50  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 1.33/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.50  thf('31', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 1.33/1.50      inference('demod', [status(thm)], ['29', '30'])).
% 1.33/1.50  thf('32', plain, (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ k1_xboole_0)),
% 1.33/1.50      inference('demod', [status(thm)], ['14', '31'])).
% 1.33/1.50  thf(d3_tarski, axiom,
% 1.33/1.50    (![A:$i,B:$i]:
% 1.33/1.50     ( ( r1_tarski @ A @ B ) <=>
% 1.33/1.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.33/1.50  thf('33', plain,
% 1.33/1.50      (![X1 : $i, X3 : $i]:
% 1.33/1.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.33/1.50      inference('cnf', [status(esa)], [d3_tarski])).
% 1.33/1.50  thf('34', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 1.33/1.50      inference('demod', [status(thm)], ['29', '30'])).
% 1.33/1.50  thf('35', plain,
% 1.33/1.50      (![X18 : $i]:
% 1.33/1.50         ((r1_tarski @ X18 @ 
% 1.33/1.50           (k2_zfmisc_1 @ (k1_relat_1 @ X18) @ (k2_relat_1 @ X18)))
% 1.33/1.50          | ~ (v1_relat_1 @ X18))),
% 1.33/1.50      inference('cnf', [status(esa)], [t21_relat_1])).
% 1.33/1.50  thf('36', plain,
% 1.33/1.50      (((r1_tarski @ sk_A @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ k1_xboole_0))
% 1.33/1.50        | ~ (v1_relat_1 @ sk_A))),
% 1.33/1.50      inference('sup+', [status(thm)], ['34', '35'])).
% 1.33/1.50  thf(t113_zfmisc_1, axiom,
% 1.33/1.50    (![A:$i,B:$i]:
% 1.33/1.50     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.33/1.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.33/1.50  thf('37', plain,
% 1.33/1.50      (![X6 : $i, X7 : $i]:
% 1.33/1.50         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 1.33/1.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.33/1.50  thf('38', plain,
% 1.33/1.50      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 1.33/1.50      inference('simplify', [status(thm)], ['37'])).
% 1.33/1.50  thf('39', plain, ((v1_relat_1 @ sk_A)),
% 1.33/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.50  thf('40', plain, ((r1_tarski @ sk_A @ k1_xboole_0)),
% 1.33/1.50      inference('demod', [status(thm)], ['36', '38', '39'])).
% 1.33/1.50  thf('41', plain,
% 1.33/1.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.33/1.50         (~ (r2_hidden @ X0 @ X1)
% 1.33/1.50          | (r2_hidden @ X0 @ X2)
% 1.33/1.50          | ~ (r1_tarski @ X1 @ X2))),
% 1.33/1.50      inference('cnf', [status(esa)], [d3_tarski])).
% 1.33/1.50  thf('42', plain,
% 1.33/1.50      (![X0 : $i]: ((r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_A))),
% 1.33/1.50      inference('sup-', [status(thm)], ['40', '41'])).
% 1.33/1.50  thf('43', plain,
% 1.33/1.50      (![X0 : $i]:
% 1.33/1.50         ((r1_tarski @ sk_A @ X0)
% 1.33/1.50          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ k1_xboole_0))),
% 1.33/1.50      inference('sup-', [status(thm)], ['33', '42'])).
% 1.33/1.50  thf(t7_ordinal1, axiom,
% 1.33/1.50    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.33/1.50  thf('44', plain,
% 1.33/1.50      (![X19 : $i, X20 : $i]:
% 1.33/1.50         (~ (r2_hidden @ X19 @ X20) | ~ (r1_tarski @ X20 @ X19))),
% 1.33/1.50      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.33/1.50  thf('45', plain,
% 1.33/1.50      (![X0 : $i]:
% 1.33/1.50         ((r1_tarski @ sk_A @ X0)
% 1.33/1.50          | ~ (r1_tarski @ k1_xboole_0 @ (sk_C @ X0 @ sk_A)))),
% 1.33/1.50      inference('sup-', [status(thm)], ['43', '44'])).
% 1.33/1.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.33/1.50  thf('46', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 1.33/1.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.33/1.50  thf('47', plain, (![X0 : $i]: (r1_tarski @ sk_A @ X0)),
% 1.33/1.50      inference('demod', [status(thm)], ['45', '46'])).
% 1.33/1.50  thf('48', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 1.33/1.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.33/1.50  thf(d4_relat_1, axiom,
% 1.33/1.50    (![A:$i,B:$i]:
% 1.33/1.50     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 1.33/1.50       ( ![C:$i]:
% 1.33/1.50         ( ( r2_hidden @ C @ B ) <=>
% 1.33/1.50           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 1.33/1.50  thf('49', plain,
% 1.33/1.50      (![X13 : $i, X16 : $i]:
% 1.33/1.50         (((X16) = (k1_relat_1 @ X13))
% 1.33/1.50          | (r2_hidden @ 
% 1.33/1.50             (k4_tarski @ (sk_C_1 @ X16 @ X13) @ (sk_D @ X16 @ X13)) @ X13)
% 1.33/1.50          | (r2_hidden @ (sk_C_1 @ X16 @ X13) @ X16))),
% 1.33/1.50      inference('cnf', [status(esa)], [d4_relat_1])).
% 1.33/1.50  thf('50', plain,
% 1.33/1.50      (![X19 : $i, X20 : $i]:
% 1.33/1.50         (~ (r2_hidden @ X19 @ X20) | ~ (r1_tarski @ X20 @ X19))),
% 1.33/1.50      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.33/1.50  thf('51', plain,
% 1.33/1.50      (![X0 : $i, X1 : $i]:
% 1.33/1.50         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 1.33/1.50          | ((X1) = (k1_relat_1 @ X0))
% 1.33/1.50          | ~ (r1_tarski @ X0 @ 
% 1.33/1.50               (k4_tarski @ (sk_C_1 @ X1 @ X0) @ (sk_D @ X1 @ X0))))),
% 1.33/1.50      inference('sup-', [status(thm)], ['49', '50'])).
% 1.33/1.50  thf('52', plain,
% 1.33/1.50      (![X0 : $i]:
% 1.33/1.50         (((X0) = (k1_relat_1 @ k1_xboole_0))
% 1.33/1.50          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 1.33/1.50      inference('sup-', [status(thm)], ['48', '51'])).
% 1.33/1.50  thf(t60_relat_1, axiom,
% 1.33/1.50    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.33/1.50     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.33/1.50  thf('53', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.33/1.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.33/1.50  thf('54', plain,
% 1.33/1.50      (![X0 : $i]:
% 1.33/1.50         (((X0) = (k1_xboole_0))
% 1.33/1.50          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 1.33/1.50      inference('demod', [status(thm)], ['52', '53'])).
% 1.33/1.50  thf('55', plain,
% 1.33/1.50      (![X19 : $i, X20 : $i]:
% 1.33/1.50         (~ (r2_hidden @ X19 @ X20) | ~ (r1_tarski @ X20 @ X19))),
% 1.33/1.50      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.33/1.50  thf('56', plain,
% 1.33/1.50      (![X0 : $i]:
% 1.33/1.50         (((X0) = (k1_xboole_0))
% 1.33/1.50          | ~ (r1_tarski @ X0 @ (sk_C_1 @ X0 @ k1_xboole_0)))),
% 1.33/1.50      inference('sup-', [status(thm)], ['54', '55'])).
% 1.33/1.50  thf('57', plain, (((sk_A) = (k1_xboole_0))),
% 1.33/1.50      inference('sup-', [status(thm)], ['47', '56'])).
% 1.33/1.50  thf('58', plain, (((sk_A) = (k1_xboole_0))),
% 1.33/1.50      inference('sup-', [status(thm)], ['47', '56'])).
% 1.33/1.50  thf('59', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.33/1.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.33/1.50  thf('60', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 1.33/1.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.33/1.50  thf('61', plain,
% 1.33/1.50      (![X8 : $i, X10 : $i]:
% 1.33/1.50         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 1.33/1.50      inference('cnf', [status(esa)], [t3_subset])).
% 1.33/1.50  thf('62', plain,
% 1.33/1.50      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.33/1.50      inference('sup-', [status(thm)], ['60', '61'])).
% 1.33/1.50  thf('63', plain,
% 1.33/1.50      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.33/1.50         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 1.33/1.50          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.33/1.50      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.33/1.50  thf('64', plain,
% 1.33/1.50      (![X0 : $i, X1 : $i]:
% 1.33/1.50         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 1.33/1.50      inference('sup-', [status(thm)], ['62', '63'])).
% 1.33/1.50  thf('65', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.33/1.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.33/1.50  thf('66', plain,
% 1.33/1.50      (![X0 : $i, X1 : $i]:
% 1.33/1.50         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.33/1.50      inference('demod', [status(thm)], ['64', '65'])).
% 1.33/1.50  thf('67', plain,
% 1.33/1.50      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.33/1.50         (((X26) != (k1_relset_1 @ X26 @ X27 @ X28))
% 1.33/1.50          | (v1_funct_2 @ X28 @ X26 @ X27)
% 1.33/1.50          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 1.33/1.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.33/1.50  thf('68', plain,
% 1.33/1.50      (![X0 : $i, X1 : $i]:
% 1.33/1.50         (((X1) != (k1_xboole_0))
% 1.33/1.50          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 1.33/1.50          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 1.33/1.50      inference('sup-', [status(thm)], ['66', '67'])).
% 1.33/1.50  thf('69', plain,
% 1.33/1.50      (![X0 : $i]:
% 1.33/1.50         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.33/1.50          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.33/1.50      inference('simplify', [status(thm)], ['68'])).
% 1.33/1.50  thf('70', plain,
% 1.33/1.50      (![X24 : $i, X25 : $i]:
% 1.33/1.50         ((zip_tseitin_0 @ X24 @ X25) | ((X25) != (k1_xboole_0)))),
% 1.33/1.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.33/1.50  thf('71', plain, (![X24 : $i]: (zip_tseitin_0 @ X24 @ k1_xboole_0)),
% 1.33/1.50      inference('simplify', [status(thm)], ['70'])).
% 1.33/1.50  thf('72', plain,
% 1.33/1.50      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.33/1.50      inference('sup-', [status(thm)], ['60', '61'])).
% 1.33/1.50  thf('73', plain,
% 1.33/1.50      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.33/1.50         (~ (zip_tseitin_0 @ X29 @ X30)
% 1.33/1.50          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 1.33/1.50          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 1.33/1.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.33/1.50  thf('74', plain,
% 1.33/1.50      (![X0 : $i, X1 : $i]:
% 1.33/1.50         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 1.33/1.50      inference('sup-', [status(thm)], ['72', '73'])).
% 1.33/1.50  thf('75', plain,
% 1.33/1.50      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.33/1.50      inference('sup-', [status(thm)], ['71', '74'])).
% 1.33/1.50  thf('76', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.33/1.50      inference('simplify_reflect+', [status(thm)], ['69', '75'])).
% 1.33/1.50  thf('77', plain, ($false),
% 1.33/1.50      inference('demod', [status(thm)], ['32', '57', '58', '59', '76'])).
% 1.33/1.50  
% 1.33/1.50  % SZS output end Refutation
% 1.33/1.50  
% 1.33/1.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
