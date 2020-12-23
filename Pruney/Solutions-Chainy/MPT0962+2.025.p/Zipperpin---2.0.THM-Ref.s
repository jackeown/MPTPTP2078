%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TbrHdLsfoR

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:52 EST 2020

% Result     : Theorem 31.67s
% Output     : Refutation 31.67s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 542 expanded)
%              Number of leaves         :   32 ( 159 expanded)
%              Depth                    :   15
%              Number of atoms          :  687 (6567 expanded)
%              Number of equality atoms :   38 ( 139 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X27 ) @ X28 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X27 ) @ X29 )
      | ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
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
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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

thf('8',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('11',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('12',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('14',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('15',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32
       != ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('17',plain,
    ( ( ( k1_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( v1_funct_1 @ sk_B )
   <= ~ ( v1_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['19'])).

thf('23',plain,(
    v1_funct_1 @ sk_B ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['19'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['19'])).

thf('28',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['23','26','27'])).

thf('29',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['20','28'])).

thf('30',plain,(
    ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['18','29'])).

thf('31',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','30'])).

thf('32',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','30'])).

thf('33',plain,
    ( ( zip_tseitin_1 @ sk_B @ k1_xboole_0 @ ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','31','32'])).

thf('34',plain,(
    ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['18','29'])).

thf('35',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','30'])).

thf('36',plain,(
    ~ ( zip_tseitin_1 @ sk_B @ k1_xboole_0 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( zip_tseitin_0 @ k1_xboole_0 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['33','36'])).

thf('38',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( sk_A
      = ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','30'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('42',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('43',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','30'])).

thf('44',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['40','41','42','43'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('45',plain,(
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

thf('46',plain,(
    ! [X16: $i,X18: $i,X20: $i,X21: $i] :
      ( ( X18
       != ( k2_relat_1 @ X16 ) )
      | ( r2_hidden @ X20 @ X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X16 ) )
      | ( X20
       != ( k1_funct_1 @ X16 @ X21 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('47',plain,(
    ! [X16: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X16 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X16 @ X21 ) @ ( k2_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('49',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( r1_tarski @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_funct_1 @ X0 @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_funct_1 @ sk_B @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_B ) ) ) )
      | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','50'])).

thf('52',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('53',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('57',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k1_relat_1 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('61',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X31 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('62',plain,(
    ! [X30: $i] :
      ( zip_tseitin_0 @ X30 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['60','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['37','59','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TbrHdLsfoR
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:45:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 31.67/31.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 31.67/31.84  % Solved by: fo/fo7.sh
% 31.67/31.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 31.67/31.84  % done 8456 iterations in 31.382s
% 31.67/31.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 31.67/31.84  % SZS output start Refutation
% 31.67/31.84  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 31.67/31.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 31.67/31.84  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 31.67/31.84  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 31.67/31.84  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 31.67/31.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 31.67/31.84  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 31.67/31.84  thf(sk_A_type, type, sk_A: $i).
% 31.67/31.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 31.67/31.84  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 31.67/31.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 31.67/31.84  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 31.67/31.84  thf(sk_B_type, type, sk_B: $i).
% 31.67/31.84  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 31.67/31.84  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 31.67/31.84  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 31.67/31.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 31.67/31.84  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 31.67/31.84  thf(t4_funct_2, conjecture,
% 31.67/31.84    (![A:$i,B:$i]:
% 31.67/31.84     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 31.67/31.84       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 31.67/31.84         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 31.67/31.84           ( m1_subset_1 @
% 31.67/31.84             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 31.67/31.84  thf(zf_stmt_0, negated_conjecture,
% 31.67/31.84    (~( ![A:$i,B:$i]:
% 31.67/31.84        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 31.67/31.84          ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 31.67/31.84            ( ( v1_funct_1 @ B ) & 
% 31.67/31.84              ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 31.67/31.84              ( m1_subset_1 @
% 31.67/31.84                B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )),
% 31.67/31.84    inference('cnf.neg', [status(esa)], [t4_funct_2])).
% 31.67/31.84  thf('0', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 31.67/31.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.84  thf(d10_xboole_0, axiom,
% 31.67/31.84    (![A:$i,B:$i]:
% 31.67/31.84     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 31.67/31.84  thf('1', plain,
% 31.67/31.84      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 31.67/31.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 31.67/31.84  thf('2', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 31.67/31.84      inference('simplify', [status(thm)], ['1'])).
% 31.67/31.84  thf(t11_relset_1, axiom,
% 31.67/31.84    (![A:$i,B:$i,C:$i]:
% 31.67/31.84     ( ( v1_relat_1 @ C ) =>
% 31.67/31.84       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 31.67/31.84           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 31.67/31.84         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 31.67/31.84  thf('3', plain,
% 31.67/31.84      (![X27 : $i, X28 : $i, X29 : $i]:
% 31.67/31.84         (~ (r1_tarski @ (k1_relat_1 @ X27) @ X28)
% 31.67/31.84          | ~ (r1_tarski @ (k2_relat_1 @ X27) @ X29)
% 31.67/31.84          | (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 31.67/31.84          | ~ (v1_relat_1 @ X27))),
% 31.67/31.84      inference('cnf', [status(esa)], [t11_relset_1])).
% 31.67/31.84  thf('4', plain,
% 31.67/31.84      (![X0 : $i, X1 : $i]:
% 31.67/31.84         (~ (v1_relat_1 @ X0)
% 31.67/31.84          | (m1_subset_1 @ X0 @ 
% 31.67/31.84             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 31.67/31.84          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 31.67/31.84      inference('sup-', [status(thm)], ['2', '3'])).
% 31.67/31.84  thf('5', plain,
% 31.67/31.84      (((m1_subset_1 @ sk_B @ 
% 31.67/31.84         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 31.67/31.84        | ~ (v1_relat_1 @ sk_B))),
% 31.67/31.84      inference('sup-', [status(thm)], ['0', '4'])).
% 31.67/31.84  thf('6', plain, ((v1_relat_1 @ sk_B)),
% 31.67/31.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.84  thf('7', plain,
% 31.67/31.84      ((m1_subset_1 @ sk_B @ 
% 31.67/31.84        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 31.67/31.84      inference('demod', [status(thm)], ['5', '6'])).
% 31.67/31.84  thf(d1_funct_2, axiom,
% 31.67/31.84    (![A:$i,B:$i,C:$i]:
% 31.67/31.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 31.67/31.84       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 31.67/31.84           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 31.67/31.84             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 31.67/31.84         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 31.67/31.84           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 31.67/31.84             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 31.67/31.84  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 31.67/31.84  thf(zf_stmt_2, axiom,
% 31.67/31.84    (![C:$i,B:$i,A:$i]:
% 31.67/31.84     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 31.67/31.84       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 31.67/31.84  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 31.67/31.84  thf(zf_stmt_4, axiom,
% 31.67/31.84    (![B:$i,A:$i]:
% 31.67/31.84     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 31.67/31.84       ( zip_tseitin_0 @ B @ A ) ))).
% 31.67/31.84  thf(zf_stmt_5, axiom,
% 31.67/31.84    (![A:$i,B:$i,C:$i]:
% 31.67/31.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 31.67/31.84       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 31.67/31.84         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 31.67/31.84           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 31.67/31.84             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 31.67/31.84  thf('8', plain,
% 31.67/31.84      (![X35 : $i, X36 : $i, X37 : $i]:
% 31.67/31.84         (~ (zip_tseitin_0 @ X35 @ X36)
% 31.67/31.84          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 31.67/31.84          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 31.67/31.84      inference('cnf', [status(esa)], [zf_stmt_5])).
% 31.67/31.84  thf('9', plain,
% 31.67/31.84      (((zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 31.67/31.84        | ~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 31.67/31.84      inference('sup-', [status(thm)], ['7', '8'])).
% 31.67/31.84  thf('10', plain,
% 31.67/31.84      (![X30 : $i, X31 : $i]:
% 31.67/31.84         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 31.67/31.84      inference('cnf', [status(esa)], [zf_stmt_4])).
% 31.67/31.84  thf('11', plain,
% 31.67/31.84      (((zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 31.67/31.84        | ~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 31.67/31.84      inference('sup-', [status(thm)], ['7', '8'])).
% 31.67/31.84  thf('12', plain,
% 31.67/31.84      ((((sk_A) = (k1_xboole_0))
% 31.67/31.84        | (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B)))),
% 31.67/31.84      inference('sup-', [status(thm)], ['10', '11'])).
% 31.67/31.84  thf('13', plain,
% 31.67/31.84      ((m1_subset_1 @ sk_B @ 
% 31.67/31.84        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 31.67/31.84      inference('demod', [status(thm)], ['5', '6'])).
% 31.67/31.84  thf(redefinition_k1_relset_1, axiom,
% 31.67/31.84    (![A:$i,B:$i,C:$i]:
% 31.67/31.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 31.67/31.84       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 31.67/31.84  thf('14', plain,
% 31.67/31.84      (![X24 : $i, X25 : $i, X26 : $i]:
% 31.67/31.84         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 31.67/31.84          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 31.67/31.84      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 31.67/31.84  thf('15', plain,
% 31.67/31.84      (((k1_relset_1 @ (k1_relat_1 @ sk_B) @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 31.67/31.84      inference('sup-', [status(thm)], ['13', '14'])).
% 31.67/31.84  thf('16', plain,
% 31.67/31.84      (![X32 : $i, X33 : $i, X34 : $i]:
% 31.67/31.84         (((X32) != (k1_relset_1 @ X32 @ X33 @ X34))
% 31.67/31.84          | (v1_funct_2 @ X34 @ X32 @ X33)
% 31.67/31.84          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 31.67/31.84      inference('cnf', [status(esa)], [zf_stmt_2])).
% 31.67/31.84  thf('17', plain,
% 31.67/31.84      ((((k1_relat_1 @ sk_B) != (k1_relat_1 @ sk_B))
% 31.67/31.84        | ~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 31.67/31.84        | (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 31.67/31.84      inference('sup-', [status(thm)], ['15', '16'])).
% 31.67/31.84  thf('18', plain,
% 31.67/31.84      (((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 31.67/31.84        | ~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B)))),
% 31.67/31.84      inference('simplify', [status(thm)], ['17'])).
% 31.67/31.84  thf('19', plain,
% 31.67/31.84      ((~ (v1_funct_1 @ sk_B)
% 31.67/31.84        | ~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 31.67/31.84        | ~ (m1_subset_1 @ sk_B @ 
% 31.67/31.84             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 31.67/31.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.84  thf('20', plain,
% 31.67/31.84      ((~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))
% 31.67/31.84         <= (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 31.67/31.84      inference('split', [status(esa)], ['19'])).
% 31.67/31.84  thf('21', plain, ((v1_funct_1 @ sk_B)),
% 31.67/31.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.84  thf('22', plain, ((~ (v1_funct_1 @ sk_B)) <= (~ ((v1_funct_1 @ sk_B)))),
% 31.67/31.84      inference('split', [status(esa)], ['19'])).
% 31.67/31.84  thf('23', plain, (((v1_funct_1 @ sk_B))),
% 31.67/31.84      inference('sup-', [status(thm)], ['21', '22'])).
% 31.67/31.84  thf('24', plain,
% 31.67/31.84      ((m1_subset_1 @ sk_B @ 
% 31.67/31.84        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 31.67/31.84      inference('demod', [status(thm)], ['5', '6'])).
% 31.67/31.84  thf('25', plain,
% 31.67/31.84      ((~ (m1_subset_1 @ sk_B @ 
% 31.67/31.84           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))
% 31.67/31.84         <= (~
% 31.67/31.84             ((m1_subset_1 @ sk_B @ 
% 31.67/31.84               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))))),
% 31.67/31.84      inference('split', [status(esa)], ['19'])).
% 31.67/31.84  thf('26', plain,
% 31.67/31.84      (((m1_subset_1 @ sk_B @ 
% 31.67/31.84         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 31.67/31.84      inference('sup-', [status(thm)], ['24', '25'])).
% 31.67/31.84  thf('27', plain,
% 31.67/31.84      (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 31.67/31.84       ~
% 31.67/31.84       ((m1_subset_1 @ sk_B @ 
% 31.67/31.84         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))) | 
% 31.67/31.84       ~ ((v1_funct_1 @ sk_B))),
% 31.67/31.84      inference('split', [status(esa)], ['19'])).
% 31.67/31.84  thf('28', plain, (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 31.67/31.84      inference('sat_resolution*', [status(thm)], ['23', '26', '27'])).
% 31.67/31.84  thf('29', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)),
% 31.67/31.84      inference('simpl_trail', [status(thm)], ['20', '28'])).
% 31.67/31.84  thf('30', plain, (~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))),
% 31.67/31.84      inference('clc', [status(thm)], ['18', '29'])).
% 31.67/31.84  thf('31', plain, (((sk_A) = (k1_xboole_0))),
% 31.67/31.84      inference('sup-', [status(thm)], ['12', '30'])).
% 31.67/31.84  thf('32', plain, (((sk_A) = (k1_xboole_0))),
% 31.67/31.84      inference('sup-', [status(thm)], ['12', '30'])).
% 31.67/31.84  thf('33', plain,
% 31.67/31.84      (((zip_tseitin_1 @ sk_B @ k1_xboole_0 @ (k1_relat_1 @ sk_B))
% 31.67/31.84        | ~ (zip_tseitin_0 @ k1_xboole_0 @ (k1_relat_1 @ sk_B)))),
% 31.67/31.84      inference('demod', [status(thm)], ['9', '31', '32'])).
% 31.67/31.84  thf('34', plain, (~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))),
% 31.67/31.84      inference('clc', [status(thm)], ['18', '29'])).
% 31.67/31.84  thf('35', plain, (((sk_A) = (k1_xboole_0))),
% 31.67/31.84      inference('sup-', [status(thm)], ['12', '30'])).
% 31.67/31.84  thf('36', plain,
% 31.67/31.84      (~ (zip_tseitin_1 @ sk_B @ k1_xboole_0 @ (k1_relat_1 @ sk_B))),
% 31.67/31.84      inference('demod', [status(thm)], ['34', '35'])).
% 31.67/31.84  thf('37', plain, (~ (zip_tseitin_0 @ k1_xboole_0 @ (k1_relat_1 @ sk_B))),
% 31.67/31.84      inference('clc', [status(thm)], ['33', '36'])).
% 31.67/31.84  thf('38', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 31.67/31.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.84  thf('39', plain,
% 31.67/31.84      (![X4 : $i, X6 : $i]:
% 31.67/31.84         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 31.67/31.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 31.67/31.84  thf('40', plain,
% 31.67/31.84      ((~ (r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))
% 31.67/31.84        | ((sk_A) = (k2_relat_1 @ sk_B)))),
% 31.67/31.84      inference('sup-', [status(thm)], ['38', '39'])).
% 31.67/31.84  thf('41', plain, (((sk_A) = (k1_xboole_0))),
% 31.67/31.84      inference('sup-', [status(thm)], ['12', '30'])).
% 31.67/31.84  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 31.67/31.84  thf('42', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 31.67/31.84      inference('cnf', [status(esa)], [t2_xboole_1])).
% 31.67/31.84  thf('43', plain, (((sk_A) = (k1_xboole_0))),
% 31.67/31.84      inference('sup-', [status(thm)], ['12', '30'])).
% 31.67/31.84  thf('44', plain, (((k1_xboole_0) = (k2_relat_1 @ sk_B))),
% 31.67/31.84      inference('demod', [status(thm)], ['40', '41', '42', '43'])).
% 31.67/31.84  thf(d3_tarski, axiom,
% 31.67/31.84    (![A:$i,B:$i]:
% 31.67/31.84     ( ( r1_tarski @ A @ B ) <=>
% 31.67/31.84       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 31.67/31.84  thf('45', plain,
% 31.67/31.84      (![X1 : $i, X3 : $i]:
% 31.67/31.84         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 31.67/31.84      inference('cnf', [status(esa)], [d3_tarski])).
% 31.67/31.84  thf(d5_funct_1, axiom,
% 31.67/31.84    (![A:$i]:
% 31.67/31.84     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 31.67/31.84       ( ![B:$i]:
% 31.67/31.84         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 31.67/31.84           ( ![C:$i]:
% 31.67/31.84             ( ( r2_hidden @ C @ B ) <=>
% 31.67/31.84               ( ?[D:$i]:
% 31.67/31.84                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 31.67/31.84                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 31.67/31.84  thf('46', plain,
% 31.67/31.84      (![X16 : $i, X18 : $i, X20 : $i, X21 : $i]:
% 31.67/31.84         (((X18) != (k2_relat_1 @ X16))
% 31.67/31.84          | (r2_hidden @ X20 @ X18)
% 31.67/31.84          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X16))
% 31.67/31.84          | ((X20) != (k1_funct_1 @ X16 @ X21))
% 31.67/31.84          | ~ (v1_funct_1 @ X16)
% 31.67/31.84          | ~ (v1_relat_1 @ X16))),
% 31.67/31.84      inference('cnf', [status(esa)], [d5_funct_1])).
% 31.67/31.84  thf('47', plain,
% 31.67/31.84      (![X16 : $i, X21 : $i]:
% 31.67/31.84         (~ (v1_relat_1 @ X16)
% 31.67/31.84          | ~ (v1_funct_1 @ X16)
% 31.67/31.84          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X16))
% 31.67/31.84          | (r2_hidden @ (k1_funct_1 @ X16 @ X21) @ (k2_relat_1 @ X16)))),
% 31.67/31.84      inference('simplify', [status(thm)], ['46'])).
% 31.67/31.84  thf('48', plain,
% 31.67/31.84      (![X0 : $i, X1 : $i]:
% 31.67/31.84         ((r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 31.67/31.84          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_C @ X1 @ (k1_relat_1 @ X0))) @ 
% 31.67/31.84             (k2_relat_1 @ X0))
% 31.67/31.84          | ~ (v1_funct_1 @ X0)
% 31.67/31.84          | ~ (v1_relat_1 @ X0))),
% 31.67/31.84      inference('sup-', [status(thm)], ['45', '47'])).
% 31.67/31.84  thf(t7_ordinal1, axiom,
% 31.67/31.84    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 31.67/31.84  thf('49', plain,
% 31.67/31.84      (![X22 : $i, X23 : $i]:
% 31.67/31.84         (~ (r2_hidden @ X22 @ X23) | ~ (r1_tarski @ X23 @ X22))),
% 31.67/31.84      inference('cnf', [status(esa)], [t7_ordinal1])).
% 31.67/31.84  thf('50', plain,
% 31.67/31.84      (![X0 : $i, X1 : $i]:
% 31.67/31.84         (~ (v1_relat_1 @ X0)
% 31.67/31.84          | ~ (v1_funct_1 @ X0)
% 31.67/31.84          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 31.67/31.84          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 31.67/31.84               (k1_funct_1 @ X0 @ (sk_C @ X1 @ (k1_relat_1 @ X0)))))),
% 31.67/31.84      inference('sup-', [status(thm)], ['48', '49'])).
% 31.67/31.84  thf('51', plain,
% 31.67/31.84      (![X0 : $i]:
% 31.67/31.84         (~ (r1_tarski @ k1_xboole_0 @ 
% 31.67/31.84             (k1_funct_1 @ sk_B @ (sk_C @ X0 @ (k1_relat_1 @ sk_B))))
% 31.67/31.84          | (r1_tarski @ (k1_relat_1 @ sk_B) @ X0)
% 31.67/31.84          | ~ (v1_funct_1 @ sk_B)
% 31.67/31.84          | ~ (v1_relat_1 @ sk_B))),
% 31.67/31.84      inference('sup-', [status(thm)], ['44', '50'])).
% 31.67/31.84  thf('52', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 31.67/31.84      inference('cnf', [status(esa)], [t2_xboole_1])).
% 31.67/31.84  thf('53', plain, ((v1_funct_1 @ sk_B)),
% 31.67/31.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.84  thf('54', plain, ((v1_relat_1 @ sk_B)),
% 31.67/31.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.84  thf('55', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ sk_B) @ X0)),
% 31.67/31.84      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 31.67/31.84  thf('56', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 31.67/31.84      inference('cnf', [status(esa)], [t2_xboole_1])).
% 31.67/31.84  thf('57', plain,
% 31.67/31.84      (![X4 : $i, X6 : $i]:
% 31.67/31.84         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 31.67/31.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 31.67/31.84  thf('58', plain,
% 31.67/31.84      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 31.67/31.84      inference('sup-', [status(thm)], ['56', '57'])).
% 31.67/31.84  thf('59', plain, (((k1_relat_1 @ sk_B) = (k1_xboole_0))),
% 31.67/31.84      inference('sup-', [status(thm)], ['55', '58'])).
% 31.67/31.84  thf('60', plain,
% 31.67/31.84      (![X30 : $i, X31 : $i]:
% 31.67/31.84         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 31.67/31.84      inference('cnf', [status(esa)], [zf_stmt_4])).
% 31.67/31.84  thf('61', plain,
% 31.67/31.84      (![X30 : $i, X31 : $i]:
% 31.67/31.84         ((zip_tseitin_0 @ X30 @ X31) | ((X31) != (k1_xboole_0)))),
% 31.67/31.84      inference('cnf', [status(esa)], [zf_stmt_4])).
% 31.67/31.84  thf('62', plain, (![X30 : $i]: (zip_tseitin_0 @ X30 @ k1_xboole_0)),
% 31.67/31.84      inference('simplify', [status(thm)], ['61'])).
% 31.67/31.84  thf('63', plain,
% 31.67/31.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.67/31.84         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 31.67/31.84      inference('sup+', [status(thm)], ['60', '62'])).
% 31.67/31.84  thf('64', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 31.67/31.84      inference('eq_fact', [status(thm)], ['63'])).
% 31.67/31.84  thf('65', plain, ($false),
% 31.67/31.84      inference('demod', [status(thm)], ['37', '59', '64'])).
% 31.67/31.84  
% 31.67/31.84  % SZS output end Refutation
% 31.67/31.84  
% 31.67/31.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
