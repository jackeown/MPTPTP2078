%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WCUWQ3Bxs8

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:23 EST 2020

% Result     : Theorem 1.16s
% Output     : Refutation 1.16s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 425 expanded)
%              Number of leaves         :   47 ( 145 expanded)
%              Depth                    :   23
%              Number of atoms          :  961 (3702 expanded)
%              Number of equality atoms :  107 ( 278 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t169_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
       => ( ( ( k1_relat_1 @ C )
            = A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
         => ( ( ( k1_relat_1 @ C )
              = A )
            & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t169_funct_2])).

thf('0',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != sk_A )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

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

thf('2',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,(
    r2_hidden @ sk_C_1 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t121_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('4',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( r2_hidden @ X43 @ ( k1_funct_2 @ X44 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

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

thf('6',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    r2_hidden @ sk_C_1 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( v1_funct_2 @ X43 @ X44 @ X45 )
      | ~ ( r2_hidden @ X43 @ ( k1_funct_2 @ X44 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('11',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('13',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('16',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('19',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != sk_A )
   <= ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ( ( sk_A != sk_A )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('26',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_zfmisc_1 @ X16 @ X17 )
        = k1_xboole_0 )
      | ( X17 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('27',plain,(
    ! [X16: $i] :
      ( ( k2_zfmisc_1 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( r1_tarski @ sk_C_1 @ k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference(demod,[status(thm)],['25','27'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ( r1_tarski @ ( k1_relat_1 @ X28 ) @ ( k1_relat_1 @ X27 ) )
      | ~ ( r1_tarski @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('30',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) )
   <= ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('33',plain,(
    ! [X22: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X22 ) )
      | ~ ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('34',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('38',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('39',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference(demod,[status(thm)],['30','31','36','39'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('41',plain,(
    ! [X8: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('42',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('44',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('48',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference('sup+',[status(thm)],['42','49'])).

thf('51',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != sk_A )
   <= ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf(fc3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_xboole_0 @ B ) )
     => ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ) )).

thf('55',plain,(
    ! [X41: $i,X42: $i] :
      ( ( v1_xboole_0 @ X41 )
      | ~ ( v1_xboole_0 @ X42 )
      | ( v1_xboole_0 @ ( k1_funct_2 @ X41 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_2])).

thf('56',plain,(
    r2_hidden @ sk_C_1 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('58',plain,(
    ~ ( v1_xboole_0 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('64',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('66',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != sk_A )
   <= ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('68',plain,
    ( ( ( sk_A != sk_A )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference(demod,[status(thm)],['51','69'])).

thf('71',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['50','70'])).

thf('72',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('73',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','73'])).

thf('75',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('76',plain,(
    ! [X8: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('77',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['75','76'])).

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('78',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) )
        = X26 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('79',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('80',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ( r1_tarski @ ( k2_relat_1 @ X28 ) @ ( k2_relat_1 @ X27 ) )
      | ~ ( r1_tarski @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('81',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('83',plain,(
    ! [X23: $i,X24: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('84',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','84'])).

thf('86',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','73'])).

thf('87',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('89',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('91',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('93',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_zfmisc_1 @ X16 @ X17 )
        = k1_xboole_0 )
      | ( X16 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('95',plain,(
    ! [X17: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X17 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('97',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['77','93','95','96'])).

thf('98',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','35'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('99',plain,(
    ! [X29: $i] :
      ( ( ( k1_relat_1 @ X29 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X29 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('100',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('102',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['102'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('104',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('105',plain,(
    $false ),
    inference(demod,[status(thm)],['74','97','103','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WCUWQ3Bxs8
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:26:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.16/1.34  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.16/1.34  % Solved by: fo/fo7.sh
% 1.16/1.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.16/1.34  % done 479 iterations in 0.828s
% 1.16/1.34  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.16/1.34  % SZS output start Refutation
% 1.16/1.34  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.16/1.34  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.16/1.34  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.16/1.34  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.16/1.34  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.16/1.34  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.16/1.34  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.16/1.34  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.16/1.34  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.16/1.34  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.16/1.34  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.16/1.34  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.16/1.34  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.16/1.34  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.16/1.34  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.16/1.34  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 1.16/1.34  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.16/1.34  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.16/1.34  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.16/1.34  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.16/1.34  thf(sk_A_type, type, sk_A: $i).
% 1.16/1.34  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.16/1.34  thf(t169_funct_2, conjecture,
% 1.16/1.34    (![A:$i,B:$i,C:$i]:
% 1.16/1.34     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.16/1.34       ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 1.16/1.34         ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 1.16/1.34           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ))).
% 1.16/1.34  thf(zf_stmt_0, negated_conjecture,
% 1.16/1.34    (~( ![A:$i,B:$i,C:$i]:
% 1.16/1.34        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.16/1.34          ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 1.16/1.34            ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 1.16/1.34              ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) )),
% 1.16/1.34    inference('cnf.neg', [status(esa)], [t169_funct_2])).
% 1.16/1.34  thf('0', plain,
% 1.16/1.34      ((((k1_relat_1 @ sk_C_1) != (sk_A))
% 1.16/1.34        | ~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.34  thf('1', plain,
% 1.16/1.34      ((~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))
% 1.16/1.34         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)))),
% 1.16/1.34      inference('split', [status(esa)], ['0'])).
% 1.16/1.34  thf(d1_funct_2, axiom,
% 1.16/1.34    (![A:$i,B:$i,C:$i]:
% 1.16/1.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.16/1.34       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.16/1.34           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.16/1.34             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.16/1.34         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.16/1.34           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.16/1.34             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.16/1.34  thf(zf_stmt_1, axiom,
% 1.16/1.34    (![B:$i,A:$i]:
% 1.16/1.34     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.16/1.34       ( zip_tseitin_0 @ B @ A ) ))).
% 1.16/1.34  thf('2', plain,
% 1.16/1.34      (![X33 : $i, X34 : $i]:
% 1.16/1.34         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.16/1.34  thf('3', plain, ((r2_hidden @ sk_C_1 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.34  thf(t121_funct_2, axiom,
% 1.16/1.34    (![A:$i,B:$i,C:$i]:
% 1.16/1.34     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 1.16/1.34       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.16/1.34         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.16/1.34  thf('4', plain,
% 1.16/1.34      (![X43 : $i, X44 : $i, X45 : $i]:
% 1.16/1.34         ((m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 1.16/1.34          | ~ (r2_hidden @ X43 @ (k1_funct_2 @ X44 @ X45)))),
% 1.16/1.34      inference('cnf', [status(esa)], [t121_funct_2])).
% 1.16/1.34  thf('5', plain,
% 1.16/1.34      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.16/1.34      inference('sup-', [status(thm)], ['3', '4'])).
% 1.16/1.34  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.16/1.34  thf(zf_stmt_3, axiom,
% 1.16/1.34    (![C:$i,B:$i,A:$i]:
% 1.16/1.34     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.16/1.34       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.16/1.34  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.16/1.34  thf(zf_stmt_5, axiom,
% 1.16/1.34    (![A:$i,B:$i,C:$i]:
% 1.16/1.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.16/1.34       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.16/1.34         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.16/1.34           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.16/1.34             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.16/1.34  thf('6', plain,
% 1.16/1.34      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.16/1.34         (~ (zip_tseitin_0 @ X38 @ X39)
% 1.16/1.34          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 1.16/1.34          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.16/1.34  thf('7', plain,
% 1.16/1.34      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.16/1.34        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.16/1.34      inference('sup-', [status(thm)], ['5', '6'])).
% 1.16/1.34  thf('8', plain,
% 1.16/1.34      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A))),
% 1.16/1.34      inference('sup-', [status(thm)], ['2', '7'])).
% 1.16/1.34  thf('9', plain, ((r2_hidden @ sk_C_1 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.34  thf('10', plain,
% 1.16/1.34      (![X43 : $i, X44 : $i, X45 : $i]:
% 1.16/1.34         ((v1_funct_2 @ X43 @ X44 @ X45)
% 1.16/1.34          | ~ (r2_hidden @ X43 @ (k1_funct_2 @ X44 @ X45)))),
% 1.16/1.34      inference('cnf', [status(esa)], [t121_funct_2])).
% 1.16/1.34  thf('11', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 1.16/1.34      inference('sup-', [status(thm)], ['9', '10'])).
% 1.16/1.34  thf('12', plain,
% 1.16/1.34      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.16/1.34         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 1.16/1.34          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 1.16/1.34          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.16/1.34  thf('13', plain,
% 1.16/1.34      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.16/1.34        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 1.16/1.34      inference('sup-', [status(thm)], ['11', '12'])).
% 1.16/1.34  thf('14', plain,
% 1.16/1.34      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.16/1.34      inference('sup-', [status(thm)], ['3', '4'])).
% 1.16/1.34  thf(redefinition_k1_relset_1, axiom,
% 1.16/1.34    (![A:$i,B:$i,C:$i]:
% 1.16/1.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.16/1.34       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.16/1.34  thf('15', plain,
% 1.16/1.34      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.16/1.34         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 1.16/1.34          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 1.16/1.34      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.16/1.34  thf('16', plain,
% 1.16/1.34      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 1.16/1.34      inference('sup-', [status(thm)], ['14', '15'])).
% 1.16/1.34  thf('17', plain,
% 1.16/1.34      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.16/1.34        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.16/1.34      inference('demod', [status(thm)], ['13', '16'])).
% 1.16/1.34  thf('18', plain,
% 1.16/1.34      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.16/1.34      inference('sup-', [status(thm)], ['8', '17'])).
% 1.16/1.34  thf('19', plain,
% 1.16/1.34      ((((k1_relat_1 @ sk_C_1) != (sk_A)))
% 1.16/1.34         <= (~ (((k1_relat_1 @ sk_C_1) = (sk_A))))),
% 1.16/1.34      inference('split', [status(esa)], ['0'])).
% 1.16/1.34  thf('20', plain,
% 1.16/1.34      (((((sk_A) != (sk_A)) | ((sk_B_1) = (k1_xboole_0))))
% 1.16/1.34         <= (~ (((k1_relat_1 @ sk_C_1) = (sk_A))))),
% 1.16/1.34      inference('sup-', [status(thm)], ['18', '19'])).
% 1.16/1.34  thf('21', plain,
% 1.16/1.34      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((k1_relat_1 @ sk_C_1) = (sk_A))))),
% 1.16/1.34      inference('simplify', [status(thm)], ['20'])).
% 1.16/1.34  thf('22', plain,
% 1.16/1.34      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.16/1.34      inference('sup-', [status(thm)], ['3', '4'])).
% 1.16/1.34  thf(t3_subset, axiom,
% 1.16/1.34    (![A:$i,B:$i]:
% 1.16/1.34     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.16/1.34  thf('23', plain,
% 1.16/1.34      (![X18 : $i, X19 : $i]:
% 1.16/1.34         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 1.16/1.34      inference('cnf', [status(esa)], [t3_subset])).
% 1.16/1.34  thf('24', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 1.16/1.34      inference('sup-', [status(thm)], ['22', '23'])).
% 1.16/1.34  thf('25', plain,
% 1.16/1.34      (((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))
% 1.16/1.34         <= (~ (((k1_relat_1 @ sk_C_1) = (sk_A))))),
% 1.16/1.34      inference('sup+', [status(thm)], ['21', '24'])).
% 1.16/1.34  thf(t113_zfmisc_1, axiom,
% 1.16/1.34    (![A:$i,B:$i]:
% 1.16/1.34     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.16/1.34       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.16/1.34  thf('26', plain,
% 1.16/1.34      (![X16 : $i, X17 : $i]:
% 1.16/1.34         (((k2_zfmisc_1 @ X16 @ X17) = (k1_xboole_0))
% 1.16/1.34          | ((X17) != (k1_xboole_0)))),
% 1.16/1.34      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.16/1.34  thf('27', plain,
% 1.16/1.34      (![X16 : $i]: ((k2_zfmisc_1 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 1.16/1.34      inference('simplify', [status(thm)], ['26'])).
% 1.16/1.34  thf('28', plain,
% 1.16/1.34      (((r1_tarski @ sk_C_1 @ k1_xboole_0))
% 1.16/1.34         <= (~ (((k1_relat_1 @ sk_C_1) = (sk_A))))),
% 1.16/1.34      inference('demod', [status(thm)], ['25', '27'])).
% 1.16/1.34  thf(t25_relat_1, axiom,
% 1.16/1.34    (![A:$i]:
% 1.16/1.34     ( ( v1_relat_1 @ A ) =>
% 1.16/1.34       ( ![B:$i]:
% 1.16/1.34         ( ( v1_relat_1 @ B ) =>
% 1.16/1.34           ( ( r1_tarski @ A @ B ) =>
% 1.16/1.34             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 1.16/1.34               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 1.16/1.34  thf('29', plain,
% 1.16/1.34      (![X27 : $i, X28 : $i]:
% 1.16/1.34         (~ (v1_relat_1 @ X27)
% 1.16/1.34          | (r1_tarski @ (k1_relat_1 @ X28) @ (k1_relat_1 @ X27))
% 1.16/1.34          | ~ (r1_tarski @ X28 @ X27)
% 1.16/1.34          | ~ (v1_relat_1 @ X28))),
% 1.16/1.34      inference('cnf', [status(esa)], [t25_relat_1])).
% 1.16/1.34  thf('30', plain,
% 1.16/1.34      (((~ (v1_relat_1 @ sk_C_1)
% 1.16/1.34         | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_relat_1 @ k1_xboole_0))
% 1.16/1.34         | ~ (v1_relat_1 @ k1_xboole_0)))
% 1.16/1.34         <= (~ (((k1_relat_1 @ sk_C_1) = (sk_A))))),
% 1.16/1.34      inference('sup-', [status(thm)], ['28', '29'])).
% 1.16/1.34  thf('31', plain, ((v1_relat_1 @ sk_C_1)),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.34  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.16/1.34  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.16/1.34      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.16/1.34  thf(fc10_relat_1, axiom,
% 1.16/1.34    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 1.16/1.34  thf('33', plain,
% 1.16/1.34      (![X22 : $i]:
% 1.16/1.34         ((v1_xboole_0 @ (k1_relat_1 @ X22)) | ~ (v1_xboole_0 @ X22))),
% 1.16/1.34      inference('cnf', [status(esa)], [fc10_relat_1])).
% 1.16/1.34  thf(l13_xboole_0, axiom,
% 1.16/1.34    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.16/1.34  thf('34', plain,
% 1.16/1.34      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 1.16/1.34      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.16/1.34  thf('35', plain,
% 1.16/1.34      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 1.16/1.34      inference('sup-', [status(thm)], ['33', '34'])).
% 1.16/1.34  thf('36', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.16/1.34      inference('sup-', [status(thm)], ['32', '35'])).
% 1.16/1.34  thf('37', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.16/1.34      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.16/1.34  thf(cc1_relat_1, axiom,
% 1.16/1.34    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 1.16/1.34  thf('38', plain, (![X21 : $i]: ((v1_relat_1 @ X21) | ~ (v1_xboole_0 @ X21))),
% 1.16/1.34      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.16/1.34  thf('39', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.16/1.34      inference('sup-', [status(thm)], ['37', '38'])).
% 1.16/1.34  thf('40', plain,
% 1.16/1.34      (((r1_tarski @ (k1_relat_1 @ sk_C_1) @ k1_xboole_0))
% 1.16/1.34         <= (~ (((k1_relat_1 @ sk_C_1) = (sk_A))))),
% 1.16/1.34      inference('demod', [status(thm)], ['30', '31', '36', '39'])).
% 1.16/1.34  thf(l32_xboole_1, axiom,
% 1.16/1.34    (![A:$i,B:$i]:
% 1.16/1.34     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.16/1.34  thf('41', plain,
% 1.16/1.34      (![X8 : $i, X10 : $i]:
% 1.16/1.34         (((k4_xboole_0 @ X8 @ X10) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ X10))),
% 1.16/1.34      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.16/1.34  thf('42', plain,
% 1.16/1.34      ((((k4_xboole_0 @ (k1_relat_1 @ sk_C_1) @ k1_xboole_0) = (k1_xboole_0)))
% 1.16/1.34         <= (~ (((k1_relat_1 @ sk_C_1) = (sk_A))))),
% 1.16/1.34      inference('sup-', [status(thm)], ['40', '41'])).
% 1.16/1.34  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.16/1.34      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.16/1.34  thf(t3_xboole_0, axiom,
% 1.16/1.34    (![A:$i,B:$i]:
% 1.16/1.34     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.16/1.34            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.16/1.34       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.16/1.34            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.16/1.34  thf('44', plain,
% 1.16/1.34      (![X4 : $i, X5 : $i]:
% 1.16/1.34         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X5))),
% 1.16/1.34      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.16/1.34  thf(d1_xboole_0, axiom,
% 1.16/1.34    (![A:$i]:
% 1.16/1.34     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.16/1.34  thf('45', plain,
% 1.16/1.34      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.16/1.34      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.16/1.34  thf('46', plain,
% 1.16/1.34      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 1.16/1.34      inference('sup-', [status(thm)], ['44', '45'])).
% 1.16/1.34  thf('47', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.16/1.34      inference('sup-', [status(thm)], ['43', '46'])).
% 1.16/1.34  thf(t83_xboole_1, axiom,
% 1.16/1.34    (![A:$i,B:$i]:
% 1.16/1.34     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.16/1.34  thf('48', plain,
% 1.16/1.34      (![X12 : $i, X13 : $i]:
% 1.16/1.34         (((k4_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_xboole_0 @ X12 @ X13))),
% 1.16/1.34      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.16/1.34  thf('49', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.16/1.34      inference('sup-', [status(thm)], ['47', '48'])).
% 1.16/1.34  thf('50', plain,
% 1.16/1.34      ((((k1_xboole_0) = (k1_relat_1 @ sk_C_1)))
% 1.16/1.34         <= (~ (((k1_relat_1 @ sk_C_1) = (sk_A))))),
% 1.16/1.34      inference('sup+', [status(thm)], ['42', '49'])).
% 1.16/1.34  thf('51', plain,
% 1.16/1.34      ((((k1_relat_1 @ sk_C_1) != (sk_A)))
% 1.16/1.34         <= (~ (((k1_relat_1 @ sk_C_1) = (sk_A))))),
% 1.16/1.34      inference('split', [status(esa)], ['0'])).
% 1.16/1.34  thf('52', plain,
% 1.16/1.34      (![X33 : $i, X34 : $i]:
% 1.16/1.34         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.16/1.34  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.16/1.34      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.16/1.34  thf('54', plain,
% 1.16/1.34      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.16/1.34      inference('sup+', [status(thm)], ['52', '53'])).
% 1.16/1.34  thf(fc3_funct_2, axiom,
% 1.16/1.34    (![A:$i,B:$i]:
% 1.16/1.34     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) ) =>
% 1.16/1.34       ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ))).
% 1.16/1.34  thf('55', plain,
% 1.16/1.34      (![X41 : $i, X42 : $i]:
% 1.16/1.34         ((v1_xboole_0 @ X41)
% 1.16/1.34          | ~ (v1_xboole_0 @ X42)
% 1.16/1.34          | (v1_xboole_0 @ (k1_funct_2 @ X41 @ X42)))),
% 1.16/1.34      inference('cnf', [status(esa)], [fc3_funct_2])).
% 1.16/1.34  thf('56', plain, ((r2_hidden @ sk_C_1 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.34  thf('57', plain,
% 1.16/1.34      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.16/1.34      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.16/1.34  thf('58', plain, (~ (v1_xboole_0 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 1.16/1.34      inference('sup-', [status(thm)], ['56', '57'])).
% 1.16/1.34  thf('59', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A))),
% 1.16/1.34      inference('sup-', [status(thm)], ['55', '58'])).
% 1.16/1.34  thf('60', plain,
% 1.16/1.34      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_A))),
% 1.16/1.34      inference('sup-', [status(thm)], ['54', '59'])).
% 1.16/1.34  thf('61', plain,
% 1.16/1.34      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 1.16/1.34      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.16/1.34  thf('62', plain,
% 1.16/1.34      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | ((sk_A) = (k1_xboole_0)))),
% 1.16/1.34      inference('sup-', [status(thm)], ['60', '61'])).
% 1.16/1.34  thf('63', plain,
% 1.16/1.34      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.16/1.34        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.16/1.34      inference('sup-', [status(thm)], ['5', '6'])).
% 1.16/1.34  thf('64', plain,
% 1.16/1.34      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A))),
% 1.16/1.34      inference('sup-', [status(thm)], ['62', '63'])).
% 1.16/1.34  thf('65', plain,
% 1.16/1.34      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.16/1.34        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.16/1.34      inference('demod', [status(thm)], ['13', '16'])).
% 1.16/1.34  thf('66', plain,
% 1.16/1.34      ((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.16/1.34      inference('sup-', [status(thm)], ['64', '65'])).
% 1.16/1.34  thf('67', plain,
% 1.16/1.34      ((((k1_relat_1 @ sk_C_1) != (sk_A)))
% 1.16/1.34         <= (~ (((k1_relat_1 @ sk_C_1) = (sk_A))))),
% 1.16/1.34      inference('split', [status(esa)], ['0'])).
% 1.16/1.34  thf('68', plain,
% 1.16/1.34      (((((sk_A) != (sk_A)) | ((sk_A) = (k1_xboole_0))))
% 1.16/1.34         <= (~ (((k1_relat_1 @ sk_C_1) = (sk_A))))),
% 1.16/1.34      inference('sup-', [status(thm)], ['66', '67'])).
% 1.16/1.34  thf('69', plain,
% 1.16/1.34      ((((sk_A) = (k1_xboole_0))) <= (~ (((k1_relat_1 @ sk_C_1) = (sk_A))))),
% 1.16/1.34      inference('simplify', [status(thm)], ['68'])).
% 1.16/1.34  thf('70', plain,
% 1.16/1.34      ((((k1_relat_1 @ sk_C_1) != (k1_xboole_0)))
% 1.16/1.34         <= (~ (((k1_relat_1 @ sk_C_1) = (sk_A))))),
% 1.16/1.34      inference('demod', [status(thm)], ['51', '69'])).
% 1.16/1.34  thf('71', plain, ((((k1_relat_1 @ sk_C_1) = (sk_A)))),
% 1.16/1.34      inference('simplify_reflect-', [status(thm)], ['50', '70'])).
% 1.16/1.34  thf('72', plain,
% 1.16/1.34      (~ ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)) | 
% 1.16/1.34       ~ (((k1_relat_1 @ sk_C_1) = (sk_A)))),
% 1.16/1.34      inference('split', [status(esa)], ['0'])).
% 1.16/1.34  thf('73', plain, (~ ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 1.16/1.34      inference('sat_resolution*', [status(thm)], ['71', '72'])).
% 1.16/1.34  thf('74', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)),
% 1.16/1.34      inference('simpl_trail', [status(thm)], ['1', '73'])).
% 1.16/1.34  thf('75', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 1.16/1.34      inference('sup-', [status(thm)], ['22', '23'])).
% 1.16/1.34  thf('76', plain,
% 1.16/1.34      (![X8 : $i, X10 : $i]:
% 1.16/1.34         (((k4_xboole_0 @ X8 @ X10) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ X10))),
% 1.16/1.34      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.16/1.34  thf('77', plain,
% 1.16/1.34      (((k4_xboole_0 @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 1.16/1.34      inference('sup-', [status(thm)], ['75', '76'])).
% 1.16/1.34  thf(t195_relat_1, axiom,
% 1.16/1.34    (![A:$i,B:$i]:
% 1.16/1.34     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.16/1.34          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 1.16/1.34               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 1.16/1.34  thf('78', plain,
% 1.16/1.34      (![X25 : $i, X26 : $i]:
% 1.16/1.34         (((X25) = (k1_xboole_0))
% 1.16/1.34          | ((k2_relat_1 @ (k2_zfmisc_1 @ X25 @ X26)) = (X26))
% 1.16/1.34          | ((X26) = (k1_xboole_0)))),
% 1.16/1.34      inference('cnf', [status(esa)], [t195_relat_1])).
% 1.16/1.34  thf('79', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 1.16/1.34      inference('sup-', [status(thm)], ['22', '23'])).
% 1.16/1.34  thf('80', plain,
% 1.16/1.34      (![X27 : $i, X28 : $i]:
% 1.16/1.34         (~ (v1_relat_1 @ X27)
% 1.16/1.34          | (r1_tarski @ (k2_relat_1 @ X28) @ (k2_relat_1 @ X27))
% 1.16/1.34          | ~ (r1_tarski @ X28 @ X27)
% 1.16/1.34          | ~ (v1_relat_1 @ X28))),
% 1.16/1.34      inference('cnf', [status(esa)], [t25_relat_1])).
% 1.16/1.34  thf('81', plain,
% 1.16/1.34      ((~ (v1_relat_1 @ sk_C_1)
% 1.16/1.34        | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ 
% 1.16/1.34           (k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 1.16/1.34        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.16/1.34      inference('sup-', [status(thm)], ['79', '80'])).
% 1.16/1.34  thf('82', plain, ((v1_relat_1 @ sk_C_1)),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.34  thf(fc6_relat_1, axiom,
% 1.16/1.34    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.16/1.34  thf('83', plain,
% 1.16/1.34      (![X23 : $i, X24 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X23 @ X24))),
% 1.16/1.34      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.16/1.34  thf('84', plain,
% 1.16/1.34      ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ 
% 1.16/1.34        (k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.16/1.34      inference('demod', [status(thm)], ['81', '82', '83'])).
% 1.16/1.34  thf('85', plain,
% 1.16/1.34      (((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)
% 1.16/1.34        | ((sk_B_1) = (k1_xboole_0))
% 1.16/1.34        | ((sk_A) = (k1_xboole_0)))),
% 1.16/1.34      inference('sup+', [status(thm)], ['78', '84'])).
% 1.16/1.34  thf('86', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)),
% 1.16/1.34      inference('simpl_trail', [status(thm)], ['1', '73'])).
% 1.16/1.34  thf('87', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 1.16/1.34      inference('clc', [status(thm)], ['85', '86'])).
% 1.16/1.34  thf('88', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A))),
% 1.16/1.34      inference('sup-', [status(thm)], ['55', '58'])).
% 1.16/1.34  thf('89', plain,
% 1.16/1.34      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.16/1.34        | ((sk_A) = (k1_xboole_0))
% 1.16/1.34        | (v1_xboole_0 @ sk_A))),
% 1.16/1.34      inference('sup-', [status(thm)], ['87', '88'])).
% 1.16/1.34  thf('90', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.16/1.34      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.16/1.34  thf('91', plain, ((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_A))),
% 1.16/1.34      inference('demod', [status(thm)], ['89', '90'])).
% 1.16/1.34  thf('92', plain,
% 1.16/1.34      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 1.16/1.34      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.16/1.34  thf('93', plain, (((sk_A) = (k1_xboole_0))),
% 1.16/1.34      inference('clc', [status(thm)], ['91', '92'])).
% 1.16/1.34  thf('94', plain,
% 1.16/1.34      (![X16 : $i, X17 : $i]:
% 1.16/1.34         (((k2_zfmisc_1 @ X16 @ X17) = (k1_xboole_0))
% 1.16/1.34          | ((X16) != (k1_xboole_0)))),
% 1.16/1.34      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.16/1.34  thf('95', plain,
% 1.16/1.34      (![X17 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X17) = (k1_xboole_0))),
% 1.16/1.34      inference('simplify', [status(thm)], ['94'])).
% 1.16/1.34  thf('96', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.16/1.34      inference('sup-', [status(thm)], ['47', '48'])).
% 1.16/1.34  thf('97', plain, (((sk_C_1) = (k1_xboole_0))),
% 1.16/1.34      inference('demod', [status(thm)], ['77', '93', '95', '96'])).
% 1.16/1.34  thf('98', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.16/1.34      inference('sup-', [status(thm)], ['32', '35'])).
% 1.16/1.34  thf(t65_relat_1, axiom,
% 1.16/1.34    (![A:$i]:
% 1.16/1.34     ( ( v1_relat_1 @ A ) =>
% 1.16/1.34       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 1.16/1.34         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 1.16/1.34  thf('99', plain,
% 1.16/1.34      (![X29 : $i]:
% 1.16/1.34         (((k1_relat_1 @ X29) != (k1_xboole_0))
% 1.16/1.34          | ((k2_relat_1 @ X29) = (k1_xboole_0))
% 1.16/1.34          | ~ (v1_relat_1 @ X29))),
% 1.16/1.34      inference('cnf', [status(esa)], [t65_relat_1])).
% 1.16/1.34  thf('100', plain,
% 1.16/1.34      ((((k1_xboole_0) != (k1_xboole_0))
% 1.16/1.34        | ~ (v1_relat_1 @ k1_xboole_0)
% 1.16/1.34        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 1.16/1.34      inference('sup-', [status(thm)], ['98', '99'])).
% 1.16/1.34  thf('101', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.16/1.34      inference('sup-', [status(thm)], ['37', '38'])).
% 1.16/1.34  thf('102', plain,
% 1.16/1.34      ((((k1_xboole_0) != (k1_xboole_0))
% 1.16/1.34        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 1.16/1.34      inference('demod', [status(thm)], ['100', '101'])).
% 1.16/1.34  thf('103', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.16/1.34      inference('simplify', [status(thm)], ['102'])).
% 1.16/1.34  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.16/1.34  thf('104', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 1.16/1.34      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.16/1.34  thf('105', plain, ($false),
% 1.16/1.34      inference('demod', [status(thm)], ['74', '97', '103', '104'])).
% 1.16/1.34  
% 1.16/1.34  % SZS output end Refutation
% 1.16/1.34  
% 1.16/1.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
