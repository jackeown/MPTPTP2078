%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bchZMq5GPh

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:26 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 385 expanded)
%              Number of leaves         :   45 ( 132 expanded)
%              Depth                    :   23
%              Number of atoms          :  819 (3452 expanded)
%              Number of equality atoms :   92 ( 274 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('3',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != sk_A )
   <= ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
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

thf('6',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,(
    r2_hidden @ sk_C_1 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t121_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('8',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( r2_hidden @ X40 @ ( k1_funct_2 @ X41 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

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

thf('10',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('11',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    r2_hidden @ sk_C_1 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( r2_hidden @ X40 @ ( k1_funct_2 @ X41 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('15',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('17',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('19',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('20',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['12','21'])).

thf('23',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != sk_A )
   <= ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,
    ( ( ( sk_A != sk_A )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('27',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X8: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k4_xboole_0 @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) )
      = k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('32',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_zfmisc_1 @ X16 @ X17 )
        = k1_xboole_0 )
      | ( X17 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('33',plain,(
    ! [X16: $i] :
      ( ( k2_zfmisc_1 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('34',plain,(
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

thf('35',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('39',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference(demod,[status(thm)],['31','33','40'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('42',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('43',plain,
    ( ( k1_xboole_0 != sk_A )
   <= ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference(demod,[status(thm)],['5','41','42'])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != X0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ sk_A ) )
   <= ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference('sup-',[status(thm)],['4','43'])).

thf('45',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference(simplify,[status(thm)],['24'])).

thf(fc3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_xboole_0 @ B ) )
     => ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ) )).

thf('46',plain,(
    ! [X38: $i,X39: $i] :
      ( ( v1_xboole_0 @ X38 )
      | ~ ( v1_xboole_0 @ X39 )
      | ( v1_xboole_0 @ ( k1_funct_2 @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_2])).

thf('47',plain,(
    r2_hidden @ sk_C_1 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('53',plain,
    ( ( v1_xboole_0 @ sk_A )
   <= ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference(demod,[status(thm)],['44','53'])).

thf('55',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('57',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('simplify_reflect+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('59',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','59'])).

thf('61',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('62',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) )
        = X24 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('63',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('64',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ( r1_tarski @ ( k2_relat_1 @ X26 ) @ ( k2_relat_1 @ X25 ) )
      | ~ ( r1_tarski @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('65',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('67',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('68',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','68'])).

thf('70',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','59'])).

thf('71',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('73',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('75',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('77',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_zfmisc_1 @ X16 @ X17 )
        = k1_xboole_0 )
      | ( X16 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('79',plain,(
    ! [X17: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X17 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('81',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','77','79','80'])).

thf('82',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('83',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('84',plain,(
    $false ),
    inference(demod,[status(thm)],['60','81','82','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bchZMq5GPh
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:01:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.71/0.92  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.71/0.92  % Solved by: fo/fo7.sh
% 0.71/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.71/0.92  % done 444 iterations in 0.464s
% 0.71/0.92  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.71/0.92  % SZS output start Refutation
% 0.71/0.92  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.71/0.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.71/0.92  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.71/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.71/0.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.71/0.92  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.71/0.92  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.71/0.92  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.71/0.92  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.71/0.92  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.71/0.92  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.71/0.92  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.71/0.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.71/0.92  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.71/0.92  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.71/0.92  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.71/0.92  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.71/0.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.71/0.92  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.71/0.92  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.71/0.92  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.71/0.92  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.71/0.92  thf(t169_funct_2, conjecture,
% 0.71/0.92    (![A:$i,B:$i,C:$i]:
% 0.71/0.92     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.71/0.92       ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.71/0.92         ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.71/0.92           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ))).
% 0.71/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.71/0.92    (~( ![A:$i,B:$i,C:$i]:
% 0.71/0.92        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.71/0.92          ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.71/0.92            ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.71/0.92              ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) )),
% 0.71/0.92    inference('cnf.neg', [status(esa)], [t169_funct_2])).
% 0.71/0.92  thf('0', plain,
% 0.71/0.92      ((((k1_relat_1 @ sk_C_1) != (sk_A))
% 0.71/0.92        | ~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('1', plain,
% 0.71/0.92      ((~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))
% 0.71/0.92         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)))),
% 0.71/0.92      inference('split', [status(esa)], ['0'])).
% 0.71/0.92  thf(l13_xboole_0, axiom,
% 0.71/0.92    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.71/0.92  thf('2', plain,
% 0.71/0.92      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.71/0.92      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.71/0.92  thf('3', plain,
% 0.71/0.92      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.71/0.92      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.71/0.92  thf('4', plain,
% 0.71/0.92      (![X0 : $i, X1 : $i]:
% 0.71/0.92         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.71/0.92      inference('sup+', [status(thm)], ['2', '3'])).
% 0.71/0.92  thf('5', plain,
% 0.71/0.92      ((((k1_relat_1 @ sk_C_1) != (sk_A)))
% 0.71/0.92         <= (~ (((k1_relat_1 @ sk_C_1) = (sk_A))))),
% 0.71/0.92      inference('split', [status(esa)], ['0'])).
% 0.71/0.92  thf(d1_funct_2, axiom,
% 0.71/0.92    (![A:$i,B:$i,C:$i]:
% 0.71/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.92       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.71/0.92           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.71/0.92             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.71/0.92         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.71/0.92           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.71/0.92             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.71/0.92  thf(zf_stmt_1, axiom,
% 0.71/0.92    (![B:$i,A:$i]:
% 0.71/0.92     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.71/0.92       ( zip_tseitin_0 @ B @ A ) ))).
% 0.71/0.92  thf('6', plain,
% 0.71/0.92      (![X30 : $i, X31 : $i]:
% 0.71/0.92         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.71/0.92  thf('7', plain, ((r2_hidden @ sk_C_1 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf(t121_funct_2, axiom,
% 0.71/0.92    (![A:$i,B:$i,C:$i]:
% 0.71/0.92     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.71/0.92       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.71/0.92         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.71/0.92  thf('8', plain,
% 0.71/0.92      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.71/0.92         ((m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.71/0.92          | ~ (r2_hidden @ X40 @ (k1_funct_2 @ X41 @ X42)))),
% 0.71/0.92      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.71/0.92  thf('9', plain,
% 0.71/0.92      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.71/0.92      inference('sup-', [status(thm)], ['7', '8'])).
% 0.71/0.92  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.71/0.92  thf(zf_stmt_3, axiom,
% 0.71/0.92    (![C:$i,B:$i,A:$i]:
% 0.71/0.92     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.71/0.92       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.71/0.92  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.71/0.92  thf(zf_stmt_5, axiom,
% 0.71/0.92    (![A:$i,B:$i,C:$i]:
% 0.71/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.92       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.71/0.92         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.71/0.92           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.71/0.92             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.71/0.92  thf('10', plain,
% 0.71/0.92      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.71/0.92         (~ (zip_tseitin_0 @ X35 @ X36)
% 0.71/0.92          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 0.71/0.92          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.71/0.92  thf('11', plain,
% 0.71/0.92      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 0.71/0.92        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.71/0.92      inference('sup-', [status(thm)], ['9', '10'])).
% 0.71/0.92  thf('12', plain,
% 0.71/0.92      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A))),
% 0.71/0.92      inference('sup-', [status(thm)], ['6', '11'])).
% 0.71/0.92  thf('13', plain, ((r2_hidden @ sk_C_1 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('14', plain,
% 0.71/0.92      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.71/0.92         ((v1_funct_2 @ X40 @ X41 @ X42)
% 0.71/0.92          | ~ (r2_hidden @ X40 @ (k1_funct_2 @ X41 @ X42)))),
% 0.71/0.92      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.71/0.92  thf('15', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 0.71/0.92      inference('sup-', [status(thm)], ['13', '14'])).
% 0.71/0.92  thf('16', plain,
% 0.71/0.92      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.71/0.92         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 0.71/0.92          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 0.71/0.92          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.71/0.92  thf('17', plain,
% 0.71/0.92      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 0.71/0.92        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.71/0.92      inference('sup-', [status(thm)], ['15', '16'])).
% 0.71/0.92  thf('18', plain,
% 0.71/0.92      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.71/0.92      inference('sup-', [status(thm)], ['7', '8'])).
% 0.71/0.92  thf(redefinition_k1_relset_1, axiom,
% 0.71/0.92    (![A:$i,B:$i,C:$i]:
% 0.71/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.92       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.71/0.92  thf('19', plain,
% 0.71/0.92      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.71/0.92         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 0.71/0.92          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.71/0.92      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.71/0.92  thf('20', plain,
% 0.71/0.92      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.71/0.92      inference('sup-', [status(thm)], ['18', '19'])).
% 0.71/0.92  thf('21', plain,
% 0.71/0.92      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 0.71/0.92        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 0.71/0.92      inference('demod', [status(thm)], ['17', '20'])).
% 0.71/0.92  thf('22', plain,
% 0.71/0.92      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 0.71/0.92      inference('sup-', [status(thm)], ['12', '21'])).
% 0.71/0.92  thf('23', plain,
% 0.71/0.92      ((((k1_relat_1 @ sk_C_1) != (sk_A)))
% 0.71/0.92         <= (~ (((k1_relat_1 @ sk_C_1) = (sk_A))))),
% 0.71/0.92      inference('split', [status(esa)], ['0'])).
% 0.71/0.92  thf('24', plain,
% 0.71/0.92      (((((sk_A) != (sk_A)) | ((sk_B_1) = (k1_xboole_0))))
% 0.71/0.92         <= (~ (((k1_relat_1 @ sk_C_1) = (sk_A))))),
% 0.71/0.92      inference('sup-', [status(thm)], ['22', '23'])).
% 0.71/0.92  thf('25', plain,
% 0.71/0.92      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((k1_relat_1 @ sk_C_1) = (sk_A))))),
% 0.71/0.92      inference('simplify', [status(thm)], ['24'])).
% 0.71/0.92  thf('26', plain,
% 0.71/0.92      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.71/0.92      inference('sup-', [status(thm)], ['7', '8'])).
% 0.71/0.92  thf(t3_subset, axiom,
% 0.71/0.92    (![A:$i,B:$i]:
% 0.71/0.92     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.71/0.92  thf('27', plain,
% 0.71/0.92      (![X18 : $i, X19 : $i]:
% 0.71/0.92         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.71/0.92      inference('cnf', [status(esa)], [t3_subset])).
% 0.71/0.92  thf('28', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.71/0.92      inference('sup-', [status(thm)], ['26', '27'])).
% 0.71/0.92  thf(l32_xboole_1, axiom,
% 0.71/0.92    (![A:$i,B:$i]:
% 0.71/0.92     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.71/0.92  thf('29', plain,
% 0.71/0.92      (![X8 : $i, X10 : $i]:
% 0.71/0.92         (((k4_xboole_0 @ X8 @ X10) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ X10))),
% 0.71/0.92      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.71/0.92  thf('30', plain,
% 0.71/0.92      (((k4_xboole_0 @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.71/0.92      inference('sup-', [status(thm)], ['28', '29'])).
% 0.71/0.92  thf('31', plain,
% 0.71/0.92      ((((k4_xboole_0 @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))
% 0.71/0.92          = (k1_xboole_0)))
% 0.71/0.92         <= (~ (((k1_relat_1 @ sk_C_1) = (sk_A))))),
% 0.71/0.92      inference('sup+', [status(thm)], ['25', '30'])).
% 0.71/0.92  thf(t113_zfmisc_1, axiom,
% 0.71/0.92    (![A:$i,B:$i]:
% 0.71/0.92     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.71/0.92       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.71/0.92  thf('32', plain,
% 0.71/0.92      (![X16 : $i, X17 : $i]:
% 0.71/0.92         (((k2_zfmisc_1 @ X16 @ X17) = (k1_xboole_0))
% 0.71/0.92          | ((X17) != (k1_xboole_0)))),
% 0.71/0.92      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.71/0.92  thf('33', plain,
% 0.71/0.92      (![X16 : $i]: ((k2_zfmisc_1 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 0.71/0.92      inference('simplify', [status(thm)], ['32'])).
% 0.71/0.92  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.71/0.92  thf('34', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.71/0.92      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.71/0.92  thf(t3_xboole_0, axiom,
% 0.71/0.92    (![A:$i,B:$i]:
% 0.71/0.92     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.71/0.92            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.71/0.92       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.71/0.92            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.71/0.92  thf('35', plain,
% 0.71/0.92      (![X4 : $i, X5 : $i]:
% 0.71/0.92         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X5))),
% 0.71/0.92      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.71/0.92  thf(d1_xboole_0, axiom,
% 0.71/0.92    (![A:$i]:
% 0.71/0.92     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.71/0.92  thf('36', plain,
% 0.71/0.92      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.71/0.92      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.71/0.92  thf('37', plain,
% 0.71/0.92      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.71/0.92      inference('sup-', [status(thm)], ['35', '36'])).
% 0.71/0.92  thf('38', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.71/0.92      inference('sup-', [status(thm)], ['34', '37'])).
% 0.71/0.92  thf(t83_xboole_1, axiom,
% 0.71/0.92    (![A:$i,B:$i]:
% 0.71/0.92     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.71/0.92  thf('39', plain,
% 0.71/0.92      (![X12 : $i, X13 : $i]:
% 0.71/0.92         (((k4_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_xboole_0 @ X12 @ X13))),
% 0.71/0.92      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.71/0.92  thf('40', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.71/0.92      inference('sup-', [status(thm)], ['38', '39'])).
% 0.71/0.92  thf('41', plain,
% 0.71/0.92      ((((sk_C_1) = (k1_xboole_0))) <= (~ (((k1_relat_1 @ sk_C_1) = (sk_A))))),
% 0.71/0.92      inference('demod', [status(thm)], ['31', '33', '40'])).
% 0.71/0.92  thf(t60_relat_1, axiom,
% 0.71/0.92    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.71/0.92     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.71/0.92  thf('42', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.71/0.92      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.71/0.92  thf('43', plain,
% 0.71/0.92      ((((k1_xboole_0) != (sk_A))) <= (~ (((k1_relat_1 @ sk_C_1) = (sk_A))))),
% 0.71/0.92      inference('demod', [status(thm)], ['5', '41', '42'])).
% 0.71/0.92  thf('44', plain,
% 0.71/0.92      ((![X0 : $i]:
% 0.71/0.92          (((k1_xboole_0) != (X0))
% 0.71/0.92           | ~ (v1_xboole_0 @ X0)
% 0.71/0.92           | ~ (v1_xboole_0 @ sk_A)))
% 0.71/0.92         <= (~ (((k1_relat_1 @ sk_C_1) = (sk_A))))),
% 0.71/0.92      inference('sup-', [status(thm)], ['4', '43'])).
% 0.71/0.92  thf('45', plain,
% 0.71/0.92      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((k1_relat_1 @ sk_C_1) = (sk_A))))),
% 0.71/0.92      inference('simplify', [status(thm)], ['24'])).
% 0.71/0.92  thf(fc3_funct_2, axiom,
% 0.71/0.92    (![A:$i,B:$i]:
% 0.71/0.92     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) ) =>
% 0.71/0.92       ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ))).
% 0.71/0.92  thf('46', plain,
% 0.71/0.92      (![X38 : $i, X39 : $i]:
% 0.71/0.92         ((v1_xboole_0 @ X38)
% 0.71/0.92          | ~ (v1_xboole_0 @ X39)
% 0.71/0.92          | (v1_xboole_0 @ (k1_funct_2 @ X38 @ X39)))),
% 0.71/0.92      inference('cnf', [status(esa)], [fc3_funct_2])).
% 0.71/0.92  thf('47', plain, ((r2_hidden @ sk_C_1 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('48', plain,
% 0.71/0.92      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.71/0.92      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.71/0.92  thf('49', plain, (~ (v1_xboole_0 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.71/0.92      inference('sup-', [status(thm)], ['47', '48'])).
% 0.71/0.92  thf('50', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A))),
% 0.71/0.92      inference('sup-', [status(thm)], ['46', '49'])).
% 0.71/0.92  thf('51', plain,
% 0.71/0.92      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_A)))
% 0.71/0.92         <= (~ (((k1_relat_1 @ sk_C_1) = (sk_A))))),
% 0.71/0.92      inference('sup-', [status(thm)], ['45', '50'])).
% 0.71/0.92  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.71/0.92      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.71/0.92  thf('53', plain,
% 0.71/0.92      (((v1_xboole_0 @ sk_A)) <= (~ (((k1_relat_1 @ sk_C_1) = (sk_A))))),
% 0.71/0.92      inference('demod', [status(thm)], ['51', '52'])).
% 0.71/0.92  thf('54', plain,
% 0.71/0.92      ((![X0 : $i]: (((k1_xboole_0) != (X0)) | ~ (v1_xboole_0 @ X0)))
% 0.71/0.92         <= (~ (((k1_relat_1 @ sk_C_1) = (sk_A))))),
% 0.71/0.92      inference('demod', [status(thm)], ['44', '53'])).
% 0.71/0.92  thf('55', plain,
% 0.71/0.92      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.71/0.92         <= (~ (((k1_relat_1 @ sk_C_1) = (sk_A))))),
% 0.71/0.92      inference('simplify', [status(thm)], ['54'])).
% 0.71/0.92  thf('56', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.71/0.92      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.71/0.92  thf('57', plain, ((((k1_relat_1 @ sk_C_1) = (sk_A)))),
% 0.71/0.92      inference('simplify_reflect+', [status(thm)], ['55', '56'])).
% 0.71/0.92  thf('58', plain,
% 0.71/0.92      (~ ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)) | 
% 0.71/0.92       ~ (((k1_relat_1 @ sk_C_1) = (sk_A)))),
% 0.71/0.92      inference('split', [status(esa)], ['0'])).
% 0.71/0.92  thf('59', plain, (~ ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.71/0.92      inference('sat_resolution*', [status(thm)], ['57', '58'])).
% 0.71/0.92  thf('60', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)),
% 0.71/0.92      inference('simpl_trail', [status(thm)], ['1', '59'])).
% 0.71/0.92  thf('61', plain,
% 0.71/0.92      (((k4_xboole_0 @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.71/0.92      inference('sup-', [status(thm)], ['28', '29'])).
% 0.71/0.92  thf(t195_relat_1, axiom,
% 0.71/0.92    (![A:$i,B:$i]:
% 0.71/0.92     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.71/0.92          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.71/0.92               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.71/0.92  thf('62', plain,
% 0.71/0.92      (![X23 : $i, X24 : $i]:
% 0.71/0.92         (((X23) = (k1_xboole_0))
% 0.71/0.92          | ((k2_relat_1 @ (k2_zfmisc_1 @ X23 @ X24)) = (X24))
% 0.71/0.92          | ((X24) = (k1_xboole_0)))),
% 0.71/0.92      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.71/0.92  thf('63', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.71/0.92      inference('sup-', [status(thm)], ['26', '27'])).
% 0.71/0.92  thf(t25_relat_1, axiom,
% 0.71/0.92    (![A:$i]:
% 0.71/0.92     ( ( v1_relat_1 @ A ) =>
% 0.71/0.92       ( ![B:$i]:
% 0.71/0.92         ( ( v1_relat_1 @ B ) =>
% 0.71/0.92           ( ( r1_tarski @ A @ B ) =>
% 0.71/0.92             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.71/0.92               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.71/0.92  thf('64', plain,
% 0.71/0.92      (![X25 : $i, X26 : $i]:
% 0.71/0.92         (~ (v1_relat_1 @ X25)
% 0.71/0.92          | (r1_tarski @ (k2_relat_1 @ X26) @ (k2_relat_1 @ X25))
% 0.71/0.92          | ~ (r1_tarski @ X26 @ X25)
% 0.71/0.92          | ~ (v1_relat_1 @ X26))),
% 0.71/0.92      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.71/0.92  thf('65', plain,
% 0.71/0.92      ((~ (v1_relat_1 @ sk_C_1)
% 0.71/0.92        | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ 
% 0.71/0.92           (k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.71/0.92        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.71/0.92      inference('sup-', [status(thm)], ['63', '64'])).
% 0.71/0.92  thf('66', plain, ((v1_relat_1 @ sk_C_1)),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf(fc6_relat_1, axiom,
% 0.71/0.92    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.71/0.92  thf('67', plain,
% 0.71/0.92      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 0.71/0.92      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.71/0.92  thf('68', plain,
% 0.71/0.92      ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ 
% 0.71/0.92        (k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.71/0.92      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.71/0.92  thf('69', plain,
% 0.71/0.92      (((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)
% 0.71/0.92        | ((sk_B_1) = (k1_xboole_0))
% 0.71/0.92        | ((sk_A) = (k1_xboole_0)))),
% 0.71/0.92      inference('sup+', [status(thm)], ['62', '68'])).
% 0.71/0.92  thf('70', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)),
% 0.71/0.92      inference('simpl_trail', [status(thm)], ['1', '59'])).
% 0.71/0.92  thf('71', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.71/0.92      inference('clc', [status(thm)], ['69', '70'])).
% 0.71/0.92  thf('72', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A))),
% 0.71/0.92      inference('sup-', [status(thm)], ['46', '49'])).
% 0.71/0.92  thf('73', plain,
% 0.71/0.92      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.71/0.92        | ((sk_A) = (k1_xboole_0))
% 0.71/0.92        | (v1_xboole_0 @ sk_A))),
% 0.71/0.92      inference('sup-', [status(thm)], ['71', '72'])).
% 0.71/0.92  thf('74', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.71/0.92      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.71/0.92  thf('75', plain, ((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_A))),
% 0.71/0.92      inference('demod', [status(thm)], ['73', '74'])).
% 0.71/0.92  thf('76', plain,
% 0.71/0.92      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.71/0.92      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.71/0.92  thf('77', plain, (((sk_A) = (k1_xboole_0))),
% 0.71/0.92      inference('clc', [status(thm)], ['75', '76'])).
% 0.71/0.92  thf('78', plain,
% 0.71/0.92      (![X16 : $i, X17 : $i]:
% 0.71/0.92         (((k2_zfmisc_1 @ X16 @ X17) = (k1_xboole_0))
% 0.71/0.92          | ((X16) != (k1_xboole_0)))),
% 0.71/0.92      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.71/0.92  thf('79', plain,
% 0.71/0.92      (![X17 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X17) = (k1_xboole_0))),
% 0.71/0.92      inference('simplify', [status(thm)], ['78'])).
% 0.71/0.92  thf('80', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.71/0.92      inference('sup-', [status(thm)], ['38', '39'])).
% 0.71/0.92  thf('81', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.71/0.92      inference('demod', [status(thm)], ['61', '77', '79', '80'])).
% 0.71/0.92  thf('82', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.71/0.92      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.71/0.92  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.71/0.92  thf('83', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.71/0.92      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.71/0.92  thf('84', plain, ($false),
% 0.71/0.92      inference('demod', [status(thm)], ['60', '81', '82', '83'])).
% 0.71/0.92  
% 0.71/0.92  % SZS output end Refutation
% 0.71/0.92  
% 0.71/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
