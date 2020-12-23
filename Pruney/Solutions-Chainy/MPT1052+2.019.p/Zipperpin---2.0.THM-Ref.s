%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0dWEUSQuSW

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:26 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 919 expanded)
%              Number of leaves         :   47 ( 296 expanded)
%              Depth                    :   25
%              Number of atoms          :  922 (8245 expanded)
%              Number of equality atoms :   87 ( 561 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf('0',plain,(
    r2_hidden @ sk_C_1 @ ( k1_funct_2 @ sk_A_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t121_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( r2_hidden @ X41 @ ( k1_funct_2 @ X42 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ( r1_tarski @ ( k1_relat_1 @ X26 ) @ ( k1_relat_1 @ X25 ) )
      | ~ ( r1_tarski @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('9',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

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

thf('10',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

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

thf('12',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('13',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A_1 )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    r2_hidden @ sk_C_1 @ ( k1_funct_2 @ sk_A_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( v1_funct_2 @ X41 @ X42 @ X43 )
      | ~ ( r2_hidden @ X41 @ ( k1_funct_2 @ X42 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('17',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A_1 )
    | ( sk_A_1
      = ( k1_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A_1 )
    | ( sk_A_1
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A_1
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['14','23'])).

thf('25',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != sk_A_1 )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != sk_A_1 )
   <= ( ( k1_relat_1 @ sk_C_1 )
     != sk_A_1 ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['25'])).

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('28',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) )
        = X24 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('29',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('30',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ( r1_tarski @ ( k2_relat_1 @ X26 ) @ ( k2_relat_1 @ X25 ) )
      | ~ ( r1_tarski @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('34',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','34'])).

thf('36',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['25'])).

thf('37',plain,
    ( ( ( sk_A_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(fc3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_xboole_0 @ B ) )
     => ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ) )).

thf('38',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v1_xboole_0 @ X39 )
      | ~ ( v1_xboole_0 @ X40 )
      | ( v1_xboole_0 @ ( k1_funct_2 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_2])).

thf('39',plain,(
    r2_hidden @ sk_C_1 @ ( k1_funct_2 @ sk_A_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('41',plain,(
    ~ ( v1_xboole_0 @ ( k1_funct_2 @ sk_A_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A_1 = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A_1 ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('44',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('45',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('46',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('47',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['44','47'])).

thf('49',plain,
    ( ( ( sk_A_1 = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A_1 ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['43','48'])).

thf('50',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('51',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A_1 )
    | ( sk_A_1
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('53',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ k1_xboole_0 )
      | ( sk_A_1
        = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('55',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('57',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A_1 )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('58',plain,
    ( ( ~ ( zip_tseitin_0 @ sk_B_1 @ k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A_1 ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X32 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('60',plain,(
    ! [X31: $i] :
      ( zip_tseitin_0 @ X31 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('62',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ k1_xboole_0 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['58','60','61'])).

thf('63',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['55','62'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('64',plain,(
    ! [X27: $i] :
      ( ( ( k1_relat_1 @ X27 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X27 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('65',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( ( k2_relat_1 @ sk_C_1 )
        = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_C_1 )
        = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['67'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('69',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('70',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['27','68','69'])).

thf('71',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != sk_A_1 )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['25'])).

thf('72',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != sk_A_1 ),
    inference('sat_resolution*',[status(thm)],['70','71'])).

thf('73',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != sk_A_1 ),
    inference(simpl_trail,[status(thm)],['26','72'])).

thf('74',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['24','73'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('75',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_zfmisc_1 @ X16 @ X17 )
        = k1_xboole_0 )
      | ( X17 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('76',plain,(
    ! [X16: $i] :
      ( ( k2_zfmisc_1 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['75'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('77',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('78',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['9','74','76','77'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('79',plain,(
    ! [X8: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('80',plain,
    ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['44','47'])).

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

thf('82',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('86',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['80','87'])).

thf('89',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != sk_A_1 ),
    inference(simpl_trail,[status(thm)],['26','72'])).

thf('90',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('91',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['24','73'])).

thf('92',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['44','47'])).

thf('93',plain,(
    v1_xboole_0 @ sk_A_1 ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('95',plain,(
    sk_A_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['89','95'])).

thf('97',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['88','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0dWEUSQuSW
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:06:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.56/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.56/0.72  % Solved by: fo/fo7.sh
% 0.56/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.56/0.72  % done 292 iterations in 0.264s
% 0.56/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.56/0.72  % SZS output start Refutation
% 0.56/0.72  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.56/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.56/0.72  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.56/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.56/0.72  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.56/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.56/0.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.56/0.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.56/0.72  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.56/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.56/0.72  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.56/0.72  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.56/0.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.56/0.72  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.56/0.72  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.56/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.56/0.72  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.56/0.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.56/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.56/0.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.56/0.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.56/0.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.56/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.56/0.72  thf(t169_funct_2, conjecture,
% 0.56/0.72    (![A:$i,B:$i,C:$i]:
% 0.56/0.72     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.56/0.72       ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.56/0.72         ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.56/0.72           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ))).
% 0.56/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.56/0.72    (~( ![A:$i,B:$i,C:$i]:
% 0.56/0.72        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.56/0.72          ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.56/0.72            ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.56/0.72              ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) )),
% 0.56/0.72    inference('cnf.neg', [status(esa)], [t169_funct_2])).
% 0.56/0.72  thf('0', plain, ((r2_hidden @ sk_C_1 @ (k1_funct_2 @ sk_A_1 @ sk_B_1))),
% 0.56/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.72  thf(t121_funct_2, axiom,
% 0.56/0.72    (![A:$i,B:$i,C:$i]:
% 0.56/0.72     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.56/0.72       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.56/0.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.56/0.72  thf('1', plain,
% 0.56/0.72      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.56/0.72         ((m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.56/0.72          | ~ (r2_hidden @ X41 @ (k1_funct_2 @ X42 @ X43)))),
% 0.56/0.72      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.56/0.72  thf('2', plain,
% 0.56/0.72      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.56/0.72      inference('sup-', [status(thm)], ['0', '1'])).
% 0.56/0.72  thf(t3_subset, axiom,
% 0.56/0.72    (![A:$i,B:$i]:
% 0.56/0.72     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.56/0.72  thf('3', plain,
% 0.56/0.72      (![X18 : $i, X19 : $i]:
% 0.56/0.72         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.56/0.72      inference('cnf', [status(esa)], [t3_subset])).
% 0.56/0.72  thf('4', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1))),
% 0.56/0.72      inference('sup-', [status(thm)], ['2', '3'])).
% 0.56/0.72  thf(t25_relat_1, axiom,
% 0.56/0.72    (![A:$i]:
% 0.56/0.72     ( ( v1_relat_1 @ A ) =>
% 0.56/0.72       ( ![B:$i]:
% 0.56/0.72         ( ( v1_relat_1 @ B ) =>
% 0.56/0.72           ( ( r1_tarski @ A @ B ) =>
% 0.56/0.72             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.56/0.72               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.56/0.72  thf('5', plain,
% 0.56/0.72      (![X25 : $i, X26 : $i]:
% 0.56/0.72         (~ (v1_relat_1 @ X25)
% 0.56/0.72          | (r1_tarski @ (k1_relat_1 @ X26) @ (k1_relat_1 @ X25))
% 0.56/0.72          | ~ (r1_tarski @ X26 @ X25)
% 0.56/0.72          | ~ (v1_relat_1 @ X26))),
% 0.56/0.72      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.56/0.72  thf('6', plain,
% 0.56/0.72      ((~ (v1_relat_1 @ sk_C_1)
% 0.56/0.72        | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ 
% 0.56/0.72           (k1_relat_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))
% 0.56/0.72        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.56/0.72      inference('sup-', [status(thm)], ['4', '5'])).
% 0.56/0.72  thf('7', plain, ((v1_relat_1 @ sk_C_1)),
% 0.56/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.72  thf(fc6_relat_1, axiom,
% 0.56/0.72    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.56/0.72  thf('8', plain,
% 0.56/0.72      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 0.56/0.72      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.56/0.72  thf('9', plain,
% 0.56/0.72      ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ 
% 0.56/0.72        (k1_relat_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.56/0.72      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.56/0.72  thf(d1_funct_2, axiom,
% 0.56/0.72    (![A:$i,B:$i,C:$i]:
% 0.56/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.56/0.72       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.56/0.72           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.56/0.72             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.56/0.72         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.56/0.72           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.56/0.72             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.56/0.72  thf(zf_stmt_1, axiom,
% 0.56/0.72    (![B:$i,A:$i]:
% 0.56/0.72     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.56/0.72       ( zip_tseitin_0 @ B @ A ) ))).
% 0.56/0.72  thf('10', plain,
% 0.56/0.72      (![X31 : $i, X32 : $i]:
% 0.56/0.72         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 0.56/0.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.56/0.72  thf('11', plain,
% 0.56/0.72      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.56/0.72      inference('sup-', [status(thm)], ['0', '1'])).
% 0.56/0.72  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.56/0.72  thf(zf_stmt_3, axiom,
% 0.56/0.72    (![C:$i,B:$i,A:$i]:
% 0.56/0.72     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.56/0.72       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.56/0.72  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.56/0.72  thf(zf_stmt_5, axiom,
% 0.56/0.72    (![A:$i,B:$i,C:$i]:
% 0.56/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.56/0.72       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.56/0.72         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.56/0.72           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.56/0.72             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.56/0.72  thf('12', plain,
% 0.56/0.72      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.56/0.72         (~ (zip_tseitin_0 @ X36 @ X37)
% 0.56/0.72          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 0.56/0.72          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 0.56/0.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.56/0.72  thf('13', plain,
% 0.56/0.72      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A_1)
% 0.56/0.72        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A_1))),
% 0.56/0.72      inference('sup-', [status(thm)], ['11', '12'])).
% 0.56/0.72  thf('14', plain,
% 0.56/0.72      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A_1))),
% 0.56/0.72      inference('sup-', [status(thm)], ['10', '13'])).
% 0.56/0.72  thf('15', plain, ((r2_hidden @ sk_C_1 @ (k1_funct_2 @ sk_A_1 @ sk_B_1))),
% 0.56/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.72  thf('16', plain,
% 0.56/0.72      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.56/0.72         ((v1_funct_2 @ X41 @ X42 @ X43)
% 0.56/0.72          | ~ (r2_hidden @ X41 @ (k1_funct_2 @ X42 @ X43)))),
% 0.56/0.72      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.56/0.72  thf('17', plain, ((v1_funct_2 @ sk_C_1 @ sk_A_1 @ sk_B_1)),
% 0.56/0.72      inference('sup-', [status(thm)], ['15', '16'])).
% 0.56/0.72  thf('18', plain,
% 0.56/0.72      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.56/0.72         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 0.56/0.72          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 0.56/0.72          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 0.56/0.72      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.56/0.72  thf('19', plain,
% 0.56/0.72      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A_1)
% 0.56/0.72        | ((sk_A_1) = (k1_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C_1)))),
% 0.56/0.72      inference('sup-', [status(thm)], ['17', '18'])).
% 0.56/0.72  thf('20', plain,
% 0.56/0.72      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.56/0.72      inference('sup-', [status(thm)], ['0', '1'])).
% 0.56/0.72  thf(redefinition_k1_relset_1, axiom,
% 0.56/0.72    (![A:$i,B:$i,C:$i]:
% 0.56/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.56/0.72       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.56/0.72  thf('21', plain,
% 0.56/0.72      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.56/0.72         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 0.56/0.72          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.56/0.72      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.56/0.72  thf('22', plain,
% 0.56/0.72      (((k1_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.56/0.72      inference('sup-', [status(thm)], ['20', '21'])).
% 0.56/0.72  thf('23', plain,
% 0.56/0.72      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A_1)
% 0.56/0.72        | ((sk_A_1) = (k1_relat_1 @ sk_C_1)))),
% 0.56/0.72      inference('demod', [status(thm)], ['19', '22'])).
% 0.56/0.72  thf('24', plain,
% 0.56/0.72      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A_1) = (k1_relat_1 @ sk_C_1)))),
% 0.56/0.72      inference('sup-', [status(thm)], ['14', '23'])).
% 0.56/0.72  thf('25', plain,
% 0.56/0.72      ((((k1_relat_1 @ sk_C_1) != (sk_A_1))
% 0.56/0.72        | ~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.56/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.72  thf('26', plain,
% 0.56/0.72      ((((k1_relat_1 @ sk_C_1) != (sk_A_1)))
% 0.56/0.72         <= (~ (((k1_relat_1 @ sk_C_1) = (sk_A_1))))),
% 0.56/0.72      inference('split', [status(esa)], ['25'])).
% 0.56/0.72  thf('27', plain,
% 0.56/0.72      ((~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))
% 0.56/0.72         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)))),
% 0.56/0.72      inference('split', [status(esa)], ['25'])).
% 0.56/0.72  thf(t195_relat_1, axiom,
% 0.56/0.72    (![A:$i,B:$i]:
% 0.56/0.72     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.56/0.72          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.56/0.72               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.56/0.72  thf('28', plain,
% 0.56/0.72      (![X23 : $i, X24 : $i]:
% 0.56/0.72         (((X23) = (k1_xboole_0))
% 0.56/0.72          | ((k2_relat_1 @ (k2_zfmisc_1 @ X23 @ X24)) = (X24))
% 0.56/0.72          | ((X24) = (k1_xboole_0)))),
% 0.56/0.72      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.56/0.72  thf('29', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1))),
% 0.56/0.72      inference('sup-', [status(thm)], ['2', '3'])).
% 0.56/0.72  thf('30', plain,
% 0.56/0.72      (![X25 : $i, X26 : $i]:
% 0.56/0.72         (~ (v1_relat_1 @ X25)
% 0.56/0.72          | (r1_tarski @ (k2_relat_1 @ X26) @ (k2_relat_1 @ X25))
% 0.56/0.72          | ~ (r1_tarski @ X26 @ X25)
% 0.56/0.72          | ~ (v1_relat_1 @ X26))),
% 0.56/0.72      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.56/0.72  thf('31', plain,
% 0.56/0.72      ((~ (v1_relat_1 @ sk_C_1)
% 0.56/0.72        | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ 
% 0.56/0.72           (k2_relat_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))
% 0.56/0.72        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.56/0.72      inference('sup-', [status(thm)], ['29', '30'])).
% 0.56/0.72  thf('32', plain, ((v1_relat_1 @ sk_C_1)),
% 0.56/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.72  thf('33', plain,
% 0.56/0.72      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 0.56/0.72      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.56/0.72  thf('34', plain,
% 0.56/0.72      ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ 
% 0.56/0.72        (k2_relat_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.56/0.72      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.56/0.72  thf('35', plain,
% 0.56/0.72      (((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)
% 0.56/0.72        | ((sk_B_1) = (k1_xboole_0))
% 0.56/0.72        | ((sk_A_1) = (k1_xboole_0)))),
% 0.56/0.72      inference('sup+', [status(thm)], ['28', '34'])).
% 0.56/0.72  thf('36', plain,
% 0.56/0.72      ((~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))
% 0.56/0.72         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)))),
% 0.56/0.72      inference('split', [status(esa)], ['25'])).
% 0.56/0.72  thf('37', plain,
% 0.56/0.72      (((((sk_A_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.56/0.72         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)))),
% 0.56/0.72      inference('sup-', [status(thm)], ['35', '36'])).
% 0.56/0.72  thf(fc3_funct_2, axiom,
% 0.56/0.72    (![A:$i,B:$i]:
% 0.56/0.72     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) ) =>
% 0.56/0.72       ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ))).
% 0.56/0.72  thf('38', plain,
% 0.56/0.72      (![X39 : $i, X40 : $i]:
% 0.56/0.72         ((v1_xboole_0 @ X39)
% 0.56/0.72          | ~ (v1_xboole_0 @ X40)
% 0.56/0.72          | (v1_xboole_0 @ (k1_funct_2 @ X39 @ X40)))),
% 0.56/0.72      inference('cnf', [status(esa)], [fc3_funct_2])).
% 0.56/0.72  thf('39', plain, ((r2_hidden @ sk_C_1 @ (k1_funct_2 @ sk_A_1 @ sk_B_1))),
% 0.56/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.72  thf(d1_xboole_0, axiom,
% 0.56/0.72    (![A:$i]:
% 0.56/0.72     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.56/0.72  thf('40', plain,
% 0.56/0.72      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.56/0.72      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.56/0.72  thf('41', plain, (~ (v1_xboole_0 @ (k1_funct_2 @ sk_A_1 @ sk_B_1))),
% 0.56/0.72      inference('sup-', [status(thm)], ['39', '40'])).
% 0.56/0.72  thf('42', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A_1))),
% 0.56/0.72      inference('sup-', [status(thm)], ['38', '41'])).
% 0.56/0.72  thf('43', plain,
% 0.56/0.72      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.56/0.72         | ((sk_A_1) = (k1_xboole_0))
% 0.56/0.72         | (v1_xboole_0 @ sk_A_1)))
% 0.56/0.72         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)))),
% 0.56/0.72      inference('sup-', [status(thm)], ['37', '42'])).
% 0.56/0.72  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.56/0.72  thf('44', plain, ((v1_xboole_0 @ sk_A)),
% 0.56/0.72      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.56/0.72  thf('45', plain, ((v1_xboole_0 @ sk_A)),
% 0.56/0.72      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.56/0.72  thf(l13_xboole_0, axiom,
% 0.56/0.72    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.56/0.72  thf('46', plain,
% 0.56/0.72      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.56/0.72      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.56/0.72  thf('47', plain, (((sk_A) = (k1_xboole_0))),
% 0.56/0.72      inference('sup-', [status(thm)], ['45', '46'])).
% 0.56/0.72  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.56/0.72      inference('demod', [status(thm)], ['44', '47'])).
% 0.56/0.72  thf('49', plain,
% 0.56/0.72      (((((sk_A_1) = (k1_xboole_0)) | (v1_xboole_0 @ sk_A_1)))
% 0.56/0.72         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)))),
% 0.56/0.72      inference('demod', [status(thm)], ['43', '48'])).
% 0.56/0.72  thf('50', plain,
% 0.56/0.72      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.56/0.72      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.56/0.72  thf('51', plain,
% 0.56/0.72      ((((sk_A_1) = (k1_xboole_0)))
% 0.56/0.72         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)))),
% 0.56/0.72      inference('clc', [status(thm)], ['49', '50'])).
% 0.56/0.72  thf('52', plain,
% 0.56/0.72      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A_1)
% 0.56/0.72        | ((sk_A_1) = (k1_relat_1 @ sk_C_1)))),
% 0.56/0.72      inference('demod', [status(thm)], ['19', '22'])).
% 0.56/0.72  thf('53', plain,
% 0.56/0.72      (((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ k1_xboole_0)
% 0.56/0.72         | ((sk_A_1) = (k1_relat_1 @ sk_C_1))))
% 0.56/0.72         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)))),
% 0.56/0.72      inference('sup-', [status(thm)], ['51', '52'])).
% 0.56/0.72  thf('54', plain,
% 0.56/0.72      ((((sk_A_1) = (k1_xboole_0)))
% 0.56/0.72         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)))),
% 0.56/0.72      inference('clc', [status(thm)], ['49', '50'])).
% 0.56/0.72  thf('55', plain,
% 0.56/0.72      (((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ k1_xboole_0)
% 0.56/0.72         | ((k1_xboole_0) = (k1_relat_1 @ sk_C_1))))
% 0.56/0.72         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)))),
% 0.56/0.72      inference('demod', [status(thm)], ['53', '54'])).
% 0.56/0.72  thf('56', plain,
% 0.56/0.72      ((((sk_A_1) = (k1_xboole_0)))
% 0.56/0.72         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)))),
% 0.56/0.72      inference('clc', [status(thm)], ['49', '50'])).
% 0.56/0.72  thf('57', plain,
% 0.56/0.72      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A_1)
% 0.56/0.72        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A_1))),
% 0.56/0.72      inference('sup-', [status(thm)], ['11', '12'])).
% 0.56/0.72  thf('58', plain,
% 0.56/0.72      (((~ (zip_tseitin_0 @ sk_B_1 @ k1_xboole_0)
% 0.56/0.72         | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A_1)))
% 0.56/0.72         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)))),
% 0.56/0.72      inference('sup-', [status(thm)], ['56', '57'])).
% 0.56/0.72  thf('59', plain,
% 0.56/0.72      (![X31 : $i, X32 : $i]:
% 0.56/0.72         ((zip_tseitin_0 @ X31 @ X32) | ((X32) != (k1_xboole_0)))),
% 0.56/0.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.56/0.72  thf('60', plain, (![X31 : $i]: (zip_tseitin_0 @ X31 @ k1_xboole_0)),
% 0.56/0.72      inference('simplify', [status(thm)], ['59'])).
% 0.56/0.72  thf('61', plain,
% 0.56/0.72      ((((sk_A_1) = (k1_xboole_0)))
% 0.56/0.72         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)))),
% 0.56/0.72      inference('clc', [status(thm)], ['49', '50'])).
% 0.56/0.72  thf('62', plain,
% 0.56/0.72      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ k1_xboole_0))
% 0.56/0.72         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)))),
% 0.56/0.72      inference('demod', [status(thm)], ['58', '60', '61'])).
% 0.56/0.72  thf('63', plain,
% 0.56/0.72      ((((k1_xboole_0) = (k1_relat_1 @ sk_C_1)))
% 0.56/0.72         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)))),
% 0.56/0.72      inference('demod', [status(thm)], ['55', '62'])).
% 0.56/0.72  thf(t65_relat_1, axiom,
% 0.56/0.72    (![A:$i]:
% 0.56/0.72     ( ( v1_relat_1 @ A ) =>
% 0.56/0.72       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.56/0.72         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.56/0.72  thf('64', plain,
% 0.56/0.72      (![X27 : $i]:
% 0.56/0.72         (((k1_relat_1 @ X27) != (k1_xboole_0))
% 0.56/0.72          | ((k2_relat_1 @ X27) = (k1_xboole_0))
% 0.56/0.72          | ~ (v1_relat_1 @ X27))),
% 0.56/0.72      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.56/0.72  thf('65', plain,
% 0.56/0.72      (((((k1_xboole_0) != (k1_xboole_0))
% 0.56/0.72         | ~ (v1_relat_1 @ sk_C_1)
% 0.56/0.72         | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0))))
% 0.56/0.72         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)))),
% 0.56/0.72      inference('sup-', [status(thm)], ['63', '64'])).
% 0.56/0.72  thf('66', plain, ((v1_relat_1 @ sk_C_1)),
% 0.56/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.72  thf('67', plain,
% 0.56/0.72      (((((k1_xboole_0) != (k1_xboole_0))
% 0.56/0.72         | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0))))
% 0.56/0.72         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)))),
% 0.56/0.72      inference('demod', [status(thm)], ['65', '66'])).
% 0.56/0.72  thf('68', plain,
% 0.56/0.72      ((((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))
% 0.56/0.72         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)))),
% 0.56/0.72      inference('simplify', [status(thm)], ['67'])).
% 0.56/0.72  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.56/0.72  thf('69', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.56/0.72      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.56/0.72  thf('70', plain, (((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.56/0.72      inference('demod', [status(thm)], ['27', '68', '69'])).
% 0.56/0.72  thf('71', plain,
% 0.56/0.72      (~ (((k1_relat_1 @ sk_C_1) = (sk_A_1))) | 
% 0.56/0.72       ~ ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.56/0.72      inference('split', [status(esa)], ['25'])).
% 0.56/0.72  thf('72', plain, (~ (((k1_relat_1 @ sk_C_1) = (sk_A_1)))),
% 0.56/0.72      inference('sat_resolution*', [status(thm)], ['70', '71'])).
% 0.56/0.72  thf('73', plain, (((k1_relat_1 @ sk_C_1) != (sk_A_1))),
% 0.56/0.72      inference('simpl_trail', [status(thm)], ['26', '72'])).
% 0.56/0.72  thf('74', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.56/0.72      inference('simplify_reflect-', [status(thm)], ['24', '73'])).
% 0.56/0.72  thf(t113_zfmisc_1, axiom,
% 0.56/0.72    (![A:$i,B:$i]:
% 0.56/0.72     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.56/0.72       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.56/0.72  thf('75', plain,
% 0.56/0.72      (![X16 : $i, X17 : $i]:
% 0.56/0.72         (((k2_zfmisc_1 @ X16 @ X17) = (k1_xboole_0))
% 0.56/0.72          | ((X17) != (k1_xboole_0)))),
% 0.56/0.72      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.56/0.72  thf('76', plain,
% 0.56/0.72      (![X16 : $i]: ((k2_zfmisc_1 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 0.56/0.72      inference('simplify', [status(thm)], ['75'])).
% 0.56/0.72  thf(t60_relat_1, axiom,
% 0.56/0.72    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.56/0.72     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.56/0.72  thf('77', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.56/0.72      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.56/0.72  thf('78', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ k1_xboole_0)),
% 0.56/0.72      inference('demod', [status(thm)], ['9', '74', '76', '77'])).
% 0.56/0.72  thf(l32_xboole_1, axiom,
% 0.56/0.72    (![A:$i,B:$i]:
% 0.56/0.72     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.56/0.72  thf('79', plain,
% 0.56/0.72      (![X8 : $i, X10 : $i]:
% 0.56/0.72         (((k4_xboole_0 @ X8 @ X10) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ X10))),
% 0.56/0.72      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.56/0.72  thf('80', plain,
% 0.56/0.72      (((k4_xboole_0 @ (k1_relat_1 @ sk_C_1) @ k1_xboole_0) = (k1_xboole_0))),
% 0.56/0.72      inference('sup-', [status(thm)], ['78', '79'])).
% 0.56/0.72  thf('81', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.56/0.72      inference('demod', [status(thm)], ['44', '47'])).
% 0.56/0.72  thf(t3_xboole_0, axiom,
% 0.56/0.72    (![A:$i,B:$i]:
% 0.56/0.72     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.56/0.72            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.56/0.72       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.56/0.72            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.56/0.72  thf('82', plain,
% 0.56/0.72      (![X4 : $i, X5 : $i]:
% 0.56/0.72         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X5))),
% 0.56/0.72      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.56/0.72  thf('83', plain,
% 0.56/0.72      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.56/0.72      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.56/0.72  thf('84', plain,
% 0.56/0.72      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.56/0.72      inference('sup-', [status(thm)], ['82', '83'])).
% 0.56/0.72  thf('85', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.56/0.72      inference('sup-', [status(thm)], ['81', '84'])).
% 0.56/0.72  thf(t83_xboole_1, axiom,
% 0.56/0.72    (![A:$i,B:$i]:
% 0.56/0.72     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.56/0.72  thf('86', plain,
% 0.56/0.72      (![X12 : $i, X13 : $i]:
% 0.56/0.72         (((k4_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_xboole_0 @ X12 @ X13))),
% 0.56/0.72      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.56/0.72  thf('87', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.56/0.72      inference('sup-', [status(thm)], ['85', '86'])).
% 0.56/0.72  thf('88', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.56/0.72      inference('demod', [status(thm)], ['80', '87'])).
% 0.56/0.72  thf('89', plain, (((k1_relat_1 @ sk_C_1) != (sk_A_1))),
% 0.56/0.72      inference('simpl_trail', [status(thm)], ['26', '72'])).
% 0.56/0.72  thf('90', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A_1))),
% 0.56/0.72      inference('sup-', [status(thm)], ['38', '41'])).
% 0.56/0.72  thf('91', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.56/0.72      inference('simplify_reflect-', [status(thm)], ['24', '73'])).
% 0.56/0.72  thf('92', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.56/0.72      inference('demod', [status(thm)], ['44', '47'])).
% 0.56/0.72  thf('93', plain, ((v1_xboole_0 @ sk_A_1)),
% 0.56/0.72      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.56/0.72  thf('94', plain,
% 0.56/0.72      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.56/0.72      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.56/0.72  thf('95', plain, (((sk_A_1) = (k1_xboole_0))),
% 0.56/0.72      inference('sup-', [status(thm)], ['93', '94'])).
% 0.56/0.72  thf('96', plain, (((k1_relat_1 @ sk_C_1) != (k1_xboole_0))),
% 0.56/0.72      inference('demod', [status(thm)], ['89', '95'])).
% 0.56/0.72  thf('97', plain, ($false),
% 0.56/0.72      inference('simplify_reflect-', [status(thm)], ['88', '96'])).
% 0.56/0.72  
% 0.56/0.72  % SZS output end Refutation
% 0.56/0.72  
% 0.56/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
