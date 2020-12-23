%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AxUU9F1BHE

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:23 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 144 expanded)
%              Number of leaves         :   49 (  65 expanded)
%              Depth                    :   28
%              Number of atoms          :  802 (1290 expanded)
%              Number of equality atoms :   57 (  76 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('0',plain,(
    ! [X43: $i] :
      ( ( X43 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X43 ) @ X43 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

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

thf('1',plain,(
    ! [X49: $i,X50: $i] :
      ( ( zip_tseitin_0 @ X49 @ X50 )
      | ( X49 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

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
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( zip_tseitin_0 @ X54 @ X55 )
      | ( zip_tseitin_1 @ X56 @ X54 @ X55 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X54 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( zip_tseitin_1 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t61_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_5,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_funct_2])).

thf('6',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v5_relat_1 @ X35 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('9',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B_2 ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t56_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf('10',plain,(
    ! [X26: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ X26 ) @ ( sk_C @ X26 ) ) @ X26 )
      | ( X26 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ( r2_hidden @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_C_1 ) @ ( sk_C @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('16',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v1_relat_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('17',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_C_1 ) @ ( sk_C @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf(t128_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
    <=> ( ( A = C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 = X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X11 ) @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('20',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( sk_B @ sk_C_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X26: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ X26 ) @ ( sk_C @ X26 ) ) @ X26 )
      | ( X26 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf('22',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ sk_C_1 ) ) @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('24',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ sk_C_1 ) ) @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ sk_C_1 ) ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('26',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X23 @ X24 ) @ X25 )
      | ( r2_hidden @ X23 @ ( k1_relat_1 @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('27',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('29',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t172_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) )).

thf('30',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k1_relat_1 @ X28 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X28 @ X27 ) @ X29 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v5_relat_1 @ X28 @ X29 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v5_relat_1 @ sk_C_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('33',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = k1_xboole_0 )
      | ~ ( v5_relat_1 @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B_2 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','34'])).

thf('36',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('37',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_2 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_2 ),
    inference(demod,[status(thm)],['6','37'])).

thf('39',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( v1_funct_2 @ X53 @ X51 @ X52 )
      | ( X51
        = ( k1_relset_1 @ X51 @ X52 @ X53 ) )
      | ~ ( zip_tseitin_1 @ X53 @ X52 @ X51 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('40',plain,
    ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ sk_B_2 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','40'])).

thf('42',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('43',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t22_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) )
      <=> ( ( k1_relset_1 @ B @ A @ C )
          = B ) ) ) )).

thf('45',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( ( k1_relset_1 @ X38 @ X39 @ X40 )
       != X38 )
      | ~ ( r2_hidden @ X41 @ X38 )
      | ( r2_hidden @ ( k4_tarski @ X41 @ ( sk_E @ X41 @ X40 ) ) @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_relset_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_E @ X2 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
       != X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B_1 @ ( k1_tarski @ sk_A ) ) @ k1_xboole_0 ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','48'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('50',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ~ ( r1_tarski @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('51',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ k1_xboole_0 @ ( k4_tarski @ ( sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B_1 @ ( k1_tarski @ sk_A ) ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('53',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','52'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('54',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('55',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X8 ) @ X9 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != k1_xboole_0 )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ~ ( r1_tarski @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('60',plain,(
    ~ ( r1_tarski @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['60','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AxUU9F1BHE
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:12:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.68/0.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.68/0.89  % Solved by: fo/fo7.sh
% 0.68/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.89  % done 499 iterations in 0.438s
% 0.68/0.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.68/0.89  % SZS output start Refutation
% 0.68/0.89  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.68/0.89  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.68/0.89  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.68/0.89  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.68/0.89  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.68/0.89  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.68/0.89  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.68/0.89  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.68/0.89  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.68/0.89  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.68/0.89  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.68/0.89  thf(sk_B_type, type, sk_B: $i > $i).
% 0.68/0.89  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.68/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.89  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.68/0.89  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.68/0.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.68/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.89  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.68/0.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.68/0.89  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.68/0.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.68/0.89  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.68/0.89  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.68/0.89  thf(sk_C_type, type, sk_C: $i > $i).
% 0.68/0.89  thf(sk_E_type, type, sk_E: $i > $i > $i).
% 0.68/0.89  thf(t6_mcart_1, axiom,
% 0.68/0.89    (![A:$i]:
% 0.68/0.89     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.68/0.89          ( ![B:$i]:
% 0.68/0.89            ( ~( ( r2_hidden @ B @ A ) & 
% 0.68/0.89                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.68/0.89                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.68/0.89                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.68/0.89                       ( r2_hidden @ G @ B ) ) =>
% 0.68/0.89                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.68/0.89  thf('0', plain,
% 0.68/0.89      (![X43 : $i]:
% 0.68/0.89         (((X43) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X43) @ X43))),
% 0.68/0.89      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.68/0.89  thf(d1_funct_2, axiom,
% 0.68/0.89    (![A:$i,B:$i,C:$i]:
% 0.68/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.89       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.68/0.89           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.68/0.89             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.68/0.89         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.68/0.89           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.68/0.89             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.68/0.89  thf(zf_stmt_0, axiom,
% 0.68/0.89    (![B:$i,A:$i]:
% 0.68/0.89     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.68/0.89       ( zip_tseitin_0 @ B @ A ) ))).
% 0.68/0.89  thf('1', plain,
% 0.68/0.89      (![X49 : $i, X50 : $i]:
% 0.68/0.89         ((zip_tseitin_0 @ X49 @ X50) | ((X49) = (k1_xboole_0)))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf(t4_subset_1, axiom,
% 0.68/0.89    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.68/0.89  thf('2', plain,
% 0.68/0.89      (![X19 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 0.68/0.89      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.68/0.89  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.68/0.89  thf(zf_stmt_2, axiom,
% 0.68/0.89    (![C:$i,B:$i,A:$i]:
% 0.68/0.89     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.68/0.89       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.68/0.89  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.68/0.89  thf(zf_stmt_4, axiom,
% 0.68/0.89    (![A:$i,B:$i,C:$i]:
% 0.68/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.89       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.68/0.89         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.68/0.89           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.68/0.89             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.68/0.89  thf('3', plain,
% 0.68/0.89      (![X54 : $i, X55 : $i, X56 : $i]:
% 0.68/0.89         (~ (zip_tseitin_0 @ X54 @ X55)
% 0.68/0.89          | (zip_tseitin_1 @ X56 @ X54 @ X55)
% 0.68/0.89          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X54))))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.68/0.89  thf('4', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.68/0.89      inference('sup-', [status(thm)], ['2', '3'])).
% 0.68/0.89  thf('5', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         (((X1) = (k1_xboole_0)) | (zip_tseitin_1 @ k1_xboole_0 @ X1 @ X0))),
% 0.68/0.89      inference('sup-', [status(thm)], ['1', '4'])).
% 0.68/0.89  thf(t61_funct_2, conjecture,
% 0.68/0.89    (![A:$i,B:$i,C:$i]:
% 0.68/0.89     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.68/0.89         ( m1_subset_1 @
% 0.68/0.89           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.68/0.89       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.68/0.89         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.68/0.89  thf(zf_stmt_5, negated_conjecture,
% 0.68/0.89    (~( ![A:$i,B:$i,C:$i]:
% 0.68/0.89        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.68/0.89            ( m1_subset_1 @
% 0.68/0.89              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.68/0.89          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.68/0.89            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.68/0.89    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.68/0.89  thf('6', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B_2)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.68/0.89  thf('7', plain,
% 0.68/0.89      ((m1_subset_1 @ sk_C_1 @ 
% 0.68/0.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.68/0.89  thf(cc2_relset_1, axiom,
% 0.68/0.89    (![A:$i,B:$i,C:$i]:
% 0.68/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.89       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.68/0.89  thf('8', plain,
% 0.68/0.89      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.68/0.89         ((v5_relat_1 @ X35 @ X37)
% 0.68/0.89          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.68/0.89      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.68/0.89  thf('9', plain, ((v5_relat_1 @ sk_C_1 @ sk_B_2)),
% 0.68/0.89      inference('sup-', [status(thm)], ['7', '8'])).
% 0.68/0.89  thf(t56_relat_1, axiom,
% 0.68/0.89    (![A:$i]:
% 0.68/0.89     ( ( v1_relat_1 @ A ) =>
% 0.68/0.89       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.68/0.89         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.68/0.89  thf('10', plain,
% 0.68/0.89      (![X26 : $i]:
% 0.68/0.89         ((r2_hidden @ (k4_tarski @ (sk_B @ X26) @ (sk_C @ X26)) @ X26)
% 0.68/0.89          | ((X26) = (k1_xboole_0))
% 0.68/0.89          | ~ (v1_relat_1 @ X26))),
% 0.68/0.89      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.68/0.89  thf('11', plain,
% 0.68/0.89      ((m1_subset_1 @ sk_C_1 @ 
% 0.68/0.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.68/0.89  thf(l3_subset_1, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.89       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.68/0.89  thf('12', plain,
% 0.68/0.89      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.68/0.89         (~ (r2_hidden @ X16 @ X17)
% 0.68/0.89          | (r2_hidden @ X16 @ X18)
% 0.68/0.89          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.68/0.89      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.68/0.89  thf('13', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2))
% 0.68/0.89          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.68/0.89      inference('sup-', [status(thm)], ['11', '12'])).
% 0.68/0.89  thf('14', plain,
% 0.68/0.89      ((~ (v1_relat_1 @ sk_C_1)
% 0.68/0.89        | ((sk_C_1) = (k1_xboole_0))
% 0.68/0.89        | (r2_hidden @ (k4_tarski @ (sk_B @ sk_C_1) @ (sk_C @ sk_C_1)) @ 
% 0.68/0.89           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['10', '13'])).
% 0.68/0.89  thf('15', plain,
% 0.68/0.89      ((m1_subset_1 @ sk_C_1 @ 
% 0.68/0.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.68/0.89  thf(cc1_relset_1, axiom,
% 0.68/0.89    (![A:$i,B:$i,C:$i]:
% 0.68/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.89       ( v1_relat_1 @ C ) ))).
% 0.68/0.89  thf('16', plain,
% 0.68/0.89      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.68/0.89         ((v1_relat_1 @ X32)
% 0.68/0.89          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.68/0.89      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.68/0.89  thf('17', plain, ((v1_relat_1 @ sk_C_1)),
% 0.68/0.89      inference('sup-', [status(thm)], ['15', '16'])).
% 0.68/0.89  thf('18', plain,
% 0.68/0.89      ((((sk_C_1) = (k1_xboole_0))
% 0.68/0.89        | (r2_hidden @ (k4_tarski @ (sk_B @ sk_C_1) @ (sk_C @ sk_C_1)) @ 
% 0.68/0.89           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.68/0.89      inference('demod', [status(thm)], ['14', '17'])).
% 0.68/0.89  thf(t128_zfmisc_1, axiom,
% 0.68/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.89     ( ( r2_hidden @
% 0.68/0.89         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.68/0.89       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.68/0.89  thf('19', plain,
% 0.68/0.89      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.68/0.89         (((X12) = (X11))
% 0.68/0.89          | ~ (r2_hidden @ (k4_tarski @ X12 @ X13) @ 
% 0.68/0.89               (k2_zfmisc_1 @ (k1_tarski @ X11) @ X14)))),
% 0.68/0.89      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 0.68/0.89  thf('20', plain, ((((sk_C_1) = (k1_xboole_0)) | ((sk_B @ sk_C_1) = (sk_A)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['18', '19'])).
% 0.68/0.89  thf('21', plain,
% 0.68/0.89      (![X26 : $i]:
% 0.68/0.89         ((r2_hidden @ (k4_tarski @ (sk_B @ X26) @ (sk_C @ X26)) @ X26)
% 0.68/0.89          | ((X26) = (k1_xboole_0))
% 0.68/0.89          | ~ (v1_relat_1 @ X26))),
% 0.68/0.89      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.68/0.89  thf('22', plain,
% 0.68/0.89      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_C @ sk_C_1)) @ sk_C_1)
% 0.68/0.89        | ((sk_C_1) = (k1_xboole_0))
% 0.68/0.89        | ~ (v1_relat_1 @ sk_C_1)
% 0.68/0.89        | ((sk_C_1) = (k1_xboole_0)))),
% 0.68/0.89      inference('sup+', [status(thm)], ['20', '21'])).
% 0.68/0.89  thf('23', plain, ((v1_relat_1 @ sk_C_1)),
% 0.68/0.89      inference('sup-', [status(thm)], ['15', '16'])).
% 0.68/0.89  thf('24', plain,
% 0.68/0.89      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_C @ sk_C_1)) @ sk_C_1)
% 0.68/0.89        | ((sk_C_1) = (k1_xboole_0))
% 0.68/0.89        | ((sk_C_1) = (k1_xboole_0)))),
% 0.68/0.89      inference('demod', [status(thm)], ['22', '23'])).
% 0.68/0.89  thf('25', plain,
% 0.68/0.89      ((((sk_C_1) = (k1_xboole_0))
% 0.68/0.89        | (r2_hidden @ (k4_tarski @ sk_A @ (sk_C @ sk_C_1)) @ sk_C_1))),
% 0.68/0.89      inference('simplify', [status(thm)], ['24'])).
% 0.68/0.89  thf(t20_relat_1, axiom,
% 0.68/0.89    (![A:$i,B:$i,C:$i]:
% 0.68/0.89     ( ( v1_relat_1 @ C ) =>
% 0.68/0.89       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.68/0.89         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.68/0.89           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.68/0.89  thf('26', plain,
% 0.68/0.89      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.68/0.89         (~ (r2_hidden @ (k4_tarski @ X23 @ X24) @ X25)
% 0.68/0.89          | (r2_hidden @ X23 @ (k1_relat_1 @ X25))
% 0.68/0.89          | ~ (v1_relat_1 @ X25))),
% 0.68/0.89      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.68/0.89  thf('27', plain,
% 0.68/0.89      ((((sk_C_1) = (k1_xboole_0))
% 0.68/0.89        | ~ (v1_relat_1 @ sk_C_1)
% 0.68/0.89        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['25', '26'])).
% 0.68/0.89  thf('28', plain, ((v1_relat_1 @ sk_C_1)),
% 0.68/0.89      inference('sup-', [status(thm)], ['15', '16'])).
% 0.68/0.89  thf('29', plain,
% 0.68/0.89      ((((sk_C_1) = (k1_xboole_0)) | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))),
% 0.68/0.89      inference('demod', [status(thm)], ['27', '28'])).
% 0.68/0.89  thf(t172_funct_1, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.68/0.89       ( ![C:$i]:
% 0.68/0.89         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.68/0.89           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 0.68/0.89  thf('30', plain,
% 0.68/0.89      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.68/0.89         (~ (r2_hidden @ X27 @ (k1_relat_1 @ X28))
% 0.68/0.89          | (r2_hidden @ (k1_funct_1 @ X28 @ X27) @ X29)
% 0.68/0.89          | ~ (v1_funct_1 @ X28)
% 0.68/0.89          | ~ (v5_relat_1 @ X28 @ X29)
% 0.68/0.89          | ~ (v1_relat_1 @ X28))),
% 0.68/0.89      inference('cnf', [status(esa)], [t172_funct_1])).
% 0.68/0.89  thf('31', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         (((sk_C_1) = (k1_xboole_0))
% 0.68/0.89          | ~ (v1_relat_1 @ sk_C_1)
% 0.68/0.89          | ~ (v5_relat_1 @ sk_C_1 @ X0)
% 0.68/0.89          | ~ (v1_funct_1 @ sk_C_1)
% 0.68/0.89          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ X0))),
% 0.68/0.89      inference('sup-', [status(thm)], ['29', '30'])).
% 0.68/0.89  thf('32', plain, ((v1_relat_1 @ sk_C_1)),
% 0.68/0.89      inference('sup-', [status(thm)], ['15', '16'])).
% 0.68/0.89  thf('33', plain, ((v1_funct_1 @ sk_C_1)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.68/0.89  thf('34', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         (((sk_C_1) = (k1_xboole_0))
% 0.68/0.89          | ~ (v5_relat_1 @ sk_C_1 @ X0)
% 0.68/0.89          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ X0))),
% 0.68/0.89      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.68/0.89  thf('35', plain,
% 0.68/0.89      (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B_2)
% 0.68/0.89        | ((sk_C_1) = (k1_xboole_0)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['9', '34'])).
% 0.68/0.89  thf('36', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B_2)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.68/0.89  thf('37', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.68/0.89      inference('clc', [status(thm)], ['35', '36'])).
% 0.68/0.89  thf('38', plain, ((v1_funct_2 @ k1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_2)),
% 0.68/0.89      inference('demod', [status(thm)], ['6', '37'])).
% 0.68/0.89  thf('39', plain,
% 0.68/0.89      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.68/0.89         (~ (v1_funct_2 @ X53 @ X51 @ X52)
% 0.68/0.89          | ((X51) = (k1_relset_1 @ X51 @ X52 @ X53))
% 0.68/0.89          | ~ (zip_tseitin_1 @ X53 @ X52 @ X51))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.68/0.89  thf('40', plain,
% 0.68/0.89      ((~ (zip_tseitin_1 @ k1_xboole_0 @ sk_B_2 @ (k1_tarski @ sk_A))
% 0.68/0.89        | ((k1_tarski @ sk_A)
% 0.68/0.89            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ k1_xboole_0)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['38', '39'])).
% 0.68/0.89  thf('41', plain,
% 0.68/0.89      ((((sk_B_2) = (k1_xboole_0))
% 0.68/0.89        | ((k1_tarski @ sk_A)
% 0.68/0.89            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ k1_xboole_0)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['5', '40'])).
% 0.68/0.89  thf('42', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.68/0.89  thf('43', plain,
% 0.68/0.89      (((k1_tarski @ sk_A)
% 0.68/0.89         = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ k1_xboole_0))),
% 0.68/0.89      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 0.68/0.89  thf('44', plain,
% 0.68/0.89      (![X19 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 0.68/0.89      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.68/0.89  thf(t22_relset_1, axiom,
% 0.68/0.89    (![A:$i,B:$i,C:$i]:
% 0.68/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.68/0.89       ( ( ![D:$i]:
% 0.68/0.89           ( ~( ( r2_hidden @ D @ B ) & 
% 0.68/0.89                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.68/0.89         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 0.68/0.89  thf('45', plain,
% 0.68/0.89      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.68/0.89         (((k1_relset_1 @ X38 @ X39 @ X40) != (X38))
% 0.68/0.89          | ~ (r2_hidden @ X41 @ X38)
% 0.68/0.89          | (r2_hidden @ (k4_tarski @ X41 @ (sk_E @ X41 @ X40)) @ X40)
% 0.68/0.89          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.68/0.89      inference('cnf', [status(esa)], [t22_relset_1])).
% 0.68/0.89  thf('46', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.89         ((r2_hidden @ (k4_tarski @ X2 @ (sk_E @ X2 @ k1_xboole_0)) @ 
% 0.68/0.89           k1_xboole_0)
% 0.68/0.89          | ~ (r2_hidden @ X2 @ X1)
% 0.68/0.89          | ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) != (X1)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['44', '45'])).
% 0.68/0.89  thf('47', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.68/0.89          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.68/0.89          | (r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ k1_xboole_0)) @ 
% 0.68/0.89             k1_xboole_0))),
% 0.68/0.89      inference('sup-', [status(thm)], ['43', '46'])).
% 0.68/0.89  thf('48', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ k1_xboole_0)) @ 
% 0.68/0.89           k1_xboole_0)
% 0.68/0.89          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.68/0.89      inference('simplify', [status(thm)], ['47'])).
% 0.68/0.89  thf('49', plain,
% 0.68/0.89      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.68/0.89        | (r2_hidden @ 
% 0.68/0.89           (k4_tarski @ (sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.68/0.89            (sk_E @ (sk_B_1 @ (k1_tarski @ sk_A)) @ k1_xboole_0)) @ 
% 0.68/0.89           k1_xboole_0))),
% 0.68/0.89      inference('sup-', [status(thm)], ['0', '48'])).
% 0.68/0.89  thf(t7_ordinal1, axiom,
% 0.68/0.89    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.68/0.89  thf('50', plain,
% 0.68/0.89      (![X30 : $i, X31 : $i]:
% 0.68/0.89         (~ (r2_hidden @ X30 @ X31) | ~ (r1_tarski @ X31 @ X30))),
% 0.68/0.89      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.68/0.89  thf('51', plain,
% 0.68/0.89      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.68/0.89        | ~ (r1_tarski @ k1_xboole_0 @ 
% 0.68/0.89             (k4_tarski @ (sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.68/0.89              (sk_E @ (sk_B_1 @ (k1_tarski @ sk_A)) @ k1_xboole_0))))),
% 0.68/0.89      inference('sup-', [status(thm)], ['49', '50'])).
% 0.68/0.89  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.68/0.89  thf('52', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.68/0.89      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.68/0.89  thf('53', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.68/0.89      inference('demod', [status(thm)], ['51', '52'])).
% 0.68/0.89  thf(t3_boole, axiom,
% 0.68/0.89    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.68/0.89  thf('54', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.68/0.89      inference('cnf', [status(esa)], [t3_boole])).
% 0.68/0.89  thf(l35_zfmisc_1, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.68/0.89       ( r2_hidden @ A @ B ) ))).
% 0.68/0.89  thf('55', plain,
% 0.68/0.89      (![X8 : $i, X9 : $i]:
% 0.68/0.89         ((r2_hidden @ X8 @ X9)
% 0.68/0.89          | ((k4_xboole_0 @ (k1_tarski @ X8) @ X9) != (k1_xboole_0)))),
% 0.68/0.89      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.68/0.89  thf('56', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         (((k1_tarski @ X0) != (k1_xboole_0)) | (r2_hidden @ X0 @ k1_xboole_0))),
% 0.68/0.89      inference('sup-', [status(thm)], ['54', '55'])).
% 0.68/0.89  thf('57', plain,
% 0.68/0.89      ((((k1_xboole_0) != (k1_xboole_0)) | (r2_hidden @ sk_A @ k1_xboole_0))),
% 0.68/0.89      inference('sup-', [status(thm)], ['53', '56'])).
% 0.68/0.89  thf('58', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.68/0.89      inference('simplify', [status(thm)], ['57'])).
% 0.68/0.89  thf('59', plain,
% 0.68/0.89      (![X30 : $i, X31 : $i]:
% 0.68/0.89         (~ (r2_hidden @ X30 @ X31) | ~ (r1_tarski @ X31 @ X30))),
% 0.68/0.89      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.68/0.89  thf('60', plain, (~ (r1_tarski @ k1_xboole_0 @ sk_A)),
% 0.68/0.89      inference('sup-', [status(thm)], ['58', '59'])).
% 0.68/0.89  thf('61', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.68/0.89      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.68/0.89  thf('62', plain, ($false), inference('demod', [status(thm)], ['60', '61'])).
% 0.68/0.89  
% 0.68/0.89  % SZS output end Refutation
% 0.68/0.89  
% 0.68/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
