%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.u6C2wSGO6u

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:44 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  191 ( 609 expanded)
%              Number of leaves         :   58 ( 211 expanded)
%              Depth                    :   28
%              Number of atoms          : 1247 (5590 expanded)
%              Number of equality atoms :   72 ( 296 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t116_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
            & ! [F: $i] :
                ( ( m1_subset_1 @ F @ A )
               => ~ ( ( r2_hidden @ F @ C )
                    & ( E
                      = ( k1_funct_1 @ D @ F ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
              & ! [F: $i] :
                  ( ( m1_subset_1 @ F @ A )
                 => ~ ( ( r2_hidden @ F @ C )
                      & ( E
                        = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t116_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X61 ) ) )
      | ( ( k7_relset_1 @ X60 @ X61 @ X59 @ X62 )
        = ( k9_relat_1 @ X59 @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d12_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_funct_1 @ A )
        & ( v1_relat_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) )
                  & ( r2_hidden @ E @ B )
                  & ( D
                    = ( k1_funct_1 @ A @ E ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( D
          = ( k1_funct_1 @ A @ E ) )
        & ( r2_hidden @ E @ B )
        & ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X41: $i,X42: $i,X44: $i,X45: $i] :
      ( ( X44
       != ( k9_relat_1 @ X42 @ X41 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X45 @ X41 @ X42 ) @ X45 @ X41 @ X42 )
      | ~ ( r2_hidden @ X45 @ X44 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X41: $i,X42: $i,X45: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( r2_hidden @ X45 @ ( k9_relat_1 @ X42 @ X41 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X45 @ X41 @ X42 ) @ X45 @ X41 @ X42 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2 ) @ sk_E_2 @ sk_C_1 @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('10',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( v1_relat_1 @ X50 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2 ) @ sk_E_2 @ sk_C_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('13',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( r2_hidden @ X36 @ X38 )
      | ~ ( zip_tseitin_0 @ X36 @ X37 @ X38 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('14',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2 ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X71: $i] :
      ( ( sk_E_2
       != ( k1_funct_1 @ sk_D_2 @ X71 ) )
      | ~ ( r2_hidden @ X71 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X71 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2 ) @ sk_A )
    | ( sk_E_2
     != ( k1_funct_1 @ sk_D_2 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2 ) @ sk_E_2 @ sk_C_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('18',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( r2_hidden @ X36 @ ( k1_relat_1 @ X35 ) )
      | ~ ( zip_tseitin_0 @ X36 @ X37 @ X38 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('19',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['17','18'])).

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

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('20',plain,(
    ! [X63: $i,X64: $i] :
      ( ( zip_tseitin_1 @ X63 @ X64 )
      | ( X63 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('25',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('26',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( v5_relat_1 @ X53 @ X55 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('28',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v5_relat_1 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','28'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('30',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v5_relat_1 @ X21 @ X22 )
      | ( r1_tarski @ ( k2_relat_1 @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('33',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('34',plain,(
    ! [X23: $i,X24: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('35',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['31','35'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('37',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('44',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('46',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X21 ) @ X22 )
      | ( v5_relat_1 @ X21 @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( v5_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v5_relat_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('50',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['33','34'])).

thf('51',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v5_relat_1 @ X21 @ X22 )
      | ( r1_tarski @ ( k2_relat_1 @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['33','34'])).

thf('55',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['42','43'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['20','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( v5_relat_1 @ X53 @ X55 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('60',plain,(
    v5_relat_1 @ sk_D_2 @ sk_B_1 ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v5_relat_1 @ X21 @ X22 )
      | ( r1_tarski @ ( k2_relat_1 @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('64',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('66',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k2_relat_1 @ sk_D_2 ) )
    | ( sk_B_1
      = ( k2_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_B_1 @ X0 )
      | ( sk_B_1
        = ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['57','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_5,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_7,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_1 @ B @ A )
         => ( zip_tseitin_2 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('69',plain,(
    ! [X68: $i,X69: $i,X70: $i] :
      ( ~ ( zip_tseitin_1 @ X68 @ X69 )
      | ( zip_tseitin_2 @ X70 @ X68 @ X69 )
      | ~ ( m1_subset_1 @ X70 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X69 @ X68 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('70',plain,
    ( ( zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( sk_B_1
      = ( k2_relat_1 @ sk_D_2 ) )
    | ( zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ~ ( v1_funct_2 @ X67 @ X65 @ X66 )
      | ( X65
        = ( k1_relset_1 @ X65 @ X66 @ X67 ) )
      | ~ ( zip_tseitin_2 @ X67 @ X66 @ X65 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('74',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('76',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ( ( k1_relset_1 @ X57 @ X58 @ X56 )
        = ( k1_relat_1 @ X56 ) )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X58 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('77',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['74','77'])).

thf('79',plain,
    ( ( sk_B_1
      = ( k2_relat_1 @ sk_D_2 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['71','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['20','56'])).

thf('81',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('82',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['62','63'])).

thf('83',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_D_2 ) )
    | ( r2_hidden @ ( sk_B @ ( k2_relat_1 @ sk_D_2 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('86',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( r2_hidden @ X48 @ X49 )
      | ~ ( r1_tarski @ X49 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('87',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_D_2 ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( sk_B @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['80','87'])).

thf('89',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_B_1 @ X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['88','93'])).

thf('95',plain,
    ( ( zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('96',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ sk_D_2 ) )
    | ( zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['74','77'])).

thf('98',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ sk_D_2 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X21 ) @ X22 )
      | ( v5_relat_1 @ X21 @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D_2 ) )
      | ~ ( v1_relat_1 @ sk_D_2 )
      | ( v5_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('102',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D_2 ) )
      | ( v5_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v5_relat_1 @ X21 @ X22 )
      | ( r1_tarski @ ( k2_relat_1 @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D_2 ) )
      | ~ ( v1_relat_1 @ sk_D_2 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D_2 ) )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D_2 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup+',[status(thm)],['79','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D_2 ) )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('111',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k9_relat_1 @ X28 @ X26 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X28 @ X26 @ X27 ) @ X27 ) @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('112',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C_1 @ sk_E_2 ) @ sk_E_2 ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('114',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C_1 @ sk_E_2 ) @ sk_E_2 ) @ sk_D_2 ),
    inference(demod,[status(thm)],['112','113'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('115',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X32 @ X33 ) @ X34 )
      | ( r2_hidden @ X33 @ ( k2_relat_1 @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('116',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r2_hidden @ sk_E_2 @ ( k2_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('118',plain,(
    r2_hidden @ sk_E_2 @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('120',plain,(
    r2_hidden @ sk_E_2 @ sk_B_1 ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( r2_hidden @ X48 @ X49 )
      | ~ ( r1_tarski @ X49 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('122',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_E_2 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['109','122'])).

thf('124',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2 ) @ sk_A ),
    inference(demod,[status(thm)],['19','123'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('125',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ X13 @ X14 )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('126',plain,(
    m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2 ) @ sk_E_2 @ sk_C_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('128',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( X37
        = ( k1_funct_1 @ X35 @ X36 ) )
      | ~ ( zip_tseitin_0 @ X36 @ X37 @ X38 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('129',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_2 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    sk_E_2 != sk_E_2 ),
    inference(demod,[status(thm)],['16','126','129'])).

thf('131',plain,(
    $false ),
    inference(simplify,[status(thm)],['130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.u6C2wSGO6u
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:39:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.49/1.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.49/1.67  % Solved by: fo/fo7.sh
% 1.49/1.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.49/1.67  % done 1772 iterations in 1.207s
% 1.49/1.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.49/1.67  % SZS output start Refutation
% 1.49/1.67  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.49/1.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.49/1.67  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.49/1.67  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.49/1.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.49/1.67  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.49/1.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.49/1.67  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.49/1.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.49/1.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.49/1.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.49/1.67  thf(sk_D_2_type, type, sk_D_2: $i).
% 1.49/1.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.49/1.67  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.49/1.67  thf(sk_B_type, type, sk_B: $i > $i).
% 1.49/1.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.49/1.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.49/1.67  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.49/1.67  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 1.49/1.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.49/1.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.49/1.67  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.49/1.67  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.49/1.67  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.49/1.67  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 1.49/1.67  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.49/1.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.49/1.67  thf(sk_E_2_type, type, sk_E_2: $i).
% 1.49/1.67  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 1.49/1.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.49/1.67  thf(sk_A_type, type, sk_A: $i).
% 1.49/1.67  thf(t116_funct_2, conjecture,
% 1.49/1.67    (![A:$i,B:$i,C:$i,D:$i]:
% 1.49/1.67     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.49/1.67         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.49/1.67       ( ![E:$i]:
% 1.49/1.67         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 1.49/1.67              ( ![F:$i]:
% 1.49/1.67                ( ( m1_subset_1 @ F @ A ) =>
% 1.49/1.67                  ( ~( ( r2_hidden @ F @ C ) & 
% 1.49/1.67                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 1.49/1.67  thf(zf_stmt_0, negated_conjecture,
% 1.49/1.67    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.49/1.67        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.49/1.67            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.49/1.67          ( ![E:$i]:
% 1.49/1.67            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 1.49/1.67                 ( ![F:$i]:
% 1.49/1.67                   ( ( m1_subset_1 @ F @ A ) =>
% 1.49/1.67                     ( ~( ( r2_hidden @ F @ C ) & 
% 1.49/1.67                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 1.49/1.67    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 1.49/1.67  thf('0', plain,
% 1.49/1.67      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ sk_C_1))),
% 1.49/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.67  thf('1', plain,
% 1.49/1.67      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.49/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.67  thf(redefinition_k7_relset_1, axiom,
% 1.49/1.67    (![A:$i,B:$i,C:$i,D:$i]:
% 1.49/1.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.49/1.67       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 1.49/1.67  thf('2', plain,
% 1.49/1.67      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 1.49/1.67         (~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X61)))
% 1.49/1.67          | ((k7_relset_1 @ X60 @ X61 @ X59 @ X62) = (k9_relat_1 @ X59 @ X62)))),
% 1.49/1.67      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.49/1.67  thf('3', plain,
% 1.49/1.67      (![X0 : $i]:
% 1.49/1.67         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0)
% 1.49/1.67           = (k9_relat_1 @ sk_D_2 @ X0))),
% 1.49/1.67      inference('sup-', [status(thm)], ['1', '2'])).
% 1.49/1.67  thf('4', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_C_1))),
% 1.49/1.67      inference('demod', [status(thm)], ['0', '3'])).
% 1.49/1.67  thf(d12_funct_1, axiom,
% 1.49/1.67    (![A:$i]:
% 1.49/1.67     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 1.49/1.67       ( ![B:$i,C:$i]:
% 1.49/1.67         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 1.49/1.67           ( ![D:$i]:
% 1.49/1.67             ( ( r2_hidden @ D @ C ) <=>
% 1.49/1.67               ( ?[E:$i]:
% 1.49/1.67                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 1.49/1.67                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 1.49/1.67  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.49/1.67  thf(zf_stmt_2, axiom,
% 1.49/1.67    (![E:$i,D:$i,B:$i,A:$i]:
% 1.49/1.67     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 1.49/1.67       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 1.49/1.67         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 1.49/1.67  thf(zf_stmt_3, axiom,
% 1.49/1.67    (![A:$i]:
% 1.49/1.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.49/1.67       ( ![B:$i,C:$i]:
% 1.49/1.67         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 1.49/1.67           ( ![D:$i]:
% 1.49/1.67             ( ( r2_hidden @ D @ C ) <=>
% 1.49/1.67               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 1.49/1.67  thf('5', plain,
% 1.49/1.67      (![X41 : $i, X42 : $i, X44 : $i, X45 : $i]:
% 1.49/1.67         (((X44) != (k9_relat_1 @ X42 @ X41))
% 1.49/1.67          | (zip_tseitin_0 @ (sk_E_1 @ X45 @ X41 @ X42) @ X45 @ X41 @ X42)
% 1.49/1.67          | ~ (r2_hidden @ X45 @ X44)
% 1.49/1.67          | ~ (v1_funct_1 @ X42)
% 1.49/1.67          | ~ (v1_relat_1 @ X42))),
% 1.49/1.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.49/1.67  thf('6', plain,
% 1.49/1.67      (![X41 : $i, X42 : $i, X45 : $i]:
% 1.49/1.67         (~ (v1_relat_1 @ X42)
% 1.49/1.67          | ~ (v1_funct_1 @ X42)
% 1.49/1.67          | ~ (r2_hidden @ X45 @ (k9_relat_1 @ X42 @ X41))
% 1.49/1.67          | (zip_tseitin_0 @ (sk_E_1 @ X45 @ X41 @ X42) @ X45 @ X41 @ X42))),
% 1.49/1.67      inference('simplify', [status(thm)], ['5'])).
% 1.49/1.67  thf('7', plain,
% 1.49/1.67      (((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2) @ sk_E_2 @ 
% 1.49/1.67         sk_C_1 @ sk_D_2)
% 1.49/1.67        | ~ (v1_funct_1 @ sk_D_2)
% 1.49/1.67        | ~ (v1_relat_1 @ sk_D_2))),
% 1.49/1.67      inference('sup-', [status(thm)], ['4', '6'])).
% 1.49/1.67  thf('8', plain, ((v1_funct_1 @ sk_D_2)),
% 1.49/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.67  thf('9', plain,
% 1.49/1.67      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.49/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.67  thf(cc1_relset_1, axiom,
% 1.49/1.67    (![A:$i,B:$i,C:$i]:
% 1.49/1.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.49/1.67       ( v1_relat_1 @ C ) ))).
% 1.49/1.67  thf('10', plain,
% 1.49/1.67      (![X50 : $i, X51 : $i, X52 : $i]:
% 1.49/1.67         ((v1_relat_1 @ X50)
% 1.49/1.67          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52))))),
% 1.49/1.67      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.49/1.67  thf('11', plain, ((v1_relat_1 @ sk_D_2)),
% 1.49/1.67      inference('sup-', [status(thm)], ['9', '10'])).
% 1.49/1.67  thf('12', plain,
% 1.49/1.67      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2) @ sk_E_2 @ 
% 1.49/1.67        sk_C_1 @ sk_D_2)),
% 1.49/1.67      inference('demod', [status(thm)], ['7', '8', '11'])).
% 1.49/1.67  thf('13', plain,
% 1.49/1.67      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.49/1.67         ((r2_hidden @ X36 @ X38) | ~ (zip_tseitin_0 @ X36 @ X37 @ X38 @ X35))),
% 1.49/1.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.49/1.67  thf('14', plain,
% 1.49/1.67      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2) @ sk_C_1)),
% 1.49/1.67      inference('sup-', [status(thm)], ['12', '13'])).
% 1.49/1.67  thf('15', plain,
% 1.49/1.67      (![X71 : $i]:
% 1.49/1.67         (((sk_E_2) != (k1_funct_1 @ sk_D_2 @ X71))
% 1.49/1.67          | ~ (r2_hidden @ X71 @ sk_C_1)
% 1.49/1.67          | ~ (m1_subset_1 @ X71 @ sk_A))),
% 1.49/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.67  thf('16', plain,
% 1.49/1.67      ((~ (m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2) @ sk_A)
% 1.49/1.67        | ((sk_E_2)
% 1.49/1.67            != (k1_funct_1 @ sk_D_2 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2))))),
% 1.49/1.67      inference('sup-', [status(thm)], ['14', '15'])).
% 1.49/1.67  thf('17', plain,
% 1.49/1.67      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2) @ sk_E_2 @ 
% 1.49/1.67        sk_C_1 @ sk_D_2)),
% 1.49/1.67      inference('demod', [status(thm)], ['7', '8', '11'])).
% 1.49/1.67  thf('18', plain,
% 1.49/1.67      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.49/1.67         ((r2_hidden @ X36 @ (k1_relat_1 @ X35))
% 1.49/1.67          | ~ (zip_tseitin_0 @ X36 @ X37 @ X38 @ X35))),
% 1.49/1.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.49/1.67  thf('19', plain,
% 1.49/1.67      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2) @ (k1_relat_1 @ sk_D_2))),
% 1.49/1.67      inference('sup-', [status(thm)], ['17', '18'])).
% 1.49/1.67  thf(d1_funct_2, axiom,
% 1.49/1.67    (![A:$i,B:$i,C:$i]:
% 1.49/1.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.49/1.67       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.49/1.67           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.49/1.67             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.49/1.67         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.49/1.67           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.49/1.67             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.49/1.67  thf(zf_stmt_4, axiom,
% 1.49/1.67    (![B:$i,A:$i]:
% 1.49/1.67     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.49/1.67       ( zip_tseitin_1 @ B @ A ) ))).
% 1.49/1.67  thf('20', plain,
% 1.49/1.67      (![X63 : $i, X64 : $i]:
% 1.49/1.67         ((zip_tseitin_1 @ X63 @ X64) | ((X63) = (k1_xboole_0)))),
% 1.49/1.67      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.49/1.67  thf(d10_xboole_0, axiom,
% 1.49/1.67    (![A:$i,B:$i]:
% 1.49/1.67     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.49/1.67  thf('21', plain,
% 1.49/1.67      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 1.49/1.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.49/1.67  thf('22', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 1.49/1.67      inference('simplify', [status(thm)], ['21'])).
% 1.49/1.67  thf(t3_subset, axiom,
% 1.49/1.67    (![A:$i,B:$i]:
% 1.49/1.67     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.49/1.67  thf('23', plain,
% 1.49/1.67      (![X15 : $i, X17 : $i]:
% 1.49/1.67         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 1.49/1.67      inference('cnf', [status(esa)], [t3_subset])).
% 1.49/1.67  thf('24', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.49/1.67      inference('sup-', [status(thm)], ['22', '23'])).
% 1.49/1.67  thf(t113_zfmisc_1, axiom,
% 1.49/1.67    (![A:$i,B:$i]:
% 1.49/1.67     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.49/1.67       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.49/1.67  thf('25', plain,
% 1.49/1.67      (![X11 : $i, X12 : $i]:
% 1.49/1.67         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 1.49/1.67          | ((X12) != (k1_xboole_0)))),
% 1.49/1.67      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.49/1.67  thf('26', plain,
% 1.49/1.67      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 1.49/1.67      inference('simplify', [status(thm)], ['25'])).
% 1.49/1.67  thf(cc2_relset_1, axiom,
% 1.49/1.67    (![A:$i,B:$i,C:$i]:
% 1.49/1.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.49/1.67       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.49/1.67  thf('27', plain,
% 1.49/1.67      (![X53 : $i, X54 : $i, X55 : $i]:
% 1.49/1.67         ((v5_relat_1 @ X53 @ X55)
% 1.49/1.67          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55))))),
% 1.49/1.67      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.49/1.67  thf('28', plain,
% 1.49/1.67      (![X1 : $i]:
% 1.49/1.67         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.49/1.67          | (v5_relat_1 @ X1 @ k1_xboole_0))),
% 1.49/1.67      inference('sup-', [status(thm)], ['26', '27'])).
% 1.49/1.67  thf('29', plain, ((v5_relat_1 @ k1_xboole_0 @ k1_xboole_0)),
% 1.49/1.67      inference('sup-', [status(thm)], ['24', '28'])).
% 1.49/1.67  thf(d19_relat_1, axiom,
% 1.49/1.67    (![A:$i,B:$i]:
% 1.49/1.67     ( ( v1_relat_1 @ B ) =>
% 1.49/1.67       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.49/1.67  thf('30', plain,
% 1.49/1.67      (![X21 : $i, X22 : $i]:
% 1.49/1.67         (~ (v5_relat_1 @ X21 @ X22)
% 1.49/1.67          | (r1_tarski @ (k2_relat_1 @ X21) @ X22)
% 1.49/1.67          | ~ (v1_relat_1 @ X21))),
% 1.49/1.67      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.49/1.67  thf('31', plain,
% 1.49/1.67      ((~ (v1_relat_1 @ k1_xboole_0)
% 1.49/1.67        | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ k1_xboole_0))),
% 1.49/1.67      inference('sup-', [status(thm)], ['29', '30'])).
% 1.49/1.67  thf('32', plain,
% 1.49/1.67      (![X11 : $i, X12 : $i]:
% 1.49/1.67         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 1.49/1.67          | ((X11) != (k1_xboole_0)))),
% 1.49/1.67      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.49/1.67  thf('33', plain,
% 1.49/1.67      (![X12 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 1.49/1.67      inference('simplify', [status(thm)], ['32'])).
% 1.49/1.67  thf(fc6_relat_1, axiom,
% 1.49/1.67    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.49/1.67  thf('34', plain,
% 1.49/1.67      (![X23 : $i, X24 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X23 @ X24))),
% 1.49/1.67      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.49/1.67  thf('35', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.49/1.67      inference('sup+', [status(thm)], ['33', '34'])).
% 1.49/1.67  thf('36', plain, ((r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 1.49/1.67      inference('demod', [status(thm)], ['31', '35'])).
% 1.49/1.67  thf(d3_tarski, axiom,
% 1.49/1.67    (![A:$i,B:$i]:
% 1.49/1.67     ( ( r1_tarski @ A @ B ) <=>
% 1.49/1.67       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.49/1.67  thf('37', plain,
% 1.49/1.67      (![X4 : $i, X6 : $i]:
% 1.49/1.67         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.49/1.67      inference('cnf', [status(esa)], [d3_tarski])).
% 1.49/1.67  thf(d1_xboole_0, axiom,
% 1.49/1.67    (![A:$i]:
% 1.49/1.67     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.49/1.67  thf('38', plain,
% 1.49/1.67      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.49/1.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.49/1.67  thf('39', plain,
% 1.49/1.67      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.49/1.67      inference('sup-', [status(thm)], ['37', '38'])).
% 1.49/1.67  thf('40', plain,
% 1.49/1.67      (![X7 : $i, X9 : $i]:
% 1.49/1.67         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 1.49/1.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.49/1.67  thf('41', plain,
% 1.49/1.67      (![X0 : $i, X1 : $i]:
% 1.49/1.67         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 1.49/1.67      inference('sup-', [status(thm)], ['39', '40'])).
% 1.49/1.67  thf('42', plain,
% 1.49/1.67      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 1.49/1.67        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.49/1.67      inference('sup-', [status(thm)], ['36', '41'])).
% 1.49/1.67  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.49/1.67  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.49/1.67      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.49/1.67  thf('44', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.49/1.67      inference('demod', [status(thm)], ['42', '43'])).
% 1.49/1.67  thf('45', plain,
% 1.49/1.67      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.49/1.67      inference('sup-', [status(thm)], ['37', '38'])).
% 1.49/1.67  thf('46', plain,
% 1.49/1.67      (![X21 : $i, X22 : $i]:
% 1.49/1.67         (~ (r1_tarski @ (k2_relat_1 @ X21) @ X22)
% 1.49/1.67          | (v5_relat_1 @ X21 @ X22)
% 1.49/1.67          | ~ (v1_relat_1 @ X21))),
% 1.49/1.67      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.49/1.67  thf('47', plain,
% 1.49/1.67      (![X0 : $i, X1 : $i]:
% 1.49/1.67         (~ (v1_xboole_0 @ (k2_relat_1 @ X1))
% 1.49/1.67          | ~ (v1_relat_1 @ X1)
% 1.49/1.67          | (v5_relat_1 @ X1 @ X0))),
% 1.49/1.67      inference('sup-', [status(thm)], ['45', '46'])).
% 1.49/1.67  thf('48', plain,
% 1.49/1.67      (![X0 : $i]:
% 1.49/1.67         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.49/1.67          | (v5_relat_1 @ k1_xboole_0 @ X0)
% 1.49/1.67          | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.49/1.67      inference('sup-', [status(thm)], ['44', '47'])).
% 1.49/1.67  thf('49', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.49/1.67      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.49/1.67  thf('50', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.49/1.67      inference('sup+', [status(thm)], ['33', '34'])).
% 1.49/1.67  thf('51', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 1.49/1.67      inference('demod', [status(thm)], ['48', '49', '50'])).
% 1.49/1.67  thf('52', plain,
% 1.49/1.67      (![X21 : $i, X22 : $i]:
% 1.49/1.67         (~ (v5_relat_1 @ X21 @ X22)
% 1.49/1.67          | (r1_tarski @ (k2_relat_1 @ X21) @ X22)
% 1.49/1.67          | ~ (v1_relat_1 @ X21))),
% 1.49/1.67      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.49/1.67  thf('53', plain,
% 1.49/1.67      (![X0 : $i]:
% 1.49/1.67         (~ (v1_relat_1 @ k1_xboole_0)
% 1.49/1.67          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))),
% 1.49/1.67      inference('sup-', [status(thm)], ['51', '52'])).
% 1.49/1.67  thf('54', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.49/1.67      inference('sup+', [status(thm)], ['33', '34'])).
% 1.49/1.67  thf('55', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.49/1.67      inference('demod', [status(thm)], ['42', '43'])).
% 1.49/1.67  thf('56', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.49/1.67      inference('demod', [status(thm)], ['53', '54', '55'])).
% 1.49/1.67  thf('57', plain,
% 1.49/1.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.49/1.67         ((r1_tarski @ X0 @ X1) | (zip_tseitin_1 @ X0 @ X2))),
% 1.49/1.67      inference('sup+', [status(thm)], ['20', '56'])).
% 1.49/1.67  thf('58', plain,
% 1.49/1.67      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.49/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.67  thf('59', plain,
% 1.49/1.67      (![X53 : $i, X54 : $i, X55 : $i]:
% 1.49/1.67         ((v5_relat_1 @ X53 @ X55)
% 1.49/1.67          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55))))),
% 1.49/1.67      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.49/1.67  thf('60', plain, ((v5_relat_1 @ sk_D_2 @ sk_B_1)),
% 1.49/1.67      inference('sup-', [status(thm)], ['58', '59'])).
% 1.49/1.67  thf('61', plain,
% 1.49/1.67      (![X21 : $i, X22 : $i]:
% 1.49/1.67         (~ (v5_relat_1 @ X21 @ X22)
% 1.49/1.67          | (r1_tarski @ (k2_relat_1 @ X21) @ X22)
% 1.49/1.67          | ~ (v1_relat_1 @ X21))),
% 1.49/1.67      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.49/1.67  thf('62', plain,
% 1.49/1.67      ((~ (v1_relat_1 @ sk_D_2) | (r1_tarski @ (k2_relat_1 @ sk_D_2) @ sk_B_1))),
% 1.49/1.67      inference('sup-', [status(thm)], ['60', '61'])).
% 1.49/1.67  thf('63', plain, ((v1_relat_1 @ sk_D_2)),
% 1.49/1.67      inference('sup-', [status(thm)], ['9', '10'])).
% 1.49/1.67  thf('64', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_2) @ sk_B_1)),
% 1.49/1.67      inference('demod', [status(thm)], ['62', '63'])).
% 1.49/1.67  thf('65', plain,
% 1.49/1.67      (![X7 : $i, X9 : $i]:
% 1.49/1.67         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 1.49/1.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.49/1.67  thf('66', plain,
% 1.49/1.67      ((~ (r1_tarski @ sk_B_1 @ (k2_relat_1 @ sk_D_2))
% 1.49/1.67        | ((sk_B_1) = (k2_relat_1 @ sk_D_2)))),
% 1.49/1.67      inference('sup-', [status(thm)], ['64', '65'])).
% 1.49/1.67  thf('67', plain,
% 1.49/1.67      (![X0 : $i]:
% 1.49/1.67         ((zip_tseitin_1 @ sk_B_1 @ X0) | ((sk_B_1) = (k2_relat_1 @ sk_D_2)))),
% 1.49/1.67      inference('sup-', [status(thm)], ['57', '66'])).
% 1.49/1.67  thf('68', plain,
% 1.49/1.67      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.49/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.67  thf(zf_stmt_5, type, zip_tseitin_2 : $i > $i > $i > $o).
% 1.49/1.67  thf(zf_stmt_6, axiom,
% 1.49/1.67    (![C:$i,B:$i,A:$i]:
% 1.49/1.67     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 1.49/1.67       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.49/1.67  thf(zf_stmt_7, type, zip_tseitin_1 : $i > $i > $o).
% 1.49/1.67  thf(zf_stmt_8, axiom,
% 1.49/1.67    (![A:$i,B:$i,C:$i]:
% 1.49/1.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.49/1.67       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 1.49/1.67         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.49/1.67           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.49/1.67             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.49/1.67  thf('69', plain,
% 1.49/1.67      (![X68 : $i, X69 : $i, X70 : $i]:
% 1.49/1.67         (~ (zip_tseitin_1 @ X68 @ X69)
% 1.49/1.67          | (zip_tseitin_2 @ X70 @ X68 @ X69)
% 1.49/1.67          | ~ (m1_subset_1 @ X70 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X69 @ X68))))),
% 1.49/1.67      inference('cnf', [status(esa)], [zf_stmt_8])).
% 1.49/1.67  thf('70', plain,
% 1.49/1.67      (((zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A)
% 1.49/1.67        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A))),
% 1.49/1.67      inference('sup-', [status(thm)], ['68', '69'])).
% 1.49/1.67  thf('71', plain,
% 1.49/1.67      ((((sk_B_1) = (k2_relat_1 @ sk_D_2))
% 1.49/1.67        | (zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A))),
% 1.49/1.67      inference('sup-', [status(thm)], ['67', '70'])).
% 1.49/1.67  thf('72', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B_1)),
% 1.49/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.67  thf('73', plain,
% 1.49/1.67      (![X65 : $i, X66 : $i, X67 : $i]:
% 1.49/1.67         (~ (v1_funct_2 @ X67 @ X65 @ X66)
% 1.49/1.67          | ((X65) = (k1_relset_1 @ X65 @ X66 @ X67))
% 1.49/1.67          | ~ (zip_tseitin_2 @ X67 @ X66 @ X65))),
% 1.49/1.67      inference('cnf', [status(esa)], [zf_stmt_6])).
% 1.49/1.67  thf('74', plain,
% 1.49/1.67      ((~ (zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A)
% 1.49/1.67        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2)))),
% 1.49/1.67      inference('sup-', [status(thm)], ['72', '73'])).
% 1.49/1.67  thf('75', plain,
% 1.49/1.67      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.49/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.67  thf(redefinition_k1_relset_1, axiom,
% 1.49/1.67    (![A:$i,B:$i,C:$i]:
% 1.49/1.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.49/1.67       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.49/1.67  thf('76', plain,
% 1.49/1.67      (![X56 : $i, X57 : $i, X58 : $i]:
% 1.49/1.67         (((k1_relset_1 @ X57 @ X58 @ X56) = (k1_relat_1 @ X56))
% 1.49/1.67          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X58))))),
% 1.49/1.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.49/1.67  thf('77', plain,
% 1.49/1.67      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 1.49/1.67      inference('sup-', [status(thm)], ['75', '76'])).
% 1.49/1.67  thf('78', plain,
% 1.49/1.67      ((~ (zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A)
% 1.49/1.67        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 1.49/1.67      inference('demod', [status(thm)], ['74', '77'])).
% 1.49/1.67  thf('79', plain,
% 1.49/1.67      ((((sk_B_1) = (k2_relat_1 @ sk_D_2)) | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 1.49/1.67      inference('sup-', [status(thm)], ['71', '78'])).
% 1.49/1.67  thf('80', plain,
% 1.49/1.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.49/1.67         ((r1_tarski @ X0 @ X1) | (zip_tseitin_1 @ X0 @ X2))),
% 1.49/1.67      inference('sup+', [status(thm)], ['20', '56'])).
% 1.49/1.67  thf('81', plain,
% 1.49/1.67      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.49/1.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.49/1.67  thf('82', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_2) @ sk_B_1)),
% 1.49/1.67      inference('demod', [status(thm)], ['62', '63'])).
% 1.49/1.67  thf('83', plain,
% 1.49/1.67      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.49/1.67         (~ (r2_hidden @ X3 @ X4)
% 1.49/1.67          | (r2_hidden @ X3 @ X5)
% 1.49/1.67          | ~ (r1_tarski @ X4 @ X5))),
% 1.49/1.67      inference('cnf', [status(esa)], [d3_tarski])).
% 1.49/1.67  thf('84', plain,
% 1.49/1.67      (![X0 : $i]:
% 1.49/1.67         ((r2_hidden @ X0 @ sk_B_1)
% 1.49/1.67          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 1.49/1.67      inference('sup-', [status(thm)], ['82', '83'])).
% 1.49/1.67  thf('85', plain,
% 1.49/1.67      (((v1_xboole_0 @ (k2_relat_1 @ sk_D_2))
% 1.49/1.67        | (r2_hidden @ (sk_B @ (k2_relat_1 @ sk_D_2)) @ sk_B_1))),
% 1.49/1.67      inference('sup-', [status(thm)], ['81', '84'])).
% 1.49/1.67  thf(t7_ordinal1, axiom,
% 1.49/1.67    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.49/1.67  thf('86', plain,
% 1.49/1.67      (![X48 : $i, X49 : $i]:
% 1.49/1.67         (~ (r2_hidden @ X48 @ X49) | ~ (r1_tarski @ X49 @ X48))),
% 1.49/1.67      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.49/1.67  thf('87', plain,
% 1.49/1.67      (((v1_xboole_0 @ (k2_relat_1 @ sk_D_2))
% 1.49/1.67        | ~ (r1_tarski @ sk_B_1 @ (sk_B @ (k2_relat_1 @ sk_D_2))))),
% 1.49/1.67      inference('sup-', [status(thm)], ['85', '86'])).
% 1.49/1.67  thf('88', plain,
% 1.49/1.67      (![X0 : $i]:
% 1.49/1.67         ((zip_tseitin_1 @ sk_B_1 @ X0) | (v1_xboole_0 @ (k2_relat_1 @ sk_D_2)))),
% 1.49/1.67      inference('sup-', [status(thm)], ['80', '87'])).
% 1.49/1.67  thf('89', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.49/1.67      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.49/1.67  thf('90', plain,
% 1.49/1.67      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.49/1.67      inference('sup-', [status(thm)], ['37', '38'])).
% 1.49/1.67  thf('91', plain,
% 1.49/1.67      (![X0 : $i, X1 : $i]:
% 1.49/1.67         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 1.49/1.67      inference('sup-', [status(thm)], ['39', '40'])).
% 1.49/1.67  thf('92', plain,
% 1.49/1.67      (![X0 : $i, X1 : $i]:
% 1.49/1.67         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.49/1.67      inference('sup-', [status(thm)], ['90', '91'])).
% 1.49/1.67  thf('93', plain,
% 1.49/1.67      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 1.49/1.67      inference('sup-', [status(thm)], ['89', '92'])).
% 1.49/1.67  thf('94', plain,
% 1.49/1.67      (![X0 : $i]:
% 1.49/1.67         ((zip_tseitin_1 @ sk_B_1 @ X0)
% 1.49/1.67          | ((k1_xboole_0) = (k2_relat_1 @ sk_D_2)))),
% 1.49/1.67      inference('sup-', [status(thm)], ['88', '93'])).
% 1.49/1.67  thf('95', plain,
% 1.49/1.67      (((zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A)
% 1.49/1.67        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A))),
% 1.49/1.67      inference('sup-', [status(thm)], ['68', '69'])).
% 1.49/1.67  thf('96', plain,
% 1.49/1.67      ((((k1_xboole_0) = (k2_relat_1 @ sk_D_2))
% 1.49/1.67        | (zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A))),
% 1.49/1.67      inference('sup-', [status(thm)], ['94', '95'])).
% 1.49/1.67  thf('97', plain,
% 1.49/1.67      ((~ (zip_tseitin_2 @ sk_D_2 @ sk_B_1 @ sk_A)
% 1.49/1.67        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 1.49/1.67      inference('demod', [status(thm)], ['74', '77'])).
% 1.49/1.67  thf('98', plain,
% 1.49/1.67      ((((k1_xboole_0) = (k2_relat_1 @ sk_D_2))
% 1.49/1.67        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 1.49/1.67      inference('sup-', [status(thm)], ['96', '97'])).
% 1.49/1.67  thf('99', plain,
% 1.49/1.67      (![X21 : $i, X22 : $i]:
% 1.49/1.67         (~ (r1_tarski @ (k2_relat_1 @ X21) @ X22)
% 1.49/1.67          | (v5_relat_1 @ X21 @ X22)
% 1.49/1.67          | ~ (v1_relat_1 @ X21))),
% 1.49/1.67      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.49/1.67  thf('100', plain,
% 1.49/1.67      (![X0 : $i]:
% 1.49/1.67         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 1.49/1.67          | ((sk_A) = (k1_relat_1 @ sk_D_2))
% 1.49/1.67          | ~ (v1_relat_1 @ sk_D_2)
% 1.49/1.67          | (v5_relat_1 @ sk_D_2 @ X0))),
% 1.49/1.67      inference('sup-', [status(thm)], ['98', '99'])).
% 1.49/1.67  thf('101', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.49/1.67      inference('demod', [status(thm)], ['53', '54', '55'])).
% 1.49/1.67  thf('102', plain, ((v1_relat_1 @ sk_D_2)),
% 1.49/1.67      inference('sup-', [status(thm)], ['9', '10'])).
% 1.49/1.67  thf('103', plain,
% 1.49/1.67      (![X0 : $i]:
% 1.49/1.67         (((sk_A) = (k1_relat_1 @ sk_D_2)) | (v5_relat_1 @ sk_D_2 @ X0))),
% 1.49/1.67      inference('demod', [status(thm)], ['100', '101', '102'])).
% 1.49/1.67  thf('104', plain,
% 1.49/1.67      (![X21 : $i, X22 : $i]:
% 1.49/1.67         (~ (v5_relat_1 @ X21 @ X22)
% 1.49/1.67          | (r1_tarski @ (k2_relat_1 @ X21) @ X22)
% 1.49/1.67          | ~ (v1_relat_1 @ X21))),
% 1.49/1.67      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.49/1.67  thf('105', plain,
% 1.49/1.67      (![X0 : $i]:
% 1.49/1.67         (((sk_A) = (k1_relat_1 @ sk_D_2))
% 1.49/1.67          | ~ (v1_relat_1 @ sk_D_2)
% 1.49/1.67          | (r1_tarski @ (k2_relat_1 @ sk_D_2) @ X0))),
% 1.49/1.67      inference('sup-', [status(thm)], ['103', '104'])).
% 1.49/1.67  thf('106', plain, ((v1_relat_1 @ sk_D_2)),
% 1.49/1.67      inference('sup-', [status(thm)], ['9', '10'])).
% 1.49/1.67  thf('107', plain,
% 1.49/1.67      (![X0 : $i]:
% 1.49/1.67         (((sk_A) = (k1_relat_1 @ sk_D_2))
% 1.49/1.67          | (r1_tarski @ (k2_relat_1 @ sk_D_2) @ X0))),
% 1.49/1.67      inference('demod', [status(thm)], ['105', '106'])).
% 1.49/1.67  thf('108', plain,
% 1.49/1.67      (![X0 : $i]:
% 1.49/1.67         ((r1_tarski @ sk_B_1 @ X0)
% 1.49/1.67          | ((sk_A) = (k1_relat_1 @ sk_D_2))
% 1.49/1.67          | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 1.49/1.67      inference('sup+', [status(thm)], ['79', '107'])).
% 1.49/1.67  thf('109', plain,
% 1.49/1.67      (![X0 : $i]:
% 1.49/1.67         (((sk_A) = (k1_relat_1 @ sk_D_2)) | (r1_tarski @ sk_B_1 @ X0))),
% 1.49/1.67      inference('simplify', [status(thm)], ['108'])).
% 1.49/1.67  thf('110', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_C_1))),
% 1.49/1.67      inference('demod', [status(thm)], ['0', '3'])).
% 1.49/1.67  thf(t143_relat_1, axiom,
% 1.49/1.67    (![A:$i,B:$i,C:$i]:
% 1.49/1.67     ( ( v1_relat_1 @ C ) =>
% 1.49/1.67       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 1.49/1.67         ( ?[D:$i]:
% 1.49/1.67           ( ( r2_hidden @ D @ B ) & 
% 1.49/1.67             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 1.49/1.67             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 1.49/1.67  thf('111', plain,
% 1.49/1.67      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.49/1.67         (~ (r2_hidden @ X27 @ (k9_relat_1 @ X28 @ X26))
% 1.49/1.67          | (r2_hidden @ (k4_tarski @ (sk_D @ X28 @ X26 @ X27) @ X27) @ X28)
% 1.49/1.67          | ~ (v1_relat_1 @ X28))),
% 1.49/1.67      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.49/1.67  thf('112', plain,
% 1.49/1.67      ((~ (v1_relat_1 @ sk_D_2)
% 1.49/1.67        | (r2_hidden @ 
% 1.49/1.67           (k4_tarski @ (sk_D @ sk_D_2 @ sk_C_1 @ sk_E_2) @ sk_E_2) @ sk_D_2))),
% 1.49/1.67      inference('sup-', [status(thm)], ['110', '111'])).
% 1.49/1.67  thf('113', plain, ((v1_relat_1 @ sk_D_2)),
% 1.49/1.67      inference('sup-', [status(thm)], ['9', '10'])).
% 1.49/1.67  thf('114', plain,
% 1.49/1.67      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_2 @ sk_C_1 @ sk_E_2) @ sk_E_2) @ 
% 1.49/1.67        sk_D_2)),
% 1.49/1.67      inference('demod', [status(thm)], ['112', '113'])).
% 1.49/1.67  thf(t20_relat_1, axiom,
% 1.49/1.67    (![A:$i,B:$i,C:$i]:
% 1.49/1.67     ( ( v1_relat_1 @ C ) =>
% 1.49/1.67       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 1.49/1.67         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 1.49/1.67           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 1.49/1.67  thf('115', plain,
% 1.49/1.67      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.49/1.67         (~ (r2_hidden @ (k4_tarski @ X32 @ X33) @ X34)
% 1.49/1.67          | (r2_hidden @ X33 @ (k2_relat_1 @ X34))
% 1.49/1.67          | ~ (v1_relat_1 @ X34))),
% 1.49/1.67      inference('cnf', [status(esa)], [t20_relat_1])).
% 1.49/1.67  thf('116', plain,
% 1.49/1.67      ((~ (v1_relat_1 @ sk_D_2) | (r2_hidden @ sk_E_2 @ (k2_relat_1 @ sk_D_2)))),
% 1.49/1.67      inference('sup-', [status(thm)], ['114', '115'])).
% 1.49/1.67  thf('117', plain, ((v1_relat_1 @ sk_D_2)),
% 1.49/1.67      inference('sup-', [status(thm)], ['9', '10'])).
% 1.49/1.67  thf('118', plain, ((r2_hidden @ sk_E_2 @ (k2_relat_1 @ sk_D_2))),
% 1.49/1.67      inference('demod', [status(thm)], ['116', '117'])).
% 1.49/1.67  thf('119', plain,
% 1.49/1.67      (![X0 : $i]:
% 1.49/1.67         ((r2_hidden @ X0 @ sk_B_1)
% 1.49/1.67          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 1.49/1.67      inference('sup-', [status(thm)], ['82', '83'])).
% 1.49/1.67  thf('120', plain, ((r2_hidden @ sk_E_2 @ sk_B_1)),
% 1.49/1.67      inference('sup-', [status(thm)], ['118', '119'])).
% 1.49/1.67  thf('121', plain,
% 1.49/1.67      (![X48 : $i, X49 : $i]:
% 1.49/1.67         (~ (r2_hidden @ X48 @ X49) | ~ (r1_tarski @ X49 @ X48))),
% 1.49/1.67      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.49/1.67  thf('122', plain, (~ (r1_tarski @ sk_B_1 @ sk_E_2)),
% 1.49/1.67      inference('sup-', [status(thm)], ['120', '121'])).
% 1.49/1.67  thf('123', plain, (((sk_A) = (k1_relat_1 @ sk_D_2))),
% 1.49/1.67      inference('sup-', [status(thm)], ['109', '122'])).
% 1.49/1.67  thf('124', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2) @ sk_A)),
% 1.49/1.67      inference('demod', [status(thm)], ['19', '123'])).
% 1.49/1.67  thf(t1_subset, axiom,
% 1.49/1.67    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.49/1.67  thf('125', plain,
% 1.49/1.67      (![X13 : $i, X14 : $i]:
% 1.49/1.67         ((m1_subset_1 @ X13 @ X14) | ~ (r2_hidden @ X13 @ X14))),
% 1.49/1.67      inference('cnf', [status(esa)], [t1_subset])).
% 1.49/1.67  thf('126', plain,
% 1.49/1.67      ((m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2) @ sk_A)),
% 1.49/1.67      inference('sup-', [status(thm)], ['124', '125'])).
% 1.49/1.67  thf('127', plain,
% 1.49/1.67      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2) @ sk_E_2 @ 
% 1.49/1.67        sk_C_1 @ sk_D_2)),
% 1.49/1.67      inference('demod', [status(thm)], ['7', '8', '11'])).
% 1.49/1.67  thf('128', plain,
% 1.49/1.67      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.49/1.67         (((X37) = (k1_funct_1 @ X35 @ X36))
% 1.49/1.67          | ~ (zip_tseitin_0 @ X36 @ X37 @ X38 @ X35))),
% 1.49/1.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.49/1.67  thf('129', plain,
% 1.49/1.67      (((sk_E_2) = (k1_funct_1 @ sk_D_2 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_2)))),
% 1.49/1.67      inference('sup-', [status(thm)], ['127', '128'])).
% 1.49/1.67  thf('130', plain, (((sk_E_2) != (sk_E_2))),
% 1.49/1.67      inference('demod', [status(thm)], ['16', '126', '129'])).
% 1.49/1.67  thf('131', plain, ($false), inference('simplify', [status(thm)], ['130'])).
% 1.49/1.67  
% 1.49/1.67  % SZS output end Refutation
% 1.49/1.67  
% 1.49/1.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
