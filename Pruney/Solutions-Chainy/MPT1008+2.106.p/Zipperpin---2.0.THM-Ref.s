%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GBHsZywwbO

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:46 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 162 expanded)
%              Number of leaves         :   48 (  71 expanded)
%              Depth                    :   11
%              Number of atoms          :  756 (1719 expanded)
%              Number of equality atoms :   69 ( 137 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t62_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
          = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
            = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_funct_2])).

thf('0',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ~ ( v1_funct_2 @ X63 @ X61 @ X62 )
      | ( X61
        = ( k1_relset_1 @ X61 @ X62 @ X63 ) )
      | ~ ( zip_tseitin_2 @ X63 @ X62 @ X61 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_2 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('3',plain,(
    ! [X59: $i,X60: $i] :
      ( ( zip_tseitin_1 @ X59 @ X60 )
      | ( X59 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_1 @ B @ A )
         => ( zip_tseitin_2 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ~ ( zip_tseitin_1 @ X64 @ X65 )
      | ( zip_tseitin_2 @ X66 @ X64 @ X65 )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X65 @ X64 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_2 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    zip_tseitin_2 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( ( k1_relset_1 @ X54 @ X55 @ X53 )
        = ( k1_relat_1 @ X53 ) )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X3 @ X3 @ X4 @ X5 )
      = ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(d3_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( F
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) )
    <=> ! [G: $i] :
          ( ( r2_hidden @ G @ F )
        <=> ~ ( ( G != E )
              & ( G != D )
              & ( G != C )
              & ( G != B )
              & ( G != A ) ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [G: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A )
    <=> ( ( G != A )
        & ( G != B )
        & ( G != C )
        & ( G != D )
        & ( G != E ) ) ) )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( F
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) )
    <=> ! [G: $i] :
          ( ( r2_hidden @ G @ F )
        <=> ~ ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 )
      | ( r2_hidden @ X35 @ X41 )
      | ( X41
       != ( k3_enumset1 @ X40 @ X39 @ X38 @ X37 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('19',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( r2_hidden @ X35 @ ( k3_enumset1 @ X40 @ X39 @ X38 @ X37 @ X36 ) )
      | ( zip_tseitin_0 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 ) ) ),
    inference('sup+',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( X29 != X28 )
      | ~ ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 @ X33 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('22',plain,(
    ! [X28: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ~ ( zip_tseitin_0 @ X28 @ X30 @ X31 @ X32 @ X33 @ X28 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','25'])).

thf('27',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['13','26'])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('28',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X51 @ ( k1_relat_1 @ X52 ) )
      | ( ( k11_relat_1 @ X52 @ X51 )
        = ( k1_tarski @ ( k1_funct_1 @ X52 @ X51 ) ) )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k11_relat_1 @ sk_C @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('31',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ( v1_relat_1 @ X44 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('33',plain,(
    ! [X48: $i,X49: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('36',plain,(
    ! [X50: $i] :
      ( ( ( k9_relat_1 @ X50 @ ( k1_relat_1 @ X50 ) )
        = ( k2_relat_1 @ X50 ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('37',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('39',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('41',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k11_relat_1 @ X46 @ X47 )
        = ( k9_relat_1 @ X46 @ ( k1_tarski @ X47 ) ) )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = ( k9_relat_1 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k11_relat_1 @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k11_relat_1 @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','43'])).

thf('45',plain,
    ( ( k11_relat_1 @ sk_C @ sk_A )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['37','44'])).

thf('46',plain,
    ( ( ( k11_relat_1 @ sk_C @ sk_A )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['36','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('48',plain,
    ( ( k11_relat_1 @ sk_C @ sk_A )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','34','35','48'])).

thf('50',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('52',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ( ( k2_relset_1 @ X57 @ X58 @ X56 )
        = ( k2_relat_1 @ X56 ) )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X58 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('53',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['49','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GBHsZywwbO
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:35:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.53  % Solved by: fo/fo7.sh
% 0.36/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.53  % done 100 iterations in 0.081s
% 0.36/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.53  % SZS output start Refutation
% 0.36/0.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o).
% 0.36/0.53  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.36/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.53  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.36/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.53  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.36/0.53  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.36/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.53  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.36/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.36/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.53  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.36/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.53  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.36/0.53  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.36/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.36/0.53  thf(t62_funct_2, conjecture,
% 0.36/0.53    (![A:$i,B:$i,C:$i]:
% 0.36/0.53     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.36/0.53         ( m1_subset_1 @
% 0.36/0.53           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.36/0.53       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.36/0.53         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.36/0.53           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.36/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.53        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.36/0.53            ( m1_subset_1 @
% 0.36/0.53              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.36/0.53          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.36/0.53            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.36/0.53              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.36/0.53    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.36/0.53  thf('0', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(d1_funct_2, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i]:
% 0.36/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.53       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.36/0.53           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.36/0.53             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.36/0.53         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.53           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.36/0.53             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.36/0.53  thf(zf_stmt_1, axiom,
% 0.36/0.53    (![C:$i,B:$i,A:$i]:
% 0.36/0.53     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.36/0.53       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.36/0.53  thf('1', plain,
% 0.36/0.53      (![X61 : $i, X62 : $i, X63 : $i]:
% 0.36/0.53         (~ (v1_funct_2 @ X63 @ X61 @ X62)
% 0.36/0.53          | ((X61) = (k1_relset_1 @ X61 @ X62 @ X63))
% 0.36/0.53          | ~ (zip_tseitin_2 @ X63 @ X62 @ X61))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.36/0.53  thf('2', plain,
% 0.36/0.53      ((~ (zip_tseitin_2 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.36/0.53        | ((k1_tarski @ sk_A)
% 0.36/0.53            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.53  thf(zf_stmt_2, axiom,
% 0.36/0.53    (![B:$i,A:$i]:
% 0.36/0.53     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.53       ( zip_tseitin_1 @ B @ A ) ))).
% 0.36/0.53  thf('3', plain,
% 0.36/0.53      (![X59 : $i, X60 : $i]:
% 0.36/0.53         ((zip_tseitin_1 @ X59 @ X60) | ((X59) = (k1_xboole_0)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.36/0.53  thf('4', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_C @ 
% 0.36/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.36/0.53  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $o).
% 0.36/0.53  thf(zf_stmt_5, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i]:
% 0.36/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.53       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.36/0.53         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.36/0.53           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.36/0.53             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.36/0.53  thf('5', plain,
% 0.36/0.53      (![X64 : $i, X65 : $i, X66 : $i]:
% 0.36/0.53         (~ (zip_tseitin_1 @ X64 @ X65)
% 0.36/0.53          | (zip_tseitin_2 @ X66 @ X64 @ X65)
% 0.36/0.53          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X65 @ X64))))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.36/0.53  thf('6', plain,
% 0.36/0.53      (((zip_tseitin_2 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.36/0.53        | ~ (zip_tseitin_1 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.53  thf('7', plain,
% 0.36/0.53      ((((sk_B) = (k1_xboole_0))
% 0.36/0.53        | (zip_tseitin_2 @ sk_C @ sk_B @ (k1_tarski @ sk_A)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['3', '6'])).
% 0.36/0.53  thf('8', plain, (((sk_B) != (k1_xboole_0))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('9', plain, ((zip_tseitin_2 @ sk_C @ sk_B @ (k1_tarski @ sk_A))),
% 0.36/0.53      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.36/0.53  thf('10', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_C @ 
% 0.36/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(redefinition_k1_relset_1, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i]:
% 0.36/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.53       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.36/0.53  thf('11', plain,
% 0.36/0.53      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.36/0.53         (((k1_relset_1 @ X54 @ X55 @ X53) = (k1_relat_1 @ X53))
% 0.36/0.53          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55))))),
% 0.36/0.53      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.36/0.53  thf('12', plain,
% 0.36/0.53      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.36/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.53  thf('13', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.36/0.53      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.36/0.53  thf(t69_enumset1, axiom,
% 0.36/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.36/0.53  thf('14', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.36/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.53  thf(t70_enumset1, axiom,
% 0.36/0.53    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.36/0.53  thf('15', plain,
% 0.36/0.53      (![X1 : $i, X2 : $i]:
% 0.36/0.53         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.36/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.36/0.53  thf(t71_enumset1, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i]:
% 0.36/0.53     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.36/0.53  thf('16', plain,
% 0.36/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.53         ((k2_enumset1 @ X3 @ X3 @ X4 @ X5) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.36/0.53      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.36/0.53  thf(t72_enumset1, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.53     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.36/0.53  thf('17', plain,
% 0.36/0.53      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.36/0.53         ((k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9)
% 0.36/0.53           = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 0.36/0.53      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.36/0.53  thf(d3_enumset1, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.36/0.53     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 0.36/0.53       ( ![G:$i]:
% 0.36/0.53         ( ( r2_hidden @ G @ F ) <=>
% 0.36/0.53           ( ~( ( ( G ) != ( E ) ) & ( ( G ) != ( D ) ) & ( ( G ) != ( C ) ) & 
% 0.36/0.53                ( ( G ) != ( B ) ) & ( ( G ) != ( A ) ) ) ) ) ) ))).
% 0.36/0.53  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $o).
% 0.36/0.53  thf(zf_stmt_7, axiom,
% 0.36/0.53    (![G:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.36/0.53     ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) <=>
% 0.36/0.53       ( ( ( G ) != ( A ) ) & ( ( G ) != ( B ) ) & ( ( G ) != ( C ) ) & 
% 0.36/0.53         ( ( G ) != ( D ) ) & ( ( G ) != ( E ) ) ) ))).
% 0.36/0.53  thf(zf_stmt_8, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.36/0.53     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 0.36/0.53       ( ![G:$i]:
% 0.36/0.53         ( ( r2_hidden @ G @ F ) <=>
% 0.36/0.53           ( ~( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.36/0.53  thf('18', plain,
% 0.36/0.53      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.36/0.53         ((zip_tseitin_0 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40)
% 0.36/0.53          | (r2_hidden @ X35 @ X41)
% 0.36/0.53          | ((X41) != (k3_enumset1 @ X40 @ X39 @ X38 @ X37 @ X36)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.36/0.53  thf('19', plain,
% 0.36/0.53      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.36/0.53         ((r2_hidden @ X35 @ (k3_enumset1 @ X40 @ X39 @ X38 @ X37 @ X36))
% 0.36/0.53          | (zip_tseitin_0 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40))),
% 0.36/0.53      inference('simplify', [status(thm)], ['18'])).
% 0.36/0.53  thf('20', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.53         ((r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.36/0.53          | (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3))),
% 0.36/0.53      inference('sup+', [status(thm)], ['17', '19'])).
% 0.36/0.53  thf('21', plain,
% 0.36/0.53      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.36/0.53         (((X29) != (X28))
% 0.36/0.53          | ~ (zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 @ X33 @ X28))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.36/0.53  thf('22', plain,
% 0.36/0.53      (![X28 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.36/0.53         ~ (zip_tseitin_0 @ X28 @ X30 @ X31 @ X32 @ X33 @ X28)),
% 0.36/0.53      inference('simplify', [status(thm)], ['21'])).
% 0.36/0.53  thf('23', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.53         (r2_hidden @ X0 @ (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.36/0.53      inference('sup-', [status(thm)], ['20', '22'])).
% 0.36/0.53  thf('24', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.53         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.36/0.53      inference('sup+', [status(thm)], ['16', '23'])).
% 0.36/0.53  thf('25', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.36/0.53      inference('sup+', [status(thm)], ['15', '24'])).
% 0.36/0.53  thf('26', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.36/0.53      inference('sup+', [status(thm)], ['14', '25'])).
% 0.36/0.53  thf('27', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.36/0.53      inference('sup+', [status(thm)], ['13', '26'])).
% 0.36/0.53  thf(t117_funct_1, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.53       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.36/0.53         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.36/0.53  thf('28', plain,
% 0.36/0.53      (![X51 : $i, X52 : $i]:
% 0.36/0.53         (~ (r2_hidden @ X51 @ (k1_relat_1 @ X52))
% 0.36/0.53          | ((k11_relat_1 @ X52 @ X51) = (k1_tarski @ (k1_funct_1 @ X52 @ X51)))
% 0.36/0.53          | ~ (v1_funct_1 @ X52)
% 0.36/0.53          | ~ (v1_relat_1 @ X52))),
% 0.36/0.53      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.36/0.53  thf('29', plain,
% 0.36/0.53      ((~ (v1_relat_1 @ sk_C)
% 0.36/0.53        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.53        | ((k11_relat_1 @ sk_C @ sk_A)
% 0.36/0.53            = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A))))),
% 0.36/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.53  thf('30', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_C @ 
% 0.36/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(cc2_relat_1, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( v1_relat_1 @ A ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.36/0.53  thf('31', plain,
% 0.36/0.53      (![X44 : $i, X45 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 0.36/0.53          | (v1_relat_1 @ X44)
% 0.36/0.53          | ~ (v1_relat_1 @ X45))),
% 0.36/0.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.36/0.53  thf('32', plain,
% 0.36/0.53      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.36/0.53        | (v1_relat_1 @ sk_C))),
% 0.36/0.53      inference('sup-', [status(thm)], ['30', '31'])).
% 0.36/0.53  thf(fc6_relat_1, axiom,
% 0.36/0.53    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.36/0.53  thf('33', plain,
% 0.36/0.53      (![X48 : $i, X49 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X48 @ X49))),
% 0.36/0.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.36/0.53  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.53      inference('demod', [status(thm)], ['32', '33'])).
% 0.36/0.53  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(t146_relat_1, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( v1_relat_1 @ A ) =>
% 0.36/0.53       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.36/0.53  thf('36', plain,
% 0.36/0.53      (![X50 : $i]:
% 0.36/0.53         (((k9_relat_1 @ X50 @ (k1_relat_1 @ X50)) = (k2_relat_1 @ X50))
% 0.36/0.53          | ~ (v1_relat_1 @ X50))),
% 0.36/0.53      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.36/0.53  thf('37', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.36/0.53      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.36/0.53  thf('38', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.36/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.53  thf('39', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.53      inference('demod', [status(thm)], ['32', '33'])).
% 0.36/0.53  thf('40', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.36/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.53  thf(d16_relat_1, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( v1_relat_1 @ A ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.36/0.53  thf('41', plain,
% 0.36/0.53      (![X46 : $i, X47 : $i]:
% 0.36/0.53         (((k11_relat_1 @ X46 @ X47) = (k9_relat_1 @ X46 @ (k1_tarski @ X47)))
% 0.36/0.53          | ~ (v1_relat_1 @ X46))),
% 0.36/0.53      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.36/0.53  thf('42', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i]:
% 0.36/0.53         (((k11_relat_1 @ X1 @ X0) = (k9_relat_1 @ X1 @ (k2_tarski @ X0 @ X0)))
% 0.36/0.53          | ~ (v1_relat_1 @ X1))),
% 0.36/0.53      inference('sup+', [status(thm)], ['40', '41'])).
% 0.36/0.53  thf('43', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         ((k11_relat_1 @ sk_C @ X0)
% 0.36/0.53           = (k9_relat_1 @ sk_C @ (k2_tarski @ X0 @ X0)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['39', '42'])).
% 0.36/0.53  thf('44', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         ((k11_relat_1 @ sk_C @ X0) = (k9_relat_1 @ sk_C @ (k1_tarski @ X0)))),
% 0.36/0.53      inference('sup+', [status(thm)], ['38', '43'])).
% 0.36/0.53  thf('45', plain,
% 0.36/0.53      (((k11_relat_1 @ sk_C @ sk_A) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.36/0.53      inference('sup+', [status(thm)], ['37', '44'])).
% 0.36/0.53  thf('46', plain,
% 0.36/0.53      ((((k11_relat_1 @ sk_C @ sk_A) = (k2_relat_1 @ sk_C))
% 0.36/0.53        | ~ (v1_relat_1 @ sk_C))),
% 0.36/0.53      inference('sup+', [status(thm)], ['36', '45'])).
% 0.36/0.53  thf('47', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.53      inference('demod', [status(thm)], ['32', '33'])).
% 0.36/0.53  thf('48', plain, (((k11_relat_1 @ sk_C @ sk_A) = (k2_relat_1 @ sk_C))),
% 0.36/0.53      inference('demod', [status(thm)], ['46', '47'])).
% 0.36/0.53  thf('49', plain,
% 0.36/0.53      (((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.36/0.53      inference('demod', [status(thm)], ['29', '34', '35', '48'])).
% 0.36/0.53  thf('50', plain,
% 0.36/0.53      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)
% 0.36/0.53         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('51', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_C @ 
% 0.36/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(redefinition_k2_relset_1, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i]:
% 0.36/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.53       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.36/0.53  thf('52', plain,
% 0.36/0.53      (![X56 : $i, X57 : $i, X58 : $i]:
% 0.36/0.53         (((k2_relset_1 @ X57 @ X58 @ X56) = (k2_relat_1 @ X56))
% 0.36/0.53          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X58))))),
% 0.36/0.53      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.36/0.53  thf('53', plain,
% 0.36/0.53      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.36/0.53      inference('sup-', [status(thm)], ['51', '52'])).
% 0.36/0.53  thf('54', plain,
% 0.36/0.53      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.36/0.53      inference('demod', [status(thm)], ['50', '53'])).
% 0.36/0.53  thf('55', plain, ($false),
% 0.36/0.53      inference('simplify_reflect-', [status(thm)], ['49', '54'])).
% 0.36/0.53  
% 0.36/0.53  % SZS output end Refutation
% 0.36/0.53  
% 0.36/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
