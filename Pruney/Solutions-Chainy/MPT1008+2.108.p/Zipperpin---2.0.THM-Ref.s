%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XhX5DQLloI

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:46 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 314 expanded)
%              Number of leaves         :   52 ( 117 expanded)
%              Depth                    :   14
%              Number of atoms          : 1022 (4132 expanded)
%              Number of equality atoms :   90 ( 326 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o )).

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
    ! [X66: $i,X67: $i,X68: $i] :
      ( ~ ( v1_funct_2 @ X68 @ X66 @ X67 )
      | ( X66
        = ( k1_relset_1 @ X66 @ X67 @ X68 ) )
      | ~ ( zip_tseitin_2 @ X68 @ X67 @ X66 ) ) ),
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
    ! [X64: $i,X65: $i] :
      ( ( zip_tseitin_1 @ X64 @ X65 )
      | ( X64 = k1_xboole_0 ) ) ),
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
    ! [X69: $i,X70: $i,X71: $i] :
      ( ~ ( zip_tseitin_1 @ X69 @ X70 )
      | ( zip_tseitin_2 @ X71 @ X69 @ X70 )
      | ~ ( m1_subset_1 @ X71 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X70 @ X69 ) ) ) ) ),
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
    ! [X54: $i,X55: $i,X56: $i] :
      ( ( ( k1_relset_1 @ X55 @ X56 @ X54 )
        = ( k1_relat_1 @ X54 ) )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X56 ) ) ) ) ),
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

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k4_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(d4_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( G
        = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) )
    <=> ! [H: $i] :
          ( ( r2_hidden @ H @ G )
        <=> ~ ( ( H != F )
              & ( H != E )
              & ( H != D )
              & ( H != C )
              & ( H != B )
              & ( H != A ) ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [H: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A )
    <=> ( ( H != A )
        & ( H != B )
        & ( H != C )
        & ( H != D )
        & ( H != E )
        & ( H != F ) ) ) )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( G
        = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) )
    <=> ! [H: $i] :
          ( ( r2_hidden @ H @ G )
        <=> ~ ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 )
      | ( r2_hidden @ X36 @ X43 )
      | ( X43
       != ( k4_enumset1 @ X42 @ X41 @ X40 @ X39 @ X38 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('20',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( r2_hidden @ X36 @ ( k4_enumset1 @ X42 @ X41 @ X40 @ X39 @ X38 @ X37 ) )
      | ( zip_tseitin_0 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 ) ) ),
    inference('sup+',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( X29 != X28 )
      | ~ ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('23',plain,(
    ! [X28: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ~ ( zip_tseitin_0 @ X28 @ X30 @ X31 @ X32 @ X33 @ X34 @ X28 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X0 @ ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','27'])).

thf('29',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['13','28'])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('30',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X52 @ ( k1_relat_1 @ X53 ) )
      | ( ( k11_relat_1 @ X53 @ X52 )
        = ( k1_tarski @ ( k1_funct_1 @ X53 @ X52 ) ) )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k11_relat_1 @ sk_C @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('33',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) )
      | ( v1_relat_1 @ X46 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('35',plain,(
    ! [X50: $i,X51: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('36',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k11_relat_1 @ sk_C @ sk_A )
    = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','36','37'])).

thf('39',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('41',plain,(
    ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(t39_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) )
          = ( k2_relset_1 @ B @ A @ C ) )
        & ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) )
          = ( k1_relset_1 @ B @ A @ C ) ) ) ) )).

thf('45',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ( ( k7_relset_1 @ X61 @ X62 @ X63 @ ( k8_relset_1 @ X61 @ X62 @ X63 @ X62 ) )
        = ( k2_relset_1 @ X61 @ X62 @ X63 ) )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X61 @ X62 ) ) ) ) ),
    inference(cnf,[status(esa)],[t39_relset_1])).

thf('46',plain,
    ( ( k7_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C @ ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C @ sk_B ) )
    = ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(t48_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k8_relset_1 @ A @ B @ C @ B )
          = A ) ) ) )).

thf('48',plain,(
    ! [X72: $i,X73: $i,X74: $i] :
      ( ( X74 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X73 )
      | ~ ( v1_funct_2 @ X73 @ X72 @ X74 )
      | ~ ( m1_subset_1 @ X73 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X72 @ X74 ) ) )
      | ( ( k8_relset_1 @ X72 @ X74 @ X73 @ X74 )
        = X72 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_2])).

thf('49',plain,
    ( ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C @ sk_B )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('52',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C @ sk_B )
      = ( k1_relat_1 @ sk_C ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','52','53'])).

thf('55',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C @ sk_B )
    = ( k1_relat_1 @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('58',plain,(
    ! [X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X59 ) ) )
      | ( ( k7_relset_1 @ X58 @ X59 @ X57 @ X60 )
        = ( k9_relat_1 @ X57 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['46','56','59'])).

thf('61',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('63',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['34','35'])).

thf('64',plain,(
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

thf('65',plain,(
    ! [X48: $i,X49: $i] :
      ( ( ( k11_relat_1 @ X48 @ X49 )
        = ( k9_relat_1 @ X48 @ ( k1_tarski @ X49 ) ) )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = ( k9_relat_1 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k11_relat_1 @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k11_relat_1 @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['62','67'])).

thf('69',plain,
    ( ( k11_relat_1 @ sk_C @ sk_A )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['61','68'])).

thf('70',plain,
    ( ( k11_relat_1 @ sk_C @ sk_A )
    = ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['60','69'])).

thf('71',plain,(
    ( k11_relat_1 @ sk_C @ sk_A )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','70'])).

thf('72',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['38','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XhX5DQLloI
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:39:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.63  % Solved by: fo/fo7.sh
% 0.42/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.63  % done 152 iterations in 0.175s
% 0.42/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.63  % SZS output start Refutation
% 0.42/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.63  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.42/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.63  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.42/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.63  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.42/0.63  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.42/0.63  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.42/0.63  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.42/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.42/0.63  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.42/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.63  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.42/0.63  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.42/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.63  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.42/0.63  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.42/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.63  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.42/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.42/0.63  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.42/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.63  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.42/0.63  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o).
% 0.42/0.63  thf(t62_funct_2, conjecture,
% 0.42/0.63    (![A:$i,B:$i,C:$i]:
% 0.42/0.63     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.42/0.63         ( m1_subset_1 @
% 0.42/0.63           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.42/0.63       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.42/0.63         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.42/0.63           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.42/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.63    (~( ![A:$i,B:$i,C:$i]:
% 0.42/0.63        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.42/0.63            ( m1_subset_1 @
% 0.42/0.63              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.42/0.63          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.42/0.63            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.42/0.63              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.42/0.63    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.42/0.63  thf('0', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf(d1_funct_2, axiom,
% 0.42/0.63    (![A:$i,B:$i,C:$i]:
% 0.42/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.63       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.63           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.42/0.63             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.42/0.63         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.63           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.42/0.63             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.42/0.63  thf(zf_stmt_1, axiom,
% 0.42/0.63    (![C:$i,B:$i,A:$i]:
% 0.42/0.63     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.42/0.63       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.42/0.63  thf('1', plain,
% 0.42/0.63      (![X66 : $i, X67 : $i, X68 : $i]:
% 0.42/0.63         (~ (v1_funct_2 @ X68 @ X66 @ X67)
% 0.42/0.63          | ((X66) = (k1_relset_1 @ X66 @ X67 @ X68))
% 0.42/0.63          | ~ (zip_tseitin_2 @ X68 @ X67 @ X66))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.63  thf('2', plain,
% 0.42/0.63      ((~ (zip_tseitin_2 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.42/0.63        | ((k1_tarski @ sk_A)
% 0.42/0.63            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['0', '1'])).
% 0.42/0.63  thf(zf_stmt_2, axiom,
% 0.42/0.63    (![B:$i,A:$i]:
% 0.42/0.63     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.63       ( zip_tseitin_1 @ B @ A ) ))).
% 0.42/0.63  thf('3', plain,
% 0.42/0.63      (![X64 : $i, X65 : $i]:
% 0.42/0.63         ((zip_tseitin_1 @ X64 @ X65) | ((X64) = (k1_xboole_0)))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.42/0.63  thf('4', plain,
% 0.42/0.63      ((m1_subset_1 @ sk_C @ 
% 0.42/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.42/0.63  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $o).
% 0.42/0.63  thf(zf_stmt_5, axiom,
% 0.42/0.63    (![A:$i,B:$i,C:$i]:
% 0.42/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.63       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.42/0.63         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.63           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.42/0.63             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.42/0.63  thf('5', plain,
% 0.42/0.63      (![X69 : $i, X70 : $i, X71 : $i]:
% 0.42/0.63         (~ (zip_tseitin_1 @ X69 @ X70)
% 0.42/0.63          | (zip_tseitin_2 @ X71 @ X69 @ X70)
% 0.42/0.63          | ~ (m1_subset_1 @ X71 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X70 @ X69))))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.42/0.63  thf('6', plain,
% 0.42/0.63      (((zip_tseitin_2 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.42/0.63        | ~ (zip_tseitin_1 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['4', '5'])).
% 0.42/0.63  thf('7', plain,
% 0.42/0.63      ((((sk_B) = (k1_xboole_0))
% 0.42/0.63        | (zip_tseitin_2 @ sk_C @ sk_B @ (k1_tarski @ sk_A)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['3', '6'])).
% 0.42/0.63  thf('8', plain, (((sk_B) != (k1_xboole_0))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('9', plain, ((zip_tseitin_2 @ sk_C @ sk_B @ (k1_tarski @ sk_A))),
% 0.42/0.63      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.42/0.63  thf('10', plain,
% 0.42/0.63      ((m1_subset_1 @ sk_C @ 
% 0.42/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf(redefinition_k1_relset_1, axiom,
% 0.42/0.63    (![A:$i,B:$i,C:$i]:
% 0.42/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.63       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.42/0.63  thf('11', plain,
% 0.42/0.63      (![X54 : $i, X55 : $i, X56 : $i]:
% 0.42/0.63         (((k1_relset_1 @ X55 @ X56 @ X54) = (k1_relat_1 @ X54))
% 0.42/0.63          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X56))))),
% 0.42/0.63      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.42/0.63  thf('12', plain,
% 0.42/0.63      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.42/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.42/0.63  thf('13', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.42/0.63      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.42/0.63  thf(t69_enumset1, axiom,
% 0.42/0.63    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.42/0.63  thf('14', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.42/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.42/0.63  thf(t70_enumset1, axiom,
% 0.42/0.63    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.42/0.63  thf('15', plain,
% 0.42/0.63      (![X1 : $i, X2 : $i]:
% 0.42/0.63         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.42/0.63      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.42/0.63  thf(t71_enumset1, axiom,
% 0.42/0.63    (![A:$i,B:$i,C:$i]:
% 0.42/0.63     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.42/0.63  thf('16', plain,
% 0.42/0.63      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.42/0.63         ((k2_enumset1 @ X3 @ X3 @ X4 @ X5) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.42/0.63      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.42/0.63  thf(t72_enumset1, axiom,
% 0.42/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.63     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.42/0.63  thf('17', plain,
% 0.42/0.63      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.42/0.63         ((k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9)
% 0.42/0.63           = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 0.42/0.63      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.42/0.63  thf(t73_enumset1, axiom,
% 0.42/0.63    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.42/0.63     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.42/0.63       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.42/0.63  thf('18', plain,
% 0.42/0.63      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.42/0.63         ((k4_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 @ X14)
% 0.42/0.63           = (k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14))),
% 0.42/0.63      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.42/0.63  thf(d4_enumset1, axiom,
% 0.42/0.63    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.42/0.63     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.42/0.63       ( ![H:$i]:
% 0.42/0.63         ( ( r2_hidden @ H @ G ) <=>
% 0.42/0.63           ( ~( ( ( H ) != ( F ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( D ) ) & 
% 0.42/0.63                ( ( H ) != ( C ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( A ) ) ) ) ) ) ))).
% 0.42/0.63  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $i > $o).
% 0.42/0.63  thf(zf_stmt_7, axiom,
% 0.42/0.63    (![H:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.42/0.63     ( ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) <=>
% 0.42/0.63       ( ( ( H ) != ( A ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( C ) ) & 
% 0.42/0.63         ( ( H ) != ( D ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( F ) ) ) ))).
% 0.42/0.63  thf(zf_stmt_8, axiom,
% 0.42/0.63    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.42/0.63     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.42/0.63       ( ![H:$i]:
% 0.42/0.63         ( ( r2_hidden @ H @ G ) <=>
% 0.42/0.63           ( ~( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.42/0.63  thf('19', plain,
% 0.42/0.63      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, 
% 0.42/0.63         X43 : $i]:
% 0.42/0.63         ((zip_tseitin_0 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42)
% 0.42/0.63          | (r2_hidden @ X36 @ X43)
% 0.42/0.63          | ((X43) != (k4_enumset1 @ X42 @ X41 @ X40 @ X39 @ X38 @ X37)))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.42/0.63  thf('20', plain,
% 0.42/0.63      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.42/0.63         ((r2_hidden @ X36 @ (k4_enumset1 @ X42 @ X41 @ X40 @ X39 @ X38 @ X37))
% 0.42/0.63          | (zip_tseitin_0 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42))),
% 0.42/0.63      inference('simplify', [status(thm)], ['19'])).
% 0.42/0.63  thf('21', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.42/0.63         ((r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.42/0.63          | (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4))),
% 0.42/0.63      inference('sup+', [status(thm)], ['18', '20'])).
% 0.42/0.63  thf('22', plain,
% 0.42/0.63      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.42/0.63         (((X29) != (X28))
% 0.42/0.63          | ~ (zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X28))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.42/0.63  thf('23', plain,
% 0.42/0.63      (![X28 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.42/0.63         ~ (zip_tseitin_0 @ X28 @ X30 @ X31 @ X32 @ X33 @ X34 @ X28)),
% 0.42/0.63      inference('simplify', [status(thm)], ['22'])).
% 0.42/0.63  thf('24', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.42/0.63         (r2_hidden @ X0 @ (k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4))),
% 0.42/0.63      inference('sup-', [status(thm)], ['21', '23'])).
% 0.42/0.63  thf('25', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.42/0.63         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.42/0.63      inference('sup+', [status(thm)], ['17', '24'])).
% 0.42/0.63  thf('26', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.63         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.42/0.63      inference('sup+', [status(thm)], ['16', '25'])).
% 0.42/0.63  thf('27', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.42/0.63      inference('sup+', [status(thm)], ['15', '26'])).
% 0.42/0.63  thf('28', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.42/0.63      inference('sup+', [status(thm)], ['14', '27'])).
% 0.42/0.63  thf('29', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.42/0.63      inference('sup+', [status(thm)], ['13', '28'])).
% 0.42/0.63  thf(t117_funct_1, axiom,
% 0.42/0.63    (![A:$i,B:$i]:
% 0.42/0.63     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.42/0.63       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.42/0.63         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.42/0.63  thf('30', plain,
% 0.42/0.63      (![X52 : $i, X53 : $i]:
% 0.42/0.63         (~ (r2_hidden @ X52 @ (k1_relat_1 @ X53))
% 0.42/0.63          | ((k11_relat_1 @ X53 @ X52) = (k1_tarski @ (k1_funct_1 @ X53 @ X52)))
% 0.42/0.63          | ~ (v1_funct_1 @ X53)
% 0.42/0.63          | ~ (v1_relat_1 @ X53))),
% 0.42/0.63      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.42/0.63  thf('31', plain,
% 0.42/0.63      ((~ (v1_relat_1 @ sk_C)
% 0.42/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.42/0.63        | ((k11_relat_1 @ sk_C @ sk_A)
% 0.42/0.63            = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A))))),
% 0.42/0.63      inference('sup-', [status(thm)], ['29', '30'])).
% 0.42/0.63  thf('32', plain,
% 0.42/0.63      ((m1_subset_1 @ sk_C @ 
% 0.42/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf(cc2_relat_1, axiom,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( v1_relat_1 @ A ) =>
% 0.42/0.63       ( ![B:$i]:
% 0.42/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.42/0.63  thf('33', plain,
% 0.42/0.63      (![X46 : $i, X47 : $i]:
% 0.42/0.63         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47))
% 0.42/0.63          | (v1_relat_1 @ X46)
% 0.42/0.63          | ~ (v1_relat_1 @ X47))),
% 0.42/0.63      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.42/0.63  thf('34', plain,
% 0.42/0.63      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.42/0.63        | (v1_relat_1 @ sk_C))),
% 0.42/0.63      inference('sup-', [status(thm)], ['32', '33'])).
% 0.42/0.63  thf(fc6_relat_1, axiom,
% 0.42/0.63    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.42/0.63  thf('35', plain,
% 0.42/0.63      (![X50 : $i, X51 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X50 @ X51))),
% 0.42/0.63      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.42/0.63  thf('36', plain, ((v1_relat_1 @ sk_C)),
% 0.42/0.63      inference('demod', [status(thm)], ['34', '35'])).
% 0.42/0.63  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('38', plain,
% 0.42/0.63      (((k11_relat_1 @ sk_C @ sk_A) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.42/0.63      inference('demod', [status(thm)], ['31', '36', '37'])).
% 0.42/0.63  thf('39', plain,
% 0.42/0.63      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)
% 0.42/0.63         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('40', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.42/0.63      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.42/0.63  thf('41', plain,
% 0.42/0.63      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C)
% 0.42/0.63         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.42/0.63      inference('demod', [status(thm)], ['39', '40'])).
% 0.42/0.63  thf('42', plain,
% 0.42/0.63      ((m1_subset_1 @ sk_C @ 
% 0.42/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('43', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.42/0.63      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.42/0.63  thf('44', plain,
% 0.42/0.63      ((m1_subset_1 @ sk_C @ 
% 0.42/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))),
% 0.42/0.63      inference('demod', [status(thm)], ['42', '43'])).
% 0.42/0.63  thf(t39_relset_1, axiom,
% 0.42/0.63    (![A:$i,B:$i,C:$i]:
% 0.42/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.42/0.63       ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.42/0.63           ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.42/0.63         ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.42/0.63           ( k1_relset_1 @ B @ A @ C ) ) ) ))).
% 0.42/0.63  thf('45', plain,
% 0.42/0.63      (![X61 : $i, X62 : $i, X63 : $i]:
% 0.42/0.63         (((k7_relset_1 @ X61 @ X62 @ X63 @ 
% 0.42/0.63            (k8_relset_1 @ X61 @ X62 @ X63 @ X62))
% 0.42/0.63            = (k2_relset_1 @ X61 @ X62 @ X63))
% 0.42/0.63          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X61 @ X62))))),
% 0.42/0.63      inference('cnf', [status(esa)], [t39_relset_1])).
% 0.42/0.63  thf('46', plain,
% 0.42/0.63      (((k7_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C @ 
% 0.42/0.63         (k8_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C @ sk_B))
% 0.42/0.63         = (k2_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C))),
% 0.42/0.63      inference('sup-', [status(thm)], ['44', '45'])).
% 0.42/0.63  thf('47', plain,
% 0.42/0.63      ((m1_subset_1 @ sk_C @ 
% 0.42/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))),
% 0.42/0.63      inference('demod', [status(thm)], ['42', '43'])).
% 0.42/0.63  thf(t48_funct_2, axiom,
% 0.42/0.63    (![A:$i,B:$i,C:$i]:
% 0.42/0.63     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.42/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.63       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.63         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ))).
% 0.42/0.63  thf('48', plain,
% 0.42/0.63      (![X72 : $i, X73 : $i, X74 : $i]:
% 0.42/0.63         (((X74) = (k1_xboole_0))
% 0.42/0.63          | ~ (v1_funct_1 @ X73)
% 0.42/0.63          | ~ (v1_funct_2 @ X73 @ X72 @ X74)
% 0.42/0.63          | ~ (m1_subset_1 @ X73 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X72 @ X74)))
% 0.42/0.63          | ((k8_relset_1 @ X72 @ X74 @ X73 @ X74) = (X72)))),
% 0.42/0.63      inference('cnf', [status(esa)], [t48_funct_2])).
% 0.42/0.63  thf('49', plain,
% 0.42/0.63      ((((k8_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C @ sk_B)
% 0.42/0.63          = (k1_relat_1 @ sk_C))
% 0.42/0.63        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_B)
% 0.42/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.42/0.63        | ((sk_B) = (k1_xboole_0)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['47', '48'])).
% 0.42/0.63  thf('50', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('51', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.42/0.63      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.42/0.63  thf('52', plain, ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_B)),
% 0.42/0.63      inference('demod', [status(thm)], ['50', '51'])).
% 0.42/0.63  thf('53', plain, ((v1_funct_1 @ sk_C)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('54', plain,
% 0.42/0.63      ((((k8_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C @ sk_B)
% 0.42/0.63          = (k1_relat_1 @ sk_C))
% 0.42/0.63        | ((sk_B) = (k1_xboole_0)))),
% 0.42/0.63      inference('demod', [status(thm)], ['49', '52', '53'])).
% 0.42/0.63  thf('55', plain, (((sk_B) != (k1_xboole_0))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('56', plain,
% 0.42/0.63      (((k8_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C @ sk_B)
% 0.42/0.63         = (k1_relat_1 @ sk_C))),
% 0.42/0.63      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 0.42/0.63  thf('57', plain,
% 0.42/0.63      ((m1_subset_1 @ sk_C @ 
% 0.42/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))),
% 0.42/0.63      inference('demod', [status(thm)], ['42', '43'])).
% 0.42/0.63  thf(redefinition_k7_relset_1, axiom,
% 0.42/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.63       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.42/0.63  thf('58', plain,
% 0.42/0.63      (![X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 0.42/0.63         (~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X59)))
% 0.42/0.63          | ((k7_relset_1 @ X58 @ X59 @ X57 @ X60) = (k9_relat_1 @ X57 @ X60)))),
% 0.42/0.63      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.42/0.63  thf('59', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         ((k7_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C @ X0)
% 0.42/0.63           = (k9_relat_1 @ sk_C @ X0))),
% 0.42/0.63      inference('sup-', [status(thm)], ['57', '58'])).
% 0.42/0.63  thf('60', plain,
% 0.42/0.63      (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.42/0.63         = (k2_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C))),
% 0.42/0.63      inference('demod', [status(thm)], ['46', '56', '59'])).
% 0.42/0.63  thf('61', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.42/0.63      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.42/0.63  thf('62', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.42/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.42/0.63  thf('63', plain, ((v1_relat_1 @ sk_C)),
% 0.42/0.63      inference('demod', [status(thm)], ['34', '35'])).
% 0.42/0.63  thf('64', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.42/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.42/0.63  thf(d16_relat_1, axiom,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( v1_relat_1 @ A ) =>
% 0.42/0.63       ( ![B:$i]:
% 0.42/0.63         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.42/0.63  thf('65', plain,
% 0.42/0.63      (![X48 : $i, X49 : $i]:
% 0.42/0.63         (((k11_relat_1 @ X48 @ X49) = (k9_relat_1 @ X48 @ (k1_tarski @ X49)))
% 0.42/0.63          | ~ (v1_relat_1 @ X48))),
% 0.42/0.63      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.42/0.63  thf('66', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         (((k11_relat_1 @ X1 @ X0) = (k9_relat_1 @ X1 @ (k2_tarski @ X0 @ X0)))
% 0.42/0.63          | ~ (v1_relat_1 @ X1))),
% 0.42/0.63      inference('sup+', [status(thm)], ['64', '65'])).
% 0.42/0.63  thf('67', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         ((k11_relat_1 @ sk_C @ X0)
% 0.42/0.63           = (k9_relat_1 @ sk_C @ (k2_tarski @ X0 @ X0)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['63', '66'])).
% 0.42/0.63  thf('68', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         ((k11_relat_1 @ sk_C @ X0) = (k9_relat_1 @ sk_C @ (k1_tarski @ X0)))),
% 0.42/0.63      inference('sup+', [status(thm)], ['62', '67'])).
% 0.42/0.63  thf('69', plain,
% 0.42/0.63      (((k11_relat_1 @ sk_C @ sk_A) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.42/0.63      inference('sup+', [status(thm)], ['61', '68'])).
% 0.42/0.63  thf('70', plain,
% 0.42/0.63      (((k11_relat_1 @ sk_C @ sk_A)
% 0.42/0.63         = (k2_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C))),
% 0.42/0.63      inference('demod', [status(thm)], ['60', '69'])).
% 0.42/0.63  thf('71', plain,
% 0.42/0.63      (((k11_relat_1 @ sk_C @ sk_A) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.42/0.63      inference('demod', [status(thm)], ['41', '70'])).
% 0.42/0.63  thf('72', plain, ($false),
% 0.42/0.63      inference('simplify_reflect-', [status(thm)], ['38', '71'])).
% 0.42/0.63  
% 0.42/0.63  % SZS output end Refutation
% 0.42/0.63  
% 0.47/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
