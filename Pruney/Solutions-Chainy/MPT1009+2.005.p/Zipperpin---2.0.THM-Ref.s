%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.L3RAnrMqDF

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:49 EST 2020

% Result     : Theorem 4.23s
% Output     : Refutation 4.23s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 856 expanded)
%              Number of leaves         :   48 ( 278 expanded)
%              Depth                    :   25
%              Number of atoms          : 1369 (9252 expanded)
%              Number of equality atoms :   83 ( 474 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t64_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_2 @ sk_C_2 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_2 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X89: $i,X90: $i,X91: $i,X92: $i] :
      ( ~ ( m1_subset_1 @ X89 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X90 @ X91 ) ) )
      | ( ( k7_relset_1 @ X90 @ X91 @ X89 @ X92 )
        = ( k9_relat_1 @ X89 @ X92 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_2 @ sk_C_2 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_2 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X82: $i,X83: $i,X84: $i] :
      ( ( v5_relat_1 @ X82 @ X84 )
      | ~ ( m1_subset_1 @ X82 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X83 @ X84 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('7',plain,(
    v5_relat_1 @ sk_D_2 @ sk_B ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X62: $i,X63: $i] :
      ( ~ ( v5_relat_1 @ X62 @ X63 )
      | ( r1_tarski @ ( k2_relat_1 @ X62 ) @ X63 )
      | ~ ( v1_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X79: $i,X80: $i,X81: $i] :
      ( ( v1_relat_1 @ X79 )
      | ~ ( m1_subset_1 @ X79 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X80 @ X81 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ sk_B ),
    inference(demod,[status(thm)],['9','12'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X94: $i,X95: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X94 ) @ X95 )
      | ( m1_subset_1 @ X94 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X94 ) @ X95 ) ) )
      | ~ ( v1_funct_1 @ X94 )
      | ~ ( v1_relat_1 @ X94 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_2 ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('17',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_2 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X54: $i,X55: $i] :
      ( ( r1_tarski @ X54 @ X55 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    r1_tarski @ sk_D_2 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_2 ) @ sk_B ) @ sk_D_2 )
    | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_2 ) @ sk_B )
      = sk_D_2 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X93: $i] :
      ( ( m1_subset_1 @ X93 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X93 ) @ ( k2_relat_1 @ X93 ) ) ) )
      | ~ ( v1_funct_1 @ X93 )
      | ~ ( v1_relat_1 @ X93 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('24',plain,(
    ! [X89: $i,X90: $i,X91: $i,X92: $i] :
      ( ~ ( m1_subset_1 @ X89 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X90 @ X91 ) ) )
      | ( ( k7_relset_1 @ X90 @ X91 @ X89 @ X92 )
        = ( k9_relat_1 @ X89 @ X92 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X93: $i] :
      ( ( m1_subset_1 @ X93 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X93 ) @ ( k2_relat_1 @ X93 ) ) ) )
      | ~ ( v1_funct_1 @ X93 )
      | ~ ( v1_relat_1 @ X93 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('27',plain,(
    ! [X85: $i,X86: $i,X87: $i,X88: $i] :
      ( ~ ( m1_subset_1 @ X85 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X86 @ X87 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X86 @ X87 @ X85 @ X88 ) @ ( k1_zfmisc_1 @ X87 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k9_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( m1_subset_1 @ ( k9_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X54: $i,X55: $i] :
      ( ( r1_tarski @ X54 @ X55 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('33',plain,(
    ! [X49: $i,X50: $i] :
      ( ( ( k2_zfmisc_1 @ X49 @ X50 )
        = k1_xboole_0 )
      | ( X50 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('34',plain,(
    ! [X49: $i] :
      ( ( k2_zfmisc_1 @ X49 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('35',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( X9 = X10 )
      | ( X9 = X11 )
      | ( X9 = X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('37',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X82: $i,X83: $i,X84: $i] :
      ( ( v4_relat_1 @ X82 @ X83 )
      | ~ ( m1_subset_1 @ X82 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X83 @ X84 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('39',plain,(
    v4_relat_1 @ sk_D_2 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('40',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( v4_relat_1 @ X60 @ X61 )
      | ( r1_tarski @ ( k1_relat_1 @ X60 ) @ X61 )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_2 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('43',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_2 ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_D_2 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_D_2 ) ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','45'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('47',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('48',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('49',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('50',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_D_2 ) @ X0 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_D_2 ) ) @ sk_A @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ ( k1_relat_1 @ sk_D_2 ) )
        = sk_A )
      | ( ( sk_C @ X0 @ ( k1_relat_1 @ sk_D_2 ) )
        = sk_A )
      | ( ( sk_C @ X0 @ ( k1_relat_1 @ sk_D_2 ) )
        = sk_A )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_D_2 ) @ X0 )
      | ( ( sk_C @ X0 @ ( k1_relat_1 @ sk_D_2 ) )
        = sk_A ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_2 ) )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D_2 ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D_2 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_D_2 ) @ X0 )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_2 ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('60',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X54: $i,X56: $i] :
      ( ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ X56 ) )
      | ~ ( r1_tarski @ X54 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('62',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X82: $i,X83: $i,X84: $i] :
      ( ( v4_relat_1 @ X82 @ X83 )
      | ~ ( m1_subset_1 @ X82 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X83 @ X84 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( v4_relat_1 @ X60 @ X61 )
      | ( r1_tarski @ ( k1_relat_1 @ X60 ) @ X61 )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('67',plain,(
    ! [X64: $i,X65: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_2 ) )
      | ( ( k1_relat_1 @ sk_D_2 )
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_2 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['58','70'])).

thf('72',plain,
    ( ( ( k1_relat_1 @ sk_D_2 )
      = ( k1_relat_1 @ k1_xboole_0 ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['34','71'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('73',plain,(
    ! [X51: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('74',plain,(
    ! [X82: $i,X83: $i,X84: $i] :
      ( ( v4_relat_1 @ X82 @ X83 )
      | ~ ( m1_subset_1 @ X82 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X83 @ X84 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('75',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( v4_relat_1 @ X60 @ X61 )
      | ( r1_tarski @ ( k1_relat_1 @ X60 ) @ X61 )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X49: $i,X50: $i] :
      ( ( ( k2_zfmisc_1 @ X49 @ X50 )
        = k1_xboole_0 )
      | ( X49 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('79',plain,(
    ! [X50: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X50 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X64: $i,X65: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('81',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['77','81'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('83',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('84',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,
    ( ( ( k1_relat_1 @ sk_D_2 )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['72','86'])).

thf('88',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( X9 = X10 )
      | ( X9 = X11 )
      | ( X9 = X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('89',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','51'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,
    ( ( ( k1_relat_1 @ sk_D_2 )
      = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['87','96'])).

thf('98',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_2 ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('99',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('100',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_D_2 ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( k1_relat_1 @ sk_D_2 )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('102',plain,(
    ! [X75: $i,X76: $i] :
      ( ( ( k1_relat_1 @ X76 )
       != ( k1_tarski @ X75 ) )
      | ( ( k2_relat_1 @ X76 )
        = ( k1_tarski @ ( k1_funct_1 @ X76 @ X75 ) ) )
      | ~ ( v1_funct_1 @ X76 )
      | ~ ( v1_relat_1 @ X76 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D_2 ) )
      | ( ( k1_relat_1 @ sk_D_2 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( k2_relat_1 @ sk_D_2 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_2 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 )
    | ( ( k1_relat_1 @ sk_D_2 )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['103'])).

thf('105',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('107',plain,
    ( ( ( k2_relat_1 @ sk_D_2 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_2 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D_2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_2 @ sk_C_2 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_2 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('109',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_2 @ sk_C_2 ) @ ( k2_relat_1 @ sk_D_2 ) )
    | ( ( k1_relat_1 @ sk_D_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ( ( k1_relat_1 @ sk_D_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','109'])).

thf('111',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('112',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( k1_relat_1 @ sk_D_2 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,(
    ! [X50: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X50 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('115',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('116',plain,
    ( ( k1_relat_1 @ sk_D_2 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('117',plain,(
    ! [X50: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X50 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('118',plain,(
    k1_xboole_0 = sk_D_2 ),
    inference(demod,[status(thm)],['22','113','114','115','116','117'])).

thf('119',plain,(
    ! [X51: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('120',plain,(
    ! [X85: $i,X86: $i,X87: $i,X88: $i] :
      ( ~ ( m1_subset_1 @ X85 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X86 @ X87 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X86 @ X87 @ X85 @ X88 ) @ ( k1_zfmisc_1 @ X87 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X51: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('123',plain,(
    ! [X89: $i,X90: $i,X91: $i,X92: $i] :
      ( ~ ( m1_subset_1 @ X89 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X90 @ X91 ) ) )
      | ( ( k7_relset_1 @ X90 @ X91 @ X89 @ X92 )
        = ( k9_relat_1 @ X89 @ X92 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k9_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X2: $i] :
      ( m1_subset_1 @ ( k9_relat_1 @ k1_xboole_0 @ X2 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['121','124'])).

thf('126',plain,(
    ! [X54: $i,X55: $i] :
      ( ( r1_tarski @ X54 @ X55 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    k1_xboole_0 = sk_D_2 ),
    inference(demod,[status(thm)],['22','113','114','115','116','117'])).

thf('131',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('132',plain,(
    $false ),
    inference(demod,[status(thm)],['4','118','129','130','131'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.L3RAnrMqDF
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:11:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.23/4.40  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.23/4.40  % Solved by: fo/fo7.sh
% 4.23/4.40  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.23/4.40  % done 5878 iterations in 3.953s
% 4.23/4.40  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.23/4.40  % SZS output start Refutation
% 4.23/4.40  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.23/4.40  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 4.23/4.40  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 4.23/4.40  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.23/4.40  thf(sk_D_2_type, type, sk_D_2: $i).
% 4.23/4.40  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.23/4.40  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.23/4.40  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 4.23/4.40  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.23/4.40  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.23/4.40  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.23/4.40  thf(sk_A_type, type, sk_A: $i).
% 4.23/4.40  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.23/4.40  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.23/4.40  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.23/4.40  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.23/4.40  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 4.23/4.40  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.23/4.40  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 4.23/4.40  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 4.23/4.40  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 4.23/4.40  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.23/4.40  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 4.23/4.40  thf(sk_C_2_type, type, sk_C_2: $i).
% 4.23/4.40  thf(sk_B_type, type, sk_B: $i).
% 4.23/4.40  thf(t64_funct_2, conjecture,
% 4.23/4.40    (![A:$i,B:$i,C:$i,D:$i]:
% 4.23/4.40     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 4.23/4.40         ( m1_subset_1 @
% 4.23/4.40           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 4.23/4.40       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 4.23/4.40         ( r1_tarski @
% 4.23/4.40           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 4.23/4.40           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 4.23/4.40  thf(zf_stmt_0, negated_conjecture,
% 4.23/4.40    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 4.23/4.40        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 4.23/4.40            ( m1_subset_1 @
% 4.23/4.40              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 4.23/4.40          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 4.23/4.40            ( r1_tarski @
% 4.23/4.40              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 4.23/4.40              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 4.23/4.40    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 4.23/4.40  thf('0', plain,
% 4.23/4.40      (~ (r1_tarski @ 
% 4.23/4.40          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_2 @ sk_C_2) @ 
% 4.23/4.40          (k1_tarski @ (k1_funct_1 @ sk_D_2 @ sk_A)))),
% 4.23/4.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.23/4.40  thf('1', plain,
% 4.23/4.40      ((m1_subset_1 @ sk_D_2 @ 
% 4.23/4.40        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 4.23/4.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.23/4.40  thf(redefinition_k7_relset_1, axiom,
% 4.23/4.40    (![A:$i,B:$i,C:$i,D:$i]:
% 4.23/4.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.23/4.40       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 4.23/4.40  thf('2', plain,
% 4.23/4.40      (![X89 : $i, X90 : $i, X91 : $i, X92 : $i]:
% 4.23/4.40         (~ (m1_subset_1 @ X89 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X90 @ X91)))
% 4.23/4.40          | ((k7_relset_1 @ X90 @ X91 @ X89 @ X92) = (k9_relat_1 @ X89 @ X92)))),
% 4.23/4.40      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 4.23/4.40  thf('3', plain,
% 4.23/4.40      (![X0 : $i]:
% 4.23/4.40         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_2 @ X0)
% 4.23/4.40           = (k9_relat_1 @ sk_D_2 @ X0))),
% 4.23/4.40      inference('sup-', [status(thm)], ['1', '2'])).
% 4.23/4.40  thf('4', plain,
% 4.23/4.40      (~ (r1_tarski @ (k9_relat_1 @ sk_D_2 @ sk_C_2) @ 
% 4.23/4.40          (k1_tarski @ (k1_funct_1 @ sk_D_2 @ sk_A)))),
% 4.23/4.40      inference('demod', [status(thm)], ['0', '3'])).
% 4.23/4.40  thf('5', plain,
% 4.23/4.40      ((m1_subset_1 @ sk_D_2 @ 
% 4.23/4.40        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 4.23/4.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.23/4.40  thf(cc2_relset_1, axiom,
% 4.23/4.40    (![A:$i,B:$i,C:$i]:
% 4.23/4.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.23/4.40       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 4.23/4.40  thf('6', plain,
% 4.23/4.40      (![X82 : $i, X83 : $i, X84 : $i]:
% 4.23/4.40         ((v5_relat_1 @ X82 @ X84)
% 4.23/4.40          | ~ (m1_subset_1 @ X82 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X83 @ X84))))),
% 4.23/4.40      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.23/4.40  thf('7', plain, ((v5_relat_1 @ sk_D_2 @ sk_B)),
% 4.23/4.40      inference('sup-', [status(thm)], ['5', '6'])).
% 4.23/4.40  thf(d19_relat_1, axiom,
% 4.23/4.40    (![A:$i,B:$i]:
% 4.23/4.40     ( ( v1_relat_1 @ B ) =>
% 4.23/4.40       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 4.23/4.40  thf('8', plain,
% 4.23/4.40      (![X62 : $i, X63 : $i]:
% 4.23/4.40         (~ (v5_relat_1 @ X62 @ X63)
% 4.23/4.40          | (r1_tarski @ (k2_relat_1 @ X62) @ X63)
% 4.23/4.40          | ~ (v1_relat_1 @ X62))),
% 4.23/4.40      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.23/4.40  thf('9', plain,
% 4.23/4.40      ((~ (v1_relat_1 @ sk_D_2) | (r1_tarski @ (k2_relat_1 @ sk_D_2) @ sk_B))),
% 4.23/4.40      inference('sup-', [status(thm)], ['7', '8'])).
% 4.23/4.40  thf('10', plain,
% 4.23/4.40      ((m1_subset_1 @ sk_D_2 @ 
% 4.23/4.40        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 4.23/4.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.23/4.40  thf(cc1_relset_1, axiom,
% 4.23/4.40    (![A:$i,B:$i,C:$i]:
% 4.23/4.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.23/4.40       ( v1_relat_1 @ C ) ))).
% 4.23/4.40  thf('11', plain,
% 4.23/4.40      (![X79 : $i, X80 : $i, X81 : $i]:
% 4.23/4.40         ((v1_relat_1 @ X79)
% 4.23/4.40          | ~ (m1_subset_1 @ X79 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X80 @ X81))))),
% 4.23/4.40      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.23/4.40  thf('12', plain, ((v1_relat_1 @ sk_D_2)),
% 4.23/4.40      inference('sup-', [status(thm)], ['10', '11'])).
% 4.23/4.40  thf('13', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_2) @ sk_B)),
% 4.23/4.40      inference('demod', [status(thm)], ['9', '12'])).
% 4.23/4.40  thf(t4_funct_2, axiom,
% 4.23/4.40    (![A:$i,B:$i]:
% 4.23/4.40     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.23/4.40       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 4.23/4.40         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 4.23/4.40           ( m1_subset_1 @
% 4.23/4.40             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 4.23/4.40  thf('14', plain,
% 4.23/4.40      (![X94 : $i, X95 : $i]:
% 4.23/4.40         (~ (r1_tarski @ (k2_relat_1 @ X94) @ X95)
% 4.23/4.40          | (m1_subset_1 @ X94 @ 
% 4.23/4.40             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X94) @ X95)))
% 4.23/4.40          | ~ (v1_funct_1 @ X94)
% 4.23/4.40          | ~ (v1_relat_1 @ X94))),
% 4.23/4.40      inference('cnf', [status(esa)], [t4_funct_2])).
% 4.23/4.40  thf('15', plain,
% 4.23/4.40      ((~ (v1_relat_1 @ sk_D_2)
% 4.23/4.40        | ~ (v1_funct_1 @ sk_D_2)
% 4.23/4.40        | (m1_subset_1 @ sk_D_2 @ 
% 4.23/4.40           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_2) @ sk_B))))),
% 4.23/4.40      inference('sup-', [status(thm)], ['13', '14'])).
% 4.23/4.40  thf('16', plain, ((v1_relat_1 @ sk_D_2)),
% 4.23/4.40      inference('sup-', [status(thm)], ['10', '11'])).
% 4.23/4.40  thf('17', plain, ((v1_funct_1 @ sk_D_2)),
% 4.23/4.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.23/4.40  thf('18', plain,
% 4.23/4.40      ((m1_subset_1 @ sk_D_2 @ 
% 4.23/4.40        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_2) @ sk_B)))),
% 4.23/4.40      inference('demod', [status(thm)], ['15', '16', '17'])).
% 4.23/4.40  thf(t3_subset, axiom,
% 4.23/4.40    (![A:$i,B:$i]:
% 4.23/4.40     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.23/4.40  thf('19', plain,
% 4.23/4.40      (![X54 : $i, X55 : $i]:
% 4.23/4.40         ((r1_tarski @ X54 @ X55) | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ X55)))),
% 4.23/4.40      inference('cnf', [status(esa)], [t3_subset])).
% 4.23/4.40  thf('20', plain,
% 4.23/4.40      ((r1_tarski @ sk_D_2 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_2) @ sk_B))),
% 4.23/4.40      inference('sup-', [status(thm)], ['18', '19'])).
% 4.23/4.40  thf(d10_xboole_0, axiom,
% 4.23/4.40    (![A:$i,B:$i]:
% 4.23/4.40     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.23/4.40  thf('21', plain,
% 4.23/4.40      (![X4 : $i, X6 : $i]:
% 4.23/4.40         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 4.23/4.40      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.23/4.40  thf('22', plain,
% 4.23/4.40      ((~ (r1_tarski @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_2) @ sk_B) @ sk_D_2)
% 4.23/4.40        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_D_2) @ sk_B) = (sk_D_2)))),
% 4.23/4.40      inference('sup-', [status(thm)], ['20', '21'])).
% 4.23/4.40  thf(t3_funct_2, axiom,
% 4.23/4.40    (![A:$i]:
% 4.23/4.40     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.23/4.40       ( ( v1_funct_1 @ A ) & 
% 4.23/4.40         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 4.23/4.40         ( m1_subset_1 @
% 4.23/4.40           A @ 
% 4.23/4.40           ( k1_zfmisc_1 @
% 4.23/4.40             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 4.23/4.40  thf('23', plain,
% 4.23/4.40      (![X93 : $i]:
% 4.23/4.40         ((m1_subset_1 @ X93 @ 
% 4.23/4.40           (k1_zfmisc_1 @ 
% 4.23/4.40            (k2_zfmisc_1 @ (k1_relat_1 @ X93) @ (k2_relat_1 @ X93))))
% 4.23/4.40          | ~ (v1_funct_1 @ X93)
% 4.23/4.40          | ~ (v1_relat_1 @ X93))),
% 4.23/4.40      inference('cnf', [status(esa)], [t3_funct_2])).
% 4.23/4.40  thf('24', plain,
% 4.23/4.40      (![X89 : $i, X90 : $i, X91 : $i, X92 : $i]:
% 4.23/4.40         (~ (m1_subset_1 @ X89 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X90 @ X91)))
% 4.23/4.40          | ((k7_relset_1 @ X90 @ X91 @ X89 @ X92) = (k9_relat_1 @ X89 @ X92)))),
% 4.23/4.40      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 4.23/4.40  thf('25', plain,
% 4.23/4.40      (![X0 : $i, X1 : $i]:
% 4.23/4.40         (~ (v1_relat_1 @ X0)
% 4.23/4.40          | ~ (v1_funct_1 @ X0)
% 4.23/4.40          | ((k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1)
% 4.23/4.40              = (k9_relat_1 @ X0 @ X1)))),
% 4.23/4.40      inference('sup-', [status(thm)], ['23', '24'])).
% 4.23/4.40  thf('26', plain,
% 4.23/4.40      (![X93 : $i]:
% 4.23/4.40         ((m1_subset_1 @ X93 @ 
% 4.23/4.40           (k1_zfmisc_1 @ 
% 4.23/4.40            (k2_zfmisc_1 @ (k1_relat_1 @ X93) @ (k2_relat_1 @ X93))))
% 4.23/4.40          | ~ (v1_funct_1 @ X93)
% 4.23/4.40          | ~ (v1_relat_1 @ X93))),
% 4.23/4.40      inference('cnf', [status(esa)], [t3_funct_2])).
% 4.23/4.40  thf(dt_k7_relset_1, axiom,
% 4.23/4.40    (![A:$i,B:$i,C:$i,D:$i]:
% 4.23/4.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.23/4.40       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 4.23/4.40  thf('27', plain,
% 4.23/4.40      (![X85 : $i, X86 : $i, X87 : $i, X88 : $i]:
% 4.23/4.40         (~ (m1_subset_1 @ X85 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X86 @ X87)))
% 4.23/4.40          | (m1_subset_1 @ (k7_relset_1 @ X86 @ X87 @ X85 @ X88) @ 
% 4.23/4.40             (k1_zfmisc_1 @ X87)))),
% 4.23/4.40      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 4.23/4.40  thf('28', plain,
% 4.23/4.40      (![X0 : $i, X1 : $i]:
% 4.23/4.40         (~ (v1_relat_1 @ X0)
% 4.23/4.40          | ~ (v1_funct_1 @ X0)
% 4.23/4.40          | (m1_subset_1 @ 
% 4.23/4.40             (k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1) @ 
% 4.23/4.40             (k1_zfmisc_1 @ (k2_relat_1 @ X0))))),
% 4.23/4.40      inference('sup-', [status(thm)], ['26', '27'])).
% 4.23/4.40  thf('29', plain,
% 4.23/4.40      (![X0 : $i, X1 : $i]:
% 4.23/4.40         ((m1_subset_1 @ (k9_relat_1 @ X1 @ X0) @ 
% 4.23/4.40           (k1_zfmisc_1 @ (k2_relat_1 @ X1)))
% 4.23/4.40          | ~ (v1_funct_1 @ X1)
% 4.23/4.40          | ~ (v1_relat_1 @ X1)
% 4.23/4.40          | ~ (v1_funct_1 @ X1)
% 4.23/4.40          | ~ (v1_relat_1 @ X1))),
% 4.23/4.40      inference('sup+', [status(thm)], ['25', '28'])).
% 4.23/4.40  thf('30', plain,
% 4.23/4.40      (![X0 : $i, X1 : $i]:
% 4.23/4.40         (~ (v1_relat_1 @ X1)
% 4.23/4.40          | ~ (v1_funct_1 @ X1)
% 4.23/4.40          | (m1_subset_1 @ (k9_relat_1 @ X1 @ X0) @ 
% 4.23/4.40             (k1_zfmisc_1 @ (k2_relat_1 @ X1))))),
% 4.23/4.40      inference('simplify', [status(thm)], ['29'])).
% 4.23/4.40  thf('31', plain,
% 4.23/4.40      (![X54 : $i, X55 : $i]:
% 4.23/4.40         ((r1_tarski @ X54 @ X55) | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ X55)))),
% 4.23/4.40      inference('cnf', [status(esa)], [t3_subset])).
% 4.23/4.40  thf('32', plain,
% 4.23/4.40      (![X0 : $i, X1 : $i]:
% 4.23/4.40         (~ (v1_funct_1 @ X0)
% 4.23/4.40          | ~ (v1_relat_1 @ X0)
% 4.23/4.40          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ (k2_relat_1 @ X0)))),
% 4.23/4.40      inference('sup-', [status(thm)], ['30', '31'])).
% 4.23/4.40  thf(t113_zfmisc_1, axiom,
% 4.23/4.40    (![A:$i,B:$i]:
% 4.23/4.40     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 4.23/4.40       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 4.23/4.40  thf('33', plain,
% 4.23/4.40      (![X49 : $i, X50 : $i]:
% 4.23/4.40         (((k2_zfmisc_1 @ X49 @ X50) = (k1_xboole_0))
% 4.23/4.40          | ((X50) != (k1_xboole_0)))),
% 4.23/4.40      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.23/4.40  thf('34', plain,
% 4.23/4.40      (![X49 : $i]: ((k2_zfmisc_1 @ X49 @ k1_xboole_0) = (k1_xboole_0))),
% 4.23/4.40      inference('simplify', [status(thm)], ['33'])).
% 4.23/4.40  thf(d1_enumset1, axiom,
% 4.23/4.40    (![A:$i,B:$i,C:$i,D:$i]:
% 4.23/4.40     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 4.23/4.40       ( ![E:$i]:
% 4.23/4.40         ( ( r2_hidden @ E @ D ) <=>
% 4.23/4.40           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 4.23/4.40  thf(zf_stmt_1, axiom,
% 4.23/4.40    (![E:$i,C:$i,B:$i,A:$i]:
% 4.23/4.40     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 4.23/4.40       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 4.23/4.40  thf('35', plain,
% 4.23/4.40      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 4.23/4.40         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 4.23/4.40          | ((X9) = (X10))
% 4.23/4.40          | ((X9) = (X11))
% 4.23/4.40          | ((X9) = (X12)))),
% 4.23/4.40      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.23/4.40  thf(d3_tarski, axiom,
% 4.23/4.40    (![A:$i,B:$i]:
% 4.23/4.40     ( ( r1_tarski @ A @ B ) <=>
% 4.23/4.40       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 4.23/4.40  thf('36', plain,
% 4.23/4.40      (![X1 : $i, X3 : $i]:
% 4.23/4.40         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 4.23/4.40      inference('cnf', [status(esa)], [d3_tarski])).
% 4.23/4.40  thf('37', plain,
% 4.23/4.40      ((m1_subset_1 @ sk_D_2 @ 
% 4.23/4.40        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 4.23/4.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.23/4.40  thf('38', plain,
% 4.23/4.40      (![X82 : $i, X83 : $i, X84 : $i]:
% 4.23/4.40         ((v4_relat_1 @ X82 @ X83)
% 4.23/4.40          | ~ (m1_subset_1 @ X82 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X83 @ X84))))),
% 4.23/4.40      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.23/4.40  thf('39', plain, ((v4_relat_1 @ sk_D_2 @ (k1_tarski @ sk_A))),
% 4.23/4.40      inference('sup-', [status(thm)], ['37', '38'])).
% 4.23/4.40  thf(d18_relat_1, axiom,
% 4.23/4.40    (![A:$i,B:$i]:
% 4.23/4.40     ( ( v1_relat_1 @ B ) =>
% 4.23/4.40       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 4.23/4.40  thf('40', plain,
% 4.23/4.40      (![X60 : $i, X61 : $i]:
% 4.23/4.40         (~ (v4_relat_1 @ X60 @ X61)
% 4.23/4.40          | (r1_tarski @ (k1_relat_1 @ X60) @ X61)
% 4.23/4.40          | ~ (v1_relat_1 @ X60))),
% 4.23/4.40      inference('cnf', [status(esa)], [d18_relat_1])).
% 4.23/4.40  thf('41', plain,
% 4.23/4.40      ((~ (v1_relat_1 @ sk_D_2)
% 4.23/4.40        | (r1_tarski @ (k1_relat_1 @ sk_D_2) @ (k1_tarski @ sk_A)))),
% 4.23/4.40      inference('sup-', [status(thm)], ['39', '40'])).
% 4.23/4.40  thf('42', plain, ((v1_relat_1 @ sk_D_2)),
% 4.23/4.40      inference('sup-', [status(thm)], ['10', '11'])).
% 4.23/4.40  thf('43', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_2) @ (k1_tarski @ sk_A))),
% 4.23/4.40      inference('demod', [status(thm)], ['41', '42'])).
% 4.23/4.40  thf('44', plain,
% 4.23/4.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.23/4.40         (~ (r2_hidden @ X0 @ X1)
% 4.23/4.40          | (r2_hidden @ X0 @ X2)
% 4.23/4.40          | ~ (r1_tarski @ X1 @ X2))),
% 4.23/4.40      inference('cnf', [status(esa)], [d3_tarski])).
% 4.23/4.40  thf('45', plain,
% 4.23/4.40      (![X0 : $i]:
% 4.23/4.40         ((r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 4.23/4.40          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_2)))),
% 4.23/4.40      inference('sup-', [status(thm)], ['43', '44'])).
% 4.23/4.40  thf('46', plain,
% 4.23/4.40      (![X0 : $i]:
% 4.23/4.40         ((r1_tarski @ (k1_relat_1 @ sk_D_2) @ X0)
% 4.23/4.40          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ sk_D_2)) @ 
% 4.23/4.40             (k1_tarski @ sk_A)))),
% 4.23/4.40      inference('sup-', [status(thm)], ['36', '45'])).
% 4.23/4.40  thf(t69_enumset1, axiom,
% 4.23/4.40    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 4.23/4.40  thf('47', plain,
% 4.23/4.40      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 4.23/4.40      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.23/4.40  thf(t70_enumset1, axiom,
% 4.23/4.40    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 4.23/4.40  thf('48', plain,
% 4.23/4.40      (![X21 : $i, X22 : $i]:
% 4.23/4.40         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 4.23/4.40      inference('cnf', [status(esa)], [t70_enumset1])).
% 4.23/4.40  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 4.23/4.40  thf(zf_stmt_3, axiom,
% 4.23/4.40    (![A:$i,B:$i,C:$i,D:$i]:
% 4.23/4.40     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 4.23/4.40       ( ![E:$i]:
% 4.23/4.40         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 4.23/4.40  thf('49', plain,
% 4.23/4.40      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 4.23/4.40         (~ (r2_hidden @ X18 @ X17)
% 4.23/4.40          | ~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 4.23/4.40          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 4.23/4.40      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.23/4.40  thf('50', plain,
% 4.23/4.40      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 4.23/4.40         (~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 4.23/4.40          | ~ (r2_hidden @ X18 @ (k1_enumset1 @ X16 @ X15 @ X14)))),
% 4.23/4.40      inference('simplify', [status(thm)], ['49'])).
% 4.23/4.40  thf('51', plain,
% 4.23/4.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.23/4.40         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 4.23/4.40          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 4.23/4.40      inference('sup-', [status(thm)], ['48', '50'])).
% 4.23/4.40  thf('52', plain,
% 4.23/4.40      (![X0 : $i, X1 : $i]:
% 4.23/4.40         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 4.23/4.40          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 4.23/4.40      inference('sup-', [status(thm)], ['47', '51'])).
% 4.23/4.40  thf('53', plain,
% 4.23/4.40      (![X0 : $i]:
% 4.23/4.40         ((r1_tarski @ (k1_relat_1 @ sk_D_2) @ X0)
% 4.23/4.40          | ~ (zip_tseitin_0 @ (sk_C @ X0 @ (k1_relat_1 @ sk_D_2)) @ sk_A @ 
% 4.23/4.40               sk_A @ sk_A))),
% 4.23/4.40      inference('sup-', [status(thm)], ['46', '52'])).
% 4.23/4.40  thf('54', plain,
% 4.23/4.40      (![X0 : $i]:
% 4.23/4.40         (((sk_C @ X0 @ (k1_relat_1 @ sk_D_2)) = (sk_A))
% 4.23/4.40          | ((sk_C @ X0 @ (k1_relat_1 @ sk_D_2)) = (sk_A))
% 4.23/4.40          | ((sk_C @ X0 @ (k1_relat_1 @ sk_D_2)) = (sk_A))
% 4.23/4.40          | (r1_tarski @ (k1_relat_1 @ sk_D_2) @ X0))),
% 4.23/4.40      inference('sup-', [status(thm)], ['35', '53'])).
% 4.23/4.40  thf('55', plain,
% 4.23/4.40      (![X0 : $i]:
% 4.23/4.40         ((r1_tarski @ (k1_relat_1 @ sk_D_2) @ X0)
% 4.23/4.40          | ((sk_C @ X0 @ (k1_relat_1 @ sk_D_2)) = (sk_A)))),
% 4.23/4.40      inference('simplify', [status(thm)], ['54'])).
% 4.23/4.40  thf('56', plain,
% 4.23/4.40      (![X1 : $i, X3 : $i]:
% 4.23/4.40         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 4.23/4.40      inference('cnf', [status(esa)], [d3_tarski])).
% 4.23/4.40  thf('57', plain,
% 4.23/4.40      (![X0 : $i]:
% 4.23/4.40         ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_2))
% 4.23/4.40          | (r1_tarski @ (k1_relat_1 @ sk_D_2) @ X0)
% 4.23/4.40          | (r1_tarski @ (k1_relat_1 @ sk_D_2) @ X0))),
% 4.23/4.40      inference('sup+', [status(thm)], ['55', '56'])).
% 4.23/4.40  thf('58', plain,
% 4.23/4.40      (![X0 : $i]:
% 4.23/4.40         ((r1_tarski @ (k1_relat_1 @ sk_D_2) @ X0)
% 4.23/4.40          | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_2)))),
% 4.23/4.40      inference('simplify', [status(thm)], ['57'])).
% 4.23/4.40  thf('59', plain,
% 4.23/4.40      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 4.23/4.40      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.23/4.40  thf('60', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 4.23/4.40      inference('simplify', [status(thm)], ['59'])).
% 4.23/4.40  thf('61', plain,
% 4.23/4.40      (![X54 : $i, X56 : $i]:
% 4.23/4.40         ((m1_subset_1 @ X54 @ (k1_zfmisc_1 @ X56)) | ~ (r1_tarski @ X54 @ X56))),
% 4.23/4.40      inference('cnf', [status(esa)], [t3_subset])).
% 4.23/4.40  thf('62', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 4.23/4.40      inference('sup-', [status(thm)], ['60', '61'])).
% 4.23/4.40  thf('63', plain,
% 4.23/4.40      (![X82 : $i, X83 : $i, X84 : $i]:
% 4.23/4.40         ((v4_relat_1 @ X82 @ X83)
% 4.23/4.40          | ~ (m1_subset_1 @ X82 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X83 @ X84))))),
% 4.23/4.40      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.23/4.40  thf('64', plain,
% 4.23/4.40      (![X0 : $i, X1 : $i]: (v4_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X1)),
% 4.23/4.40      inference('sup-', [status(thm)], ['62', '63'])).
% 4.23/4.40  thf('65', plain,
% 4.23/4.40      (![X60 : $i, X61 : $i]:
% 4.23/4.40         (~ (v4_relat_1 @ X60 @ X61)
% 4.23/4.40          | (r1_tarski @ (k1_relat_1 @ X60) @ X61)
% 4.23/4.40          | ~ (v1_relat_1 @ X60))),
% 4.23/4.40      inference('cnf', [status(esa)], [d18_relat_1])).
% 4.23/4.40  thf('66', plain,
% 4.23/4.40      (![X0 : $i, X1 : $i]:
% 4.23/4.40         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))
% 4.23/4.40          | (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0))),
% 4.23/4.40      inference('sup-', [status(thm)], ['64', '65'])).
% 4.23/4.40  thf(fc6_relat_1, axiom,
% 4.23/4.40    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 4.23/4.40  thf('67', plain,
% 4.23/4.40      (![X64 : $i, X65 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X64 @ X65))),
% 4.23/4.40      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.23/4.40  thf('68', plain,
% 4.23/4.40      (![X0 : $i, X1 : $i]:
% 4.23/4.40         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0)),
% 4.23/4.40      inference('demod', [status(thm)], ['66', '67'])).
% 4.23/4.40  thf('69', plain,
% 4.23/4.40      (![X4 : $i, X6 : $i]:
% 4.23/4.40         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 4.23/4.40      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.23/4.40  thf('70', plain,
% 4.23/4.40      (![X0 : $i, X1 : $i]:
% 4.23/4.40         (~ (r1_tarski @ X0 @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 4.23/4.40          | ((X0) = (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 4.23/4.40      inference('sup-', [status(thm)], ['68', '69'])).
% 4.23/4.40  thf('71', plain,
% 4.23/4.40      (![X0 : $i]:
% 4.23/4.40         ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_2))
% 4.23/4.40          | ((k1_relat_1 @ sk_D_2)
% 4.23/4.40              = (k1_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_2) @ X0))))),
% 4.23/4.40      inference('sup-', [status(thm)], ['58', '70'])).
% 4.23/4.40  thf('72', plain,
% 4.23/4.40      ((((k1_relat_1 @ sk_D_2) = (k1_relat_1 @ k1_xboole_0))
% 4.23/4.40        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_2)))),
% 4.23/4.40      inference('sup+', [status(thm)], ['34', '71'])).
% 4.23/4.40  thf(t4_subset_1, axiom,
% 4.23/4.40    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 4.23/4.40  thf('73', plain,
% 4.23/4.40      (![X51 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X51))),
% 4.23/4.40      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.23/4.40  thf('74', plain,
% 4.23/4.40      (![X82 : $i, X83 : $i, X84 : $i]:
% 4.23/4.40         ((v4_relat_1 @ X82 @ X83)
% 4.23/4.40          | ~ (m1_subset_1 @ X82 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X83 @ X84))))),
% 4.23/4.40      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.23/4.40  thf('75', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 4.23/4.40      inference('sup-', [status(thm)], ['73', '74'])).
% 4.23/4.40  thf('76', plain,
% 4.23/4.40      (![X60 : $i, X61 : $i]:
% 4.23/4.40         (~ (v4_relat_1 @ X60 @ X61)
% 4.23/4.40          | (r1_tarski @ (k1_relat_1 @ X60) @ X61)
% 4.23/4.40          | ~ (v1_relat_1 @ X60))),
% 4.23/4.40      inference('cnf', [status(esa)], [d18_relat_1])).
% 4.23/4.40  thf('77', plain,
% 4.23/4.40      (![X0 : $i]:
% 4.23/4.40         (~ (v1_relat_1 @ k1_xboole_0)
% 4.23/4.40          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 4.23/4.40      inference('sup-', [status(thm)], ['75', '76'])).
% 4.23/4.40  thf('78', plain,
% 4.23/4.40      (![X49 : $i, X50 : $i]:
% 4.23/4.40         (((k2_zfmisc_1 @ X49 @ X50) = (k1_xboole_0))
% 4.23/4.40          | ((X49) != (k1_xboole_0)))),
% 4.23/4.40      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.23/4.40  thf('79', plain,
% 4.23/4.40      (![X50 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X50) = (k1_xboole_0))),
% 4.23/4.40      inference('simplify', [status(thm)], ['78'])).
% 4.23/4.40  thf('80', plain,
% 4.23/4.40      (![X64 : $i, X65 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X64 @ X65))),
% 4.23/4.40      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.23/4.40  thf('81', plain, ((v1_relat_1 @ k1_xboole_0)),
% 4.23/4.40      inference('sup+', [status(thm)], ['79', '80'])).
% 4.23/4.40  thf('82', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 4.23/4.40      inference('demod', [status(thm)], ['77', '81'])).
% 4.23/4.40  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 4.23/4.40  thf('83', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 4.23/4.40      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.23/4.40  thf('84', plain,
% 4.23/4.40      (![X4 : $i, X6 : $i]:
% 4.23/4.40         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 4.23/4.40      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.23/4.40  thf('85', plain,
% 4.23/4.40      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 4.23/4.40      inference('sup-', [status(thm)], ['83', '84'])).
% 4.23/4.40  thf('86', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.23/4.40      inference('sup-', [status(thm)], ['82', '85'])).
% 4.23/4.40  thf('87', plain,
% 4.23/4.40      ((((k1_relat_1 @ sk_D_2) = (k1_xboole_0))
% 4.23/4.40        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_2)))),
% 4.23/4.40      inference('demod', [status(thm)], ['72', '86'])).
% 4.23/4.40  thf('88', plain,
% 4.23/4.40      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 4.23/4.40         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 4.23/4.40          | ((X9) = (X10))
% 4.23/4.40          | ((X9) = (X11))
% 4.23/4.40          | ((X9) = (X12)))),
% 4.23/4.40      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.23/4.40  thf('89', plain,
% 4.23/4.40      (![X1 : $i, X3 : $i]:
% 4.23/4.40         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 4.23/4.40      inference('cnf', [status(esa)], [d3_tarski])).
% 4.23/4.40  thf('90', plain,
% 4.23/4.40      (![X0 : $i, X1 : $i]:
% 4.23/4.40         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 4.23/4.40          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 4.23/4.40      inference('sup-', [status(thm)], ['47', '51'])).
% 4.23/4.40  thf('91', plain,
% 4.23/4.40      (![X0 : $i, X1 : $i]:
% 4.23/4.40         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 4.23/4.40          | ~ (zip_tseitin_0 @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 4.23/4.40      inference('sup-', [status(thm)], ['89', '90'])).
% 4.23/4.40  thf('92', plain,
% 4.23/4.40      (![X0 : $i, X1 : $i]:
% 4.23/4.40         (((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 4.23/4.40          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 4.23/4.40          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 4.23/4.40          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 4.23/4.40      inference('sup-', [status(thm)], ['88', '91'])).
% 4.23/4.40  thf('93', plain,
% 4.23/4.40      (![X0 : $i, X1 : $i]:
% 4.23/4.40         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 4.23/4.40          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 4.23/4.40      inference('simplify', [status(thm)], ['92'])).
% 4.23/4.40  thf('94', plain,
% 4.23/4.40      (![X1 : $i, X3 : $i]:
% 4.23/4.40         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 4.23/4.40      inference('cnf', [status(esa)], [d3_tarski])).
% 4.23/4.40  thf('95', plain,
% 4.23/4.40      (![X0 : $i, X1 : $i]:
% 4.23/4.40         (~ (r2_hidden @ X0 @ X1)
% 4.23/4.40          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 4.23/4.40          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 4.23/4.40      inference('sup-', [status(thm)], ['93', '94'])).
% 4.23/4.40  thf('96', plain,
% 4.23/4.40      (![X0 : $i, X1 : $i]:
% 4.23/4.40         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 4.23/4.40      inference('simplify', [status(thm)], ['95'])).
% 4.23/4.40  thf('97', plain,
% 4.23/4.40      ((((k1_relat_1 @ sk_D_2) = (k1_xboole_0))
% 4.23/4.40        | (r1_tarski @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_D_2)))),
% 4.23/4.40      inference('sup-', [status(thm)], ['87', '96'])).
% 4.23/4.40  thf('98', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_2) @ (k1_tarski @ sk_A))),
% 4.23/4.40      inference('demod', [status(thm)], ['41', '42'])).
% 4.23/4.40  thf('99', plain,
% 4.23/4.40      (![X4 : $i, X6 : $i]:
% 4.23/4.40         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 4.23/4.40      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.23/4.40  thf('100', plain,
% 4.23/4.40      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_D_2))
% 4.23/4.40        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_2)))),
% 4.23/4.40      inference('sup-', [status(thm)], ['98', '99'])).
% 4.23/4.40  thf('101', plain,
% 4.23/4.40      ((((k1_relat_1 @ sk_D_2) = (k1_xboole_0))
% 4.23/4.40        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_2)))),
% 4.23/4.40      inference('sup-', [status(thm)], ['97', '100'])).
% 4.23/4.40  thf(t14_funct_1, axiom,
% 4.23/4.40    (![A:$i,B:$i]:
% 4.23/4.40     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.23/4.40       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 4.23/4.40         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 4.23/4.40  thf('102', plain,
% 4.23/4.40      (![X75 : $i, X76 : $i]:
% 4.23/4.40         (((k1_relat_1 @ X76) != (k1_tarski @ X75))
% 4.23/4.40          | ((k2_relat_1 @ X76) = (k1_tarski @ (k1_funct_1 @ X76 @ X75)))
% 4.23/4.40          | ~ (v1_funct_1 @ X76)
% 4.23/4.40          | ~ (v1_relat_1 @ X76))),
% 4.23/4.40      inference('cnf', [status(esa)], [t14_funct_1])).
% 4.23/4.40  thf('103', plain,
% 4.23/4.40      (![X0 : $i]:
% 4.23/4.40         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D_2))
% 4.23/4.40          | ((k1_relat_1 @ sk_D_2) = (k1_xboole_0))
% 4.23/4.40          | ~ (v1_relat_1 @ X0)
% 4.23/4.40          | ~ (v1_funct_1 @ X0)
% 4.23/4.40          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 4.23/4.40      inference('sup-', [status(thm)], ['101', '102'])).
% 4.23/4.40  thf('104', plain,
% 4.23/4.40      ((((k2_relat_1 @ sk_D_2) = (k1_tarski @ (k1_funct_1 @ sk_D_2 @ sk_A)))
% 4.23/4.40        | ~ (v1_funct_1 @ sk_D_2)
% 4.23/4.40        | ~ (v1_relat_1 @ sk_D_2)
% 4.23/4.40        | ((k1_relat_1 @ sk_D_2) = (k1_xboole_0)))),
% 4.23/4.40      inference('eq_res', [status(thm)], ['103'])).
% 4.23/4.40  thf('105', plain, ((v1_funct_1 @ sk_D_2)),
% 4.23/4.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.23/4.40  thf('106', plain, ((v1_relat_1 @ sk_D_2)),
% 4.23/4.40      inference('sup-', [status(thm)], ['10', '11'])).
% 4.23/4.40  thf('107', plain,
% 4.23/4.40      ((((k2_relat_1 @ sk_D_2) = (k1_tarski @ (k1_funct_1 @ sk_D_2 @ sk_A)))
% 4.23/4.40        | ((k1_relat_1 @ sk_D_2) = (k1_xboole_0)))),
% 4.23/4.40      inference('demod', [status(thm)], ['104', '105', '106'])).
% 4.23/4.40  thf('108', plain,
% 4.23/4.40      (~ (r1_tarski @ (k9_relat_1 @ sk_D_2 @ sk_C_2) @ 
% 4.23/4.40          (k1_tarski @ (k1_funct_1 @ sk_D_2 @ sk_A)))),
% 4.23/4.40      inference('demod', [status(thm)], ['0', '3'])).
% 4.23/4.40  thf('109', plain,
% 4.23/4.40      ((~ (r1_tarski @ (k9_relat_1 @ sk_D_2 @ sk_C_2) @ (k2_relat_1 @ sk_D_2))
% 4.23/4.40        | ((k1_relat_1 @ sk_D_2) = (k1_xboole_0)))),
% 4.23/4.40      inference('sup-', [status(thm)], ['107', '108'])).
% 4.23/4.40  thf('110', plain,
% 4.23/4.40      ((~ (v1_relat_1 @ sk_D_2)
% 4.23/4.40        | ~ (v1_funct_1 @ sk_D_2)
% 4.23/4.40        | ((k1_relat_1 @ sk_D_2) = (k1_xboole_0)))),
% 4.23/4.40      inference('sup-', [status(thm)], ['32', '109'])).
% 4.23/4.40  thf('111', plain, ((v1_relat_1 @ sk_D_2)),
% 4.23/4.40      inference('sup-', [status(thm)], ['10', '11'])).
% 4.23/4.40  thf('112', plain, ((v1_funct_1 @ sk_D_2)),
% 4.23/4.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.23/4.40  thf('113', plain, (((k1_relat_1 @ sk_D_2) = (k1_xboole_0))),
% 4.23/4.40      inference('demod', [status(thm)], ['110', '111', '112'])).
% 4.23/4.40  thf('114', plain,
% 4.23/4.40      (![X50 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X50) = (k1_xboole_0))),
% 4.23/4.40      inference('simplify', [status(thm)], ['78'])).
% 4.23/4.40  thf('115', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 4.23/4.40      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.23/4.40  thf('116', plain, (((k1_relat_1 @ sk_D_2) = (k1_xboole_0))),
% 4.23/4.40      inference('demod', [status(thm)], ['110', '111', '112'])).
% 4.23/4.40  thf('117', plain,
% 4.23/4.40      (![X50 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X50) = (k1_xboole_0))),
% 4.23/4.40      inference('simplify', [status(thm)], ['78'])).
% 4.23/4.40  thf('118', plain, (((k1_xboole_0) = (sk_D_2))),
% 4.23/4.40      inference('demod', [status(thm)],
% 4.23/4.40                ['22', '113', '114', '115', '116', '117'])).
% 4.23/4.40  thf('119', plain,
% 4.23/4.40      (![X51 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X51))),
% 4.23/4.40      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.23/4.40  thf('120', plain,
% 4.23/4.40      (![X85 : $i, X86 : $i, X87 : $i, X88 : $i]:
% 4.23/4.40         (~ (m1_subset_1 @ X85 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X86 @ X87)))
% 4.23/4.40          | (m1_subset_1 @ (k7_relset_1 @ X86 @ X87 @ X85 @ X88) @ 
% 4.23/4.40             (k1_zfmisc_1 @ X87)))),
% 4.23/4.40      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 4.23/4.40  thf('121', plain,
% 4.23/4.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.23/4.40         (m1_subset_1 @ (k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2) @ 
% 4.23/4.40          (k1_zfmisc_1 @ X0))),
% 4.23/4.40      inference('sup-', [status(thm)], ['119', '120'])).
% 4.23/4.40  thf('122', plain,
% 4.23/4.40      (![X51 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X51))),
% 4.23/4.40      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.23/4.40  thf('123', plain,
% 4.23/4.40      (![X89 : $i, X90 : $i, X91 : $i, X92 : $i]:
% 4.23/4.40         (~ (m1_subset_1 @ X89 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X90 @ X91)))
% 4.23/4.40          | ((k7_relset_1 @ X90 @ X91 @ X89 @ X92) = (k9_relat_1 @ X89 @ X92)))),
% 4.23/4.40      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 4.23/4.40  thf('124', plain,
% 4.23/4.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.23/4.40         ((k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 4.23/4.40           = (k9_relat_1 @ k1_xboole_0 @ X2))),
% 4.23/4.40      inference('sup-', [status(thm)], ['122', '123'])).
% 4.23/4.40  thf('125', plain,
% 4.23/4.40      (![X0 : $i, X2 : $i]:
% 4.23/4.40         (m1_subset_1 @ (k9_relat_1 @ k1_xboole_0 @ X2) @ (k1_zfmisc_1 @ X0))),
% 4.23/4.40      inference('demod', [status(thm)], ['121', '124'])).
% 4.23/4.40  thf('126', plain,
% 4.23/4.40      (![X54 : $i, X55 : $i]:
% 4.23/4.40         ((r1_tarski @ X54 @ X55) | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ X55)))),
% 4.23/4.40      inference('cnf', [status(esa)], [t3_subset])).
% 4.23/4.40  thf('127', plain,
% 4.23/4.40      (![X0 : $i, X1 : $i]: (r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X1) @ X0)),
% 4.23/4.40      inference('sup-', [status(thm)], ['125', '126'])).
% 4.23/4.40  thf('128', plain,
% 4.23/4.40      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 4.23/4.40      inference('sup-', [status(thm)], ['83', '84'])).
% 4.23/4.40  thf('129', plain,
% 4.23/4.40      (![X0 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 4.23/4.40      inference('sup-', [status(thm)], ['127', '128'])).
% 4.23/4.40  thf('130', plain, (((k1_xboole_0) = (sk_D_2))),
% 4.23/4.40      inference('demod', [status(thm)],
% 4.23/4.40                ['22', '113', '114', '115', '116', '117'])).
% 4.23/4.40  thf('131', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 4.23/4.40      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.23/4.40  thf('132', plain, ($false),
% 4.23/4.40      inference('demod', [status(thm)], ['4', '118', '129', '130', '131'])).
% 4.23/4.40  
% 4.23/4.40  % SZS output end Refutation
% 4.23/4.40  
% 4.23/4.41  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
