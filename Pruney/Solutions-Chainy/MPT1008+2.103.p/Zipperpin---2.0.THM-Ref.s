%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kQv0R0ENwV

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:46 EST 2020

% Result     : Theorem 0.32s
% Output     : Refutation 0.32s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 163 expanded)
%              Number of leaves         :   48 (  71 expanded)
%              Depth                    :   11
%              Number of atoms          :  745 (1708 expanded)
%              Number of equality atoms :   69 ( 137 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_2 @ X45 @ X43 @ X44 )
      | ( X43
        = ( k1_relset_1 @ X43 @ X44 @ X45 ) )
      | ~ ( zip_tseitin_2 @ X45 @ X44 @ X43 ) ) ),
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
    ! [X41: $i,X42: $i] :
      ( ( zip_tseitin_1 @ X41 @ X42 )
      | ( X41 = k1_xboole_0 ) ) ),
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
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( zip_tseitin_1 @ X46 @ X47 )
      | ( zip_tseitin_2 @ X48 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k1_relset_1 @ X36 @ X37 @ X35 )
        = ( k1_relat_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
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

thf(d2_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( ( F != D )
              & ( F != C )
              & ( F != B )
              & ( F != A ) ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [F: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ D @ C @ B @ A )
    <=> ( ( F != A )
        & ( F != B )
        & ( F != C )
        & ( F != D ) ) ) )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 @ X20 )
      | ( r2_hidden @ X16 @ X21 )
      | ( X21
       != ( k2_enumset1 @ X20 @ X19 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('18',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X16 @ ( k2_enumset1 @ X20 @ X19 @ X18 @ X17 ) )
      | ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 ) ) ),
    inference('sup+',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X11 != X10 )
      | ~ ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('21',plain,(
    ! [X10: $i,X12: $i,X13: $i,X14: $i] :
      ~ ( zip_tseitin_0 @ X10 @ X12 @ X13 @ X14 @ X10 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','23'])).

thf('25',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['13','24'])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('26',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X33 @ ( k1_relat_1 @ X34 ) )
      | ( ( k11_relat_1 @ X34 @ X33 )
        = ( k1_tarski @ ( k1_funct_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k11_relat_1 @ sk_C @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('29',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ( v1_relat_1 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('31',plain,(
    ! [X28: $i,X29: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('34',plain,(
    ! [X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ ( k1_relat_1 @ X32 ) )
        = X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X30 @ X31 ) )
        = ( k9_relat_1 @ X30 @ X31 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('40',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['30','31'])).

thf('41',plain,(
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

thf('42',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k11_relat_1 @ X26 @ X27 )
        = ( k9_relat_1 @ X26 @ ( k1_tarski @ X27 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = ( k9_relat_1 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k11_relat_1 @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k11_relat_1 @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf('46',plain,
    ( ( k11_relat_1 @ sk_C @ sk_A )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['38','45'])).

thf('47',plain,
    ( ( ( k11_relat_1 @ sk_C @ sk_A )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['37','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['30','31'])).

thf('49',plain,
    ( ( k11_relat_1 @ sk_C @ sk_A )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','32','33','49'])).

thf('51',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('53',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k2_relset_1 @ X39 @ X40 @ X38 )
        = ( k2_relat_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('54',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['50','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kQv0R0ENwV
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:55:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.32/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.32/0.53  % Solved by: fo/fo7.sh
% 0.32/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.32/0.53  % done 100 iterations in 0.062s
% 0.32/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.32/0.53  % SZS output start Refutation
% 0.32/0.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.32/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.32/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.32/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.32/0.53  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.32/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.32/0.53  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.32/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.32/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.32/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.32/0.53  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.32/0.53  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.32/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.32/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.32/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.32/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.32/0.53  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.32/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.32/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.32/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.32/0.53  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.32/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.32/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.32/0.53  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.32/0.53  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.32/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.32/0.53  thf(t62_funct_2, conjecture,
% 0.32/0.53    (![A:$i,B:$i,C:$i]:
% 0.32/0.53     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.32/0.53         ( m1_subset_1 @
% 0.32/0.53           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.32/0.53       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.32/0.53         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.32/0.53           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.32/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.32/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.32/0.53        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.32/0.53            ( m1_subset_1 @
% 0.32/0.53              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.32/0.53          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.32/0.53            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.32/0.53              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.32/0.53    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.32/0.53  thf('0', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)),
% 0.32/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.32/0.53  thf(d1_funct_2, axiom,
% 0.32/0.53    (![A:$i,B:$i,C:$i]:
% 0.32/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.32/0.53       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.32/0.53           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.32/0.53             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.32/0.53         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.32/0.53           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.32/0.53             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.32/0.53  thf(zf_stmt_1, axiom,
% 0.32/0.53    (![C:$i,B:$i,A:$i]:
% 0.32/0.53     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.32/0.53       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.32/0.53  thf('1', plain,
% 0.32/0.53      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.32/0.53         (~ (v1_funct_2 @ X45 @ X43 @ X44)
% 0.32/0.53          | ((X43) = (k1_relset_1 @ X43 @ X44 @ X45))
% 0.32/0.53          | ~ (zip_tseitin_2 @ X45 @ X44 @ X43))),
% 0.32/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.32/0.53  thf('2', plain,
% 0.32/0.53      ((~ (zip_tseitin_2 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.32/0.53        | ((k1_tarski @ sk_A)
% 0.32/0.53            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)))),
% 0.32/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.32/0.53  thf(zf_stmt_2, axiom,
% 0.32/0.53    (![B:$i,A:$i]:
% 0.32/0.53     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.32/0.53       ( zip_tseitin_1 @ B @ A ) ))).
% 0.32/0.53  thf('3', plain,
% 0.32/0.53      (![X41 : $i, X42 : $i]:
% 0.32/0.53         ((zip_tseitin_1 @ X41 @ X42) | ((X41) = (k1_xboole_0)))),
% 0.32/0.53      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.32/0.53  thf('4', plain,
% 0.32/0.53      ((m1_subset_1 @ sk_C @ 
% 0.32/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.32/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.32/0.53  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.32/0.53  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $o).
% 0.32/0.53  thf(zf_stmt_5, axiom,
% 0.32/0.53    (![A:$i,B:$i,C:$i]:
% 0.32/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.32/0.53       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.32/0.53         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.32/0.53           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.32/0.53             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.32/0.53  thf('5', plain,
% 0.32/0.53      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.32/0.53         (~ (zip_tseitin_1 @ X46 @ X47)
% 0.32/0.53          | (zip_tseitin_2 @ X48 @ X46 @ X47)
% 0.32/0.53          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46))))),
% 0.32/0.53      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.32/0.53  thf('6', plain,
% 0.32/0.53      (((zip_tseitin_2 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.32/0.53        | ~ (zip_tseitin_1 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.32/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.32/0.53  thf('7', plain,
% 0.32/0.53      ((((sk_B) = (k1_xboole_0))
% 0.32/0.53        | (zip_tseitin_2 @ sk_C @ sk_B @ (k1_tarski @ sk_A)))),
% 0.32/0.53      inference('sup-', [status(thm)], ['3', '6'])).
% 0.32/0.53  thf('8', plain, (((sk_B) != (k1_xboole_0))),
% 0.32/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.32/0.53  thf('9', plain, ((zip_tseitin_2 @ sk_C @ sk_B @ (k1_tarski @ sk_A))),
% 0.32/0.53      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.32/0.53  thf('10', plain,
% 0.32/0.53      ((m1_subset_1 @ sk_C @ 
% 0.32/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.32/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.32/0.53  thf(redefinition_k1_relset_1, axiom,
% 0.32/0.53    (![A:$i,B:$i,C:$i]:
% 0.32/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.32/0.53       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.32/0.53  thf('11', plain,
% 0.32/0.53      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.32/0.53         (((k1_relset_1 @ X36 @ X37 @ X35) = (k1_relat_1 @ X35))
% 0.32/0.53          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.32/0.53      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.32/0.53  thf('12', plain,
% 0.32/0.53      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.32/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.32/0.53  thf('13', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.32/0.53      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.32/0.53  thf(t69_enumset1, axiom,
% 0.32/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.32/0.53  thf('14', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.32/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.32/0.53  thf(t70_enumset1, axiom,
% 0.32/0.53    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.32/0.53  thf('15', plain,
% 0.32/0.53      (![X1 : $i, X2 : $i]:
% 0.32/0.53         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.32/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.32/0.53  thf(t71_enumset1, axiom,
% 0.32/0.53    (![A:$i,B:$i,C:$i]:
% 0.32/0.53     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.32/0.53  thf('16', plain,
% 0.32/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.32/0.53         ((k2_enumset1 @ X3 @ X3 @ X4 @ X5) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.32/0.53      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.32/0.53  thf(d2_enumset1, axiom,
% 0.32/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.32/0.53     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.32/0.53       ( ![F:$i]:
% 0.32/0.53         ( ( r2_hidden @ F @ E ) <=>
% 0.32/0.53           ( ~( ( ( F ) != ( D ) ) & ( ( F ) != ( C ) ) & ( ( F ) != ( B ) ) & 
% 0.32/0.53                ( ( F ) != ( A ) ) ) ) ) ) ))).
% 0.32/0.53  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.32/0.53  thf(zf_stmt_7, axiom,
% 0.32/0.53    (![F:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.32/0.53     ( ( zip_tseitin_0 @ F @ D @ C @ B @ A ) <=>
% 0.32/0.53       ( ( ( F ) != ( A ) ) & ( ( F ) != ( B ) ) & ( ( F ) != ( C ) ) & 
% 0.32/0.53         ( ( F ) != ( D ) ) ) ))).
% 0.32/0.53  thf(zf_stmt_8, axiom,
% 0.32/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.32/0.53     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.32/0.53       ( ![F:$i]:
% 0.32/0.53         ( ( r2_hidden @ F @ E ) <=> ( ~( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) ) ))).
% 0.32/0.53  thf('17', plain,
% 0.32/0.53      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.32/0.53         ((zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 @ X20)
% 0.32/0.53          | (r2_hidden @ X16 @ X21)
% 0.32/0.53          | ((X21) != (k2_enumset1 @ X20 @ X19 @ X18 @ X17)))),
% 0.32/0.53      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.32/0.53  thf('18', plain,
% 0.32/0.53      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.32/0.53         ((r2_hidden @ X16 @ (k2_enumset1 @ X20 @ X19 @ X18 @ X17))
% 0.32/0.53          | (zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 0.32/0.53      inference('simplify', [status(thm)], ['17'])).
% 0.32/0.53  thf('19', plain,
% 0.32/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.32/0.53         ((r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.32/0.53          | (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2))),
% 0.32/0.53      inference('sup+', [status(thm)], ['16', '18'])).
% 0.32/0.53  thf('20', plain,
% 0.32/0.53      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.32/0.53         (((X11) != (X10)) | ~ (zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 @ X10))),
% 0.32/0.53      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.32/0.53  thf('21', plain,
% 0.32/0.53      (![X10 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.32/0.53         ~ (zip_tseitin_0 @ X10 @ X12 @ X13 @ X14 @ X10)),
% 0.32/0.53      inference('simplify', [status(thm)], ['20'])).
% 0.32/0.53  thf('22', plain,
% 0.32/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.32/0.53         (r2_hidden @ X0 @ (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.32/0.53      inference('sup-', [status(thm)], ['19', '21'])).
% 0.32/0.53  thf('23', plain,
% 0.32/0.53      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.32/0.53      inference('sup+', [status(thm)], ['15', '22'])).
% 0.32/0.53  thf('24', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.32/0.53      inference('sup+', [status(thm)], ['14', '23'])).
% 0.32/0.53  thf('25', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.32/0.53      inference('sup+', [status(thm)], ['13', '24'])).
% 0.32/0.53  thf(t117_funct_1, axiom,
% 0.32/0.53    (![A:$i,B:$i]:
% 0.32/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.32/0.53       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.32/0.53         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.32/0.53  thf('26', plain,
% 0.32/0.53      (![X33 : $i, X34 : $i]:
% 0.32/0.53         (~ (r2_hidden @ X33 @ (k1_relat_1 @ X34))
% 0.32/0.53          | ((k11_relat_1 @ X34 @ X33) = (k1_tarski @ (k1_funct_1 @ X34 @ X33)))
% 0.32/0.53          | ~ (v1_funct_1 @ X34)
% 0.32/0.53          | ~ (v1_relat_1 @ X34))),
% 0.32/0.53      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.32/0.53  thf('27', plain,
% 0.32/0.53      ((~ (v1_relat_1 @ sk_C)
% 0.32/0.53        | ~ (v1_funct_1 @ sk_C)
% 0.32/0.53        | ((k11_relat_1 @ sk_C @ sk_A)
% 0.32/0.53            = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A))))),
% 0.32/0.53      inference('sup-', [status(thm)], ['25', '26'])).
% 0.32/0.53  thf('28', plain,
% 0.32/0.53      ((m1_subset_1 @ sk_C @ 
% 0.32/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.32/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.32/0.53  thf(cc2_relat_1, axiom,
% 0.32/0.53    (![A:$i]:
% 0.32/0.53     ( ( v1_relat_1 @ A ) =>
% 0.32/0.53       ( ![B:$i]:
% 0.32/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.32/0.53  thf('29', plain,
% 0.32/0.53      (![X24 : $i, X25 : $i]:
% 0.32/0.53         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 0.32/0.53          | (v1_relat_1 @ X24)
% 0.32/0.53          | ~ (v1_relat_1 @ X25))),
% 0.32/0.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.32/0.53  thf('30', plain,
% 0.32/0.53      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.32/0.53        | (v1_relat_1 @ sk_C))),
% 0.32/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.32/0.53  thf(fc6_relat_1, axiom,
% 0.32/0.53    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.32/0.53  thf('31', plain,
% 0.32/0.53      (![X28 : $i, X29 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X28 @ X29))),
% 0.32/0.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.32/0.53  thf('32', plain, ((v1_relat_1 @ sk_C)),
% 0.32/0.53      inference('demod', [status(thm)], ['30', '31'])).
% 0.32/0.53  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.32/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.32/0.53  thf(t98_relat_1, axiom,
% 0.32/0.53    (![A:$i]:
% 0.32/0.53     ( ( v1_relat_1 @ A ) =>
% 0.32/0.53       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.32/0.53  thf('34', plain,
% 0.32/0.53      (![X32 : $i]:
% 0.32/0.53         (((k7_relat_1 @ X32 @ (k1_relat_1 @ X32)) = (X32))
% 0.32/0.53          | ~ (v1_relat_1 @ X32))),
% 0.32/0.53      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.32/0.53  thf(t148_relat_1, axiom,
% 0.32/0.53    (![A:$i,B:$i]:
% 0.32/0.53     ( ( v1_relat_1 @ B ) =>
% 0.32/0.53       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.32/0.53  thf('35', plain,
% 0.32/0.53      (![X30 : $i, X31 : $i]:
% 0.32/0.53         (((k2_relat_1 @ (k7_relat_1 @ X30 @ X31)) = (k9_relat_1 @ X30 @ X31))
% 0.32/0.53          | ~ (v1_relat_1 @ X30))),
% 0.32/0.53      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.32/0.53  thf('36', plain,
% 0.32/0.53      (![X0 : $i]:
% 0.32/0.53         (((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.32/0.53          | ~ (v1_relat_1 @ X0)
% 0.32/0.53          | ~ (v1_relat_1 @ X0))),
% 0.32/0.53      inference('sup+', [status(thm)], ['34', '35'])).
% 0.32/0.53  thf('37', plain,
% 0.32/0.53      (![X0 : $i]:
% 0.32/0.53         (~ (v1_relat_1 @ X0)
% 0.32/0.53          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.32/0.53      inference('simplify', [status(thm)], ['36'])).
% 0.32/0.53  thf('38', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.32/0.53      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.32/0.53  thf('39', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.32/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.32/0.53  thf('40', plain, ((v1_relat_1 @ sk_C)),
% 0.32/0.53      inference('demod', [status(thm)], ['30', '31'])).
% 0.32/0.53  thf('41', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.32/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.32/0.53  thf(d16_relat_1, axiom,
% 0.32/0.53    (![A:$i]:
% 0.32/0.53     ( ( v1_relat_1 @ A ) =>
% 0.32/0.53       ( ![B:$i]:
% 0.32/0.53         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.32/0.53  thf('42', plain,
% 0.32/0.53      (![X26 : $i, X27 : $i]:
% 0.32/0.53         (((k11_relat_1 @ X26 @ X27) = (k9_relat_1 @ X26 @ (k1_tarski @ X27)))
% 0.32/0.53          | ~ (v1_relat_1 @ X26))),
% 0.32/0.53      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.32/0.53  thf('43', plain,
% 0.32/0.53      (![X0 : $i, X1 : $i]:
% 0.32/0.53         (((k11_relat_1 @ X1 @ X0) = (k9_relat_1 @ X1 @ (k2_tarski @ X0 @ X0)))
% 0.32/0.53          | ~ (v1_relat_1 @ X1))),
% 0.32/0.53      inference('sup+', [status(thm)], ['41', '42'])).
% 0.32/0.53  thf('44', plain,
% 0.32/0.53      (![X0 : $i]:
% 0.32/0.53         ((k11_relat_1 @ sk_C @ X0)
% 0.32/0.53           = (k9_relat_1 @ sk_C @ (k2_tarski @ X0 @ X0)))),
% 0.32/0.53      inference('sup-', [status(thm)], ['40', '43'])).
% 0.32/0.53  thf('45', plain,
% 0.32/0.53      (![X0 : $i]:
% 0.32/0.53         ((k11_relat_1 @ sk_C @ X0) = (k9_relat_1 @ sk_C @ (k1_tarski @ X0)))),
% 0.32/0.53      inference('sup+', [status(thm)], ['39', '44'])).
% 0.32/0.53  thf('46', plain,
% 0.32/0.53      (((k11_relat_1 @ sk_C @ sk_A) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.32/0.53      inference('sup+', [status(thm)], ['38', '45'])).
% 0.32/0.53  thf('47', plain,
% 0.32/0.53      ((((k11_relat_1 @ sk_C @ sk_A) = (k2_relat_1 @ sk_C))
% 0.32/0.53        | ~ (v1_relat_1 @ sk_C))),
% 0.32/0.53      inference('sup+', [status(thm)], ['37', '46'])).
% 0.32/0.53  thf('48', plain, ((v1_relat_1 @ sk_C)),
% 0.32/0.53      inference('demod', [status(thm)], ['30', '31'])).
% 0.32/0.53  thf('49', plain, (((k11_relat_1 @ sk_C @ sk_A) = (k2_relat_1 @ sk_C))),
% 0.32/0.53      inference('demod', [status(thm)], ['47', '48'])).
% 0.32/0.53  thf('50', plain,
% 0.32/0.53      (((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.32/0.53      inference('demod', [status(thm)], ['27', '32', '33', '49'])).
% 0.32/0.53  thf('51', plain,
% 0.32/0.53      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)
% 0.32/0.53         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.32/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.32/0.53  thf('52', plain,
% 0.32/0.53      ((m1_subset_1 @ sk_C @ 
% 0.32/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.32/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.32/0.53  thf(redefinition_k2_relset_1, axiom,
% 0.32/0.53    (![A:$i,B:$i,C:$i]:
% 0.32/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.32/0.53       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.32/0.53  thf('53', plain,
% 0.32/0.53      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.32/0.53         (((k2_relset_1 @ X39 @ X40 @ X38) = (k2_relat_1 @ X38))
% 0.32/0.53          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 0.32/0.53      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.32/0.53  thf('54', plain,
% 0.32/0.53      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.32/0.53      inference('sup-', [status(thm)], ['52', '53'])).
% 0.32/0.53  thf('55', plain,
% 0.32/0.53      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.32/0.53      inference('demod', [status(thm)], ['51', '54'])).
% 0.32/0.53  thf('56', plain, ($false),
% 0.32/0.53      inference('simplify_reflect-', [status(thm)], ['50', '55'])).
% 0.32/0.53  
% 0.32/0.53  % SZS output end Refutation
% 0.32/0.53  
% 0.37/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
