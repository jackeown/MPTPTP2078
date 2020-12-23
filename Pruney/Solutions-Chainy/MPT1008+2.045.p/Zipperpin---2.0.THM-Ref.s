%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jHQX71BkwY

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:37 EST 2020

% Result     : Theorem 2.03s
% Output     : Refutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 610 expanded)
%              Number of leaves         :   49 ( 200 expanded)
%              Depth                    :   20
%              Number of atoms          : 1129 (8322 expanded)
%              Number of equality atoms :  140 ( 905 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('0',plain,(
    ! [X37: $i] :
      ( ( X37 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X37 ) @ X37 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

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

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t22_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) )
      <=> ( ( k1_relset_1 @ B @ A @ C )
          = B ) ) ) )).

thf('2',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( ( k1_relset_1 @ X32 @ X33 @ X34 )
       != X32 )
      | ~ ( r2_hidden @ X35 @ X32 )
      | ( r2_hidden @ ( k4_tarski @ X35 @ ( sk_E @ X35 @ X34 ) ) @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_C ) ) @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
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
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('5',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ( X42
        = ( k1_relset_1 @ X42 @ X43 @ X44 ) )
      | ~ ( zip_tseitin_1 @ X44 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_0 @ X40 @ X41 )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('9',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( zip_tseitin_0 @ X45 @ X46 )
      | ( zip_tseitin_1 @ X47 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    zip_tseitin_1 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_C ) ) @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_C ) ) @ sk_C ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ sk_C ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['0','16'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('18',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( r1_tarski @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('19',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ sk_C @ ( k4_tarski @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('22',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('26',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['24','27'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('29',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X4 @ X4 @ X5 @ X6 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('32',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X4 @ X4 @ X5 @ X6 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t142_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) )
    <=> ~ ( ( D != k1_xboole_0 )
          & ( D
           != ( k1_tarski @ A ) )
          & ( D
           != ( k1_tarski @ B ) )
          & ( D
           != ( k1_tarski @ C ) )
          & ( D
           != ( k2_tarski @ A @ B ) )
          & ( D
           != ( k2_tarski @ B @ C ) )
          & ( D
           != ( k2_tarski @ A @ C ) )
          & ( D
           != ( k1_enumset1 @ A @ B @ C ) ) ) ) )).

thf('35',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X10
        = ( k1_enumset1 @ X7 @ X8 @ X9 ) )
      | ( X10
        = ( k2_tarski @ X7 @ X9 ) )
      | ( X10
        = ( k2_tarski @ X8 @ X9 ) )
      | ( X10
        = ( k2_tarski @ X7 @ X8 ) )
      | ( X10
        = ( k1_tarski @ X9 ) )
      | ( X10
        = ( k1_tarski @ X8 ) )
      | ( X10
        = ( k1_tarski @ X7 ) )
      | ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X3
        = ( k1_tarski @ X2 ) )
      | ( X3
        = ( k1_tarski @ X1 ) )
      | ( X3
        = ( k1_tarski @ X0 ) )
      | ( X3
        = ( k2_tarski @ X2 @ X1 ) )
      | ( X3
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X3
        = ( k2_tarski @ X2 @ X0 ) )
      | ( X3
        = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_enumset1 @ X0 @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_tarski @ sk_A @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','40'])).

thf('42',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('43',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('45',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k1_relat_1 @ X20 )
       != ( k1_tarski @ X19 ) )
      | ( ( k2_relat_1 @ X20 )
        = ( k1_tarski @ ( k1_funct_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['46'])).

thf('48',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('50',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('53',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('54',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['50','55'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('57',plain,(
    ! [X18: $i] :
      ( ( ( k1_relat_1 @ X18 )
       != k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('58',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('60',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['60'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('64',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['19','61','62','63'])).

thf('65',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['50','55'])).

thf('66',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k1_relat_1 @ X20 )
       != ( k1_tarski @ X19 ) )
      | ( ( k2_relat_1 @ X20 )
        = ( k1_tarski @ ( k1_funct_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k2_relat_1 @ sk_C )
        = ( k1_tarski @ ( k1_funct_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_C )
        = ( k1_tarski @ ( k1_funct_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['60'])).

thf('72',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['60'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['64','73'])).

thf('75',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('77',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['60'])).

thf('78',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['60'])).

thf('79',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['75','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jHQX71BkwY
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:04:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 2.03/2.27  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.03/2.27  % Solved by: fo/fo7.sh
% 2.03/2.27  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.03/2.27  % done 1293 iterations in 1.828s
% 2.03/2.27  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.03/2.27  % SZS output start Refutation
% 2.03/2.27  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 2.03/2.27  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.03/2.27  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.03/2.27  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.03/2.27  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.03/2.27  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.03/2.27  thf(sk_E_type, type, sk_E: $i > $i > $i).
% 2.03/2.27  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.03/2.27  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.03/2.27  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.03/2.27  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 2.03/2.27  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.03/2.27  thf(sk_B_type, type, sk_B: $i > $i).
% 2.03/2.27  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.03/2.27  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.03/2.27  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.03/2.27  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.03/2.27  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.03/2.27  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 2.03/2.27  thf(sk_C_type, type, sk_C: $i).
% 2.03/2.27  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.03/2.27  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.03/2.27  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.03/2.27  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.03/2.27  thf(sk_A_type, type, sk_A: $i).
% 2.03/2.27  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 2.03/2.27  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.03/2.27  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.03/2.27  thf(t9_mcart_1, axiom,
% 2.03/2.27    (![A:$i]:
% 2.03/2.27     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.03/2.27          ( ![B:$i]:
% 2.03/2.27            ( ~( ( r2_hidden @ B @ A ) & 
% 2.03/2.27                 ( ![C:$i,D:$i]:
% 2.03/2.27                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 2.03/2.27                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 2.03/2.27  thf('0', plain,
% 2.03/2.27      (![X37 : $i]:
% 2.03/2.27         (((X37) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X37) @ X37))),
% 2.03/2.27      inference('cnf', [status(esa)], [t9_mcart_1])).
% 2.03/2.27  thf(t62_funct_2, conjecture,
% 2.03/2.27    (![A:$i,B:$i,C:$i]:
% 2.03/2.27     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 2.03/2.27         ( m1_subset_1 @
% 2.03/2.27           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 2.03/2.27       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 2.03/2.27         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 2.03/2.27           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 2.03/2.27  thf(zf_stmt_0, negated_conjecture,
% 2.03/2.27    (~( ![A:$i,B:$i,C:$i]:
% 2.03/2.27        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 2.03/2.27            ( m1_subset_1 @
% 2.03/2.27              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 2.03/2.27          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 2.03/2.27            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 2.03/2.27              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 2.03/2.27    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 2.03/2.27  thf('1', plain,
% 2.03/2.27      ((m1_subset_1 @ sk_C @ 
% 2.03/2.27        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 2.03/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.27  thf(t22_relset_1, axiom,
% 2.03/2.27    (![A:$i,B:$i,C:$i]:
% 2.03/2.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 2.03/2.27       ( ( ![D:$i]:
% 2.03/2.27           ( ~( ( r2_hidden @ D @ B ) & 
% 2.03/2.27                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 2.03/2.27         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 2.03/2.27  thf('2', plain,
% 2.03/2.27      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 2.03/2.27         (((k1_relset_1 @ X32 @ X33 @ X34) != (X32))
% 2.03/2.27          | ~ (r2_hidden @ X35 @ X32)
% 2.03/2.27          | (r2_hidden @ (k4_tarski @ X35 @ (sk_E @ X35 @ X34)) @ X34)
% 2.03/2.27          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 2.03/2.27      inference('cnf', [status(esa)], [t22_relset_1])).
% 2.03/2.27  thf('3', plain,
% 2.03/2.27      (![X0 : $i]:
% 2.03/2.27         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C)) @ sk_C)
% 2.03/2.27          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 2.03/2.27          | ((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 2.03/2.27              != (k1_tarski @ sk_A)))),
% 2.03/2.27      inference('sup-', [status(thm)], ['1', '2'])).
% 2.03/2.27  thf('4', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)),
% 2.03/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.27  thf(d1_funct_2, axiom,
% 2.03/2.27    (![A:$i,B:$i,C:$i]:
% 2.03/2.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.03/2.27       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.03/2.27           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.03/2.27             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.03/2.27         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.03/2.27           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.03/2.27             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.03/2.27  thf(zf_stmt_1, axiom,
% 2.03/2.27    (![C:$i,B:$i,A:$i]:
% 2.03/2.27     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.03/2.27       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.03/2.27  thf('5', plain,
% 2.03/2.27      (![X42 : $i, X43 : $i, X44 : $i]:
% 2.03/2.27         (~ (v1_funct_2 @ X44 @ X42 @ X43)
% 2.03/2.27          | ((X42) = (k1_relset_1 @ X42 @ X43 @ X44))
% 2.03/2.27          | ~ (zip_tseitin_1 @ X44 @ X43 @ X42))),
% 2.03/2.27      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.03/2.27  thf('6', plain,
% 2.03/2.27      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A))
% 2.03/2.27        | ((k1_tarski @ sk_A)
% 2.03/2.27            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)))),
% 2.03/2.27      inference('sup-', [status(thm)], ['4', '5'])).
% 2.03/2.27  thf(zf_stmt_2, axiom,
% 2.03/2.27    (![B:$i,A:$i]:
% 2.03/2.27     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.03/2.27       ( zip_tseitin_0 @ B @ A ) ))).
% 2.03/2.27  thf('7', plain,
% 2.03/2.27      (![X40 : $i, X41 : $i]:
% 2.03/2.27         ((zip_tseitin_0 @ X40 @ X41) | ((X40) = (k1_xboole_0)))),
% 2.03/2.27      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.03/2.27  thf('8', plain,
% 2.03/2.27      ((m1_subset_1 @ sk_C @ 
% 2.03/2.27        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 2.03/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.27  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.03/2.27  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.03/2.27  thf(zf_stmt_5, axiom,
% 2.03/2.27    (![A:$i,B:$i,C:$i]:
% 2.03/2.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.03/2.27       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.03/2.27         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.03/2.27           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.03/2.27             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.03/2.27  thf('9', plain,
% 2.03/2.27      (![X45 : $i, X46 : $i, X47 : $i]:
% 2.03/2.27         (~ (zip_tseitin_0 @ X45 @ X46)
% 2.03/2.27          | (zip_tseitin_1 @ X47 @ X45 @ X46)
% 2.03/2.27          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45))))),
% 2.03/2.27      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.03/2.27  thf('10', plain,
% 2.03/2.27      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A))
% 2.03/2.27        | ~ (zip_tseitin_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 2.03/2.27      inference('sup-', [status(thm)], ['8', '9'])).
% 2.03/2.27  thf('11', plain,
% 2.03/2.27      ((((sk_B_1) = (k1_xboole_0))
% 2.03/2.27        | (zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 2.03/2.27      inference('sup-', [status(thm)], ['7', '10'])).
% 2.03/2.27  thf('12', plain, (((sk_B_1) != (k1_xboole_0))),
% 2.03/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.27  thf('13', plain, ((zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A))),
% 2.03/2.27      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 2.03/2.27  thf('14', plain,
% 2.03/2.27      (((k1_tarski @ sk_A) = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C))),
% 2.03/2.27      inference('demod', [status(thm)], ['6', '13'])).
% 2.03/2.27  thf('15', plain,
% 2.03/2.27      (![X0 : $i]:
% 2.03/2.27         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C)) @ sk_C)
% 2.03/2.27          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 2.03/2.27          | ((k1_tarski @ sk_A) != (k1_tarski @ sk_A)))),
% 2.03/2.27      inference('demod', [status(thm)], ['3', '14'])).
% 2.03/2.27  thf('16', plain,
% 2.03/2.27      (![X0 : $i]:
% 2.03/2.27         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 2.03/2.27          | (r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C)) @ sk_C))),
% 2.03/2.27      inference('simplify', [status(thm)], ['15'])).
% 2.03/2.27  thf('17', plain,
% 2.03/2.27      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 2.03/2.27        | (r2_hidden @ 
% 2.03/2.27           (k4_tarski @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 2.03/2.27            (sk_E @ (sk_B @ (k1_tarski @ sk_A)) @ sk_C)) @ 
% 2.03/2.27           sk_C))),
% 2.03/2.27      inference('sup-', [status(thm)], ['0', '16'])).
% 2.03/2.27  thf(t7_ordinal1, axiom,
% 2.03/2.27    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.03/2.27  thf('18', plain,
% 2.03/2.27      (![X21 : $i, X22 : $i]:
% 2.03/2.27         (~ (r2_hidden @ X21 @ X22) | ~ (r1_tarski @ X22 @ X21))),
% 2.03/2.27      inference('cnf', [status(esa)], [t7_ordinal1])).
% 2.03/2.27  thf('19', plain,
% 2.03/2.27      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 2.03/2.27        | ~ (r1_tarski @ sk_C @ 
% 2.03/2.27             (k4_tarski @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 2.03/2.27              (sk_E @ (sk_B @ (k1_tarski @ sk_A)) @ sk_C))))),
% 2.03/2.27      inference('sup-', [status(thm)], ['17', '18'])).
% 2.03/2.27  thf('20', plain,
% 2.03/2.27      ((m1_subset_1 @ sk_C @ 
% 2.03/2.27        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 2.03/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.27  thf(cc2_relset_1, axiom,
% 2.03/2.27    (![A:$i,B:$i,C:$i]:
% 2.03/2.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.03/2.27       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.03/2.27  thf('21', plain,
% 2.03/2.27      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.03/2.27         ((v4_relat_1 @ X26 @ X27)
% 2.03/2.27          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 2.03/2.27      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.03/2.27  thf('22', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 2.03/2.27      inference('sup-', [status(thm)], ['20', '21'])).
% 2.03/2.27  thf(d18_relat_1, axiom,
% 2.03/2.27    (![A:$i,B:$i]:
% 2.03/2.27     ( ( v1_relat_1 @ B ) =>
% 2.03/2.27       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 2.03/2.27  thf('23', plain,
% 2.03/2.27      (![X16 : $i, X17 : $i]:
% 2.03/2.27         (~ (v4_relat_1 @ X16 @ X17)
% 2.03/2.27          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 2.03/2.27          | ~ (v1_relat_1 @ X16))),
% 2.03/2.27      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.03/2.27  thf('24', plain,
% 2.03/2.27      ((~ (v1_relat_1 @ sk_C)
% 2.03/2.27        | (r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A)))),
% 2.03/2.27      inference('sup-', [status(thm)], ['22', '23'])).
% 2.03/2.27  thf('25', plain,
% 2.03/2.27      ((m1_subset_1 @ sk_C @ 
% 2.03/2.27        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 2.03/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.27  thf(cc1_relset_1, axiom,
% 2.03/2.27    (![A:$i,B:$i,C:$i]:
% 2.03/2.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.03/2.27       ( v1_relat_1 @ C ) ))).
% 2.03/2.27  thf('26', plain,
% 2.03/2.27      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.03/2.27         ((v1_relat_1 @ X23)
% 2.03/2.27          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 2.03/2.27      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.03/2.27  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 2.03/2.27      inference('sup-', [status(thm)], ['25', '26'])).
% 2.03/2.27  thf('28', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A))),
% 2.03/2.27      inference('demod', [status(thm)], ['24', '27'])).
% 2.03/2.27  thf(t71_enumset1, axiom,
% 2.03/2.27    (![A:$i,B:$i,C:$i]:
% 2.03/2.27     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 2.03/2.27  thf('29', plain,
% 2.03/2.27      (![X4 : $i, X5 : $i, X6 : $i]:
% 2.03/2.27         ((k2_enumset1 @ X4 @ X4 @ X5 @ X6) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 2.03/2.27      inference('cnf', [status(esa)], [t71_enumset1])).
% 2.03/2.27  thf(t70_enumset1, axiom,
% 2.03/2.27    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 2.03/2.27  thf('30', plain,
% 2.03/2.27      (![X2 : $i, X3 : $i]:
% 2.03/2.27         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 2.03/2.27      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.03/2.27  thf('31', plain,
% 2.03/2.27      (![X0 : $i, X1 : $i]:
% 2.03/2.27         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 2.03/2.27      inference('sup+', [status(thm)], ['29', '30'])).
% 2.03/2.27  thf(t69_enumset1, axiom,
% 2.03/2.27    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 2.03/2.27  thf('32', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 2.03/2.27      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.03/2.27  thf('33', plain,
% 2.03/2.27      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 2.03/2.27      inference('sup+', [status(thm)], ['31', '32'])).
% 2.03/2.27  thf('34', plain,
% 2.03/2.27      (![X4 : $i, X5 : $i, X6 : $i]:
% 2.03/2.27         ((k2_enumset1 @ X4 @ X4 @ X5 @ X6) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 2.03/2.27      inference('cnf', [status(esa)], [t71_enumset1])).
% 2.03/2.27  thf(t142_zfmisc_1, axiom,
% 2.03/2.27    (![A:$i,B:$i,C:$i,D:$i]:
% 2.03/2.27     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 2.03/2.27       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 2.03/2.27            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 2.03/2.27            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 2.03/2.27            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 2.03/2.27            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 2.03/2.27            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 2.03/2.27  thf('35', plain,
% 2.03/2.27      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 2.03/2.27         (((X10) = (k1_enumset1 @ X7 @ X8 @ X9))
% 2.03/2.27          | ((X10) = (k2_tarski @ X7 @ X9))
% 2.03/2.27          | ((X10) = (k2_tarski @ X8 @ X9))
% 2.03/2.27          | ((X10) = (k2_tarski @ X7 @ X8))
% 2.03/2.27          | ((X10) = (k1_tarski @ X9))
% 2.03/2.27          | ((X10) = (k1_tarski @ X8))
% 2.03/2.27          | ((X10) = (k1_tarski @ X7))
% 2.03/2.27          | ((X10) = (k1_xboole_0))
% 2.03/2.27          | ~ (r1_tarski @ X10 @ (k1_enumset1 @ X7 @ X8 @ X9)))),
% 2.03/2.27      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 2.03/2.27  thf('36', plain,
% 2.03/2.27      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.03/2.27         (~ (r1_tarski @ X3 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0))
% 2.03/2.27          | ((X3) = (k1_xboole_0))
% 2.03/2.27          | ((X3) = (k1_tarski @ X2))
% 2.03/2.27          | ((X3) = (k1_tarski @ X1))
% 2.03/2.27          | ((X3) = (k1_tarski @ X0))
% 2.03/2.27          | ((X3) = (k2_tarski @ X2 @ X1))
% 2.03/2.27          | ((X3) = (k2_tarski @ X1 @ X0))
% 2.03/2.27          | ((X3) = (k2_tarski @ X2 @ X0))
% 2.03/2.27          | ((X3) = (k1_enumset1 @ X2 @ X1 @ X0)))),
% 2.03/2.27      inference('sup-', [status(thm)], ['34', '35'])).
% 2.03/2.27  thf('37', plain,
% 2.03/2.27      (![X0 : $i, X1 : $i]:
% 2.03/2.27         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 2.03/2.27          | ((X1) = (k1_enumset1 @ X0 @ X0 @ X0))
% 2.03/2.27          | ((X1) = (k2_tarski @ X0 @ X0))
% 2.03/2.27          | ((X1) = (k2_tarski @ X0 @ X0))
% 2.03/2.27          | ((X1) = (k2_tarski @ X0 @ X0))
% 2.03/2.27          | ((X1) = (k1_tarski @ X0))
% 2.03/2.27          | ((X1) = (k1_tarski @ X0))
% 2.03/2.27          | ((X1) = (k1_tarski @ X0))
% 2.03/2.27          | ((X1) = (k1_xboole_0)))),
% 2.03/2.27      inference('sup-', [status(thm)], ['33', '36'])).
% 2.03/2.27  thf('38', plain,
% 2.03/2.27      (![X2 : $i, X3 : $i]:
% 2.03/2.27         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 2.03/2.27      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.03/2.27  thf('39', plain,
% 2.03/2.27      (![X0 : $i, X1 : $i]:
% 2.03/2.27         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 2.03/2.27          | ((X1) = (k2_tarski @ X0 @ X0))
% 2.03/2.27          | ((X1) = (k2_tarski @ X0 @ X0))
% 2.03/2.27          | ((X1) = (k2_tarski @ X0 @ X0))
% 2.03/2.27          | ((X1) = (k2_tarski @ X0 @ X0))
% 2.03/2.27          | ((X1) = (k1_tarski @ X0))
% 2.03/2.27          | ((X1) = (k1_tarski @ X0))
% 2.03/2.27          | ((X1) = (k1_tarski @ X0))
% 2.03/2.27          | ((X1) = (k1_xboole_0)))),
% 2.03/2.27      inference('demod', [status(thm)], ['37', '38'])).
% 2.03/2.27  thf('40', plain,
% 2.03/2.27      (![X0 : $i, X1 : $i]:
% 2.03/2.27         (((X1) = (k1_xboole_0))
% 2.03/2.27          | ((X1) = (k1_tarski @ X0))
% 2.03/2.27          | ((X1) = (k2_tarski @ X0 @ X0))
% 2.03/2.27          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 2.03/2.27      inference('simplify', [status(thm)], ['39'])).
% 2.03/2.27  thf('41', plain,
% 2.03/2.27      ((((k1_relat_1 @ sk_C) = (k2_tarski @ sk_A @ sk_A))
% 2.03/2.27        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 2.03/2.27        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 2.03/2.27      inference('sup-', [status(thm)], ['28', '40'])).
% 2.03/2.27  thf('42', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 2.03/2.27      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.03/2.27  thf('43', plain,
% 2.03/2.27      ((((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 2.03/2.27        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 2.03/2.27        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 2.03/2.27      inference('demod', [status(thm)], ['41', '42'])).
% 2.03/2.27  thf('44', plain,
% 2.03/2.27      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 2.03/2.27        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A)))),
% 2.03/2.27      inference('simplify', [status(thm)], ['43'])).
% 2.03/2.27  thf(t14_funct_1, axiom,
% 2.03/2.27    (![A:$i,B:$i]:
% 2.03/2.27     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.03/2.27       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 2.03/2.27         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 2.03/2.27  thf('45', plain,
% 2.03/2.27      (![X19 : $i, X20 : $i]:
% 2.03/2.27         (((k1_relat_1 @ X20) != (k1_tarski @ X19))
% 2.03/2.27          | ((k2_relat_1 @ X20) = (k1_tarski @ (k1_funct_1 @ X20 @ X19)))
% 2.03/2.27          | ~ (v1_funct_1 @ X20)
% 2.03/2.27          | ~ (v1_relat_1 @ X20))),
% 2.03/2.27      inference('cnf', [status(esa)], [t14_funct_1])).
% 2.03/2.27  thf('46', plain,
% 2.03/2.27      (![X0 : $i]:
% 2.03/2.27         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 2.03/2.27          | ((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 2.03/2.27          | ~ (v1_relat_1 @ X0)
% 2.03/2.27          | ~ (v1_funct_1 @ X0)
% 2.03/2.27          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 2.03/2.27      inference('sup-', [status(thm)], ['44', '45'])).
% 2.03/2.27  thf('47', plain,
% 2.03/2.27      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 2.03/2.27        | ~ (v1_funct_1 @ sk_C)
% 2.03/2.27        | ~ (v1_relat_1 @ sk_C)
% 2.03/2.27        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 2.03/2.27      inference('eq_res', [status(thm)], ['46'])).
% 2.03/2.27  thf('48', plain, ((v1_funct_1 @ sk_C)),
% 2.03/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.27  thf('49', plain, ((v1_relat_1 @ sk_C)),
% 2.03/2.27      inference('sup-', [status(thm)], ['25', '26'])).
% 2.03/2.27  thf('50', plain,
% 2.03/2.27      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 2.03/2.27        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 2.03/2.27      inference('demod', [status(thm)], ['47', '48', '49'])).
% 2.03/2.27  thf('51', plain,
% 2.03/2.27      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 2.03/2.27         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 2.03/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.27  thf('52', plain,
% 2.03/2.27      ((m1_subset_1 @ sk_C @ 
% 2.03/2.27        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 2.03/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.27  thf(redefinition_k2_relset_1, axiom,
% 2.03/2.27    (![A:$i,B:$i,C:$i]:
% 2.03/2.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.03/2.27       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.03/2.27  thf('53', plain,
% 2.03/2.27      (![X29 : $i, X30 : $i, X31 : $i]:
% 2.03/2.27         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 2.03/2.27          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 2.03/2.27      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.03/2.27  thf('54', plain,
% 2.03/2.27      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 2.03/2.27         = (k2_relat_1 @ sk_C))),
% 2.03/2.27      inference('sup-', [status(thm)], ['52', '53'])).
% 2.03/2.27  thf('55', plain,
% 2.03/2.27      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 2.03/2.27      inference('demod', [status(thm)], ['51', '54'])).
% 2.03/2.27  thf('56', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 2.03/2.27      inference('simplify_reflect-', [status(thm)], ['50', '55'])).
% 2.03/2.27  thf(t64_relat_1, axiom,
% 2.03/2.27    (![A:$i]:
% 2.03/2.27     ( ( v1_relat_1 @ A ) =>
% 2.03/2.27       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 2.03/2.27           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 2.03/2.27         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 2.03/2.27  thf('57', plain,
% 2.03/2.27      (![X18 : $i]:
% 2.03/2.27         (((k1_relat_1 @ X18) != (k1_xboole_0))
% 2.03/2.27          | ((X18) = (k1_xboole_0))
% 2.03/2.27          | ~ (v1_relat_1 @ X18))),
% 2.03/2.27      inference('cnf', [status(esa)], [t64_relat_1])).
% 2.03/2.27  thf('58', plain,
% 2.03/2.27      ((((k1_xboole_0) != (k1_xboole_0))
% 2.03/2.27        | ~ (v1_relat_1 @ sk_C)
% 2.03/2.27        | ((sk_C) = (k1_xboole_0)))),
% 2.03/2.27      inference('sup-', [status(thm)], ['56', '57'])).
% 2.03/2.27  thf('59', plain, ((v1_relat_1 @ sk_C)),
% 2.03/2.27      inference('sup-', [status(thm)], ['25', '26'])).
% 2.03/2.27  thf('60', plain,
% 2.03/2.27      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 2.03/2.27      inference('demod', [status(thm)], ['58', '59'])).
% 2.03/2.27  thf('61', plain, (((sk_C) = (k1_xboole_0))),
% 2.03/2.27      inference('simplify', [status(thm)], ['60'])).
% 2.03/2.27  thf('62', plain, (((sk_C) = (k1_xboole_0))),
% 2.03/2.27      inference('simplify', [status(thm)], ['60'])).
% 2.03/2.27  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 2.03/2.27  thf('63', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.03/2.27      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.03/2.27  thf('64', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 2.03/2.27      inference('demod', [status(thm)], ['19', '61', '62', '63'])).
% 2.03/2.27  thf('65', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 2.03/2.27      inference('simplify_reflect-', [status(thm)], ['50', '55'])).
% 2.03/2.27  thf('66', plain,
% 2.03/2.27      (![X19 : $i, X20 : $i]:
% 2.03/2.27         (((k1_relat_1 @ X20) != (k1_tarski @ X19))
% 2.03/2.27          | ((k2_relat_1 @ X20) = (k1_tarski @ (k1_funct_1 @ X20 @ X19)))
% 2.03/2.27          | ~ (v1_funct_1 @ X20)
% 2.03/2.27          | ~ (v1_relat_1 @ X20))),
% 2.03/2.27      inference('cnf', [status(esa)], [t14_funct_1])).
% 2.03/2.27  thf('67', plain,
% 2.03/2.27      (![X0 : $i]:
% 2.03/2.27         (((k1_xboole_0) != (k1_tarski @ X0))
% 2.03/2.27          | ~ (v1_relat_1 @ sk_C)
% 2.03/2.27          | ~ (v1_funct_1 @ sk_C)
% 2.03/2.27          | ((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ X0))))),
% 2.03/2.27      inference('sup-', [status(thm)], ['65', '66'])).
% 2.03/2.27  thf('68', plain, ((v1_relat_1 @ sk_C)),
% 2.03/2.27      inference('sup-', [status(thm)], ['25', '26'])).
% 2.03/2.27  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 2.03/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.27  thf('70', plain,
% 2.03/2.27      (![X0 : $i]:
% 2.03/2.27         (((k1_xboole_0) != (k1_tarski @ X0))
% 2.03/2.27          | ((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ X0))))),
% 2.03/2.27      inference('demod', [status(thm)], ['67', '68', '69'])).
% 2.03/2.27  thf('71', plain, (((sk_C) = (k1_xboole_0))),
% 2.03/2.27      inference('simplify', [status(thm)], ['60'])).
% 2.03/2.28  thf('72', plain, (((sk_C) = (k1_xboole_0))),
% 2.03/2.28      inference('simplify', [status(thm)], ['60'])).
% 2.03/2.28  thf('73', plain,
% 2.03/2.28      (![X0 : $i]:
% 2.03/2.28         (((k1_xboole_0) != (k1_tarski @ X0))
% 2.03/2.28          | ((k2_relat_1 @ k1_xboole_0)
% 2.03/2.28              = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 2.03/2.28      inference('demod', [status(thm)], ['70', '71', '72'])).
% 2.03/2.28  thf('74', plain,
% 2.03/2.28      ((((k1_xboole_0) != (k1_xboole_0))
% 2.03/2.28        | ((k2_relat_1 @ k1_xboole_0)
% 2.03/2.28            = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A))))),
% 2.03/2.28      inference('sup-', [status(thm)], ['64', '73'])).
% 2.03/2.28  thf('75', plain,
% 2.03/2.28      (((k2_relat_1 @ k1_xboole_0)
% 2.03/2.28         = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 2.03/2.28      inference('simplify', [status(thm)], ['74'])).
% 2.03/2.28  thf('76', plain,
% 2.03/2.28      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 2.03/2.28      inference('demod', [status(thm)], ['51', '54'])).
% 2.03/2.28  thf('77', plain, (((sk_C) = (k1_xboole_0))),
% 2.03/2.28      inference('simplify', [status(thm)], ['60'])).
% 2.03/2.28  thf('78', plain, (((sk_C) = (k1_xboole_0))),
% 2.03/2.28      inference('simplify', [status(thm)], ['60'])).
% 2.03/2.28  thf('79', plain,
% 2.03/2.28      (((k2_relat_1 @ k1_xboole_0)
% 2.03/2.28         != (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 2.03/2.28      inference('demod', [status(thm)], ['76', '77', '78'])).
% 2.03/2.28  thf('80', plain, ($false),
% 2.03/2.28      inference('simplify_reflect-', [status(thm)], ['75', '79'])).
% 2.03/2.28  
% 2.03/2.28  % SZS output end Refutation
% 2.03/2.28  
% 2.03/2.28  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
