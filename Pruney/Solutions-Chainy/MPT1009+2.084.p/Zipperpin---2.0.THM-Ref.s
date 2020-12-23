%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TBx4uQFqGF

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:00 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 282 expanded)
%              Number of leaves         :   47 ( 105 expanded)
%              Depth                    :   19
%              Number of atoms          :  796 (3574 expanded)
%              Number of equality atoms :   68 ( 203 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('0',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X21 @ X22 ) @ ( k2_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

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

thf('1',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    v1_funct_2 @ sk_D_1 @ ( k1_tarski @ sk_A ) @ sk_B ),
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

thf('3',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ( X41
        = ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ~ ( zip_tseitin_1 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('4',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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

thf('7',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X44 @ X45 )
      | ( zip_tseitin_1 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('8',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k1_relset_1 @ X33 @ X34 @ X32 )
        = ( k1_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('14',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf('16',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','15'])).

thf('17',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('18',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('20',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','20'])).

thf('22',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['17','21'])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k1_relat_1 @ X28 ) )
      | ( ( k11_relat_1 @ X28 @ X27 )
        = ( k1_tarski @ ( k1_funct_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( ( k11_relat_1 @ sk_D_1 @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('26',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v1_relat_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('27',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k11_relat_1 @ sk_D_1 @ sk_A )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','27','28'])).

thf('30',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B @ sk_D_1 @ sk_C ) @ ( k11_relat_1 @ sk_D_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf('33',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('34',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( ( k7_relset_1 @ X36 @ X37 @ X35 @ X38 )
        = ( k9_relat_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k11_relat_1 @ sk_D_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','35'])).

thf('37',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('38',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X7 @ X7 @ X8 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('39',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

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

thf('41',plain,(
    ! [X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ( r1_tarski @ X16 @ ( k1_enumset1 @ X12 @ X13 @ X14 ) )
      | ( X16
       != ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('42',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( r1_tarski @ ( k1_tarski @ X12 ) @ ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','42'])).

thf('44',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['37','43'])).

thf('45',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf('46',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('47',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X19 ) @ X20 )
      | ( v4_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( v4_relat_1 @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('50',plain,(
    v4_relat_1 @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('51',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X25
        = ( k7_relat_1 @ X25 @ X26 ) )
      | ~ ( v4_relat_1 @ X25 @ X26 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( sk_D_1
      = ( k7_relat_1 @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('54',plain,
    ( sk_D_1
    = ( k7_relat_1 @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('55',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X23 @ X24 ) )
        = ( k9_relat_1 @ X23 @ X24 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('56',plain,
    ( ( ( k2_relat_1 @ sk_D_1 )
      = ( k9_relat_1 @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) ) )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('58',plain,
    ( ( k2_relat_1 @ sk_D_1 )
    = ( k9_relat_1 @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('60',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k11_relat_1 @ X17 @ X18 )
        = ( k9_relat_1 @ X17 @ ( k1_tarski @ X18 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ sk_A )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k11_relat_1 @ sk_D_1 @ sk_A )
      = ( k2_relat_1 @ sk_D_1 ) )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['58','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('64',plain,
    ( ( k11_relat_1 @ sk_D_1 @ sk_A )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k2_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['36','64'])).

thf('66',plain,(
    ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['0','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('68',plain,(
    $false ),
    inference(demod,[status(thm)],['66','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TBx4uQFqGF
% 0.16/0.37  % Computer   : n017.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 13:58:31 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.44/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.70  % Solved by: fo/fo7.sh
% 0.44/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.70  % done 367 iterations in 0.217s
% 0.44/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.70  % SZS output start Refutation
% 0.44/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.70  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.44/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.70  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.44/0.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.44/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.44/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.70  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.70  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.44/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.70  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.44/0.70  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.44/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.70  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.44/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.70  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.44/0.70  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.44/0.70  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.44/0.70  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.44/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.70  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.44/0.70  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.44/0.70  thf(t144_relat_1, axiom,
% 0.44/0.70    (![A:$i,B:$i]:
% 0.44/0.70     ( ( v1_relat_1 @ B ) =>
% 0.44/0.70       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.44/0.70  thf('0', plain,
% 0.44/0.70      (![X21 : $i, X22 : $i]:
% 0.44/0.70         ((r1_tarski @ (k9_relat_1 @ X21 @ X22) @ (k2_relat_1 @ X21))
% 0.44/0.70          | ~ (v1_relat_1 @ X21))),
% 0.44/0.70      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.44/0.70  thf(t64_funct_2, conjecture,
% 0.44/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.70     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.44/0.70         ( m1_subset_1 @
% 0.44/0.70           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.44/0.70       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.44/0.70         ( r1_tarski @
% 0.44/0.70           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.44/0.70           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.44/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.70    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.70        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.44/0.70            ( m1_subset_1 @
% 0.44/0.70              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.44/0.70          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.44/0.70            ( r1_tarski @
% 0.44/0.70              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.44/0.70              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.44/0.70    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.44/0.70  thf('1', plain,
% 0.44/0.70      (~ (r1_tarski @ 
% 0.44/0.70          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ sk_C) @ 
% 0.44/0.70          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.44/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.70  thf('2', plain, ((v1_funct_2 @ sk_D_1 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.44/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.70  thf(d1_funct_2, axiom,
% 0.44/0.70    (![A:$i,B:$i,C:$i]:
% 0.44/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.70       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.44/0.70           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.44/0.70             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.44/0.70         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.70           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.44/0.70             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.44/0.70  thf(zf_stmt_1, axiom,
% 0.44/0.70    (![C:$i,B:$i,A:$i]:
% 0.44/0.70     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.44/0.70       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.44/0.70  thf('3', plain,
% 0.44/0.70      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.44/0.70         (~ (v1_funct_2 @ X43 @ X41 @ X42)
% 0.44/0.70          | ((X41) = (k1_relset_1 @ X41 @ X42 @ X43))
% 0.44/0.70          | ~ (zip_tseitin_1 @ X43 @ X42 @ X41))),
% 0.44/0.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.70  thf('4', plain,
% 0.44/0.70      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.44/0.70        | ((k1_tarski @ sk_A)
% 0.44/0.70            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1)))),
% 0.44/0.70      inference('sup-', [status(thm)], ['2', '3'])).
% 0.44/0.70  thf(zf_stmt_2, axiom,
% 0.44/0.70    (![B:$i,A:$i]:
% 0.44/0.70     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.70       ( zip_tseitin_0 @ B @ A ) ))).
% 0.44/0.70  thf('5', plain,
% 0.44/0.70      (![X39 : $i, X40 : $i]:
% 0.44/0.70         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 0.44/0.70      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.44/0.70  thf('6', plain,
% 0.44/0.70      ((m1_subset_1 @ sk_D_1 @ 
% 0.44/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.44/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.70  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.44/0.70  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.44/0.70  thf(zf_stmt_5, axiom,
% 0.44/0.70    (![A:$i,B:$i,C:$i]:
% 0.44/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.70       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.44/0.70         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.44/0.70           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.44/0.70             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.44/0.70  thf('7', plain,
% 0.44/0.70      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.44/0.70         (~ (zip_tseitin_0 @ X44 @ X45)
% 0.44/0.70          | (zip_tseitin_1 @ X46 @ X44 @ X45)
% 0.44/0.70          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 0.44/0.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.44/0.70  thf('8', plain,
% 0.44/0.70      (((zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.44/0.70        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.44/0.70      inference('sup-', [status(thm)], ['6', '7'])).
% 0.44/0.70  thf('9', plain,
% 0.44/0.70      ((((sk_B) = (k1_xboole_0))
% 0.44/0.70        | (zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.44/0.70      inference('sup-', [status(thm)], ['5', '8'])).
% 0.44/0.70  thf('10', plain, (((sk_B) != (k1_xboole_0))),
% 0.44/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.70  thf('11', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A))),
% 0.44/0.70      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.44/0.70  thf('12', plain,
% 0.44/0.70      ((m1_subset_1 @ sk_D_1 @ 
% 0.44/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.44/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.70  thf(redefinition_k1_relset_1, axiom,
% 0.44/0.70    (![A:$i,B:$i,C:$i]:
% 0.44/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.70       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.44/0.70  thf('13', plain,
% 0.44/0.70      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.44/0.70         (((k1_relset_1 @ X33 @ X34 @ X32) = (k1_relat_1 @ X32))
% 0.44/0.70          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.44/0.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.44/0.70  thf('14', plain,
% 0.44/0.70      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1)
% 0.44/0.70         = (k1_relat_1 @ sk_D_1))),
% 0.44/0.70      inference('sup-', [status(thm)], ['12', '13'])).
% 0.44/0.70  thf('15', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.44/0.70      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.44/0.70  thf('16', plain,
% 0.44/0.70      (~ (r1_tarski @ 
% 0.44/0.70          (k7_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_B @ sk_D_1 @ sk_C) @ 
% 0.44/0.70          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.44/0.70      inference('demod', [status(thm)], ['1', '15'])).
% 0.44/0.70  thf('17', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.44/0.70      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.44/0.70  thf(t69_enumset1, axiom,
% 0.44/0.70    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.44/0.70  thf('18', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.44/0.70      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.44/0.70  thf(d2_tarski, axiom,
% 0.44/0.70    (![A:$i,B:$i,C:$i]:
% 0.44/0.70     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.44/0.70       ( ![D:$i]:
% 0.44/0.70         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.44/0.70  thf('19', plain,
% 0.44/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.44/0.70         (((X1) != (X0))
% 0.44/0.70          | (r2_hidden @ X1 @ X2)
% 0.44/0.70          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.44/0.70      inference('cnf', [status(esa)], [d2_tarski])).
% 0.44/0.70  thf('20', plain,
% 0.44/0.70      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.44/0.70      inference('simplify', [status(thm)], ['19'])).
% 0.44/0.70  thf('21', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.44/0.70      inference('sup+', [status(thm)], ['18', '20'])).
% 0.44/0.70  thf('22', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_1))),
% 0.44/0.70      inference('sup+', [status(thm)], ['17', '21'])).
% 0.44/0.70  thf(t117_funct_1, axiom,
% 0.44/0.70    (![A:$i,B:$i]:
% 0.44/0.70     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.44/0.70       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.44/0.70         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.44/0.70  thf('23', plain,
% 0.44/0.70      (![X27 : $i, X28 : $i]:
% 0.44/0.70         (~ (r2_hidden @ X27 @ (k1_relat_1 @ X28))
% 0.44/0.70          | ((k11_relat_1 @ X28 @ X27) = (k1_tarski @ (k1_funct_1 @ X28 @ X27)))
% 0.44/0.70          | ~ (v1_funct_1 @ X28)
% 0.44/0.70          | ~ (v1_relat_1 @ X28))),
% 0.44/0.70      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.44/0.70  thf('24', plain,
% 0.44/0.70      ((~ (v1_relat_1 @ sk_D_1)
% 0.44/0.70        | ~ (v1_funct_1 @ sk_D_1)
% 0.44/0.70        | ((k11_relat_1 @ sk_D_1 @ sk_A)
% 0.44/0.70            = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A))))),
% 0.44/0.70      inference('sup-', [status(thm)], ['22', '23'])).
% 0.44/0.70  thf('25', plain,
% 0.44/0.70      ((m1_subset_1 @ sk_D_1 @ 
% 0.44/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.44/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.70  thf(cc1_relset_1, axiom,
% 0.44/0.70    (![A:$i,B:$i,C:$i]:
% 0.44/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.70       ( v1_relat_1 @ C ) ))).
% 0.44/0.70  thf('26', plain,
% 0.44/0.70      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.44/0.70         ((v1_relat_1 @ X29)
% 0.44/0.70          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.44/0.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.44/0.70  thf('27', plain, ((v1_relat_1 @ sk_D_1)),
% 0.44/0.70      inference('sup-', [status(thm)], ['25', '26'])).
% 0.44/0.70  thf('28', plain, ((v1_funct_1 @ sk_D_1)),
% 0.44/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.70  thf('29', plain,
% 0.44/0.70      (((k11_relat_1 @ sk_D_1 @ sk_A)
% 0.44/0.70         = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.44/0.70      inference('demod', [status(thm)], ['24', '27', '28'])).
% 0.44/0.70  thf('30', plain,
% 0.44/0.70      (~ (r1_tarski @ 
% 0.44/0.70          (k7_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_B @ sk_D_1 @ sk_C) @ 
% 0.44/0.70          (k11_relat_1 @ sk_D_1 @ sk_A))),
% 0.44/0.70      inference('demod', [status(thm)], ['16', '29'])).
% 0.44/0.70  thf('31', plain,
% 0.44/0.70      ((m1_subset_1 @ sk_D_1 @ 
% 0.44/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.44/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.70  thf('32', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.44/0.70      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.44/0.70  thf('33', plain,
% 0.44/0.70      ((m1_subset_1 @ sk_D_1 @ 
% 0.44/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ sk_B)))),
% 0.44/0.70      inference('demod', [status(thm)], ['31', '32'])).
% 0.44/0.70  thf(redefinition_k7_relset_1, axiom,
% 0.44/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.70       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.44/0.70  thf('34', plain,
% 0.44/0.70      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.44/0.70         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.44/0.70          | ((k7_relset_1 @ X36 @ X37 @ X35 @ X38) = (k9_relat_1 @ X35 @ X38)))),
% 0.44/0.70      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.44/0.70  thf('35', plain,
% 0.44/0.70      (![X0 : $i]:
% 0.44/0.70         ((k7_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_B @ sk_D_1 @ X0)
% 0.44/0.70           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.44/0.70      inference('sup-', [status(thm)], ['33', '34'])).
% 0.44/0.70  thf('36', plain,
% 0.44/0.70      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ 
% 0.44/0.70          (k11_relat_1 @ sk_D_1 @ sk_A))),
% 0.44/0.70      inference('demod', [status(thm)], ['30', '35'])).
% 0.44/0.70  thf('37', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.44/0.70      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.44/0.70  thf(t70_enumset1, axiom,
% 0.44/0.70    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.44/0.70  thf('38', plain,
% 0.44/0.70      (![X7 : $i, X8 : $i]:
% 0.44/0.70         ((k1_enumset1 @ X7 @ X7 @ X8) = (k2_tarski @ X7 @ X8))),
% 0.44/0.70      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.44/0.70  thf('39', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.44/0.70      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.44/0.70  thf('40', plain,
% 0.44/0.70      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.44/0.70      inference('sup+', [status(thm)], ['38', '39'])).
% 0.44/0.70  thf(t142_zfmisc_1, axiom,
% 0.44/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.70     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.44/0.70       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 0.44/0.70            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 0.44/0.70            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 0.44/0.70            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 0.44/0.70            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 0.44/0.70            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 0.44/0.70  thf('41', plain,
% 0.44/0.70      (![X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 0.44/0.70         ((r1_tarski @ X16 @ (k1_enumset1 @ X12 @ X13 @ X14))
% 0.44/0.70          | ((X16) != (k1_tarski @ X12)))),
% 0.44/0.70      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 0.44/0.70  thf('42', plain,
% 0.44/0.70      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.44/0.70         (r1_tarski @ (k1_tarski @ X12) @ (k1_enumset1 @ X12 @ X13 @ X14))),
% 0.44/0.70      inference('simplify', [status(thm)], ['41'])).
% 0.44/0.70  thf('43', plain,
% 0.44/0.70      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.44/0.70      inference('sup+', [status(thm)], ['40', '42'])).
% 0.44/0.70  thf('44', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_D_1))),
% 0.44/0.70      inference('sup+', [status(thm)], ['37', '43'])).
% 0.44/0.70  thf('45', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.44/0.70      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.44/0.70  thf('46', plain,
% 0.44/0.70      ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_relat_1 @ sk_D_1))),
% 0.44/0.70      inference('demod', [status(thm)], ['44', '45'])).
% 0.44/0.70  thf(d18_relat_1, axiom,
% 0.44/0.70    (![A:$i,B:$i]:
% 0.44/0.70     ( ( v1_relat_1 @ B ) =>
% 0.44/0.70       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.44/0.70  thf('47', plain,
% 0.44/0.70      (![X19 : $i, X20 : $i]:
% 0.44/0.70         (~ (r1_tarski @ (k1_relat_1 @ X19) @ X20)
% 0.44/0.70          | (v4_relat_1 @ X19 @ X20)
% 0.44/0.70          | ~ (v1_relat_1 @ X19))),
% 0.44/0.70      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.44/0.70  thf('48', plain,
% 0.44/0.70      ((~ (v1_relat_1 @ sk_D_1) | (v4_relat_1 @ sk_D_1 @ (k1_relat_1 @ sk_D_1)))),
% 0.44/0.70      inference('sup-', [status(thm)], ['46', '47'])).
% 0.44/0.70  thf('49', plain, ((v1_relat_1 @ sk_D_1)),
% 0.44/0.70      inference('sup-', [status(thm)], ['25', '26'])).
% 0.44/0.70  thf('50', plain, ((v4_relat_1 @ sk_D_1 @ (k1_relat_1 @ sk_D_1))),
% 0.44/0.70      inference('demod', [status(thm)], ['48', '49'])).
% 0.44/0.70  thf(t209_relat_1, axiom,
% 0.44/0.70    (![A:$i,B:$i]:
% 0.44/0.70     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.44/0.70       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.44/0.70  thf('51', plain,
% 0.44/0.70      (![X25 : $i, X26 : $i]:
% 0.44/0.70         (((X25) = (k7_relat_1 @ X25 @ X26))
% 0.44/0.70          | ~ (v4_relat_1 @ X25 @ X26)
% 0.44/0.70          | ~ (v1_relat_1 @ X25))),
% 0.44/0.70      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.44/0.70  thf('52', plain,
% 0.44/0.70      ((~ (v1_relat_1 @ sk_D_1)
% 0.44/0.70        | ((sk_D_1) = (k7_relat_1 @ sk_D_1 @ (k1_relat_1 @ sk_D_1))))),
% 0.44/0.70      inference('sup-', [status(thm)], ['50', '51'])).
% 0.44/0.70  thf('53', plain, ((v1_relat_1 @ sk_D_1)),
% 0.44/0.70      inference('sup-', [status(thm)], ['25', '26'])).
% 0.44/0.70  thf('54', plain,
% 0.44/0.70      (((sk_D_1) = (k7_relat_1 @ sk_D_1 @ (k1_relat_1 @ sk_D_1)))),
% 0.44/0.70      inference('demod', [status(thm)], ['52', '53'])).
% 0.44/0.70  thf(t148_relat_1, axiom,
% 0.44/0.70    (![A:$i,B:$i]:
% 0.44/0.70     ( ( v1_relat_1 @ B ) =>
% 0.44/0.70       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.44/0.70  thf('55', plain,
% 0.44/0.70      (![X23 : $i, X24 : $i]:
% 0.44/0.70         (((k2_relat_1 @ (k7_relat_1 @ X23 @ X24)) = (k9_relat_1 @ X23 @ X24))
% 0.44/0.70          | ~ (v1_relat_1 @ X23))),
% 0.44/0.70      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.44/0.70  thf('56', plain,
% 0.44/0.70      ((((k2_relat_1 @ sk_D_1) = (k9_relat_1 @ sk_D_1 @ (k1_relat_1 @ sk_D_1)))
% 0.44/0.70        | ~ (v1_relat_1 @ sk_D_1))),
% 0.44/0.70      inference('sup+', [status(thm)], ['54', '55'])).
% 0.44/0.70  thf('57', plain, ((v1_relat_1 @ sk_D_1)),
% 0.44/0.70      inference('sup-', [status(thm)], ['25', '26'])).
% 0.44/0.70  thf('58', plain,
% 0.44/0.70      (((k2_relat_1 @ sk_D_1) = (k9_relat_1 @ sk_D_1 @ (k1_relat_1 @ sk_D_1)))),
% 0.44/0.70      inference('demod', [status(thm)], ['56', '57'])).
% 0.44/0.70  thf('59', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.44/0.70      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.44/0.70  thf(d16_relat_1, axiom,
% 0.44/0.70    (![A:$i]:
% 0.44/0.70     ( ( v1_relat_1 @ A ) =>
% 0.44/0.70       ( ![B:$i]:
% 0.44/0.70         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.44/0.70  thf('60', plain,
% 0.44/0.70      (![X17 : $i, X18 : $i]:
% 0.44/0.70         (((k11_relat_1 @ X17 @ X18) = (k9_relat_1 @ X17 @ (k1_tarski @ X18)))
% 0.44/0.70          | ~ (v1_relat_1 @ X17))),
% 0.44/0.70      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.44/0.70  thf('61', plain,
% 0.44/0.70      (![X0 : $i]:
% 0.44/0.70         (((k11_relat_1 @ X0 @ sk_A)
% 0.44/0.70            = (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_D_1)))
% 0.44/0.70          | ~ (v1_relat_1 @ X0))),
% 0.44/0.70      inference('sup+', [status(thm)], ['59', '60'])).
% 0.44/0.70  thf('62', plain,
% 0.44/0.70      ((((k11_relat_1 @ sk_D_1 @ sk_A) = (k2_relat_1 @ sk_D_1))
% 0.44/0.70        | ~ (v1_relat_1 @ sk_D_1))),
% 0.44/0.70      inference('sup+', [status(thm)], ['58', '61'])).
% 0.44/0.70  thf('63', plain, ((v1_relat_1 @ sk_D_1)),
% 0.44/0.70      inference('sup-', [status(thm)], ['25', '26'])).
% 0.44/0.70  thf('64', plain, (((k11_relat_1 @ sk_D_1 @ sk_A) = (k2_relat_1 @ sk_D_1))),
% 0.44/0.70      inference('demod', [status(thm)], ['62', '63'])).
% 0.44/0.70  thf('65', plain,
% 0.44/0.70      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ (k2_relat_1 @ sk_D_1))),
% 0.44/0.70      inference('demod', [status(thm)], ['36', '64'])).
% 0.44/0.70  thf('66', plain, (~ (v1_relat_1 @ sk_D_1)),
% 0.44/0.70      inference('sup-', [status(thm)], ['0', '65'])).
% 0.44/0.70  thf('67', plain, ((v1_relat_1 @ sk_D_1)),
% 0.44/0.70      inference('sup-', [status(thm)], ['25', '26'])).
% 0.44/0.70  thf('68', plain, ($false), inference('demod', [status(thm)], ['66', '67'])).
% 0.44/0.70  
% 0.44/0.70  % SZS output end Refutation
% 0.44/0.70  
% 0.52/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
