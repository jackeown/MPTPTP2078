%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.54WDhDzq0i

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:01 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 288 expanded)
%              Number of leaves         :   43 ( 106 expanded)
%              Depth                    :   14
%              Number of atoms          :  712 (3873 expanded)
%              Number of equality atoms :   56 ( 216 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('0',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X14 @ X15 ) @ ( k2_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ( X36
        = ( k1_relset_1 @ X36 @ X37 @ X38 ) )
      | ~ ( zip_tseitin_1 @ X38 @ X37 @ X36 ) ) ),
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
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 )
      | ( X34 = k1_xboole_0 ) ) ),
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
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( zip_tseitin_0 @ X39 @ X40 )
      | ( zip_tseitin_1 @ X41 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X17 ) )
      | ( ( k11_relat_1 @ X17 @ X16 )
        = ( k1_tarski @ ( k1_funct_1 @ X17 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k7_relset_1 @ X28 @ X29 @ X27 @ X30 )
        = ( k9_relat_1 @ X27 @ X30 ) ) ) ),
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

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k11_relat_1 @ X12 @ X13 )
        = ( k9_relat_1 @ X12 @ ( k1_tarski @ X13 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ sk_A )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('41',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k7_relset_1 @ X31 @ X32 @ X33 @ X31 )
        = ( k2_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('42',plain,
    ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) )
    = ( k2_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('44',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('45',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('46',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf('48',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k9_relat_1 @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['42','43','48'])).

thf('50',plain,
    ( ( ( k11_relat_1 @ sk_D_1 @ sk_A )
      = ( k2_relat_1 @ sk_D_1 ) )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['39','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('52',plain,
    ( ( k11_relat_1 @ sk_D_1 @ sk_A )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k2_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['36','52'])).

thf('54',plain,(
    ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['0','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['54','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.54WDhDzq0i
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:09:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.45/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.61  % Solved by: fo/fo7.sh
% 0.45/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.61  % done 116 iterations in 0.114s
% 0.45/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.61  % SZS output start Refutation
% 0.45/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.45/0.61  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.45/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.61  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.45/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.61  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.45/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.61  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.45/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.61  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.45/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.61  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.45/0.61  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.45/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.61  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.45/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.61  thf(t144_relat_1, axiom,
% 0.45/0.61    (![A:$i,B:$i]:
% 0.45/0.61     ( ( v1_relat_1 @ B ) =>
% 0.45/0.61       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.45/0.61  thf('0', plain,
% 0.45/0.61      (![X14 : $i, X15 : $i]:
% 0.45/0.61         ((r1_tarski @ (k9_relat_1 @ X14 @ X15) @ (k2_relat_1 @ X14))
% 0.45/0.61          | ~ (v1_relat_1 @ X14))),
% 0.45/0.61      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.45/0.61  thf(t64_funct_2, conjecture,
% 0.45/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.61     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.45/0.61         ( m1_subset_1 @
% 0.45/0.61           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.45/0.61       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.45/0.61         ( r1_tarski @
% 0.45/0.61           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.45/0.61           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.45/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.61    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.61        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.45/0.61            ( m1_subset_1 @
% 0.45/0.61              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.45/0.61          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.45/0.61            ( r1_tarski @
% 0.45/0.61              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.45/0.61              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.45/0.61    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.45/0.61  thf('1', plain,
% 0.45/0.61      (~ (r1_tarski @ 
% 0.45/0.61          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ sk_C) @ 
% 0.45/0.61          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.45/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.61  thf('2', plain, ((v1_funct_2 @ sk_D_1 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.45/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.61  thf(d1_funct_2, axiom,
% 0.45/0.61    (![A:$i,B:$i,C:$i]:
% 0.45/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.61       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.61           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.45/0.61             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.45/0.61         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.61           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.45/0.61             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.45/0.61  thf(zf_stmt_1, axiom,
% 0.45/0.61    (![C:$i,B:$i,A:$i]:
% 0.45/0.61     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.45/0.61       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.45/0.61  thf('3', plain,
% 0.45/0.61      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.45/0.61         (~ (v1_funct_2 @ X38 @ X36 @ X37)
% 0.45/0.61          | ((X36) = (k1_relset_1 @ X36 @ X37 @ X38))
% 0.45/0.61          | ~ (zip_tseitin_1 @ X38 @ X37 @ X36))),
% 0.45/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.61  thf('4', plain,
% 0.45/0.61      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.45/0.61        | ((k1_tarski @ sk_A)
% 0.45/0.61            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1)))),
% 0.45/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.61  thf(zf_stmt_2, axiom,
% 0.45/0.61    (![B:$i,A:$i]:
% 0.45/0.61     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.61       ( zip_tseitin_0 @ B @ A ) ))).
% 0.45/0.61  thf('5', plain,
% 0.45/0.61      (![X34 : $i, X35 : $i]:
% 0.45/0.61         ((zip_tseitin_0 @ X34 @ X35) | ((X34) = (k1_xboole_0)))),
% 0.45/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.61  thf('6', plain,
% 0.45/0.61      ((m1_subset_1 @ sk_D_1 @ 
% 0.45/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.61  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.45/0.61  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.45/0.61  thf(zf_stmt_5, axiom,
% 0.45/0.61    (![A:$i,B:$i,C:$i]:
% 0.45/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.61       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.45/0.61         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.61           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.45/0.61             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.45/0.61  thf('7', plain,
% 0.45/0.61      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.45/0.61         (~ (zip_tseitin_0 @ X39 @ X40)
% 0.45/0.61          | (zip_tseitin_1 @ X41 @ X39 @ X40)
% 0.45/0.61          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39))))),
% 0.45/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.61  thf('8', plain,
% 0.45/0.61      (((zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.45/0.61        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.45/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.61  thf('9', plain,
% 0.45/0.61      ((((sk_B) = (k1_xboole_0))
% 0.45/0.61        | (zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.45/0.61      inference('sup-', [status(thm)], ['5', '8'])).
% 0.45/0.61  thf('10', plain, (((sk_B) != (k1_xboole_0))),
% 0.45/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.61  thf('11', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A))),
% 0.45/0.61      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.45/0.61  thf('12', plain,
% 0.45/0.61      ((m1_subset_1 @ sk_D_1 @ 
% 0.45/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.61  thf(redefinition_k1_relset_1, axiom,
% 0.45/0.61    (![A:$i,B:$i,C:$i]:
% 0.45/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.45/0.61  thf('13', plain,
% 0.45/0.61      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.61         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 0.45/0.61          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.45/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.61  thf('14', plain,
% 0.45/0.61      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1)
% 0.45/0.61         = (k1_relat_1 @ sk_D_1))),
% 0.45/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.45/0.61  thf('15', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.45/0.61      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.45/0.61  thf('16', plain,
% 0.45/0.61      (~ (r1_tarski @ 
% 0.45/0.61          (k7_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_B @ sk_D_1 @ sk_C) @ 
% 0.45/0.61          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.45/0.61      inference('demod', [status(thm)], ['1', '15'])).
% 0.45/0.61  thf('17', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.45/0.61      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.45/0.61  thf(t69_enumset1, axiom,
% 0.45/0.61    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.61  thf('18', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.45/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.61  thf(d2_tarski, axiom,
% 0.45/0.61    (![A:$i,B:$i,C:$i]:
% 0.45/0.61     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.45/0.61       ( ![D:$i]:
% 0.45/0.61         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.45/0.61  thf('19', plain,
% 0.45/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.61         (((X1) != (X0))
% 0.45/0.61          | (r2_hidden @ X1 @ X2)
% 0.45/0.61          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.45/0.61      inference('cnf', [status(esa)], [d2_tarski])).
% 0.45/0.61  thf('20', plain,
% 0.45/0.61      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.45/0.61      inference('simplify', [status(thm)], ['19'])).
% 0.45/0.61  thf('21', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.45/0.61      inference('sup+', [status(thm)], ['18', '20'])).
% 0.45/0.61  thf('22', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_1))),
% 0.45/0.61      inference('sup+', [status(thm)], ['17', '21'])).
% 0.45/0.61  thf(t117_funct_1, axiom,
% 0.45/0.61    (![A:$i,B:$i]:
% 0.45/0.61     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.45/0.61       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.45/0.61         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.45/0.61  thf('23', plain,
% 0.45/0.61      (![X16 : $i, X17 : $i]:
% 0.45/0.61         (~ (r2_hidden @ X16 @ (k1_relat_1 @ X17))
% 0.45/0.61          | ((k11_relat_1 @ X17 @ X16) = (k1_tarski @ (k1_funct_1 @ X17 @ X16)))
% 0.45/0.61          | ~ (v1_funct_1 @ X17)
% 0.45/0.61          | ~ (v1_relat_1 @ X17))),
% 0.45/0.61      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.45/0.61  thf('24', plain,
% 0.45/0.61      ((~ (v1_relat_1 @ sk_D_1)
% 0.45/0.61        | ~ (v1_funct_1 @ sk_D_1)
% 0.45/0.61        | ((k11_relat_1 @ sk_D_1 @ sk_A)
% 0.45/0.61            = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A))))),
% 0.45/0.61      inference('sup-', [status(thm)], ['22', '23'])).
% 0.45/0.61  thf('25', plain,
% 0.45/0.61      ((m1_subset_1 @ sk_D_1 @ 
% 0.45/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.61  thf(cc1_relset_1, axiom,
% 0.45/0.61    (![A:$i,B:$i,C:$i]:
% 0.45/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.61       ( v1_relat_1 @ C ) ))).
% 0.45/0.61  thf('26', plain,
% 0.45/0.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.61         ((v1_relat_1 @ X18)
% 0.45/0.61          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.45/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.61  thf('27', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.61      inference('sup-', [status(thm)], ['25', '26'])).
% 0.45/0.61  thf('28', plain, ((v1_funct_1 @ sk_D_1)),
% 0.45/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.61  thf('29', plain,
% 0.45/0.61      (((k11_relat_1 @ sk_D_1 @ sk_A)
% 0.45/0.61         = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.45/0.61      inference('demod', [status(thm)], ['24', '27', '28'])).
% 0.45/0.61  thf('30', plain,
% 0.45/0.61      (~ (r1_tarski @ 
% 0.45/0.61          (k7_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_B @ sk_D_1 @ sk_C) @ 
% 0.45/0.61          (k11_relat_1 @ sk_D_1 @ sk_A))),
% 0.45/0.61      inference('demod', [status(thm)], ['16', '29'])).
% 0.45/0.61  thf('31', plain,
% 0.45/0.61      ((m1_subset_1 @ sk_D_1 @ 
% 0.45/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.61  thf('32', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.45/0.61      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.45/0.61  thf('33', plain,
% 0.45/0.61      ((m1_subset_1 @ sk_D_1 @ 
% 0.45/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ sk_B)))),
% 0.45/0.61      inference('demod', [status(thm)], ['31', '32'])).
% 0.45/0.61  thf(redefinition_k7_relset_1, axiom,
% 0.45/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.61       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.45/0.61  thf('34', plain,
% 0.45/0.61      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.45/0.61         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.45/0.61          | ((k7_relset_1 @ X28 @ X29 @ X27 @ X30) = (k9_relat_1 @ X27 @ X30)))),
% 0.45/0.61      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.45/0.61  thf('35', plain,
% 0.45/0.61      (![X0 : $i]:
% 0.45/0.61         ((k7_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_B @ sk_D_1 @ X0)
% 0.45/0.61           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.45/0.61      inference('sup-', [status(thm)], ['33', '34'])).
% 0.45/0.61  thf('36', plain,
% 0.45/0.61      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ 
% 0.45/0.61          (k11_relat_1 @ sk_D_1 @ sk_A))),
% 0.45/0.61      inference('demod', [status(thm)], ['30', '35'])).
% 0.45/0.61  thf('37', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.45/0.61      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.45/0.61  thf(d16_relat_1, axiom,
% 0.45/0.61    (![A:$i]:
% 0.45/0.61     ( ( v1_relat_1 @ A ) =>
% 0.45/0.61       ( ![B:$i]:
% 0.45/0.61         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.45/0.61  thf('38', plain,
% 0.45/0.61      (![X12 : $i, X13 : $i]:
% 0.45/0.61         (((k11_relat_1 @ X12 @ X13) = (k9_relat_1 @ X12 @ (k1_tarski @ X13)))
% 0.45/0.61          | ~ (v1_relat_1 @ X12))),
% 0.45/0.61      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.45/0.61  thf('39', plain,
% 0.45/0.61      (![X0 : $i]:
% 0.45/0.61         (((k11_relat_1 @ X0 @ sk_A)
% 0.45/0.61            = (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_D_1)))
% 0.45/0.61          | ~ (v1_relat_1 @ X0))),
% 0.45/0.61      inference('sup+', [status(thm)], ['37', '38'])).
% 0.45/0.61  thf('40', plain,
% 0.45/0.61      ((m1_subset_1 @ sk_D_1 @ 
% 0.45/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ sk_B)))),
% 0.45/0.61      inference('demod', [status(thm)], ['31', '32'])).
% 0.45/0.61  thf(t38_relset_1, axiom,
% 0.45/0.61    (![A:$i,B:$i,C:$i]:
% 0.45/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.61       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.45/0.61         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.45/0.61  thf('41', plain,
% 0.45/0.61      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.45/0.61         (((k7_relset_1 @ X31 @ X32 @ X33 @ X31)
% 0.45/0.61            = (k2_relset_1 @ X31 @ X32 @ X33))
% 0.45/0.61          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.45/0.61      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.45/0.61  thf('42', plain,
% 0.45/0.61      (((k7_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_B @ sk_D_1 @ 
% 0.45/0.61         (k1_relat_1 @ sk_D_1))
% 0.45/0.61         = (k2_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_B @ sk_D_1))),
% 0.45/0.61      inference('sup-', [status(thm)], ['40', '41'])).
% 0.45/0.61  thf('43', plain,
% 0.45/0.61      (![X0 : $i]:
% 0.45/0.61         ((k7_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_B @ sk_D_1 @ X0)
% 0.45/0.61           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.45/0.61      inference('sup-', [status(thm)], ['33', '34'])).
% 0.45/0.61  thf('44', plain,
% 0.45/0.61      ((m1_subset_1 @ sk_D_1 @ 
% 0.45/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.61  thf(redefinition_k2_relset_1, axiom,
% 0.45/0.61    (![A:$i,B:$i,C:$i]:
% 0.45/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.61       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.45/0.61  thf('45', plain,
% 0.45/0.61      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.45/0.61         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 0.45/0.61          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.45/0.61      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.61  thf('46', plain,
% 0.45/0.61      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1)
% 0.45/0.61         = (k2_relat_1 @ sk_D_1))),
% 0.45/0.61      inference('sup-', [status(thm)], ['44', '45'])).
% 0.45/0.61  thf('47', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.45/0.61      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.45/0.61  thf('48', plain,
% 0.45/0.61      (((k2_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_B @ sk_D_1)
% 0.45/0.61         = (k2_relat_1 @ sk_D_1))),
% 0.45/0.61      inference('demod', [status(thm)], ['46', '47'])).
% 0.45/0.61  thf('49', plain,
% 0.45/0.61      (((k9_relat_1 @ sk_D_1 @ (k1_relat_1 @ sk_D_1)) = (k2_relat_1 @ sk_D_1))),
% 0.45/0.61      inference('demod', [status(thm)], ['42', '43', '48'])).
% 0.45/0.61  thf('50', plain,
% 0.45/0.61      ((((k11_relat_1 @ sk_D_1 @ sk_A) = (k2_relat_1 @ sk_D_1))
% 0.45/0.61        | ~ (v1_relat_1 @ sk_D_1))),
% 0.45/0.61      inference('sup+', [status(thm)], ['39', '49'])).
% 0.45/0.61  thf('51', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.61      inference('sup-', [status(thm)], ['25', '26'])).
% 0.45/0.61  thf('52', plain, (((k11_relat_1 @ sk_D_1 @ sk_A) = (k2_relat_1 @ sk_D_1))),
% 0.45/0.61      inference('demod', [status(thm)], ['50', '51'])).
% 0.45/0.61  thf('53', plain,
% 0.45/0.61      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ (k2_relat_1 @ sk_D_1))),
% 0.45/0.61      inference('demod', [status(thm)], ['36', '52'])).
% 0.45/0.61  thf('54', plain, (~ (v1_relat_1 @ sk_D_1)),
% 0.45/0.61      inference('sup-', [status(thm)], ['0', '53'])).
% 0.45/0.61  thf('55', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.61      inference('sup-', [status(thm)], ['25', '26'])).
% 0.45/0.61  thf('56', plain, ($false), inference('demod', [status(thm)], ['54', '55'])).
% 0.45/0.61  
% 0.45/0.61  % SZS output end Refutation
% 0.45/0.61  
% 0.45/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
