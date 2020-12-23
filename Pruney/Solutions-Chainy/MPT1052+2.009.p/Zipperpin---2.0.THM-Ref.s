%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tGvaEaPukx

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:24 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 419 expanded)
%              Number of leaves         :   38 ( 138 expanded)
%              Depth                    :   16
%              Number of atoms          :  582 (3884 expanded)
%              Number of equality atoms :   47 ( 241 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t121_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( r2_hidden @ X23 @ ( k1_funct_2 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('2',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','1'])).

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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_2 @ X17 @ X15 @ X16 )
      | ( X15
        = ( k1_relset_1 @ X15 @ X16 @ X17 ) )
      | ~ ( zip_tseitin_1 @ X17 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('4',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( r2_hidden @ X23 @ ( k1_funct_2 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('9',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('11',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != sk_A )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != sk_A )
   <= ( ( k1_relat_1 @ sk_C )
     != sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v5_relat_1 @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('15',plain,(
    v5_relat_1 @ sk_C @ sk_B_1 ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['11'])).

thf('21',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != sk_A )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['11'])).

thf('23',plain,(
    ( k1_relat_1 @ sk_C )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['21','22'])).

thf('24',plain,(
    ( k1_relat_1 @ sk_C )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['12','23'])).

thf('25',plain,(
    ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['10','24'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('26',plain,(
    ! [X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('27',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('28',plain,(
    ! [X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 )
      | ( X13 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

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

thf('30',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X19 )
      | ( zip_tseitin_1 @ X20 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('31',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_B_1 = o_0_0_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['10','24'])).

thf('34',plain,(
    sk_B_1 = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( zip_tseitin_1 @ sk_C @ o_0_0_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','34'])).

thf(fc3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_xboole_0 @ B ) )
     => ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ) )).

thf('36',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X21 )
      | ~ ( v1_xboole_0 @ X22 )
      | ( v1_xboole_0 @ ( k1_funct_2 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_2])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('37',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('38',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( o_0_0_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 )
      | ( o_0_0_xboole_0
        = ( k1_funct_2 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( o_0_0_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( o_0_0_xboole_0
        = ( k1_funct_2 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( o_0_0_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('45',plain,(
    ~ ( v1_xboole_0 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
    | ( o_0_0_xboole_0 = sk_A )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('48',plain,
    ( ( o_0_0_xboole_0 = sk_A )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    sk_B_1 = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('50',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('51',plain,(
    o_0_0_xboole_0 = sk_A ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ~ ( zip_tseitin_1 @ sk_C @ o_0_0_xboole_0 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['35','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('54',plain,(
    sk_B_1 = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    o_0_0_xboole_0 = sk_A ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X19 )
      | ( zip_tseitin_1 @ X20 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('59',plain,
    ( ( zip_tseitin_1 @ sk_C @ o_0_0_xboole_0 @ o_0_0_xboole_0 )
    | ~ ( zip_tseitin_0 @ o_0_0_xboole_0 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('61',plain,(
    ! [X13: $i] :
      ( zip_tseitin_0 @ X13 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('63',plain,(
    ! [X13: $i] :
      ( zip_tseitin_0 @ X13 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    zip_tseitin_1 @ sk_C @ o_0_0_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['59','63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['52','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tGvaEaPukx
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:27:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.56/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.56/0.73  % Solved by: fo/fo7.sh
% 0.56/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.56/0.73  % done 249 iterations in 0.283s
% 0.56/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.56/0.73  % SZS output start Refutation
% 0.56/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.56/0.73  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.56/0.73  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.56/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.56/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.56/0.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.56/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.56/0.73  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.56/0.73  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.56/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.56/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.56/0.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.56/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.56/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.56/0.73  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.56/0.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.56/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.56/0.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.56/0.73  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.56/0.73  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.56/0.73  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.56/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.56/0.73  thf(t169_funct_2, conjecture,
% 0.56/0.73    (![A:$i,B:$i,C:$i]:
% 0.56/0.73     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.56/0.73       ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.56/0.73         ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.56/0.73           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ))).
% 0.56/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.56/0.73    (~( ![A:$i,B:$i,C:$i]:
% 0.56/0.73        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.56/0.73          ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.56/0.73            ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.56/0.73              ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) )),
% 0.56/0.73    inference('cnf.neg', [status(esa)], [t169_funct_2])).
% 0.56/0.73  thf('0', plain, ((r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf(t121_funct_2, axiom,
% 0.56/0.73    (![A:$i,B:$i,C:$i]:
% 0.56/0.73     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.56/0.73       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.56/0.73         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.56/0.73  thf('1', plain,
% 0.56/0.73      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.56/0.73         ((v1_funct_2 @ X23 @ X24 @ X25)
% 0.56/0.73          | ~ (r2_hidden @ X23 @ (k1_funct_2 @ X24 @ X25)))),
% 0.56/0.73      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.56/0.73  thf('2', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.56/0.73      inference('sup-', [status(thm)], ['0', '1'])).
% 0.56/0.73  thf(d1_funct_2, axiom,
% 0.56/0.73    (![A:$i,B:$i,C:$i]:
% 0.56/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.56/0.73       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.56/0.73           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.56/0.73             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.56/0.73         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.56/0.73           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.56/0.73             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.56/0.73  thf(zf_stmt_1, axiom,
% 0.56/0.73    (![C:$i,B:$i,A:$i]:
% 0.56/0.73     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.56/0.73       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.56/0.73  thf('3', plain,
% 0.56/0.73      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.56/0.73         (~ (v1_funct_2 @ X17 @ X15 @ X16)
% 0.56/0.73          | ((X15) = (k1_relset_1 @ X15 @ X16 @ X17))
% 0.56/0.73          | ~ (zip_tseitin_1 @ X17 @ X16 @ X15))),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.56/0.73  thf('4', plain,
% 0.56/0.73      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.56/0.73        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.56/0.73      inference('sup-', [status(thm)], ['2', '3'])).
% 0.56/0.73  thf('5', plain, ((r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf('6', plain,
% 0.56/0.73      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.56/0.73         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.56/0.73          | ~ (r2_hidden @ X23 @ (k1_funct_2 @ X24 @ X25)))),
% 0.56/0.73      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.56/0.73  thf('7', plain,
% 0.56/0.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.56/0.73      inference('sup-', [status(thm)], ['5', '6'])).
% 0.56/0.73  thf(redefinition_k1_relset_1, axiom,
% 0.56/0.73    (![A:$i,B:$i,C:$i]:
% 0.56/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.56/0.73       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.56/0.73  thf('8', plain,
% 0.56/0.73      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.56/0.73         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 0.56/0.73          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.56/0.73      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.56/0.73  thf('9', plain,
% 0.56/0.73      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.56/0.73      inference('sup-', [status(thm)], ['7', '8'])).
% 0.56/0.73  thf('10', plain,
% 0.56/0.73      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.56/0.73        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.56/0.73      inference('demod', [status(thm)], ['4', '9'])).
% 0.56/0.73  thf('11', plain,
% 0.56/0.73      ((((k1_relat_1 @ sk_C) != (sk_A))
% 0.56/0.73        | ~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf('12', plain,
% 0.56/0.73      ((((k1_relat_1 @ sk_C) != (sk_A)))
% 0.56/0.73         <= (~ (((k1_relat_1 @ sk_C) = (sk_A))))),
% 0.56/0.73      inference('split', [status(esa)], ['11'])).
% 0.56/0.73  thf('13', plain,
% 0.56/0.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.56/0.73      inference('sup-', [status(thm)], ['5', '6'])).
% 0.56/0.73  thf(cc2_relset_1, axiom,
% 0.56/0.73    (![A:$i,B:$i,C:$i]:
% 0.56/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.56/0.73       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.56/0.73  thf('14', plain,
% 0.56/0.73      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.56/0.73         ((v5_relat_1 @ X7 @ X9)
% 0.56/0.73          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.56/0.73      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.56/0.73  thf('15', plain, ((v5_relat_1 @ sk_C @ sk_B_1)),
% 0.56/0.73      inference('sup-', [status(thm)], ['13', '14'])).
% 0.56/0.73  thf(d19_relat_1, axiom,
% 0.56/0.73    (![A:$i,B:$i]:
% 0.56/0.73     ( ( v1_relat_1 @ B ) =>
% 0.56/0.73       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.56/0.73  thf('16', plain,
% 0.56/0.73      (![X5 : $i, X6 : $i]:
% 0.56/0.73         (~ (v5_relat_1 @ X5 @ X6)
% 0.56/0.73          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.56/0.73          | ~ (v1_relat_1 @ X5))),
% 0.56/0.73      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.56/0.73  thf('17', plain,
% 0.56/0.73      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))),
% 0.56/0.73      inference('sup-', [status(thm)], ['15', '16'])).
% 0.56/0.73  thf('18', plain, ((v1_relat_1 @ sk_C)),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf('19', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)),
% 0.56/0.73      inference('demod', [status(thm)], ['17', '18'])).
% 0.56/0.73  thf('20', plain,
% 0.56/0.73      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))
% 0.56/0.73         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.56/0.73      inference('split', [status(esa)], ['11'])).
% 0.56/0.73  thf('21', plain, (((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))),
% 0.56/0.73      inference('sup-', [status(thm)], ['19', '20'])).
% 0.56/0.73  thf('22', plain,
% 0.56/0.73      (~ (((k1_relat_1 @ sk_C) = (sk_A))) | 
% 0.56/0.73       ~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))),
% 0.56/0.73      inference('split', [status(esa)], ['11'])).
% 0.56/0.73  thf('23', plain, (~ (((k1_relat_1 @ sk_C) = (sk_A)))),
% 0.56/0.73      inference('sat_resolution*', [status(thm)], ['21', '22'])).
% 0.56/0.73  thf('24', plain, (((k1_relat_1 @ sk_C) != (sk_A))),
% 0.56/0.73      inference('simpl_trail', [status(thm)], ['12', '23'])).
% 0.56/0.73  thf('25', plain, (~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)),
% 0.56/0.73      inference('simplify_reflect-', [status(thm)], ['10', '24'])).
% 0.56/0.73  thf(zf_stmt_2, axiom,
% 0.56/0.73    (![B:$i,A:$i]:
% 0.56/0.73     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.56/0.73       ( zip_tseitin_0 @ B @ A ) ))).
% 0.56/0.73  thf('26', plain,
% 0.56/0.73      (![X13 : $i, X14 : $i]:
% 0.56/0.73         ((zip_tseitin_0 @ X13 @ X14) | ((X13) = (k1_xboole_0)))),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.56/0.73  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.56/0.73  thf('27', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.56/0.73      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.56/0.73  thf('28', plain,
% 0.56/0.73      (![X13 : $i, X14 : $i]:
% 0.56/0.73         ((zip_tseitin_0 @ X13 @ X14) | ((X13) = (o_0_0_xboole_0)))),
% 0.56/0.73      inference('demod', [status(thm)], ['26', '27'])).
% 0.56/0.73  thf('29', plain,
% 0.56/0.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.56/0.73      inference('sup-', [status(thm)], ['5', '6'])).
% 0.56/0.73  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.56/0.73  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.56/0.73  thf(zf_stmt_5, axiom,
% 0.56/0.73    (![A:$i,B:$i,C:$i]:
% 0.56/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.56/0.73       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.56/0.73         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.56/0.73           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.56/0.73             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.56/0.73  thf('30', plain,
% 0.56/0.73      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.56/0.73         (~ (zip_tseitin_0 @ X18 @ X19)
% 0.56/0.73          | (zip_tseitin_1 @ X20 @ X18 @ X19)
% 0.56/0.73          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X18))))),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.56/0.73  thf('31', plain,
% 0.56/0.73      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.56/0.73        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.56/0.73      inference('sup-', [status(thm)], ['29', '30'])).
% 0.56/0.73  thf('32', plain,
% 0.56/0.73      ((((sk_B_1) = (o_0_0_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A))),
% 0.56/0.73      inference('sup-', [status(thm)], ['28', '31'])).
% 0.56/0.73  thf('33', plain, (~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)),
% 0.56/0.73      inference('simplify_reflect-', [status(thm)], ['10', '24'])).
% 0.56/0.73  thf('34', plain, (((sk_B_1) = (o_0_0_xboole_0))),
% 0.56/0.73      inference('sup-', [status(thm)], ['32', '33'])).
% 0.56/0.73  thf('35', plain, (~ (zip_tseitin_1 @ sk_C @ o_0_0_xboole_0 @ sk_A)),
% 0.56/0.73      inference('demod', [status(thm)], ['25', '34'])).
% 0.56/0.73  thf(fc3_funct_2, axiom,
% 0.56/0.73    (![A:$i,B:$i]:
% 0.56/0.73     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) ) =>
% 0.56/0.73       ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ))).
% 0.56/0.73  thf('36', plain,
% 0.56/0.73      (![X21 : $i, X22 : $i]:
% 0.56/0.73         ((v1_xboole_0 @ X21)
% 0.56/0.73          | ~ (v1_xboole_0 @ X22)
% 0.56/0.73          | (v1_xboole_0 @ (k1_funct_2 @ X21 @ X22)))),
% 0.56/0.73      inference('cnf', [status(esa)], [fc3_funct_2])).
% 0.56/0.73  thf(dt_o_0_0_xboole_0, axiom, (v1_xboole_0 @ o_0_0_xboole_0)).
% 0.56/0.73  thf('37', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.56/0.73      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 0.56/0.73  thf(t8_boole, axiom,
% 0.56/0.73    (![A:$i,B:$i]:
% 0.56/0.73     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.56/0.73  thf('38', plain,
% 0.56/0.73      (![X3 : $i, X4 : $i]:
% 0.56/0.73         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 0.56/0.73      inference('cnf', [status(esa)], [t8_boole])).
% 0.56/0.73  thf('39', plain,
% 0.56/0.73      (![X0 : $i]: (((o_0_0_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.56/0.73      inference('sup-', [status(thm)], ['37', '38'])).
% 0.56/0.73  thf('40', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         (~ (v1_xboole_0 @ X0)
% 0.56/0.73          | (v1_xboole_0 @ X1)
% 0.56/0.73          | ((o_0_0_xboole_0) = (k1_funct_2 @ X1 @ X0)))),
% 0.56/0.73      inference('sup-', [status(thm)], ['36', '39'])).
% 0.56/0.73  thf('41', plain,
% 0.56/0.73      (![X0 : $i]: (((o_0_0_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.56/0.73      inference('sup-', [status(thm)], ['37', '38'])).
% 0.56/0.73  thf('42', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         (((o_0_0_xboole_0) = (k1_funct_2 @ X0 @ X1))
% 0.56/0.73          | ~ (v1_xboole_0 @ X1)
% 0.56/0.73          | ((o_0_0_xboole_0) = (X0)))),
% 0.56/0.73      inference('sup-', [status(thm)], ['40', '41'])).
% 0.56/0.73  thf('43', plain, ((r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf(d1_xboole_0, axiom,
% 0.56/0.73    (![A:$i]:
% 0.56/0.73     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.56/0.73  thf('44', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.56/0.73      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.56/0.73  thf('45', plain, (~ (v1_xboole_0 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.56/0.73      inference('sup-', [status(thm)], ['43', '44'])).
% 0.56/0.73  thf('46', plain,
% 0.56/0.73      ((~ (v1_xboole_0 @ o_0_0_xboole_0)
% 0.56/0.73        | ((o_0_0_xboole_0) = (sk_A))
% 0.56/0.73        | ~ (v1_xboole_0 @ sk_B_1))),
% 0.56/0.73      inference('sup-', [status(thm)], ['42', '45'])).
% 0.56/0.73  thf('47', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.56/0.73      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 0.56/0.73  thf('48', plain, ((((o_0_0_xboole_0) = (sk_A)) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.56/0.73      inference('demod', [status(thm)], ['46', '47'])).
% 0.56/0.73  thf('49', plain, (((sk_B_1) = (o_0_0_xboole_0))),
% 0.56/0.73      inference('sup-', [status(thm)], ['32', '33'])).
% 0.56/0.73  thf('50', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.56/0.73      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 0.56/0.73  thf('51', plain, (((o_0_0_xboole_0) = (sk_A))),
% 0.56/0.73      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.56/0.73  thf('52', plain,
% 0.56/0.73      (~ (zip_tseitin_1 @ sk_C @ o_0_0_xboole_0 @ o_0_0_xboole_0)),
% 0.56/0.73      inference('demod', [status(thm)], ['35', '51'])).
% 0.56/0.73  thf('53', plain,
% 0.56/0.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.56/0.73      inference('sup-', [status(thm)], ['5', '6'])).
% 0.56/0.73  thf('54', plain, (((sk_B_1) = (o_0_0_xboole_0))),
% 0.56/0.73      inference('sup-', [status(thm)], ['32', '33'])).
% 0.56/0.73  thf('55', plain,
% 0.56/0.73      ((m1_subset_1 @ sk_C @ 
% 0.56/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ o_0_0_xboole_0)))),
% 0.56/0.73      inference('demod', [status(thm)], ['53', '54'])).
% 0.56/0.73  thf('56', plain, (((o_0_0_xboole_0) = (sk_A))),
% 0.56/0.73      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.56/0.73  thf('57', plain,
% 0.56/0.73      ((m1_subset_1 @ sk_C @ 
% 0.56/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0)))),
% 0.56/0.73      inference('demod', [status(thm)], ['55', '56'])).
% 0.56/0.73  thf('58', plain,
% 0.56/0.73      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.56/0.73         (~ (zip_tseitin_0 @ X18 @ X19)
% 0.56/0.73          | (zip_tseitin_1 @ X20 @ X18 @ X19)
% 0.56/0.73          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X18))))),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.56/0.73  thf('59', plain,
% 0.56/0.73      (((zip_tseitin_1 @ sk_C @ o_0_0_xboole_0 @ o_0_0_xboole_0)
% 0.56/0.73        | ~ (zip_tseitin_0 @ o_0_0_xboole_0 @ o_0_0_xboole_0))),
% 0.56/0.73      inference('sup-', [status(thm)], ['57', '58'])).
% 0.56/0.73  thf('60', plain,
% 0.56/0.73      (![X13 : $i, X14 : $i]:
% 0.56/0.73         ((zip_tseitin_0 @ X13 @ X14) | ((X14) != (k1_xboole_0)))),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.56/0.73  thf('61', plain, (![X13 : $i]: (zip_tseitin_0 @ X13 @ k1_xboole_0)),
% 0.56/0.73      inference('simplify', [status(thm)], ['60'])).
% 0.56/0.73  thf('62', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.56/0.73      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.56/0.73  thf('63', plain, (![X13 : $i]: (zip_tseitin_0 @ X13 @ o_0_0_xboole_0)),
% 0.56/0.73      inference('demod', [status(thm)], ['61', '62'])).
% 0.56/0.73  thf('64', plain, ((zip_tseitin_1 @ sk_C @ o_0_0_xboole_0 @ o_0_0_xboole_0)),
% 0.56/0.73      inference('demod', [status(thm)], ['59', '63'])).
% 0.56/0.73  thf('65', plain, ($false), inference('demod', [status(thm)], ['52', '64'])).
% 0.56/0.73  
% 0.56/0.73  % SZS output end Refutation
% 0.56/0.73  
% 0.56/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
