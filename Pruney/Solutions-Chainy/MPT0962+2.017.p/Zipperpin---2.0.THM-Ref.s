%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q8Zs89AKmU

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:51 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 329 expanded)
%              Number of leaves         :   35 ( 104 expanded)
%              Depth                    :   14
%              Number of atoms          :  685 (3622 expanded)
%              Number of equality atoms :   49 ( 112 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t4_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
         => ( ( v1_funct_1 @ B )
            & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t4_funct_2])).

thf('0',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X23 ) @ X24 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ X25 )
      | ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X28
       != ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('14',plain,
    ( ( ( k1_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_B )
   <= ~ ( v1_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('20',plain,(
    v1_funct_1 @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('22',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('25',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['20','23','24'])).

thf('26',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['17','25'])).

thf('27',plain,(
    ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['15','26'])).

thf('28',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['9','27'])).

thf('29',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('30',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['9','27'])).

thf('31',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( zip_tseitin_0 @ k1_xboole_0 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    r1_tarski @ sk_B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('37',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('38',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    r1_tarski @ sk_B @ k1_xboole_0 ),
    inference(demod,[status(thm)],['35','36','38'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('40',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('41',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ k1_xboole_0 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('44',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('45',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('46',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ k1_xboole_0 @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['42','46'])).

thf('48',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('49',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('50',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('51',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('52',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['48','53'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('55',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['44','45'])).

thf('58',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(demod,[status(thm)],['47','58','59'])).

thf('61',plain,(
    k1_xboole_0 = sk_B ),
    inference('sup-',[status(thm)],['39','60'])).

thf('62',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('63',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('64',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X27 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('65',plain,(
    ! [X26: $i] :
      ( zip_tseitin_0 @ X26 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['63','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['66'])).

thf('68',plain,(
    $false ),
    inference(demod,[status(thm)],['32','61','62','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q8Zs89AKmU
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:49:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.61  % Solved by: fo/fo7.sh
% 0.36/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.61  % done 190 iterations in 0.147s
% 0.36/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.61  % SZS output start Refutation
% 0.36/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.61  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.36/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.36/0.61  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.36/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.61  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.36/0.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.36/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.36/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.61  thf(t4_funct_2, conjecture,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.61       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.36/0.61         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.36/0.61           ( m1_subset_1 @
% 0.36/0.61             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.36/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.61    (~( ![A:$i,B:$i]:
% 0.36/0.61        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.61          ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.36/0.61            ( ( v1_funct_1 @ B ) & 
% 0.36/0.61              ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.36/0.61              ( m1_subset_1 @
% 0.36/0.61                B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )),
% 0.36/0.61    inference('cnf.neg', [status(esa)], [t4_funct_2])).
% 0.36/0.61  thf('0', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(d10_xboole_0, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.61  thf('1', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.36/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.61  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.36/0.61      inference('simplify', [status(thm)], ['1'])).
% 0.36/0.61  thf(t11_relset_1, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( v1_relat_1 @ C ) =>
% 0.36/0.61       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.36/0.61           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.36/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.36/0.61  thf('3', plain,
% 0.36/0.61      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.36/0.61         (~ (r1_tarski @ (k1_relat_1 @ X23) @ X24)
% 0.36/0.61          | ~ (r1_tarski @ (k2_relat_1 @ X23) @ X25)
% 0.36/0.61          | (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.36/0.61          | ~ (v1_relat_1 @ X23))),
% 0.36/0.61      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.36/0.61  thf('4', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         (~ (v1_relat_1 @ X0)
% 0.36/0.61          | (m1_subset_1 @ X0 @ 
% 0.36/0.61             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.36/0.61          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.36/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.61  thf('5', plain,
% 0.36/0.61      (((m1_subset_1 @ sk_B @ 
% 0.36/0.61         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.36/0.61        | ~ (v1_relat_1 @ sk_B))),
% 0.36/0.61      inference('sup-', [status(thm)], ['0', '4'])).
% 0.36/0.61  thf('6', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('7', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_B @ 
% 0.36/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.36/0.61      inference('demod', [status(thm)], ['5', '6'])).
% 0.36/0.61  thf(d1_funct_2, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.61       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.36/0.61           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.36/0.61             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.36/0.61         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.61           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.36/0.61             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.36/0.61  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.36/0.61  thf(zf_stmt_2, axiom,
% 0.36/0.61    (![C:$i,B:$i,A:$i]:
% 0.36/0.61     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.36/0.61       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.36/0.61  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.36/0.61  thf(zf_stmt_4, axiom,
% 0.36/0.61    (![B:$i,A:$i]:
% 0.36/0.61     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.61       ( zip_tseitin_0 @ B @ A ) ))).
% 0.36/0.61  thf(zf_stmt_5, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.61       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.36/0.61         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.36/0.61           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.36/0.61             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.36/0.61  thf('8', plain,
% 0.36/0.61      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.36/0.61         (~ (zip_tseitin_0 @ X31 @ X32)
% 0.36/0.61          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 0.36/0.61          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.36/0.61  thf('9', plain,
% 0.36/0.61      (((zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 0.36/0.61        | ~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.61  thf('10', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_B @ 
% 0.36/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.36/0.61      inference('demod', [status(thm)], ['5', '6'])).
% 0.36/0.61  thf(redefinition_k1_relset_1, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.36/0.61  thf('11', plain,
% 0.36/0.61      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.36/0.61         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.36/0.61          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.36/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.36/0.61  thf('12', plain,
% 0.36/0.61      (((k1_relset_1 @ (k1_relat_1 @ sk_B) @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.36/0.61      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.61  thf('13', plain,
% 0.36/0.61      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.36/0.61         (((X28) != (k1_relset_1 @ X28 @ X29 @ X30))
% 0.36/0.61          | (v1_funct_2 @ X30 @ X28 @ X29)
% 0.36/0.61          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.36/0.61  thf('14', plain,
% 0.36/0.61      ((((k1_relat_1 @ sk_B) != (k1_relat_1 @ sk_B))
% 0.36/0.61        | ~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 0.36/0.61        | (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.36/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.36/0.61  thf('15', plain,
% 0.36/0.61      (((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.36/0.61        | ~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.36/0.61      inference('simplify', [status(thm)], ['14'])).
% 0.36/0.61  thf('16', plain,
% 0.36/0.61      ((~ (v1_funct_1 @ sk_B)
% 0.36/0.61        | ~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.36/0.61        | ~ (m1_subset_1 @ sk_B @ 
% 0.36/0.61             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('17', plain,
% 0.36/0.61      ((~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.36/0.61         <= (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.36/0.61      inference('split', [status(esa)], ['16'])).
% 0.36/0.61  thf('18', plain, ((v1_funct_1 @ sk_B)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('19', plain, ((~ (v1_funct_1 @ sk_B)) <= (~ ((v1_funct_1 @ sk_B)))),
% 0.36/0.61      inference('split', [status(esa)], ['16'])).
% 0.36/0.61  thf('20', plain, (((v1_funct_1 @ sk_B))),
% 0.36/0.61      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.61  thf('21', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_B @ 
% 0.36/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.36/0.61      inference('demod', [status(thm)], ['5', '6'])).
% 0.36/0.61  thf('22', plain,
% 0.36/0.61      ((~ (m1_subset_1 @ sk_B @ 
% 0.36/0.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))
% 0.36/0.61         <= (~
% 0.36/0.61             ((m1_subset_1 @ sk_B @ 
% 0.36/0.61               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))))),
% 0.36/0.61      inference('split', [status(esa)], ['16'])).
% 0.36/0.61  thf('23', plain,
% 0.36/0.61      (((m1_subset_1 @ sk_B @ 
% 0.36/0.61         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 0.36/0.61      inference('sup-', [status(thm)], ['21', '22'])).
% 0.36/0.61  thf('24', plain,
% 0.36/0.61      (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.36/0.61       ~
% 0.36/0.61       ((m1_subset_1 @ sk_B @ 
% 0.36/0.61         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))) | 
% 0.36/0.61       ~ ((v1_funct_1 @ sk_B))),
% 0.36/0.61      inference('split', [status(esa)], ['16'])).
% 0.36/0.61  thf('25', plain, (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.36/0.61      inference('sat_resolution*', [status(thm)], ['20', '23', '24'])).
% 0.36/0.61  thf('26', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.36/0.61      inference('simpl_trail', [status(thm)], ['17', '25'])).
% 0.36/0.61  thf('27', plain, (~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.36/0.61      inference('clc', [status(thm)], ['15', '26'])).
% 0.36/0.61  thf('28', plain, (~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.36/0.61      inference('clc', [status(thm)], ['9', '27'])).
% 0.36/0.61  thf('29', plain,
% 0.36/0.61      (![X26 : $i, X27 : $i]:
% 0.36/0.61         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.36/0.61  thf('30', plain, (~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.36/0.61      inference('clc', [status(thm)], ['9', '27'])).
% 0.36/0.61  thf('31', plain, (((sk_A) = (k1_xboole_0))),
% 0.36/0.61      inference('sup-', [status(thm)], ['29', '30'])).
% 0.36/0.61  thf('32', plain, (~ (zip_tseitin_0 @ k1_xboole_0 @ (k1_relat_1 @ sk_B))),
% 0.36/0.61      inference('demod', [status(thm)], ['28', '31'])).
% 0.36/0.61  thf('33', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_B @ 
% 0.36/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.36/0.61      inference('demod', [status(thm)], ['5', '6'])).
% 0.36/0.61  thf(t3_subset, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.61  thf('34', plain,
% 0.36/0.61      (![X6 : $i, X7 : $i]:
% 0.36/0.61         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.36/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.61  thf('35', plain,
% 0.36/0.61      ((r1_tarski @ sk_B @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.36/0.61      inference('sup-', [status(thm)], ['33', '34'])).
% 0.36/0.61  thf('36', plain, (((sk_A) = (k1_xboole_0))),
% 0.36/0.61      inference('sup-', [status(thm)], ['29', '30'])).
% 0.36/0.61  thf(t113_zfmisc_1, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.36/0.61       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.36/0.61  thf('37', plain,
% 0.36/0.61      (![X4 : $i, X5 : $i]:
% 0.36/0.61         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.36/0.61      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.36/0.61  thf('38', plain,
% 0.36/0.61      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.61      inference('simplify', [status(thm)], ['37'])).
% 0.36/0.61  thf('39', plain, ((r1_tarski @ sk_B @ k1_xboole_0)),
% 0.36/0.61      inference('demod', [status(thm)], ['35', '36', '38'])).
% 0.36/0.61  thf(t60_relat_1, axiom,
% 0.36/0.61    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.36/0.61     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.36/0.61  thf('40', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.61      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.36/0.61  thf(t91_relat_1, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( v1_relat_1 @ B ) =>
% 0.36/0.61       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.36/0.61         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.36/0.61  thf('41', plain,
% 0.36/0.61      (![X15 : $i, X16 : $i]:
% 0.36/0.61         (~ (r1_tarski @ X15 @ (k1_relat_1 @ X16))
% 0.36/0.61          | ((k1_relat_1 @ (k7_relat_1 @ X16 @ X15)) = (X15))
% 0.36/0.61          | ~ (v1_relat_1 @ X16))),
% 0.36/0.61      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.36/0.61  thf('42', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         (~ (r1_tarski @ X0 @ k1_xboole_0)
% 0.36/0.61          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.36/0.61          | ((k1_relat_1 @ (k7_relat_1 @ k1_xboole_0 @ X0)) = (X0)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['40', '41'])).
% 0.36/0.61  thf('43', plain,
% 0.36/0.61      (![X4 : $i, X5 : $i]:
% 0.36/0.61         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.36/0.61      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.36/0.61  thf('44', plain,
% 0.36/0.61      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.36/0.61      inference('simplify', [status(thm)], ['43'])).
% 0.36/0.61  thf(fc6_relat_1, axiom,
% 0.36/0.61    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.36/0.61  thf('45', plain,
% 0.36/0.61      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.36/0.61      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.36/0.61  thf('46', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.36/0.61      inference('sup+', [status(thm)], ['44', '45'])).
% 0.36/0.61  thf('47', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         (~ (r1_tarski @ X0 @ k1_xboole_0)
% 0.36/0.61          | ((k1_relat_1 @ (k7_relat_1 @ k1_xboole_0 @ X0)) = (X0)))),
% 0.36/0.61      inference('demod', [status(thm)], ['42', '46'])).
% 0.36/0.61  thf('48', plain,
% 0.36/0.61      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.61      inference('simplify', [status(thm)], ['37'])).
% 0.36/0.61  thf('49', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.36/0.61      inference('simplify', [status(thm)], ['1'])).
% 0.36/0.61  thf('50', plain,
% 0.36/0.61      (![X6 : $i, X8 : $i]:
% 0.36/0.61         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.36/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.61  thf('51', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.36/0.61      inference('sup-', [status(thm)], ['49', '50'])).
% 0.36/0.61  thf(cc2_relset_1, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.61       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.36/0.61  thf('52', plain,
% 0.36/0.61      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.36/0.61         ((v4_relat_1 @ X17 @ X18)
% 0.36/0.61          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.36/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.36/0.61  thf('53', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]: (v4_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X1)),
% 0.36/0.61      inference('sup-', [status(thm)], ['51', '52'])).
% 0.36/0.61  thf('54', plain, (![X0 : $i]: (v4_relat_1 @ k1_xboole_0 @ X0)),
% 0.36/0.61      inference('sup+', [status(thm)], ['48', '53'])).
% 0.36/0.61  thf(t209_relat_1, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.36/0.61       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.36/0.61  thf('55', plain,
% 0.36/0.61      (![X11 : $i, X12 : $i]:
% 0.36/0.61         (((X11) = (k7_relat_1 @ X11 @ X12))
% 0.36/0.61          | ~ (v4_relat_1 @ X11 @ X12)
% 0.36/0.61          | ~ (v1_relat_1 @ X11))),
% 0.36/0.61      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.36/0.61  thf('56', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         (~ (v1_relat_1 @ k1_xboole_0)
% 0.36/0.61          | ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['54', '55'])).
% 0.36/0.61  thf('57', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.36/0.61      inference('sup+', [status(thm)], ['44', '45'])).
% 0.36/0.61  thf('58', plain,
% 0.36/0.61      (![X0 : $i]: ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0))),
% 0.36/0.61      inference('demod', [status(thm)], ['56', '57'])).
% 0.36/0.61  thf('59', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.61      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.36/0.61  thf('60', plain,
% 0.36/0.61      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((k1_xboole_0) = (X0)))),
% 0.36/0.61      inference('demod', [status(thm)], ['47', '58', '59'])).
% 0.36/0.61  thf('61', plain, (((k1_xboole_0) = (sk_B))),
% 0.36/0.61      inference('sup-', [status(thm)], ['39', '60'])).
% 0.36/0.61  thf('62', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.61      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.36/0.61  thf('63', plain,
% 0.36/0.61      (![X26 : $i, X27 : $i]:
% 0.36/0.61         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.36/0.61  thf('64', plain,
% 0.36/0.61      (![X26 : $i, X27 : $i]:
% 0.36/0.61         ((zip_tseitin_0 @ X26 @ X27) | ((X27) != (k1_xboole_0)))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.36/0.61  thf('65', plain, (![X26 : $i]: (zip_tseitin_0 @ X26 @ k1_xboole_0)),
% 0.36/0.61      inference('simplify', [status(thm)], ['64'])).
% 0.36/0.61  thf('66', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.61         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.36/0.61      inference('sup+', [status(thm)], ['63', '65'])).
% 0.36/0.61  thf('67', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.36/0.61      inference('eq_fact', [status(thm)], ['66'])).
% 0.36/0.61  thf('68', plain, ($false),
% 0.36/0.61      inference('demod', [status(thm)], ['32', '61', '62', '67'])).
% 0.36/0.61  
% 0.36/0.61  % SZS output end Refutation
% 0.36/0.61  
% 0.36/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
