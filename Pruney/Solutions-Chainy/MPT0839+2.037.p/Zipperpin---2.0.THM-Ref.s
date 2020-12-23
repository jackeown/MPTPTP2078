%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qmvXSwmqJZ

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:16 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 309 expanded)
%              Number of leaves         :   43 ( 110 expanded)
%              Depth                    :   17
%              Number of atoms          :  698 (2555 expanded)
%              Number of equality atoms :   47 ( 132 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t50_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
             => ~ ( ( ( k2_relset_1 @ B @ A @ C )
                   != k1_xboole_0 )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ B )
                     => ~ ( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
               => ~ ( ( ( k2_relset_1 @ B @ A @ C )
                     != k1_xboole_0 )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ B )
                       => ~ ( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_relset_1])).

thf('0',plain,(
    ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( ( k2_relset_1 @ X48 @ X49 @ X47 )
        = ( k2_relat_1 @ X47 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','3'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('6',plain,(
    ! [X50: $i] :
      ( ~ ( r2_hidden @ X50 @ ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X50 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_1 )
      = k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_1 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( ( k1_relset_1 @ X45 @ X46 @ X44 )
        = ( k1_relat_1 @ X44 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('10',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('12',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k1_relat_1 @ sk_C_1 ) ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['7','10','11'])).

thf('13',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( v4_relat_1 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('16',plain,(
    v4_relat_1 @ sk_C_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('17',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v4_relat_1 @ X30 @ X31 )
      | ( r1_tarski @ ( k1_relat_1 @ X30 ) @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('20',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( v1_relat_1 @ X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('22',plain,(
    ! [X33: $i,X34: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('23',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['18','23'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ ( k1_relat_1 @ sk_C_1 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['13','26'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('28',plain,(
    ! [X20: $i,X21: $i] :
      ( ( m1_subset_1 @ X20 @ X21 )
      | ~ ( r2_hidden @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('29',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_B @ ( k1_relat_1 @ sk_C_1 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['12','29'])).

thf('31',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X30 ) @ X31 )
      | ( v4_relat_1 @ X30 @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( v4_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('34',plain,(
    ! [X16: $i] :
      ( ( r1_xboole_0 @ X16 @ X16 )
      | ( X16 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('35',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['34'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('36',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('37',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('38',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('39',plain,(
    ! [X22: $i,X24: $i] :
      ( ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('41',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ~ ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['34'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('45',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_tarski @ X18 @ X19 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('46',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('47',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( X11 != X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('48',plain,(
    ! [X12: $i] :
      ( r1_tarski @ X12 @ X12 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['46','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['33','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['21','22'])).

thf('53',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ sk_C_1 @ X0 ) ),
    inference(demod,[status(thm)],['32','51','52'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('54',plain,(
    ! [X38: $i,X39: $i] :
      ( ( X38
        = ( k7_relat_1 @ X38 @ X39 ) )
      | ~ ( v4_relat_1 @ X38 @ X39 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( sk_C_1
        = ( k7_relat_1 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['21','22'])).

thf('57',plain,(
    ! [X0: $i] :
      ( sk_C_1
      = ( k7_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['33','50'])).

thf('60',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf(t207_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf('66',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r1_xboole_0 @ X35 @ X36 )
      | ~ ( v1_relat_1 @ X37 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X37 @ X35 ) @ X36 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ k1_xboole_0 ) @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_C_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['57','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( sk_C_1
      = ( k7_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('70',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['21','22'])).

thf('71',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['46','48'])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('73',plain,(
    ! [X32: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X32 ) )
      | ~ ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('74',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['4','71','76'])).

thf('78',plain,(
    $false ),
    inference(simplify,[status(thm)],['77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qmvXSwmqJZ
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:30:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.61/0.84  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.61/0.84  % Solved by: fo/fo7.sh
% 0.61/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.84  % done 865 iterations in 0.380s
% 0.61/0.84  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.61/0.84  % SZS output start Refutation
% 0.61/0.84  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.61/0.84  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.61/0.84  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.61/0.84  thf(sk_B_type, type, sk_B: $i > $i).
% 0.61/0.84  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.61/0.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.61/0.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.61/0.84  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.61/0.84  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.61/0.84  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.61/0.84  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.61/0.84  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.61/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.61/0.84  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.61/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.84  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.61/0.84  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.61/0.84  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.61/0.84  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.61/0.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.84  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.61/0.84  thf(t50_relset_1, conjecture,
% 0.61/0.84    (![A:$i]:
% 0.61/0.84     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.61/0.84       ( ![B:$i]:
% 0.61/0.84         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.61/0.84           ( ![C:$i]:
% 0.61/0.84             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.61/0.84               ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.61/0.84                    ( ![D:$i]:
% 0.61/0.84                      ( ( m1_subset_1 @ D @ B ) =>
% 0.61/0.84                        ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.61/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.84    (~( ![A:$i]:
% 0.61/0.84        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.61/0.84          ( ![B:$i]:
% 0.61/0.84            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.61/0.84              ( ![C:$i]:
% 0.61/0.84                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.61/0.84                  ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.61/0.84                       ( ![D:$i]:
% 0.61/0.84                         ( ( m1_subset_1 @ D @ B ) =>
% 0.61/0.84                           ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.61/0.84    inference('cnf.neg', [status(esa)], [t50_relset_1])).
% 0.61/0.84  thf('0', plain, (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_1) != (k1_xboole_0))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('1', plain,
% 0.61/0.84      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf(redefinition_k2_relset_1, axiom,
% 0.61/0.84    (![A:$i,B:$i,C:$i]:
% 0.61/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.84       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.61/0.84  thf('2', plain,
% 0.61/0.84      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.61/0.84         (((k2_relset_1 @ X48 @ X49 @ X47) = (k2_relat_1 @ X47))
% 0.61/0.84          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49))))),
% 0.61/0.84      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.61/0.84  thf('3', plain,
% 0.61/0.84      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.61/0.84      inference('sup-', [status(thm)], ['1', '2'])).
% 0.61/0.84  thf('4', plain, (((k2_relat_1 @ sk_C_1) != (k1_xboole_0))),
% 0.61/0.84      inference('demod', [status(thm)], ['0', '3'])).
% 0.61/0.84  thf(t7_xboole_0, axiom,
% 0.61/0.84    (![A:$i]:
% 0.61/0.84     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.61/0.84          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.61/0.84  thf('5', plain,
% 0.61/0.84      (![X10 : $i]:
% 0.61/0.84         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.61/0.84      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.61/0.84  thf('6', plain,
% 0.61/0.84      (![X50 : $i]:
% 0.61/0.84         (~ (r2_hidden @ X50 @ (k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_1))
% 0.61/0.84          | ~ (m1_subset_1 @ X50 @ sk_B_1))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('7', plain,
% 0.61/0.84      ((((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_1) = (k1_xboole_0))
% 0.61/0.84        | ~ (m1_subset_1 @ (sk_B @ (k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_1)) @ 
% 0.61/0.84             sk_B_1))),
% 0.61/0.84      inference('sup-', [status(thm)], ['5', '6'])).
% 0.61/0.84  thf('8', plain,
% 0.61/0.84      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf(redefinition_k1_relset_1, axiom,
% 0.61/0.84    (![A:$i,B:$i,C:$i]:
% 0.61/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.84       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.61/0.84  thf('9', plain,
% 0.61/0.84      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.61/0.84         (((k1_relset_1 @ X45 @ X46 @ X44) = (k1_relat_1 @ X44))
% 0.61/0.84          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46))))),
% 0.61/0.84      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.61/0.84  thf('10', plain,
% 0.61/0.84      (((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.61/0.84      inference('sup-', [status(thm)], ['8', '9'])).
% 0.61/0.84  thf('11', plain,
% 0.61/0.84      (((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.61/0.84      inference('sup-', [status(thm)], ['8', '9'])).
% 0.61/0.84  thf('12', plain,
% 0.61/0.84      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.61/0.84        | ~ (m1_subset_1 @ (sk_B @ (k1_relat_1 @ sk_C_1)) @ sk_B_1))),
% 0.61/0.84      inference('demod', [status(thm)], ['7', '10', '11'])).
% 0.61/0.84  thf('13', plain,
% 0.61/0.84      (![X10 : $i]:
% 0.61/0.84         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.61/0.84      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.61/0.84  thf('14', plain,
% 0.61/0.84      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf(cc2_relset_1, axiom,
% 0.61/0.84    (![A:$i,B:$i,C:$i]:
% 0.61/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.84       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.61/0.84  thf('15', plain,
% 0.61/0.84      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.61/0.84         ((v4_relat_1 @ X41 @ X42)
% 0.61/0.84          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43))))),
% 0.61/0.84      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.61/0.84  thf('16', plain, ((v4_relat_1 @ sk_C_1 @ sk_B_1)),
% 0.61/0.84      inference('sup-', [status(thm)], ['14', '15'])).
% 0.61/0.84  thf(d18_relat_1, axiom,
% 0.61/0.84    (![A:$i,B:$i]:
% 0.61/0.84     ( ( v1_relat_1 @ B ) =>
% 0.61/0.84       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.61/0.84  thf('17', plain,
% 0.61/0.84      (![X30 : $i, X31 : $i]:
% 0.61/0.84         (~ (v4_relat_1 @ X30 @ X31)
% 0.61/0.84          | (r1_tarski @ (k1_relat_1 @ X30) @ X31)
% 0.61/0.84          | ~ (v1_relat_1 @ X30))),
% 0.61/0.84      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.61/0.84  thf('18', plain,
% 0.61/0.84      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.61/0.84      inference('sup-', [status(thm)], ['16', '17'])).
% 0.61/0.84  thf('19', plain,
% 0.61/0.84      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf(cc2_relat_1, axiom,
% 0.61/0.84    (![A:$i]:
% 0.61/0.84     ( ( v1_relat_1 @ A ) =>
% 0.61/0.84       ( ![B:$i]:
% 0.61/0.84         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.61/0.84  thf('20', plain,
% 0.61/0.84      (![X28 : $i, X29 : $i]:
% 0.61/0.84         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 0.61/0.84          | (v1_relat_1 @ X28)
% 0.61/0.84          | ~ (v1_relat_1 @ X29))),
% 0.61/0.84      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.61/0.84  thf('21', plain,
% 0.61/0.84      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)) | (v1_relat_1 @ sk_C_1))),
% 0.61/0.84      inference('sup-', [status(thm)], ['19', '20'])).
% 0.61/0.84  thf(fc6_relat_1, axiom,
% 0.61/0.84    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.61/0.84  thf('22', plain,
% 0.61/0.84      (![X33 : $i, X34 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X33 @ X34))),
% 0.61/0.84      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.61/0.84  thf('23', plain, ((v1_relat_1 @ sk_C_1)),
% 0.61/0.84      inference('demod', [status(thm)], ['21', '22'])).
% 0.61/0.84  thf('24', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_B_1)),
% 0.61/0.84      inference('demod', [status(thm)], ['18', '23'])).
% 0.61/0.84  thf(d3_tarski, axiom,
% 0.61/0.84    (![A:$i,B:$i]:
% 0.61/0.84     ( ( r1_tarski @ A @ B ) <=>
% 0.61/0.84       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.61/0.84  thf('25', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.84         (~ (r2_hidden @ X0 @ X1)
% 0.61/0.84          | (r2_hidden @ X0 @ X2)
% 0.61/0.84          | ~ (r1_tarski @ X1 @ X2))),
% 0.61/0.84      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.84  thf('26', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         ((r2_hidden @ X0 @ sk_B_1)
% 0.61/0.84          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['24', '25'])).
% 0.61/0.84  thf('27', plain,
% 0.61/0.84      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.61/0.84        | (r2_hidden @ (sk_B @ (k1_relat_1 @ sk_C_1)) @ sk_B_1))),
% 0.61/0.84      inference('sup-', [status(thm)], ['13', '26'])).
% 0.61/0.84  thf(t1_subset, axiom,
% 0.61/0.84    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.61/0.84  thf('28', plain,
% 0.61/0.84      (![X20 : $i, X21 : $i]:
% 0.61/0.84         ((m1_subset_1 @ X20 @ X21) | ~ (r2_hidden @ X20 @ X21))),
% 0.61/0.84      inference('cnf', [status(esa)], [t1_subset])).
% 0.61/0.84  thf('29', plain,
% 0.61/0.84      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.61/0.84        | (m1_subset_1 @ (sk_B @ (k1_relat_1 @ sk_C_1)) @ sk_B_1))),
% 0.61/0.84      inference('sup-', [status(thm)], ['27', '28'])).
% 0.61/0.84  thf('30', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.61/0.84      inference('clc', [status(thm)], ['12', '29'])).
% 0.61/0.84  thf('31', plain,
% 0.61/0.84      (![X30 : $i, X31 : $i]:
% 0.61/0.84         (~ (r1_tarski @ (k1_relat_1 @ X30) @ X31)
% 0.61/0.84          | (v4_relat_1 @ X30 @ X31)
% 0.61/0.84          | ~ (v1_relat_1 @ X30))),
% 0.61/0.84      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.61/0.84  thf('32', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.61/0.84          | ~ (v1_relat_1 @ sk_C_1)
% 0.61/0.84          | (v4_relat_1 @ sk_C_1 @ X0))),
% 0.61/0.84      inference('sup-', [status(thm)], ['30', '31'])).
% 0.61/0.84  thf('33', plain,
% 0.61/0.84      (![X1 : $i, X3 : $i]:
% 0.61/0.84         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.61/0.84      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.84  thf(t66_xboole_1, axiom,
% 0.61/0.84    (![A:$i]:
% 0.61/0.84     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.61/0.84       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.61/0.84  thf('34', plain,
% 0.61/0.84      (![X16 : $i]: ((r1_xboole_0 @ X16 @ X16) | ((X16) != (k1_xboole_0)))),
% 0.61/0.84      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.61/0.84  thf('35', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.61/0.84      inference('simplify', [status(thm)], ['34'])).
% 0.61/0.84  thf(d7_xboole_0, axiom,
% 0.61/0.84    (![A:$i,B:$i]:
% 0.61/0.84     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.61/0.84       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.61/0.84  thf('36', plain,
% 0.61/0.84      (![X4 : $i, X5 : $i]:
% 0.61/0.84         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.61/0.84      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.61/0.84  thf('37', plain,
% 0.61/0.84      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.61/0.84      inference('sup-', [status(thm)], ['35', '36'])).
% 0.61/0.84  thf(t17_xboole_1, axiom,
% 0.61/0.84    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.61/0.84  thf('38', plain,
% 0.61/0.84      (![X14 : $i, X15 : $i]: (r1_tarski @ (k3_xboole_0 @ X14 @ X15) @ X14)),
% 0.61/0.84      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.61/0.84  thf(t3_subset, axiom,
% 0.61/0.84    (![A:$i,B:$i]:
% 0.61/0.84     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.61/0.84  thf('39', plain,
% 0.61/0.84      (![X22 : $i, X24 : $i]:
% 0.61/0.84         ((m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X24)) | ~ (r1_tarski @ X22 @ X24))),
% 0.61/0.84      inference('cnf', [status(esa)], [t3_subset])).
% 0.61/0.84  thf('40', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i]:
% 0.61/0.84         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.61/0.84      inference('sup-', [status(thm)], ['38', '39'])).
% 0.61/0.84  thf(t5_subset, axiom,
% 0.61/0.84    (![A:$i,B:$i,C:$i]:
% 0.61/0.84     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.61/0.84          ( v1_xboole_0 @ C ) ) ))).
% 0.61/0.84  thf('41', plain,
% 0.61/0.84      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.61/0.84         (~ (r2_hidden @ X25 @ X26)
% 0.61/0.84          | ~ (v1_xboole_0 @ X27)
% 0.61/0.84          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 0.61/0.84      inference('cnf', [status(esa)], [t5_subset])).
% 0.61/0.84  thf('42', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.84         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['40', '41'])).
% 0.61/0.84  thf('43', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.61/0.84      inference('sup-', [status(thm)], ['37', '42'])).
% 0.61/0.84  thf('44', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.61/0.84      inference('simplify', [status(thm)], ['34'])).
% 0.61/0.84  thf(t69_xboole_1, axiom,
% 0.61/0.84    (![A:$i,B:$i]:
% 0.61/0.84     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.61/0.84       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.61/0.84  thf('45', plain,
% 0.61/0.84      (![X18 : $i, X19 : $i]:
% 0.61/0.84         (~ (r1_xboole_0 @ X18 @ X19)
% 0.61/0.84          | ~ (r1_tarski @ X18 @ X19)
% 0.61/0.84          | (v1_xboole_0 @ X18))),
% 0.61/0.84      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.61/0.84  thf('46', plain,
% 0.61/0.84      (((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0))),
% 0.61/0.84      inference('sup-', [status(thm)], ['44', '45'])).
% 0.61/0.84  thf(d10_xboole_0, axiom,
% 0.61/0.84    (![A:$i,B:$i]:
% 0.61/0.84     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.61/0.84  thf('47', plain,
% 0.61/0.84      (![X11 : $i, X12 : $i]: ((r1_tarski @ X11 @ X12) | ((X11) != (X12)))),
% 0.61/0.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.61/0.84  thf('48', plain, (![X12 : $i]: (r1_tarski @ X12 @ X12)),
% 0.61/0.84      inference('simplify', [status(thm)], ['47'])).
% 0.61/0.84  thf('49', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.61/0.84      inference('demod', [status(thm)], ['46', '48'])).
% 0.61/0.84  thf('50', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.61/0.84      inference('demod', [status(thm)], ['43', '49'])).
% 0.61/0.84  thf('51', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.61/0.84      inference('sup-', [status(thm)], ['33', '50'])).
% 0.61/0.84  thf('52', plain, ((v1_relat_1 @ sk_C_1)),
% 0.61/0.84      inference('demod', [status(thm)], ['21', '22'])).
% 0.61/0.84  thf('53', plain, (![X0 : $i]: (v4_relat_1 @ sk_C_1 @ X0)),
% 0.61/0.84      inference('demod', [status(thm)], ['32', '51', '52'])).
% 0.61/0.84  thf(t209_relat_1, axiom,
% 0.61/0.84    (![A:$i,B:$i]:
% 0.61/0.84     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.61/0.84       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.61/0.84  thf('54', plain,
% 0.61/0.84      (![X38 : $i, X39 : $i]:
% 0.61/0.84         (((X38) = (k7_relat_1 @ X38 @ X39))
% 0.61/0.84          | ~ (v4_relat_1 @ X38 @ X39)
% 0.61/0.84          | ~ (v1_relat_1 @ X38))),
% 0.61/0.84      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.61/0.84  thf('55', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         (~ (v1_relat_1 @ sk_C_1) | ((sk_C_1) = (k7_relat_1 @ sk_C_1 @ X0)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['53', '54'])).
% 0.61/0.84  thf('56', plain, ((v1_relat_1 @ sk_C_1)),
% 0.61/0.84      inference('demod', [status(thm)], ['21', '22'])).
% 0.61/0.84  thf('57', plain, (![X0 : $i]: ((sk_C_1) = (k7_relat_1 @ sk_C_1 @ X0))),
% 0.61/0.84      inference('demod', [status(thm)], ['55', '56'])).
% 0.61/0.84  thf('58', plain,
% 0.61/0.84      (![X14 : $i, X15 : $i]: (r1_tarski @ (k3_xboole_0 @ X14 @ X15) @ X14)),
% 0.61/0.84      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.61/0.84  thf('59', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.61/0.84      inference('sup-', [status(thm)], ['33', '50'])).
% 0.61/0.84  thf('60', plain,
% 0.61/0.84      (![X11 : $i, X13 : $i]:
% 0.61/0.84         (((X11) = (X13))
% 0.61/0.84          | ~ (r1_tarski @ X13 @ X11)
% 0.61/0.84          | ~ (r1_tarski @ X11 @ X13))),
% 0.61/0.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.61/0.84  thf('61', plain,
% 0.61/0.84      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['59', '60'])).
% 0.61/0.84  thf('62', plain,
% 0.61/0.84      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.61/0.84      inference('sup-', [status(thm)], ['58', '61'])).
% 0.61/0.84  thf('63', plain,
% 0.61/0.84      (![X4 : $i, X6 : $i]:
% 0.61/0.84         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 0.61/0.84      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.61/0.84  thf('64', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.61/0.84      inference('sup-', [status(thm)], ['62', '63'])).
% 0.61/0.84  thf('65', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.61/0.84      inference('simplify', [status(thm)], ['64'])).
% 0.61/0.84  thf(t207_relat_1, axiom,
% 0.61/0.84    (![A:$i,B:$i,C:$i]:
% 0.61/0.84     ( ( v1_relat_1 @ C ) =>
% 0.61/0.84       ( ( r1_xboole_0 @ A @ B ) =>
% 0.61/0.84         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.61/0.84  thf('66', plain,
% 0.61/0.84      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.61/0.84         (~ (r1_xboole_0 @ X35 @ X36)
% 0.61/0.84          | ~ (v1_relat_1 @ X37)
% 0.61/0.84          | ((k7_relat_1 @ (k7_relat_1 @ X37 @ X35) @ X36) = (k1_xboole_0)))),
% 0.61/0.84      inference('cnf', [status(esa)], [t207_relat_1])).
% 0.61/0.84  thf('67', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i]:
% 0.61/0.84         (((k7_relat_1 @ (k7_relat_1 @ X1 @ k1_xboole_0) @ X0) = (k1_xboole_0))
% 0.61/0.84          | ~ (v1_relat_1 @ X1))),
% 0.61/0.84      inference('sup-', [status(thm)], ['65', '66'])).
% 0.61/0.84  thf('68', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         (((k7_relat_1 @ sk_C_1 @ X0) = (k1_xboole_0))
% 0.61/0.84          | ~ (v1_relat_1 @ sk_C_1))),
% 0.61/0.84      inference('sup+', [status(thm)], ['57', '67'])).
% 0.61/0.84  thf('69', plain, (![X0 : $i]: ((sk_C_1) = (k7_relat_1 @ sk_C_1 @ X0))),
% 0.61/0.84      inference('demod', [status(thm)], ['55', '56'])).
% 0.61/0.84  thf('70', plain, ((v1_relat_1 @ sk_C_1)),
% 0.61/0.84      inference('demod', [status(thm)], ['21', '22'])).
% 0.61/0.84  thf('71', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.61/0.84      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.61/0.84  thf('72', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.61/0.84      inference('demod', [status(thm)], ['46', '48'])).
% 0.61/0.84  thf(fc11_relat_1, axiom,
% 0.61/0.84    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 0.61/0.84  thf('73', plain,
% 0.61/0.84      (![X32 : $i]:
% 0.61/0.84         ((v1_xboole_0 @ (k2_relat_1 @ X32)) | ~ (v1_xboole_0 @ X32))),
% 0.61/0.84      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.61/0.84  thf(l13_xboole_0, axiom,
% 0.61/0.84    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.61/0.84  thf('74', plain,
% 0.61/0.84      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.61/0.84      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.61/0.84  thf('75', plain,
% 0.61/0.84      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['73', '74'])).
% 0.61/0.84  thf('76', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.61/0.84      inference('sup-', [status(thm)], ['72', '75'])).
% 0.61/0.84  thf('77', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.61/0.84      inference('demod', [status(thm)], ['4', '71', '76'])).
% 0.61/0.84  thf('78', plain, ($false), inference('simplify', [status(thm)], ['77'])).
% 0.61/0.84  
% 0.61/0.84  % SZS output end Refutation
% 0.61/0.84  
% 0.61/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
