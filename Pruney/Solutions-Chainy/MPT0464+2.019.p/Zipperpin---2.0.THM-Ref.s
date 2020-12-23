%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.adGim8VXqr

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:11 EST 2020

% Result     : Theorem 2.46s
% Output     : Refutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 108 expanded)
%              Number of leaves         :   29 (  45 expanded)
%              Depth                    :   14
%              Number of atoms          :  648 ( 994 expanded)
%              Number of equality atoms :   21 (  37 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X7 @ X7 @ X8 @ X9 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
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

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ D @ C @ B @ A )
    <=> ( ( F != A )
        & ( F != B )
        & ( F != C )
        & ( F != D ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 @ X24 )
      | ( r2_hidden @ X20 @ X25 )
      | ( X25
       != ( k2_enumset1 @ X24 @ X23 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('3',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X20 @ ( k2_enumset1 @ X24 @ X23 @ X22 @ X21 ) )
      | ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X15 != X16 )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    ! [X14: $i,X16: $i,X17: $i,X18: $i] :
      ~ ( zip_tseitin_0 @ X16 @ X16 @ X17 @ X18 @ X14 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('9',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X33 ) @ X34 )
      | ~ ( r2_hidden @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X30: $i,X32: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( r1_tarski @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('13',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ( v1_relat_1 @ X35 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t48_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( r1_tarski @ A @ B )
               => ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ~ ( r1_tarski @ X38 @ X37 )
      | ( r1_tarski @ ( k5_relat_1 @ X39 @ X38 ) @ ( k5_relat_1 @ X39 @ X37 ) )
      | ~ ( v1_relat_1 @ X39 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t48_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X30: $i,X32: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( r1_tarski @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ( v1_relat_1 @ X35 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('28',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ~ ( r1_tarski @ X38 @ X37 )
      | ( r1_tarski @ ( k5_relat_1 @ X39 @ X38 ) @ ( k5_relat_1 @ X39 @ X37 ) )
      | ~ ( v1_relat_1 @ X39 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t48_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('33',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('34',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) ) )
      | ~ ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf(t52_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( r1_tarski @ ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ! [C: $i] :
                ( ( v1_relat_1 @ C )
               => ( r1_tarski @ ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_relat_1])).

thf('38',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('40',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('41',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_A @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ sk_C ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('44',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('45',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['42','43','44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.adGim8VXqr
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:06:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 2.46/2.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.46/2.64  % Solved by: fo/fo7.sh
% 2.46/2.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.46/2.64  % done 3738 iterations in 2.180s
% 2.46/2.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.46/2.64  % SZS output start Refutation
% 2.46/2.64  thf(sk_C_type, type, sk_C: $i).
% 2.46/2.64  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 2.46/2.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.46/2.64  thf(sk_A_type, type, sk_A: $i).
% 2.46/2.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.46/2.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.46/2.64  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 2.46/2.64  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.46/2.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.46/2.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.46/2.64  thf(sk_B_type, type, sk_B: $i).
% 2.46/2.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.46/2.64  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 2.46/2.64  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 2.46/2.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.46/2.64  thf(t70_enumset1, axiom,
% 2.46/2.64    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 2.46/2.64  thf('0', plain,
% 2.46/2.64      (![X5 : $i, X6 : $i]:
% 2.46/2.64         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 2.46/2.64      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.46/2.64  thf(t71_enumset1, axiom,
% 2.46/2.64    (![A:$i,B:$i,C:$i]:
% 2.46/2.64     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 2.46/2.64  thf('1', plain,
% 2.46/2.64      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.46/2.64         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 2.46/2.64      inference('cnf', [status(esa)], [t71_enumset1])).
% 2.46/2.64  thf(d2_enumset1, axiom,
% 2.46/2.64    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 2.46/2.64     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 2.46/2.64       ( ![F:$i]:
% 2.46/2.64         ( ( r2_hidden @ F @ E ) <=>
% 2.46/2.64           ( ~( ( ( F ) != ( D ) ) & ( ( F ) != ( C ) ) & ( ( F ) != ( B ) ) & 
% 2.46/2.64                ( ( F ) != ( A ) ) ) ) ) ) ))).
% 2.46/2.64  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 2.46/2.64  thf(zf_stmt_1, axiom,
% 2.46/2.64    (![F:$i,D:$i,C:$i,B:$i,A:$i]:
% 2.46/2.64     ( ( zip_tseitin_0 @ F @ D @ C @ B @ A ) <=>
% 2.46/2.64       ( ( ( F ) != ( A ) ) & ( ( F ) != ( B ) ) & ( ( F ) != ( C ) ) & 
% 2.46/2.64         ( ( F ) != ( D ) ) ) ))).
% 2.46/2.64  thf(zf_stmt_2, axiom,
% 2.46/2.64    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 2.46/2.64     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 2.46/2.64       ( ![F:$i]:
% 2.46/2.64         ( ( r2_hidden @ F @ E ) <=> ( ~( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) ) ))).
% 2.46/2.64  thf('2', plain,
% 2.46/2.64      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 2.46/2.64         ((zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 @ X24)
% 2.46/2.64          | (r2_hidden @ X20 @ X25)
% 2.46/2.64          | ((X25) != (k2_enumset1 @ X24 @ X23 @ X22 @ X21)))),
% 2.46/2.64      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.46/2.64  thf('3', plain,
% 2.46/2.64      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 2.46/2.64         ((r2_hidden @ X20 @ (k2_enumset1 @ X24 @ X23 @ X22 @ X21))
% 2.46/2.64          | (zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 @ X24))),
% 2.46/2.64      inference('simplify', [status(thm)], ['2'])).
% 2.46/2.64  thf('4', plain,
% 2.46/2.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.46/2.64         ((r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 2.46/2.64          | (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2))),
% 2.46/2.64      inference('sup+', [status(thm)], ['1', '3'])).
% 2.46/2.64  thf('5', plain,
% 2.46/2.64      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 2.46/2.64         (((X15) != (X16)) | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 @ X14))),
% 2.46/2.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.46/2.64  thf('6', plain,
% 2.46/2.64      (![X14 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 2.46/2.64         ~ (zip_tseitin_0 @ X16 @ X16 @ X17 @ X18 @ X14)),
% 2.46/2.64      inference('simplify', [status(thm)], ['5'])).
% 2.46/2.64  thf('7', plain,
% 2.46/2.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.46/2.64         (r2_hidden @ X2 @ (k1_enumset1 @ X0 @ X1 @ X2))),
% 2.46/2.64      inference('sup-', [status(thm)], ['4', '6'])).
% 2.46/2.64  thf('8', plain,
% 2.46/2.64      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 2.46/2.64      inference('sup+', [status(thm)], ['0', '7'])).
% 2.46/2.64  thf(t4_setfam_1, axiom,
% 2.46/2.64    (![A:$i,B:$i]:
% 2.46/2.64     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 2.46/2.64  thf('9', plain,
% 2.46/2.64      (![X33 : $i, X34 : $i]:
% 2.46/2.64         ((r1_tarski @ (k1_setfam_1 @ X33) @ X34) | ~ (r2_hidden @ X34 @ X33))),
% 2.46/2.64      inference('cnf', [status(esa)], [t4_setfam_1])).
% 2.46/2.64  thf('10', plain,
% 2.46/2.64      (![X0 : $i, X1 : $i]:
% 2.46/2.64         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 2.46/2.64      inference('sup-', [status(thm)], ['8', '9'])).
% 2.46/2.64  thf(t3_subset, axiom,
% 2.46/2.64    (![A:$i,B:$i]:
% 2.46/2.64     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.46/2.64  thf('11', plain,
% 2.46/2.64      (![X30 : $i, X32 : $i]:
% 2.46/2.64         ((m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X32)) | ~ (r1_tarski @ X30 @ X32))),
% 2.46/2.64      inference('cnf', [status(esa)], [t3_subset])).
% 2.46/2.64  thf('12', plain,
% 2.46/2.64      (![X0 : $i, X1 : $i]:
% 2.46/2.64         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 2.46/2.64          (k1_zfmisc_1 @ X0))),
% 2.46/2.64      inference('sup-', [status(thm)], ['10', '11'])).
% 2.46/2.64  thf(cc2_relat_1, axiom,
% 2.46/2.64    (![A:$i]:
% 2.46/2.64     ( ( v1_relat_1 @ A ) =>
% 2.46/2.64       ( ![B:$i]:
% 2.46/2.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.46/2.64  thf('13', plain,
% 2.46/2.64      (![X35 : $i, X36 : $i]:
% 2.46/2.64         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 2.46/2.64          | (v1_relat_1 @ X35)
% 2.46/2.64          | ~ (v1_relat_1 @ X36))),
% 2.46/2.64      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.46/2.64  thf('14', plain,
% 2.46/2.64      (![X0 : $i, X1 : $i]:
% 2.46/2.64         (~ (v1_relat_1 @ X0)
% 2.46/2.64          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 2.46/2.64      inference('sup-', [status(thm)], ['12', '13'])).
% 2.46/2.64  thf('15', plain,
% 2.46/2.64      (![X0 : $i, X1 : $i]:
% 2.46/2.64         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 2.46/2.64      inference('sup-', [status(thm)], ['8', '9'])).
% 2.46/2.64  thf(t48_relat_1, axiom,
% 2.46/2.64    (![A:$i]:
% 2.46/2.64     ( ( v1_relat_1 @ A ) =>
% 2.46/2.64       ( ![B:$i]:
% 2.46/2.64         ( ( v1_relat_1 @ B ) =>
% 2.46/2.64           ( ![C:$i]:
% 2.46/2.64             ( ( v1_relat_1 @ C ) =>
% 2.46/2.64               ( ( r1_tarski @ A @ B ) =>
% 2.46/2.64                 ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ) ))).
% 2.46/2.64  thf('16', plain,
% 2.46/2.64      (![X37 : $i, X38 : $i, X39 : $i]:
% 2.46/2.64         (~ (v1_relat_1 @ X37)
% 2.46/2.64          | ~ (r1_tarski @ X38 @ X37)
% 2.46/2.64          | (r1_tarski @ (k5_relat_1 @ X39 @ X38) @ (k5_relat_1 @ X39 @ X37))
% 2.46/2.64          | ~ (v1_relat_1 @ X39)
% 2.46/2.64          | ~ (v1_relat_1 @ X38))),
% 2.46/2.64      inference('cnf', [status(esa)], [t48_relat_1])).
% 2.46/2.64  thf('17', plain,
% 2.46/2.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.46/2.64         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 2.46/2.64          | ~ (v1_relat_1 @ X2)
% 2.46/2.64          | (r1_tarski @ 
% 2.46/2.64             (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 2.46/2.64             (k5_relat_1 @ X2 @ X0))
% 2.46/2.64          | ~ (v1_relat_1 @ X0))),
% 2.46/2.64      inference('sup-', [status(thm)], ['15', '16'])).
% 2.46/2.64  thf('18', plain,
% 2.46/2.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.46/2.64         (~ (v1_relat_1 @ X0)
% 2.46/2.64          | ~ (v1_relat_1 @ X0)
% 2.46/2.64          | (r1_tarski @ 
% 2.46/2.64             (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 2.46/2.64             (k5_relat_1 @ X2 @ X0))
% 2.46/2.64          | ~ (v1_relat_1 @ X2))),
% 2.46/2.64      inference('sup-', [status(thm)], ['14', '17'])).
% 2.46/2.64  thf('19', plain,
% 2.46/2.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.46/2.64         (~ (v1_relat_1 @ X2)
% 2.46/2.64          | (r1_tarski @ 
% 2.46/2.64             (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 2.46/2.64             (k5_relat_1 @ X2 @ X0))
% 2.46/2.64          | ~ (v1_relat_1 @ X0))),
% 2.46/2.64      inference('simplify', [status(thm)], ['18'])).
% 2.46/2.64  thf(t17_xboole_1, axiom,
% 2.46/2.64    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 2.46/2.64  thf('20', plain,
% 2.46/2.64      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 2.46/2.64      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.46/2.64  thf(t12_setfam_1, axiom,
% 2.46/2.64    (![A:$i,B:$i]:
% 2.46/2.64     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.46/2.64  thf('21', plain,
% 2.46/2.64      (![X28 : $i, X29 : $i]:
% 2.46/2.64         ((k1_setfam_1 @ (k2_tarski @ X28 @ X29)) = (k3_xboole_0 @ X28 @ X29))),
% 2.46/2.64      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.46/2.64  thf('22', plain,
% 2.46/2.64      (![X0 : $i, X1 : $i]:
% 2.46/2.64         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 2.46/2.64      inference('demod', [status(thm)], ['20', '21'])).
% 2.46/2.64  thf('23', plain,
% 2.46/2.64      (![X30 : $i, X32 : $i]:
% 2.46/2.64         ((m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X32)) | ~ (r1_tarski @ X30 @ X32))),
% 2.46/2.64      inference('cnf', [status(esa)], [t3_subset])).
% 2.46/2.64  thf('24', plain,
% 2.46/2.64      (![X0 : $i, X1 : $i]:
% 2.46/2.64         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 2.46/2.64          (k1_zfmisc_1 @ X0))),
% 2.46/2.64      inference('sup-', [status(thm)], ['22', '23'])).
% 2.46/2.64  thf('25', plain,
% 2.46/2.64      (![X35 : $i, X36 : $i]:
% 2.46/2.64         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 2.46/2.64          | (v1_relat_1 @ X35)
% 2.46/2.64          | ~ (v1_relat_1 @ X36))),
% 2.46/2.64      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.46/2.64  thf('26', plain,
% 2.46/2.64      (![X0 : $i, X1 : $i]:
% 2.46/2.64         (~ (v1_relat_1 @ X0)
% 2.46/2.64          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 2.46/2.64      inference('sup-', [status(thm)], ['24', '25'])).
% 2.46/2.64  thf('27', plain,
% 2.46/2.64      (![X0 : $i, X1 : $i]:
% 2.46/2.64         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 2.46/2.64      inference('demod', [status(thm)], ['20', '21'])).
% 2.46/2.64  thf('28', plain,
% 2.46/2.64      (![X37 : $i, X38 : $i, X39 : $i]:
% 2.46/2.64         (~ (v1_relat_1 @ X37)
% 2.46/2.64          | ~ (r1_tarski @ X38 @ X37)
% 2.46/2.64          | (r1_tarski @ (k5_relat_1 @ X39 @ X38) @ (k5_relat_1 @ X39 @ X37))
% 2.46/2.64          | ~ (v1_relat_1 @ X39)
% 2.46/2.64          | ~ (v1_relat_1 @ X38))),
% 2.46/2.64      inference('cnf', [status(esa)], [t48_relat_1])).
% 2.46/2.64  thf('29', plain,
% 2.46/2.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.46/2.64         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 2.46/2.64          | ~ (v1_relat_1 @ X2)
% 2.46/2.64          | (r1_tarski @ 
% 2.46/2.64             (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 2.46/2.64             (k5_relat_1 @ X2 @ X0))
% 2.46/2.64          | ~ (v1_relat_1 @ X0))),
% 2.46/2.64      inference('sup-', [status(thm)], ['27', '28'])).
% 2.46/2.64  thf('30', plain,
% 2.46/2.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.46/2.64         (~ (v1_relat_1 @ X1)
% 2.46/2.64          | ~ (v1_relat_1 @ X1)
% 2.46/2.64          | (r1_tarski @ 
% 2.46/2.64             (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 2.46/2.64             (k5_relat_1 @ X2 @ X1))
% 2.46/2.64          | ~ (v1_relat_1 @ X2))),
% 2.46/2.64      inference('sup-', [status(thm)], ['26', '29'])).
% 2.46/2.64  thf('31', plain,
% 2.46/2.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.46/2.64         (~ (v1_relat_1 @ X2)
% 2.46/2.64          | (r1_tarski @ 
% 2.46/2.64             (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 2.46/2.64             (k5_relat_1 @ X2 @ X1))
% 2.46/2.64          | ~ (v1_relat_1 @ X1))),
% 2.46/2.64      inference('simplify', [status(thm)], ['30'])).
% 2.46/2.64  thf(t19_xboole_1, axiom,
% 2.46/2.64    (![A:$i,B:$i,C:$i]:
% 2.46/2.64     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 2.46/2.64       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 2.46/2.64  thf('32', plain,
% 2.46/2.64      (![X2 : $i, X3 : $i, X4 : $i]:
% 2.46/2.64         (~ (r1_tarski @ X2 @ X3)
% 2.46/2.64          | ~ (r1_tarski @ X2 @ X4)
% 2.46/2.64          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 2.46/2.64      inference('cnf', [status(esa)], [t19_xboole_1])).
% 2.46/2.64  thf('33', plain,
% 2.46/2.64      (![X28 : $i, X29 : $i]:
% 2.46/2.64         ((k1_setfam_1 @ (k2_tarski @ X28 @ X29)) = (k3_xboole_0 @ X28 @ X29))),
% 2.46/2.64      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.46/2.64  thf('34', plain,
% 2.46/2.64      (![X2 : $i, X3 : $i, X4 : $i]:
% 2.46/2.64         (~ (r1_tarski @ X2 @ X3)
% 2.46/2.64          | ~ (r1_tarski @ X2 @ X4)
% 2.46/2.64          | (r1_tarski @ X2 @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4))))),
% 2.46/2.64      inference('demod', [status(thm)], ['32', '33'])).
% 2.46/2.64  thf('35', plain,
% 2.46/2.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.46/2.64         (~ (v1_relat_1 @ X0)
% 2.46/2.64          | ~ (v1_relat_1 @ X1)
% 2.46/2.64          | (r1_tarski @ 
% 2.46/2.64             (k5_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X2))) @ 
% 2.46/2.64             (k1_setfam_1 @ (k2_tarski @ (k5_relat_1 @ X1 @ X0) @ X3)))
% 2.46/2.64          | ~ (r1_tarski @ 
% 2.46/2.64               (k5_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X2))) @ X3))),
% 2.46/2.64      inference('sup-', [status(thm)], ['31', '34'])).
% 2.46/2.64  thf('36', plain,
% 2.46/2.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.46/2.64         (~ (v1_relat_1 @ X0)
% 2.46/2.64          | ~ (v1_relat_1 @ X1)
% 2.46/2.64          | (r1_tarski @ 
% 2.46/2.64             (k5_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X0))) @ 
% 2.46/2.64             (k1_setfam_1 @ 
% 2.46/2.64              (k2_tarski @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0))))
% 2.46/2.64          | ~ (v1_relat_1 @ X1)
% 2.46/2.64          | ~ (v1_relat_1 @ X2))),
% 2.46/2.64      inference('sup-', [status(thm)], ['19', '35'])).
% 2.46/2.64  thf('37', plain,
% 2.46/2.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.46/2.64         (~ (v1_relat_1 @ X2)
% 2.46/2.64          | (r1_tarski @ 
% 2.46/2.64             (k5_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X0))) @ 
% 2.46/2.64             (k1_setfam_1 @ 
% 2.46/2.64              (k2_tarski @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0))))
% 2.46/2.64          | ~ (v1_relat_1 @ X1)
% 2.46/2.64          | ~ (v1_relat_1 @ X0))),
% 2.46/2.64      inference('simplify', [status(thm)], ['36'])).
% 2.46/2.64  thf(t52_relat_1, conjecture,
% 2.46/2.64    (![A:$i]:
% 2.46/2.64     ( ( v1_relat_1 @ A ) =>
% 2.46/2.64       ( ![B:$i]:
% 2.46/2.64         ( ( v1_relat_1 @ B ) =>
% 2.46/2.64           ( ![C:$i]:
% 2.46/2.64             ( ( v1_relat_1 @ C ) =>
% 2.46/2.64               ( r1_tarski @
% 2.46/2.64                 ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 2.46/2.64                 ( k3_xboole_0 @
% 2.46/2.64                   ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ))).
% 2.46/2.64  thf(zf_stmt_3, negated_conjecture,
% 2.46/2.64    (~( ![A:$i]:
% 2.46/2.64        ( ( v1_relat_1 @ A ) =>
% 2.46/2.64          ( ![B:$i]:
% 2.46/2.64            ( ( v1_relat_1 @ B ) =>
% 2.46/2.64              ( ![C:$i]:
% 2.46/2.64                ( ( v1_relat_1 @ C ) =>
% 2.46/2.64                  ( r1_tarski @
% 2.46/2.64                    ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 2.46/2.64                    ( k3_xboole_0 @
% 2.46/2.64                      ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 2.46/2.64    inference('cnf.neg', [status(esa)], [t52_relat_1])).
% 2.46/2.64  thf('38', plain,
% 2.46/2.64      (~ (r1_tarski @ (k5_relat_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 2.46/2.64          (k3_xboole_0 @ (k5_relat_1 @ sk_A @ sk_B) @ 
% 2.46/2.64           (k5_relat_1 @ sk_A @ sk_C)))),
% 2.46/2.64      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.46/2.64  thf('39', plain,
% 2.46/2.64      (![X28 : $i, X29 : $i]:
% 2.46/2.64         ((k1_setfam_1 @ (k2_tarski @ X28 @ X29)) = (k3_xboole_0 @ X28 @ X29))),
% 2.46/2.64      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.46/2.64  thf('40', plain,
% 2.46/2.64      (![X28 : $i, X29 : $i]:
% 2.46/2.64         ((k1_setfam_1 @ (k2_tarski @ X28 @ X29)) = (k3_xboole_0 @ X28 @ X29))),
% 2.46/2.64      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.46/2.64  thf('41', plain,
% 2.46/2.64      (~ (r1_tarski @ 
% 2.46/2.64          (k5_relat_1 @ sk_A @ (k1_setfam_1 @ (k2_tarski @ sk_B @ sk_C))) @ 
% 2.46/2.64          (k1_setfam_1 @ 
% 2.46/2.64           (k2_tarski @ (k5_relat_1 @ sk_A @ sk_B) @ (k5_relat_1 @ sk_A @ sk_C))))),
% 2.46/2.64      inference('demod', [status(thm)], ['38', '39', '40'])).
% 2.46/2.64  thf('42', plain,
% 2.46/2.64      ((~ (v1_relat_1 @ sk_C) | ~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 2.46/2.64      inference('sup-', [status(thm)], ['37', '41'])).
% 2.46/2.64  thf('43', plain, ((v1_relat_1 @ sk_C)),
% 2.46/2.64      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.46/2.64  thf('44', plain, ((v1_relat_1 @ sk_A)),
% 2.46/2.64      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.46/2.64  thf('45', plain, ((v1_relat_1 @ sk_B)),
% 2.46/2.64      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.46/2.64  thf('46', plain, ($false),
% 2.46/2.64      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 2.46/2.64  
% 2.46/2.64  % SZS output end Refutation
% 2.46/2.64  
% 2.46/2.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
