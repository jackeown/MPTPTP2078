%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mC8p6vwc8Z

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:10 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 101 expanded)
%              Number of leaves         :   27 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :  604 ( 910 expanded)
%              Number of equality atoms :   17 (  30 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 )
      | ( r2_hidden @ X10 @ X14 )
      | ( X14
       != ( k1_enumset1 @ X13 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X10 @ ( k1_enumset1 @ X13 @ X12 @ X11 ) )
      | ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6 != X7 )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ~ ( zip_tseitin_0 @ X7 @ X7 @ X8 @ X5 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('7',plain,(
    ! [X49: $i,X50: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X49 ) @ X50 )
      | ~ ( r2_hidden @ X50 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X46: $i,X48: $i] :
      ( ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X48 ) )
      | ~ ( r1_tarski @ X46 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X52 ) )
      | ( v1_relat_1 @ X51 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t48_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( r1_tarski @ A @ B )
               => ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( v1_relat_1 @ X53 )
      | ~ ( r1_tarski @ X54 @ X53 )
      | ( r1_tarski @ ( k5_relat_1 @ X55 @ X54 ) @ ( k5_relat_1 @ X55 @ X53 ) )
      | ~ ( v1_relat_1 @ X55 )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t48_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X44 @ X45 ) )
      = ( k3_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X46: $i,X48: $i] :
      ( ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X48 ) )
      | ~ ( r1_tarski @ X46 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X52 ) )
      | ( v1_relat_1 @ X51 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('26',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( v1_relat_1 @ X53 )
      | ~ ( r1_tarski @ X54 @ X53 )
      | ( r1_tarski @ ( k5_relat_1 @ X55 @ X54 ) @ ( k5_relat_1 @ X55 @ X53 ) )
      | ~ ( v1_relat_1 @ X55 )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t48_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('31',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X44 @ X45 ) )
      = ( k3_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('32',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) ) )
      | ~ ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

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

thf('36',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('37',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X44 @ X45 ) )
      = ( k3_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('38',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X44 @ X45 ) )
      = ( k3_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('39',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_A @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ sk_C ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('42',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('43',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['40','41','42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mC8p6vwc8Z
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:15:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.48/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.69  % Solved by: fo/fo7.sh
% 0.48/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.69  % done 394 iterations in 0.240s
% 0.48/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.69  % SZS output start Refutation
% 0.48/0.69  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.48/0.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.48/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.48/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.69  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.48/0.69  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.48/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.69  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.48/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.69  thf(sk_C_type, type, sk_C: $i).
% 0.48/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.48/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.69  thf(t70_enumset1, axiom,
% 0.48/0.69    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.48/0.69  thf('0', plain,
% 0.48/0.69      (![X17 : $i, X18 : $i]:
% 0.48/0.69         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.48/0.69      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.48/0.69  thf(d1_enumset1, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.69     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.48/0.69       ( ![E:$i]:
% 0.48/0.69         ( ( r2_hidden @ E @ D ) <=>
% 0.48/0.69           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.48/0.69  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.48/0.69  thf(zf_stmt_1, axiom,
% 0.48/0.69    (![E:$i,C:$i,B:$i,A:$i]:
% 0.48/0.69     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.48/0.69       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.48/0.69  thf(zf_stmt_2, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.69     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.48/0.69       ( ![E:$i]:
% 0.48/0.69         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.48/0.69  thf('1', plain,
% 0.48/0.69      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.48/0.69         ((zip_tseitin_0 @ X10 @ X11 @ X12 @ X13)
% 0.48/0.69          | (r2_hidden @ X10 @ X14)
% 0.48/0.69          | ((X14) != (k1_enumset1 @ X13 @ X12 @ X11)))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.48/0.69  thf('2', plain,
% 0.48/0.69      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.48/0.69         ((r2_hidden @ X10 @ (k1_enumset1 @ X13 @ X12 @ X11))
% 0.48/0.69          | (zip_tseitin_0 @ X10 @ X11 @ X12 @ X13))),
% 0.48/0.69      inference('simplify', [status(thm)], ['1'])).
% 0.48/0.69  thf('3', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.69         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.48/0.69          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.48/0.69      inference('sup+', [status(thm)], ['0', '2'])).
% 0.48/0.69  thf('4', plain,
% 0.48/0.69      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.48/0.69         (((X6) != (X7)) | ~ (zip_tseitin_0 @ X6 @ X7 @ X8 @ X5))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.48/0.69  thf('5', plain,
% 0.48/0.69      (![X5 : $i, X7 : $i, X8 : $i]: ~ (zip_tseitin_0 @ X7 @ X7 @ X8 @ X5)),
% 0.48/0.69      inference('simplify', [status(thm)], ['4'])).
% 0.48/0.69  thf('6', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.48/0.69      inference('sup-', [status(thm)], ['3', '5'])).
% 0.48/0.69  thf(t4_setfam_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.48/0.69  thf('7', plain,
% 0.48/0.69      (![X49 : $i, X50 : $i]:
% 0.48/0.69         ((r1_tarski @ (k1_setfam_1 @ X49) @ X50) | ~ (r2_hidden @ X50 @ X49))),
% 0.48/0.69      inference('cnf', [status(esa)], [t4_setfam_1])).
% 0.48/0.69  thf('8', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.48/0.69      inference('sup-', [status(thm)], ['6', '7'])).
% 0.48/0.69  thf(t3_subset, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.48/0.69  thf('9', plain,
% 0.48/0.69      (![X46 : $i, X48 : $i]:
% 0.48/0.69         ((m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X48)) | ~ (r1_tarski @ X46 @ X48))),
% 0.48/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.69  thf('10', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 0.48/0.69          (k1_zfmisc_1 @ X0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['8', '9'])).
% 0.48/0.69  thf(cc2_relat_1, axiom,
% 0.48/0.69    (![A:$i]:
% 0.48/0.69     ( ( v1_relat_1 @ A ) =>
% 0.48/0.69       ( ![B:$i]:
% 0.48/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.48/0.69  thf('11', plain,
% 0.48/0.69      (![X51 : $i, X52 : $i]:
% 0.48/0.69         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ X52))
% 0.48/0.69          | (v1_relat_1 @ X51)
% 0.48/0.69          | ~ (v1_relat_1 @ X52))),
% 0.48/0.69      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.48/0.69  thf('12', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         (~ (v1_relat_1 @ X0)
% 0.48/0.69          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.48/0.69      inference('sup-', [status(thm)], ['10', '11'])).
% 0.48/0.69  thf('13', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.48/0.69      inference('sup-', [status(thm)], ['6', '7'])).
% 0.48/0.69  thf(t48_relat_1, axiom,
% 0.48/0.69    (![A:$i]:
% 0.48/0.69     ( ( v1_relat_1 @ A ) =>
% 0.48/0.69       ( ![B:$i]:
% 0.48/0.69         ( ( v1_relat_1 @ B ) =>
% 0.48/0.69           ( ![C:$i]:
% 0.48/0.69             ( ( v1_relat_1 @ C ) =>
% 0.48/0.69               ( ( r1_tarski @ A @ B ) =>
% 0.48/0.69                 ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ) ))).
% 0.48/0.69  thf('14', plain,
% 0.48/0.69      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.48/0.69         (~ (v1_relat_1 @ X53)
% 0.48/0.69          | ~ (r1_tarski @ X54 @ X53)
% 0.48/0.69          | (r1_tarski @ (k5_relat_1 @ X55 @ X54) @ (k5_relat_1 @ X55 @ X53))
% 0.48/0.69          | ~ (v1_relat_1 @ X55)
% 0.48/0.69          | ~ (v1_relat_1 @ X54))),
% 0.48/0.69      inference('cnf', [status(esa)], [t48_relat_1])).
% 0.48/0.69  thf('15', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.69         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.48/0.69          | ~ (v1_relat_1 @ X2)
% 0.48/0.69          | (r1_tarski @ 
% 0.48/0.69             (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.48/0.69             (k5_relat_1 @ X2 @ X0))
% 0.48/0.69          | ~ (v1_relat_1 @ X0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['13', '14'])).
% 0.48/0.69  thf('16', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.69         (~ (v1_relat_1 @ X0)
% 0.48/0.69          | ~ (v1_relat_1 @ X0)
% 0.48/0.69          | (r1_tarski @ 
% 0.48/0.69             (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.48/0.69             (k5_relat_1 @ X2 @ X0))
% 0.48/0.69          | ~ (v1_relat_1 @ X2))),
% 0.48/0.69      inference('sup-', [status(thm)], ['12', '15'])).
% 0.48/0.69  thf('17', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.69         (~ (v1_relat_1 @ X2)
% 0.48/0.69          | (r1_tarski @ 
% 0.48/0.69             (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.48/0.69             (k5_relat_1 @ X2 @ X0))
% 0.48/0.69          | ~ (v1_relat_1 @ X0))),
% 0.48/0.69      inference('simplify', [status(thm)], ['16'])).
% 0.48/0.69  thf(t17_xboole_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.48/0.69  thf('18', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.48/0.69      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.48/0.69  thf(t12_setfam_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.48/0.69  thf('19', plain,
% 0.48/0.69      (![X44 : $i, X45 : $i]:
% 0.48/0.69         ((k1_setfam_1 @ (k2_tarski @ X44 @ X45)) = (k3_xboole_0 @ X44 @ X45))),
% 0.48/0.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.48/0.69  thf('20', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 0.48/0.69      inference('demod', [status(thm)], ['18', '19'])).
% 0.48/0.69  thf('21', plain,
% 0.48/0.69      (![X46 : $i, X48 : $i]:
% 0.48/0.69         ((m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X48)) | ~ (r1_tarski @ X46 @ X48))),
% 0.48/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.69  thf('22', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 0.48/0.69          (k1_zfmisc_1 @ X0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['20', '21'])).
% 0.48/0.69  thf('23', plain,
% 0.48/0.69      (![X51 : $i, X52 : $i]:
% 0.48/0.69         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ X52))
% 0.48/0.69          | (v1_relat_1 @ X51)
% 0.48/0.69          | ~ (v1_relat_1 @ X52))),
% 0.48/0.69      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.48/0.69  thf('24', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         (~ (v1_relat_1 @ X0)
% 0.48/0.69          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 0.48/0.69      inference('sup-', [status(thm)], ['22', '23'])).
% 0.48/0.69  thf('25', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 0.48/0.69      inference('demod', [status(thm)], ['18', '19'])).
% 0.48/0.69  thf('26', plain,
% 0.48/0.69      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.48/0.69         (~ (v1_relat_1 @ X53)
% 0.48/0.69          | ~ (r1_tarski @ X54 @ X53)
% 0.48/0.69          | (r1_tarski @ (k5_relat_1 @ X55 @ X54) @ (k5_relat_1 @ X55 @ X53))
% 0.48/0.69          | ~ (v1_relat_1 @ X55)
% 0.48/0.69          | ~ (v1_relat_1 @ X54))),
% 0.48/0.69      inference('cnf', [status(esa)], [t48_relat_1])).
% 0.48/0.69  thf('27', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.69         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 0.48/0.69          | ~ (v1_relat_1 @ X2)
% 0.48/0.69          | (r1_tarski @ 
% 0.48/0.69             (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.48/0.69             (k5_relat_1 @ X2 @ X0))
% 0.48/0.69          | ~ (v1_relat_1 @ X0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['25', '26'])).
% 0.48/0.69  thf('28', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.69         (~ (v1_relat_1 @ X1)
% 0.48/0.69          | ~ (v1_relat_1 @ X1)
% 0.48/0.69          | (r1_tarski @ 
% 0.48/0.69             (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.48/0.69             (k5_relat_1 @ X2 @ X1))
% 0.48/0.69          | ~ (v1_relat_1 @ X2))),
% 0.48/0.69      inference('sup-', [status(thm)], ['24', '27'])).
% 0.48/0.69  thf('29', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.69         (~ (v1_relat_1 @ X2)
% 0.48/0.69          | (r1_tarski @ 
% 0.48/0.69             (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.48/0.69             (k5_relat_1 @ X2 @ X1))
% 0.48/0.69          | ~ (v1_relat_1 @ X1))),
% 0.48/0.69      inference('simplify', [status(thm)], ['28'])).
% 0.48/0.69  thf(t19_xboole_1, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i]:
% 0.48/0.69     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.48/0.69       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.48/0.69  thf('30', plain,
% 0.48/0.69      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.48/0.69         (~ (r1_tarski @ X2 @ X3)
% 0.48/0.69          | ~ (r1_tarski @ X2 @ X4)
% 0.48/0.69          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.48/0.69      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.48/0.69  thf('31', plain,
% 0.48/0.69      (![X44 : $i, X45 : $i]:
% 0.48/0.69         ((k1_setfam_1 @ (k2_tarski @ X44 @ X45)) = (k3_xboole_0 @ X44 @ X45))),
% 0.48/0.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.48/0.69  thf('32', plain,
% 0.48/0.69      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.48/0.69         (~ (r1_tarski @ X2 @ X3)
% 0.48/0.69          | ~ (r1_tarski @ X2 @ X4)
% 0.48/0.69          | (r1_tarski @ X2 @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4))))),
% 0.48/0.69      inference('demod', [status(thm)], ['30', '31'])).
% 0.48/0.69  thf('33', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.48/0.69         (~ (v1_relat_1 @ X0)
% 0.48/0.69          | ~ (v1_relat_1 @ X1)
% 0.48/0.69          | (r1_tarski @ 
% 0.48/0.69             (k5_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X2))) @ 
% 0.48/0.69             (k1_setfam_1 @ (k2_tarski @ (k5_relat_1 @ X1 @ X0) @ X3)))
% 0.48/0.69          | ~ (r1_tarski @ 
% 0.48/0.69               (k5_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X2))) @ X3))),
% 0.48/0.69      inference('sup-', [status(thm)], ['29', '32'])).
% 0.48/0.69  thf('34', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.69         (~ (v1_relat_1 @ X0)
% 0.48/0.69          | ~ (v1_relat_1 @ X1)
% 0.48/0.69          | (r1_tarski @ 
% 0.48/0.69             (k5_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X0))) @ 
% 0.48/0.69             (k1_setfam_1 @ 
% 0.48/0.69              (k2_tarski @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0))))
% 0.48/0.69          | ~ (v1_relat_1 @ X1)
% 0.48/0.69          | ~ (v1_relat_1 @ X2))),
% 0.48/0.69      inference('sup-', [status(thm)], ['17', '33'])).
% 0.48/0.69  thf('35', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.69         (~ (v1_relat_1 @ X2)
% 0.48/0.69          | (r1_tarski @ 
% 0.48/0.69             (k5_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X0))) @ 
% 0.48/0.69             (k1_setfam_1 @ 
% 0.48/0.69              (k2_tarski @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0))))
% 0.48/0.69          | ~ (v1_relat_1 @ X1)
% 0.48/0.69          | ~ (v1_relat_1 @ X0))),
% 0.48/0.69      inference('simplify', [status(thm)], ['34'])).
% 0.48/0.69  thf(t52_relat_1, conjecture,
% 0.48/0.69    (![A:$i]:
% 0.48/0.69     ( ( v1_relat_1 @ A ) =>
% 0.48/0.69       ( ![B:$i]:
% 0.48/0.69         ( ( v1_relat_1 @ B ) =>
% 0.48/0.69           ( ![C:$i]:
% 0.48/0.69             ( ( v1_relat_1 @ C ) =>
% 0.48/0.69               ( r1_tarski @
% 0.48/0.69                 ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 0.48/0.69                 ( k3_xboole_0 @
% 0.48/0.69                   ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.48/0.69  thf(zf_stmt_3, negated_conjecture,
% 0.48/0.69    (~( ![A:$i]:
% 0.48/0.69        ( ( v1_relat_1 @ A ) =>
% 0.48/0.69          ( ![B:$i]:
% 0.48/0.69            ( ( v1_relat_1 @ B ) =>
% 0.48/0.69              ( ![C:$i]:
% 0.48/0.69                ( ( v1_relat_1 @ C ) =>
% 0.48/0.69                  ( r1_tarski @
% 0.48/0.69                    ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 0.48/0.69                    ( k3_xboole_0 @
% 0.48/0.69                      ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 0.48/0.69    inference('cnf.neg', [status(esa)], [t52_relat_1])).
% 0.48/0.69  thf('36', plain,
% 0.48/0.69      (~ (r1_tarski @ (k5_relat_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 0.48/0.69          (k3_xboole_0 @ (k5_relat_1 @ sk_A @ sk_B) @ 
% 0.48/0.69           (k5_relat_1 @ sk_A @ sk_C)))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.48/0.69  thf('37', plain,
% 0.48/0.69      (![X44 : $i, X45 : $i]:
% 0.48/0.69         ((k1_setfam_1 @ (k2_tarski @ X44 @ X45)) = (k3_xboole_0 @ X44 @ X45))),
% 0.48/0.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.48/0.69  thf('38', plain,
% 0.48/0.69      (![X44 : $i, X45 : $i]:
% 0.48/0.69         ((k1_setfam_1 @ (k2_tarski @ X44 @ X45)) = (k3_xboole_0 @ X44 @ X45))),
% 0.48/0.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.48/0.69  thf('39', plain,
% 0.48/0.69      (~ (r1_tarski @ 
% 0.48/0.69          (k5_relat_1 @ sk_A @ (k1_setfam_1 @ (k2_tarski @ sk_B @ sk_C))) @ 
% 0.48/0.69          (k1_setfam_1 @ 
% 0.48/0.69           (k2_tarski @ (k5_relat_1 @ sk_A @ sk_B) @ (k5_relat_1 @ sk_A @ sk_C))))),
% 0.48/0.69      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.48/0.69  thf('40', plain,
% 0.48/0.69      ((~ (v1_relat_1 @ sk_C) | ~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 0.48/0.69      inference('sup-', [status(thm)], ['35', '39'])).
% 0.48/0.69  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.48/0.69  thf('42', plain, ((v1_relat_1 @ sk_A)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.48/0.69  thf('43', plain, ((v1_relat_1 @ sk_B)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.48/0.69  thf('44', plain, ($false),
% 0.48/0.69      inference('demod', [status(thm)], ['40', '41', '42', '43'])).
% 0.48/0.69  
% 0.48/0.69  % SZS output end Refutation
% 0.48/0.69  
% 0.48/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
