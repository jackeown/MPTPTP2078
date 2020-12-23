%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AXQbP7VlyG

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:12 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 365 expanded)
%              Number of leaves         :   28 ( 120 expanded)
%              Depth                    :   20
%              Number of atoms          :  796 (4186 expanded)
%              Number of equality atoms :   61 ( 309 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t91_orders_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( ( k3_tarski @ A )
           != k1_xboole_0 )
          & ! [B: $i] :
              ~ ( ( B != k1_xboole_0 )
                & ( r2_hidden @ B @ A ) ) )
      & ~ ( ? [B: $i] :
              ( ( r2_hidden @ B @ A )
              & ( B != k1_xboole_0 ) )
          & ( ( k3_tarski @ A )
            = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X29: $i] :
      ( ( ( k3_tarski @ X29 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X29 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t91_orders_1])).

thf(t12_tops_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
          = ( k3_subset_1 @ A @ ( k6_setfam_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ( ( B != k1_xboole_0 )
         => ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
            = ( k3_subset_1 @ A @ ( k6_setfam_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_tops_2])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) )
          <=> ( r2_hidden @ C @ B ) ) ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r2_hidden @ X19 @ X21 )
      | ( r2_hidden @ ( k3_subset_1 @ X20 @ X19 ) @ ( k7_setfam_1 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[t49_setfam_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( m1_subset_1 @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['4','7'])).

thf('9',plain,
    ( ( ( k3_tarski @ sk_B_1 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('10',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ~ ( r1_tarski @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('11',plain,
    ( ( ( k3_tarski @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('14',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t11_tops_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k6_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
          = ( k3_subset_1 @ A @ ( k5_setfam_1 @ A @ B ) ) ) ) ) )).

thf('15',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( ( k6_setfam_1 @ X31 @ ( k7_setfam_1 @ X31 @ X30 ) )
        = ( k3_subset_1 @ X31 @ ( k5_setfam_1 @ X31 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[t11_tops_2])).

thf('16',plain,
    ( ( ( k6_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) ) )
      = ( k3_subset_1 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) ) ) )
    | ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k7_setfam_1 @ X13 @ ( k7_setfam_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('19',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(redefinition_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k5_setfam_1 @ A @ B )
        = ( k3_tarski @ B ) ) ) )).

thf('21',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k5_setfam_1 @ X15 @ X14 )
        = ( k3_tarski @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('22',plain,
    ( ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) )
    = ( k3_tarski @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k6_setfam_1 @ sk_A @ sk_B_1 )
      = ( k3_subset_1 @ sk_A @ ( k3_tarski @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) ) ) )
    | ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','19','22'])).

thf('24',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(dt_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_setfam_1])).

thf('26',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) )
    = ( k3_tarski @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('28',plain,(
    m1_subset_1 @ ( k3_tarski @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('29',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X7 @ ( k3_subset_1 @ X7 @ X6 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('30',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ ( k3_tarski @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) ) ) )
    = ( k3_tarski @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k3_subset_1 @ sk_A @ ( k6_setfam_1 @ sk_A @ sk_B_1 ) )
      = ( k3_tarski @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) ) )
    | ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','30'])).

thf('32',plain,(
    ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) )
 != ( k3_subset_1 @ sk_A @ ( k6_setfam_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) )
    = ( k3_tarski @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('34',plain,(
    ( k3_tarski @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) )
 != ( k3_subset_1 @ sk_A @ ( k6_setfam_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['31','34'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('36',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('37',plain,
    ( ( k3_tarski @ sk_B_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['11','35','36'])).

thf('38',plain,(
    ! [X27: $i,X28: $i] :
      ( ( X27 = k1_xboole_0 )
      | ~ ( r2_hidden @ X27 @ X28 )
      | ( ( k3_tarski @ X28 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t91_orders_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( ( sk_C @ X0 @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','40'])).

thf('42',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ sk_B_1 )
      | ( r1_tarski @ sk_B_1 @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ k1_xboole_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['4','7'])).

thf('46',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['31','34'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( ( k6_setfam_1 @ X31 @ ( k7_setfam_1 @ X31 @ X30 ) )
        = ( k3_subset_1 @ X31 @ ( k5_setfam_1 @ X31 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[t11_tops_2])).

thf('51',plain,
    ( ( ( k6_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) )
      = ( k3_subset_1 @ sk_A @ ( k5_setfam_1 @ sk_A @ sk_B_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k5_setfam_1 @ X15 @ X14 )
        = ( k3_tarski @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('54',plain,
    ( ( k5_setfam_1 @ sk_A @ sk_B_1 )
    = ( k3_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k6_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) )
      = ( k3_subset_1 @ sk_A @ ( k3_tarski @ sk_B_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k6_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) )
    = ( k3_subset_1 @ sk_A @ ( k3_tarski @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['31','34'])).

thf('59',plain,
    ( ( k6_setfam_1 @ sk_A @ k1_xboole_0 )
    = ( k3_subset_1 @ sk_A @ ( k3_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k3_tarski @ sk_B_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['11','35','36'])).

thf('61',plain,
    ( ( k6_setfam_1 @ sk_A @ k1_xboole_0 )
    = ( k3_subset_1 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( k6_setfam_1 @ sk_A @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['48','61'])).

thf('63',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ~ ( r1_tarski @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ ( k6_setfam_1 @ sk_A @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B_1 @ X0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('67',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('68',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AXQbP7VlyG
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:23:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.59/0.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.80  % Solved by: fo/fo7.sh
% 0.59/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.80  % done 647 iterations in 0.342s
% 0.59/0.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.80  % SZS output start Refutation
% 0.59/0.80  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.59/0.80  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.59/0.80  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.59/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.80  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.59/0.80  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.59/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.80  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.59/0.80  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.59/0.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.80  thf(sk_B_type, type, sk_B: $i > $i).
% 0.59/0.80  thf(d3_tarski, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( r1_tarski @ A @ B ) <=>
% 0.59/0.80       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.59/0.80  thf('0', plain,
% 0.59/0.80      (![X1 : $i, X3 : $i]:
% 0.59/0.80         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.59/0.80      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.80  thf(t91_orders_1, axiom,
% 0.59/0.80    (![A:$i]:
% 0.59/0.80     ( ( ~( ( ( k3_tarski @ A ) != ( k1_xboole_0 ) ) & 
% 0.59/0.80            ( ![B:$i]:
% 0.59/0.80              ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( r2_hidden @ B @ A ) ) ) ) ) ) & 
% 0.59/0.80       ( ~( ( ?[B:$i]: ( ( r2_hidden @ B @ A ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.59/0.80            ( ( k3_tarski @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.59/0.80  thf('1', plain,
% 0.59/0.80      (![X29 : $i]:
% 0.59/0.80         (((k3_tarski @ X29) = (k1_xboole_0))
% 0.59/0.80          | (r2_hidden @ (sk_B @ X29) @ X29))),
% 0.59/0.80      inference('cnf', [status(esa)], [t91_orders_1])).
% 0.59/0.80  thf(t12_tops_2, conjecture,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.59/0.80       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.59/0.80         ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.59/0.80           ( k3_subset_1 @ A @ ( k6_setfam_1 @ A @ B ) ) ) ) ))).
% 0.59/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.80    (~( ![A:$i,B:$i]:
% 0.59/0.80        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.59/0.80          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.59/0.80            ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.59/0.80              ( k3_subset_1 @ A @ ( k6_setfam_1 @ A @ B ) ) ) ) ) )),
% 0.59/0.80    inference('cnf.neg', [status(esa)], [t12_tops_2])).
% 0.59/0.80  thf('2', plain,
% 0.59/0.80      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf(t49_setfam_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.59/0.80       ( ![C:$i]:
% 0.59/0.80         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.59/0.80           ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) ) <=>
% 0.59/0.80             ( r2_hidden @ C @ B ) ) ) ) ))).
% 0.59/0.80  thf('3', plain,
% 0.59/0.80      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.59/0.80         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.59/0.80          | ~ (r2_hidden @ X19 @ X21)
% 0.59/0.80          | (r2_hidden @ (k3_subset_1 @ X20 @ X19) @ (k7_setfam_1 @ X20 @ X21))
% 0.59/0.80          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.59/0.80      inference('cnf', [status(esa)], [t49_setfam_1])).
% 0.59/0.80  thf('4', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ 
% 0.59/0.80           (k7_setfam_1 @ sk_A @ sk_B_1))
% 0.59/0.80          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.59/0.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['2', '3'])).
% 0.59/0.80  thf('5', plain,
% 0.59/0.80      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf(t4_subset, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i]:
% 0.59/0.80     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.59/0.80       ( m1_subset_1 @ A @ C ) ))).
% 0.59/0.80  thf('6', plain,
% 0.59/0.80      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.59/0.80         (~ (r2_hidden @ X22 @ X23)
% 0.59/0.80          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 0.59/0.80          | (m1_subset_1 @ X22 @ X24))),
% 0.59/0.80      inference('cnf', [status(esa)], [t4_subset])).
% 0.59/0.80  thf('7', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.59/0.80          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.59/0.80      inference('sup-', [status(thm)], ['5', '6'])).
% 0.59/0.80  thf('8', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.59/0.80          | (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ 
% 0.59/0.80             (k7_setfam_1 @ sk_A @ sk_B_1)))),
% 0.59/0.80      inference('clc', [status(thm)], ['4', '7'])).
% 0.59/0.80  thf('9', plain,
% 0.59/0.80      ((((k3_tarski @ sk_B_1) = (k1_xboole_0))
% 0.59/0.80        | (r2_hidden @ (k3_subset_1 @ sk_A @ (sk_B @ sk_B_1)) @ 
% 0.59/0.80           (k7_setfam_1 @ sk_A @ sk_B_1)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['1', '8'])).
% 0.59/0.80  thf(t7_ordinal1, axiom,
% 0.59/0.80    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.80  thf('10', plain,
% 0.59/0.80      (![X25 : $i, X26 : $i]:
% 0.59/0.80         (~ (r2_hidden @ X25 @ X26) | ~ (r1_tarski @ X26 @ X25))),
% 0.59/0.80      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.59/0.80  thf('11', plain,
% 0.59/0.80      ((((k3_tarski @ sk_B_1) = (k1_xboole_0))
% 0.59/0.80        | ~ (r1_tarski @ (k7_setfam_1 @ sk_A @ sk_B_1) @ 
% 0.59/0.80             (k3_subset_1 @ sk_A @ (sk_B @ sk_B_1))))),
% 0.59/0.80      inference('sup-', [status(thm)], ['9', '10'])).
% 0.59/0.80  thf('12', plain,
% 0.59/0.80      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf(dt_k7_setfam_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.59/0.80       ( m1_subset_1 @
% 0.59/0.80         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.59/0.80  thf('13', plain,
% 0.59/0.80      (![X10 : $i, X11 : $i]:
% 0.59/0.80         ((m1_subset_1 @ (k7_setfam_1 @ X10 @ X11) @ 
% 0.59/0.80           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10)))
% 0.59/0.80          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10))))),
% 0.59/0.80      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.59/0.80  thf('14', plain,
% 0.59/0.80      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B_1) @ 
% 0.59/0.80        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['12', '13'])).
% 0.59/0.80  thf(t11_tops_2, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.59/0.80       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.59/0.80         ( ( k6_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.59/0.80           ( k3_subset_1 @ A @ ( k5_setfam_1 @ A @ B ) ) ) ) ))).
% 0.59/0.80  thf('15', plain,
% 0.59/0.80      (![X30 : $i, X31 : $i]:
% 0.59/0.80         (((X30) = (k1_xboole_0))
% 0.59/0.80          | ((k6_setfam_1 @ X31 @ (k7_setfam_1 @ X31 @ X30))
% 0.59/0.80              = (k3_subset_1 @ X31 @ (k5_setfam_1 @ X31 @ X30)))
% 0.59/0.80          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X31))))),
% 0.59/0.80      inference('cnf', [status(esa)], [t11_tops_2])).
% 0.59/0.80  thf('16', plain,
% 0.59/0.80      ((((k6_setfam_1 @ sk_A @ 
% 0.59/0.80          (k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1)))
% 0.59/0.80          = (k3_subset_1 @ sk_A @ 
% 0.59/0.80             (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1))))
% 0.59/0.80        | ((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['14', '15'])).
% 0.59/0.80  thf('17', plain,
% 0.59/0.80      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf(involutiveness_k7_setfam_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.59/0.80       ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) = ( B ) ) ))).
% 0.59/0.80  thf('18', plain,
% 0.59/0.80      (![X12 : $i, X13 : $i]:
% 0.59/0.80         (((k7_setfam_1 @ X13 @ (k7_setfam_1 @ X13 @ X12)) = (X12))
% 0.59/0.80          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 0.59/0.80      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.59/0.80  thf('19', plain,
% 0.59/0.80      (((k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.59/0.80      inference('sup-', [status(thm)], ['17', '18'])).
% 0.59/0.80  thf('20', plain,
% 0.59/0.80      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B_1) @ 
% 0.59/0.80        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['12', '13'])).
% 0.59/0.80  thf(redefinition_k5_setfam_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.59/0.80       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 0.59/0.80  thf('21', plain,
% 0.59/0.80      (![X14 : $i, X15 : $i]:
% 0.59/0.80         (((k5_setfam_1 @ X15 @ X14) = (k3_tarski @ X14))
% 0.59/0.80          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.59/0.80      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.59/0.80  thf('22', plain,
% 0.59/0.80      (((k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1))
% 0.59/0.80         = (k3_tarski @ (k7_setfam_1 @ sk_A @ sk_B_1)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['20', '21'])).
% 0.59/0.80  thf('23', plain,
% 0.59/0.80      ((((k6_setfam_1 @ sk_A @ sk_B_1)
% 0.59/0.80          = (k3_subset_1 @ sk_A @ (k3_tarski @ (k7_setfam_1 @ sk_A @ sk_B_1))))
% 0.59/0.80        | ((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.59/0.80      inference('demod', [status(thm)], ['16', '19', '22'])).
% 0.59/0.80  thf('24', plain,
% 0.59/0.80      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B_1) @ 
% 0.59/0.80        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['12', '13'])).
% 0.59/0.80  thf(dt_k5_setfam_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.59/0.80       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.59/0.80  thf('25', plain,
% 0.59/0.80      (![X8 : $i, X9 : $i]:
% 0.59/0.80         ((m1_subset_1 @ (k5_setfam_1 @ X8 @ X9) @ (k1_zfmisc_1 @ X8))
% 0.59/0.80          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X8))))),
% 0.59/0.80      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 0.59/0.80  thf('26', plain,
% 0.59/0.80      ((m1_subset_1 @ (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1)) @ 
% 0.59/0.80        (k1_zfmisc_1 @ sk_A))),
% 0.59/0.80      inference('sup-', [status(thm)], ['24', '25'])).
% 0.59/0.80  thf('27', plain,
% 0.59/0.80      (((k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1))
% 0.59/0.80         = (k3_tarski @ (k7_setfam_1 @ sk_A @ sk_B_1)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['20', '21'])).
% 0.59/0.80  thf('28', plain,
% 0.59/0.80      ((m1_subset_1 @ (k3_tarski @ (k7_setfam_1 @ sk_A @ sk_B_1)) @ 
% 0.59/0.80        (k1_zfmisc_1 @ sk_A))),
% 0.59/0.80      inference('demod', [status(thm)], ['26', '27'])).
% 0.59/0.80  thf(involutiveness_k3_subset_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.59/0.80       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.59/0.80  thf('29', plain,
% 0.59/0.80      (![X6 : $i, X7 : $i]:
% 0.59/0.80         (((k3_subset_1 @ X7 @ (k3_subset_1 @ X7 @ X6)) = (X6))
% 0.59/0.80          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.59/0.80      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.59/0.80  thf('30', plain,
% 0.59/0.80      (((k3_subset_1 @ sk_A @ 
% 0.59/0.80         (k3_subset_1 @ sk_A @ (k3_tarski @ (k7_setfam_1 @ sk_A @ sk_B_1))))
% 0.59/0.80         = (k3_tarski @ (k7_setfam_1 @ sk_A @ sk_B_1)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['28', '29'])).
% 0.59/0.80  thf('31', plain,
% 0.59/0.80      ((((k3_subset_1 @ sk_A @ (k6_setfam_1 @ sk_A @ sk_B_1))
% 0.59/0.80          = (k3_tarski @ (k7_setfam_1 @ sk_A @ sk_B_1)))
% 0.59/0.80        | ((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['23', '30'])).
% 0.59/0.80  thf('32', plain,
% 0.59/0.80      (((k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1))
% 0.59/0.80         != (k3_subset_1 @ sk_A @ (k6_setfam_1 @ sk_A @ sk_B_1)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('33', plain,
% 0.59/0.80      (((k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1))
% 0.59/0.80         = (k3_tarski @ (k7_setfam_1 @ sk_A @ sk_B_1)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['20', '21'])).
% 0.59/0.80  thf('34', plain,
% 0.59/0.80      (((k3_tarski @ (k7_setfam_1 @ sk_A @ sk_B_1))
% 0.59/0.80         != (k3_subset_1 @ sk_A @ (k6_setfam_1 @ sk_A @ sk_B_1)))),
% 0.59/0.80      inference('demod', [status(thm)], ['32', '33'])).
% 0.59/0.80  thf('35', plain, (((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.59/0.80      inference('simplify_reflect-', [status(thm)], ['31', '34'])).
% 0.59/0.80  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.59/0.80  thf('36', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.59/0.80      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.59/0.80  thf('37', plain, (((k3_tarski @ sk_B_1) = (k1_xboole_0))),
% 0.59/0.80      inference('demod', [status(thm)], ['11', '35', '36'])).
% 0.59/0.80  thf('38', plain,
% 0.59/0.80      (![X27 : $i, X28 : $i]:
% 0.59/0.80         (((X27) = (k1_xboole_0))
% 0.59/0.80          | ~ (r2_hidden @ X27 @ X28)
% 0.59/0.80          | ((k3_tarski @ X28) != (k1_xboole_0)))),
% 0.59/0.80      inference('cnf', [status(esa)], [t91_orders_1])).
% 0.59/0.80  thf('39', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.80          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.59/0.80          | ((X0) = (k1_xboole_0)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['37', '38'])).
% 0.59/0.80  thf('40', plain,
% 0.59/0.80      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.59/0.80      inference('simplify', [status(thm)], ['39'])).
% 0.59/0.80  thf('41', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((r1_tarski @ sk_B_1 @ X0) | ((sk_C @ X0 @ sk_B_1) = (k1_xboole_0)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['0', '40'])).
% 0.59/0.80  thf('42', plain,
% 0.59/0.80      (![X1 : $i, X3 : $i]:
% 0.59/0.80         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.59/0.80      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.80  thf('43', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((r2_hidden @ k1_xboole_0 @ sk_B_1)
% 0.59/0.80          | (r1_tarski @ sk_B_1 @ X0)
% 0.59/0.80          | (r1_tarski @ sk_B_1 @ X0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['41', '42'])).
% 0.59/0.80  thf('44', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((r1_tarski @ sk_B_1 @ X0) | (r2_hidden @ k1_xboole_0 @ sk_B_1))),
% 0.59/0.80      inference('simplify', [status(thm)], ['43'])).
% 0.59/0.80  thf('45', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.59/0.80          | (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ 
% 0.59/0.80             (k7_setfam_1 @ sk_A @ sk_B_1)))),
% 0.59/0.80      inference('clc', [status(thm)], ['4', '7'])).
% 0.59/0.80  thf('46', plain, (((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.59/0.80      inference('simplify_reflect-', [status(thm)], ['31', '34'])).
% 0.59/0.80  thf('47', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.59/0.80          | (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ k1_xboole_0))),
% 0.59/0.80      inference('demod', [status(thm)], ['45', '46'])).
% 0.59/0.80  thf('48', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((r1_tarski @ sk_B_1 @ X0)
% 0.59/0.80          | (r2_hidden @ (k3_subset_1 @ sk_A @ k1_xboole_0) @ k1_xboole_0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['44', '47'])).
% 0.59/0.80  thf('49', plain,
% 0.59/0.80      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('50', plain,
% 0.59/0.80      (![X30 : $i, X31 : $i]:
% 0.59/0.80         (((X30) = (k1_xboole_0))
% 0.59/0.80          | ((k6_setfam_1 @ X31 @ (k7_setfam_1 @ X31 @ X30))
% 0.59/0.80              = (k3_subset_1 @ X31 @ (k5_setfam_1 @ X31 @ X30)))
% 0.59/0.80          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X31))))),
% 0.59/0.80      inference('cnf', [status(esa)], [t11_tops_2])).
% 0.59/0.80  thf('51', plain,
% 0.59/0.80      ((((k6_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1))
% 0.59/0.80          = (k3_subset_1 @ sk_A @ (k5_setfam_1 @ sk_A @ sk_B_1)))
% 0.59/0.80        | ((sk_B_1) = (k1_xboole_0)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['49', '50'])).
% 0.59/0.80  thf('52', plain,
% 0.59/0.80      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('53', plain,
% 0.59/0.80      (![X14 : $i, X15 : $i]:
% 0.59/0.80         (((k5_setfam_1 @ X15 @ X14) = (k3_tarski @ X14))
% 0.59/0.80          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.59/0.80      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.59/0.80  thf('54', plain, (((k5_setfam_1 @ sk_A @ sk_B_1) = (k3_tarski @ sk_B_1))),
% 0.59/0.80      inference('sup-', [status(thm)], ['52', '53'])).
% 0.59/0.80  thf('55', plain,
% 0.59/0.80      ((((k6_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1))
% 0.59/0.80          = (k3_subset_1 @ sk_A @ (k3_tarski @ sk_B_1)))
% 0.59/0.80        | ((sk_B_1) = (k1_xboole_0)))),
% 0.59/0.80      inference('demod', [status(thm)], ['51', '54'])).
% 0.59/0.80  thf('56', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('57', plain,
% 0.59/0.80      (((k6_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1))
% 0.59/0.80         = (k3_subset_1 @ sk_A @ (k3_tarski @ sk_B_1)))),
% 0.59/0.80      inference('simplify_reflect-', [status(thm)], ['55', '56'])).
% 0.59/0.80  thf('58', plain, (((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.59/0.80      inference('simplify_reflect-', [status(thm)], ['31', '34'])).
% 0.59/0.80  thf('59', plain,
% 0.59/0.80      (((k6_setfam_1 @ sk_A @ k1_xboole_0)
% 0.59/0.80         = (k3_subset_1 @ sk_A @ (k3_tarski @ sk_B_1)))),
% 0.59/0.80      inference('demod', [status(thm)], ['57', '58'])).
% 0.59/0.80  thf('60', plain, (((k3_tarski @ sk_B_1) = (k1_xboole_0))),
% 0.59/0.80      inference('demod', [status(thm)], ['11', '35', '36'])).
% 0.59/0.80  thf('61', plain,
% 0.59/0.80      (((k6_setfam_1 @ sk_A @ k1_xboole_0) = (k3_subset_1 @ sk_A @ k1_xboole_0))),
% 0.59/0.80      inference('demod', [status(thm)], ['59', '60'])).
% 0.59/0.80  thf('62', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((r1_tarski @ sk_B_1 @ X0)
% 0.59/0.80          | (r2_hidden @ (k6_setfam_1 @ sk_A @ k1_xboole_0) @ k1_xboole_0))),
% 0.59/0.80      inference('demod', [status(thm)], ['48', '61'])).
% 0.59/0.80  thf('63', plain,
% 0.59/0.80      (![X25 : $i, X26 : $i]:
% 0.59/0.80         (~ (r2_hidden @ X25 @ X26) | ~ (r1_tarski @ X26 @ X25))),
% 0.59/0.80      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.59/0.80  thf('64', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((r1_tarski @ sk_B_1 @ X0)
% 0.59/0.80          | ~ (r1_tarski @ k1_xboole_0 @ (k6_setfam_1 @ sk_A @ k1_xboole_0)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['62', '63'])).
% 0.59/0.80  thf('65', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.59/0.80      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.59/0.80  thf('66', plain, (![X0 : $i]: (r1_tarski @ sk_B_1 @ X0)),
% 0.59/0.80      inference('demod', [status(thm)], ['64', '65'])).
% 0.59/0.80  thf(t3_xboole_1, axiom,
% 0.59/0.80    (![A:$i]:
% 0.59/0.80     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.59/0.80  thf('67', plain,
% 0.59/0.80      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ k1_xboole_0))),
% 0.59/0.80      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.59/0.80  thf('68', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['66', '67'])).
% 0.59/0.80  thf('69', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('70', plain, ($false),
% 0.59/0.80      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 0.59/0.80  
% 0.59/0.80  % SZS output end Refutation
% 0.59/0.80  
% 0.59/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
