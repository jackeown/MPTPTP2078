%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nqHiQXqa9X

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:07 EST 2020

% Result     : Theorem 2.04s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :  209 (1170 expanded)
%              Number of leaves         :   41 ( 381 expanded)
%              Depth                    :   28
%              Number of atoms          : 1420 (9249 expanded)
%              Number of equality atoms :  100 ( 713 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t31_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_tarski @ B @ C )
            <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_subset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ~ ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X52 @ X53 )
      | ( r2_hidden @ X52 @ X53 )
      | ( v1_xboole_0 @ X53 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X57: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('6',plain,(
    r2_hidden @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['4','5'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('7',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( r2_hidden @ X48 @ X47 )
      | ( r1_tarski @ X48 @ X46 )
      | ( X47
       != ( k1_zfmisc_1 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('8',plain,(
    ! [X46: $i,X48: $i] :
      ( ( r1_tarski @ X48 @ X46 )
      | ~ ( r2_hidden @ X48 @ ( k1_zfmisc_1 @ X46 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    r1_tarski @ sk_C_2 @ sk_A ),
    inference('sup-',[status(thm)],['6','8'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ sk_A )
    = sk_C_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_2 )
    = ( k5_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X55: $i,X56: $i] :
      ( ( ( k3_subset_1 @ X55 @ X56 )
        = ( k4_xboole_0 @ X55 @ X56 ) )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k4_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k5_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X52 @ X53 )
      | ( r2_hidden @ X52 @ X53 )
      | ( v1_xboole_0 @ X53 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X57: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('24',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X46: $i,X48: $i] :
      ( ( r1_tarski @ X48 @ X46 )
      | ~ ( r2_hidden @ X48 @ ( k1_zfmisc_1 @ X46 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('26',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('28',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X55: $i,X56: $i] :
      ( ( ( k3_subset_1 @ X55 @ X56 )
        = ( k4_xboole_0 @ X55 @ X56 ) )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('33',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['1','19','34'])).

thf('36',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ~ ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('38',plain,(
    ! [X31: $i,X32: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X31 @ X32 ) @ X32 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('39',plain,(
    r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference('sup+',[status(thm)],['37','38'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('40',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('41',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_xboole_0 @ ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('45',plain,(
    v1_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('47',plain,(
    v1_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('48',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('49',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('51',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) )
    = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('52',plain,(
    ! [X27: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X27 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('53',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k2_xboole_0 @ X39 @ X40 )
      = ( k5_xboole_0 @ X39 @ ( k4_xboole_0 @ X40 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('55',plain,(
    ! [X17: $i] :
      ( ( k2_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['51','56'])).

thf('58',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['58'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('60',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ X33 @ X34 )
      | ( r1_xboole_0 @ X33 @ ( k4_xboole_0 @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('61',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k5_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('63',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( r1_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['57','64'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('66',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('67',plain,
    ( ( r1_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_2 )
    = ( k5_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('69',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) )
      = ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('70',plain,
    ( ( k2_xboole_0 @ sk_C_2 @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) )
    = ( k2_xboole_0 @ sk_C_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ sk_A )
    = sk_C_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('72',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('73',plain,
    ( ( k4_xboole_0 @ sk_C_2 @ sk_A )
    = ( k5_xboole_0 @ sk_C_2 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('74',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k2_tarski @ X42 @ X41 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('75',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X50 @ X51 ) )
      = ( k2_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X50 @ X51 ) )
      = ( k2_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X17: $i] :
      ( ( k2_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) )
      = ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('85',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X23 @ X24 ) @ X23 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( r1_tarski @ X45 @ X46 )
      | ( r2_hidden @ X45 @ X47 )
      | ( X47
       != ( k1_zfmisc_1 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('88',plain,(
    ! [X45: $i,X46: $i] :
      ( ( r2_hidden @ X45 @ ( k1_zfmisc_1 @ X46 ) )
      | ~ ( r1_tarski @ X45 @ X46 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','88'])).

thf('90',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X52 @ X53 )
      | ( m1_subset_1 @ X52 @ X53 )
      | ( v1_xboole_0 @ X53 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('91',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('92',plain,(
    ! [X52: $i,X53: $i] :
      ( ( m1_subset_1 @ X52 @ X53 )
      | ~ ( r2_hidden @ X52 @ X53 ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,(
    ! [X55: $i,X56: $i] :
      ( ( ( k3_subset_1 @ X55 @ X56 )
        = ( k4_xboole_0 @ X55 @ X56 ) )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('97',plain,(
    ! [X31: $i,X32: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X31 @ X32 ) @ X32 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_subset_1 @ X0 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf(t73_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('100',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r1_tarski @ X28 @ X29 )
      | ~ ( r1_tarski @ X28 @ ( k2_xboole_0 @ X29 @ X30 ) )
      | ~ ( r1_xboole_0 @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ k1_xboole_0 )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('104',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X23 @ X24 ) @ X23 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['102','105'])).

thf('107',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_subset_1 @ X0 @ X0 ) @ k1_xboole_0 )
      = ( k3_subset_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('110',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k2_xboole_0 @ X39 @ X40 )
      = ( k5_xboole_0 @ X39 @ ( k4_xboole_0 @ X40 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X27: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X27 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_subset_1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['108','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('123',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['121','126'])).

thf('128',plain,
    ( ( k4_xboole_0 @ sk_C_2 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['73','127'])).

thf('129',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) )
      = ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('130',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('134',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['130','131','132','133'])).

thf('135',plain,
    ( ( k2_xboole_0 @ sk_C_2 @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) )
    = sk_A ),
    inference(demod,[status(thm)],['70','134'])).

thf('136',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r1_tarski @ X28 @ X29 )
      | ~ ( r1_tarski @ X28 @ ( k2_xboole_0 @ X29 @ X30 ) )
      | ~ ( r1_xboole_0 @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( r1_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) )
      | ( r1_tarski @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( ( r1_tarski @ sk_B_1 @ sk_C_2 )
      | ~ ( r1_tarski @ sk_B_1 @ sk_A ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['67','137'])).

thf('139',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf('140',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_2 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_C_2 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('142',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_2 )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['36','142'])).

thf('144',plain,(
    ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(simpl_trail,[status(thm)],['35','143'])).

thf('145',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_2 )
    = ( k5_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('146',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X23 @ X24 ) @ X23 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('147',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) @ sk_A ),
    inference('sup+',[status(thm)],['145','146'])).

thf('148',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k4_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('149',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_2 )
   <= ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['58'])).

thf('150',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ X33 @ X34 )
      | ( r1_xboole_0 @ X33 @ ( k4_xboole_0 @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('151',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ X0 @ sk_C_2 ) )
   <= ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('153',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_2 ) @ sk_B_1 )
   <= ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,
    ( ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ sk_B_1 )
   <= ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['148','153'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('155',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( r1_tarski @ X36 @ X37 )
      | ~ ( r1_xboole_0 @ X36 @ X38 )
      | ( r1_tarski @ X36 @ ( k4_xboole_0 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('156',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k4_xboole_0 @ X0 @ sk_B_1 ) )
        | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ X0 ) )
   <= ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k5_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('158',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k5_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('159',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) @ ( k4_xboole_0 @ X0 @ sk_B_1 ) )
        | ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) @ X0 ) )
   <= ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('160',plain,
    ( ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['147','159'])).

thf('161',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('162',plain,
    ( ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_2 )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['58'])).

thf('164',plain,(
    r1_tarski @ sk_B_1 @ sk_C_2 ),
    inference('sat_resolution*',[status(thm)],['36','142','163'])).

thf('165',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['162','164'])).

thf('166',plain,(
    $false ),
    inference(demod,[status(thm)],['144','165'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nqHiQXqa9X
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.04/2.29  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.04/2.29  % Solved by: fo/fo7.sh
% 2.04/2.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.04/2.29  % done 4591 iterations in 1.828s
% 2.04/2.29  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.04/2.29  % SZS output start Refutation
% 2.04/2.29  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 2.04/2.29  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.04/2.29  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.04/2.29  thf(sk_C_2_type, type, sk_C_2: $i).
% 2.04/2.29  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.04/2.29  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 2.04/2.29  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.04/2.29  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.04/2.29  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.04/2.29  thf(sk_A_type, type, sk_A: $i).
% 2.04/2.29  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.04/2.29  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.04/2.29  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.04/2.29  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.04/2.29  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.04/2.29  thf(sk_B_type, type, sk_B: $i > $i).
% 2.04/2.29  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.04/2.29  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.04/2.29  thf(t31_subset_1, conjecture,
% 2.04/2.29    (![A:$i,B:$i]:
% 2.04/2.29     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.04/2.29       ( ![C:$i]:
% 2.04/2.29         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.04/2.29           ( ( r1_tarski @ B @ C ) <=>
% 2.04/2.29             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 2.04/2.29  thf(zf_stmt_0, negated_conjecture,
% 2.04/2.29    (~( ![A:$i,B:$i]:
% 2.04/2.29        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.04/2.29          ( ![C:$i]:
% 2.04/2.29            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.04/2.29              ( ( r1_tarski @ B @ C ) <=>
% 2.04/2.29                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 2.04/2.29    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 2.04/2.29  thf('0', plain,
% 2.04/2.29      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.04/2.29           (k3_subset_1 @ sk_A @ sk_B_1))
% 2.04/2.29        | ~ (r1_tarski @ sk_B_1 @ sk_C_2))),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('1', plain,
% 2.04/2.29      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.04/2.29           (k3_subset_1 @ sk_A @ sk_B_1)))
% 2.04/2.29         <= (~
% 2.04/2.29             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.04/2.29               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 2.04/2.29      inference('split', [status(esa)], ['0'])).
% 2.04/2.29  thf('2', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf(d2_subset_1, axiom,
% 2.04/2.29    (![A:$i,B:$i]:
% 2.04/2.29     ( ( ( v1_xboole_0 @ A ) =>
% 2.04/2.29         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 2.04/2.29       ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.04/2.29         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 2.04/2.29  thf('3', plain,
% 2.04/2.29      (![X52 : $i, X53 : $i]:
% 2.04/2.29         (~ (m1_subset_1 @ X52 @ X53)
% 2.04/2.29          | (r2_hidden @ X52 @ X53)
% 2.04/2.29          | (v1_xboole_0 @ X53))),
% 2.04/2.29      inference('cnf', [status(esa)], [d2_subset_1])).
% 2.04/2.29  thf('4', plain,
% 2.04/2.29      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 2.04/2.29        | (r2_hidden @ sk_C_2 @ (k1_zfmisc_1 @ sk_A)))),
% 2.04/2.29      inference('sup-', [status(thm)], ['2', '3'])).
% 2.04/2.29  thf(fc1_subset_1, axiom,
% 2.04/2.29    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.04/2.29  thf('5', plain, (![X57 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X57))),
% 2.04/2.29      inference('cnf', [status(esa)], [fc1_subset_1])).
% 2.04/2.29  thf('6', plain, ((r2_hidden @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 2.04/2.29      inference('clc', [status(thm)], ['4', '5'])).
% 2.04/2.29  thf(d1_zfmisc_1, axiom,
% 2.04/2.29    (![A:$i,B:$i]:
% 2.04/2.29     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 2.04/2.29       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 2.04/2.29  thf('7', plain,
% 2.04/2.29      (![X46 : $i, X47 : $i, X48 : $i]:
% 2.04/2.29         (~ (r2_hidden @ X48 @ X47)
% 2.04/2.29          | (r1_tarski @ X48 @ X46)
% 2.04/2.29          | ((X47) != (k1_zfmisc_1 @ X46)))),
% 2.04/2.29      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 2.04/2.29  thf('8', plain,
% 2.04/2.29      (![X46 : $i, X48 : $i]:
% 2.04/2.29         ((r1_tarski @ X48 @ X46) | ~ (r2_hidden @ X48 @ (k1_zfmisc_1 @ X46)))),
% 2.04/2.29      inference('simplify', [status(thm)], ['7'])).
% 2.04/2.29  thf('9', plain, ((r1_tarski @ sk_C_2 @ sk_A)),
% 2.04/2.29      inference('sup-', [status(thm)], ['6', '8'])).
% 2.04/2.29  thf(t28_xboole_1, axiom,
% 2.04/2.29    (![A:$i,B:$i]:
% 2.04/2.29     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.04/2.29  thf('10', plain,
% 2.04/2.29      (![X21 : $i, X22 : $i]:
% 2.04/2.29         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 2.04/2.29      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.04/2.29  thf('11', plain, (((k3_xboole_0 @ sk_C_2 @ sk_A) = (sk_C_2))),
% 2.04/2.29      inference('sup-', [status(thm)], ['9', '10'])).
% 2.04/2.29  thf(commutativity_k3_xboole_0, axiom,
% 2.04/2.29    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.04/2.29  thf('12', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.04/2.29      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.04/2.29  thf(t100_xboole_1, axiom,
% 2.04/2.29    (![A:$i,B:$i]:
% 2.04/2.29     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.04/2.29  thf('13', plain,
% 2.04/2.29      (![X12 : $i, X13 : $i]:
% 2.04/2.29         ((k4_xboole_0 @ X12 @ X13)
% 2.04/2.29           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 2.04/2.29      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.04/2.29  thf('14', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i]:
% 2.04/2.29         ((k4_xboole_0 @ X0 @ X1)
% 2.04/2.29           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.04/2.29      inference('sup+', [status(thm)], ['12', '13'])).
% 2.04/2.29  thf('15', plain,
% 2.04/2.29      (((k4_xboole_0 @ sk_A @ sk_C_2) = (k5_xboole_0 @ sk_A @ sk_C_2))),
% 2.04/2.29      inference('sup+', [status(thm)], ['11', '14'])).
% 2.04/2.29  thf('16', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf(d5_subset_1, axiom,
% 2.04/2.29    (![A:$i,B:$i]:
% 2.04/2.29     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.04/2.29       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 2.04/2.29  thf('17', plain,
% 2.04/2.29      (![X55 : $i, X56 : $i]:
% 2.04/2.29         (((k3_subset_1 @ X55 @ X56) = (k4_xboole_0 @ X55 @ X56))
% 2.04/2.29          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ X55)))),
% 2.04/2.29      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.04/2.29  thf('18', plain,
% 2.04/2.29      (((k3_subset_1 @ sk_A @ sk_C_2) = (k4_xboole_0 @ sk_A @ sk_C_2))),
% 2.04/2.29      inference('sup-', [status(thm)], ['16', '17'])).
% 2.04/2.29  thf('19', plain,
% 2.04/2.29      (((k3_subset_1 @ sk_A @ sk_C_2) = (k5_xboole_0 @ sk_A @ sk_C_2))),
% 2.04/2.29      inference('sup+', [status(thm)], ['15', '18'])).
% 2.04/2.29  thf('20', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('21', plain,
% 2.04/2.29      (![X52 : $i, X53 : $i]:
% 2.04/2.29         (~ (m1_subset_1 @ X52 @ X53)
% 2.04/2.29          | (r2_hidden @ X52 @ X53)
% 2.04/2.29          | (v1_xboole_0 @ X53))),
% 2.04/2.29      inference('cnf', [status(esa)], [d2_subset_1])).
% 2.04/2.29  thf('22', plain,
% 2.04/2.29      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 2.04/2.29        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 2.04/2.29      inference('sup-', [status(thm)], ['20', '21'])).
% 2.04/2.29  thf('23', plain, (![X57 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X57))),
% 2.04/2.29      inference('cnf', [status(esa)], [fc1_subset_1])).
% 2.04/2.29  thf('24', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 2.04/2.29      inference('clc', [status(thm)], ['22', '23'])).
% 2.04/2.29  thf('25', plain,
% 2.04/2.29      (![X46 : $i, X48 : $i]:
% 2.04/2.29         ((r1_tarski @ X48 @ X46) | ~ (r2_hidden @ X48 @ (k1_zfmisc_1 @ X46)))),
% 2.04/2.29      inference('simplify', [status(thm)], ['7'])).
% 2.04/2.29  thf('26', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 2.04/2.29      inference('sup-', [status(thm)], ['24', '25'])).
% 2.04/2.29  thf('27', plain,
% 2.04/2.29      (![X21 : $i, X22 : $i]:
% 2.04/2.29         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 2.04/2.29      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.04/2.29  thf('28', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1))),
% 2.04/2.29      inference('sup-', [status(thm)], ['26', '27'])).
% 2.04/2.29  thf('29', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i]:
% 2.04/2.29         ((k4_xboole_0 @ X0 @ X1)
% 2.04/2.29           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.04/2.29      inference('sup+', [status(thm)], ['12', '13'])).
% 2.04/2.29  thf('30', plain,
% 2.04/2.29      (((k4_xboole_0 @ sk_A @ sk_B_1) = (k5_xboole_0 @ sk_A @ sk_B_1))),
% 2.04/2.29      inference('sup+', [status(thm)], ['28', '29'])).
% 2.04/2.29  thf('31', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('32', plain,
% 2.04/2.29      (![X55 : $i, X56 : $i]:
% 2.04/2.29         (((k3_subset_1 @ X55 @ X56) = (k4_xboole_0 @ X55 @ X56))
% 2.04/2.29          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ X55)))),
% 2.04/2.29      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.04/2.29  thf('33', plain,
% 2.04/2.29      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 2.04/2.29      inference('sup-', [status(thm)], ['31', '32'])).
% 2.04/2.29  thf('34', plain,
% 2.04/2.29      (((k3_subset_1 @ sk_A @ sk_B_1) = (k5_xboole_0 @ sk_A @ sk_B_1))),
% 2.04/2.29      inference('sup+', [status(thm)], ['30', '33'])).
% 2.04/2.29  thf('35', plain,
% 2.04/2.29      ((~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_2) @ 
% 2.04/2.29           (k5_xboole_0 @ sk_A @ sk_B_1)))
% 2.04/2.29         <= (~
% 2.04/2.29             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.04/2.29               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 2.04/2.29      inference('demod', [status(thm)], ['1', '19', '34'])).
% 2.04/2.29  thf('36', plain,
% 2.04/2.29      (~
% 2.04/2.29       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.04/2.29         (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 2.04/2.29       ~ ((r1_tarski @ sk_B_1 @ sk_C_2))),
% 2.04/2.29      inference('split', [status(esa)], ['0'])).
% 2.04/2.29  thf('37', plain,
% 2.04/2.29      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 2.04/2.29      inference('sup-', [status(thm)], ['31', '32'])).
% 2.04/2.29  thf(t79_xboole_1, axiom,
% 2.04/2.29    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 2.04/2.29  thf('38', plain,
% 2.04/2.29      (![X31 : $i, X32 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X31 @ X32) @ X32)),
% 2.04/2.29      inference('cnf', [status(esa)], [t79_xboole_1])).
% 2.04/2.29  thf('39', plain, ((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 2.04/2.29      inference('sup+', [status(thm)], ['37', '38'])).
% 2.04/2.29  thf(d1_xboole_0, axiom,
% 2.04/2.29    (![A:$i]:
% 2.04/2.29     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.04/2.29  thf('40', plain,
% 2.04/2.29      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 2.04/2.29      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.04/2.29  thf(t4_xboole_0, axiom,
% 2.04/2.29    (![A:$i,B:$i]:
% 2.04/2.29     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 2.04/2.29            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.04/2.29       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.04/2.29            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 2.04/2.29  thf('41', plain,
% 2.04/2.29      (![X8 : $i, X10 : $i, X11 : $i]:
% 2.04/2.29         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 2.04/2.29          | ~ (r1_xboole_0 @ X8 @ X11))),
% 2.04/2.29      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.04/2.29  thf('42', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i]:
% 2.04/2.29         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 2.04/2.29      inference('sup-', [status(thm)], ['40', '41'])).
% 2.04/2.29  thf('43', plain,
% 2.04/2.29      ((v1_xboole_0 @ (k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 2.04/2.29      inference('sup-', [status(thm)], ['39', '42'])).
% 2.04/2.29  thf('44', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.04/2.29      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.04/2.29  thf('45', plain,
% 2.04/2.29      ((v1_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 2.04/2.29      inference('demod', [status(thm)], ['43', '44'])).
% 2.04/2.29  thf('46', plain,
% 2.04/2.29      (((k3_subset_1 @ sk_A @ sk_B_1) = (k5_xboole_0 @ sk_A @ sk_B_1))),
% 2.04/2.29      inference('sup+', [status(thm)], ['30', '33'])).
% 2.04/2.29  thf('47', plain,
% 2.04/2.29      ((v1_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_A @ sk_B_1)))),
% 2.04/2.29      inference('demod', [status(thm)], ['45', '46'])).
% 2.04/2.29  thf(l13_xboole_0, axiom,
% 2.04/2.29    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 2.04/2.29  thf('48', plain,
% 2.04/2.29      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 2.04/2.29      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.04/2.29  thf('49', plain,
% 2.04/2.29      (((k3_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 2.04/2.29      inference('sup-', [status(thm)], ['47', '48'])).
% 2.04/2.29  thf('50', plain,
% 2.04/2.29      (![X12 : $i, X13 : $i]:
% 2.04/2.29         ((k4_xboole_0 @ X12 @ X13)
% 2.04/2.29           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 2.04/2.29      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.04/2.29  thf('51', plain,
% 2.04/2.29      (((k4_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_A @ sk_B_1))
% 2.04/2.29         = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0))),
% 2.04/2.29      inference('sup+', [status(thm)], ['49', '50'])).
% 2.04/2.29  thf(t4_boole, axiom,
% 2.04/2.29    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 2.04/2.29  thf('52', plain,
% 2.04/2.29      (![X27 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X27) = (k1_xboole_0))),
% 2.04/2.29      inference('cnf', [status(esa)], [t4_boole])).
% 2.04/2.29  thf(t98_xboole_1, axiom,
% 2.04/2.29    (![A:$i,B:$i]:
% 2.04/2.29     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 2.04/2.29  thf('53', plain,
% 2.04/2.29      (![X39 : $i, X40 : $i]:
% 2.04/2.29         ((k2_xboole_0 @ X39 @ X40)
% 2.04/2.29           = (k5_xboole_0 @ X39 @ (k4_xboole_0 @ X40 @ X39)))),
% 2.04/2.29      inference('cnf', [status(esa)], [t98_xboole_1])).
% 2.04/2.29  thf('54', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 2.04/2.29      inference('sup+', [status(thm)], ['52', '53'])).
% 2.04/2.29  thf(t1_boole, axiom,
% 2.04/2.29    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.04/2.29  thf('55', plain, (![X17 : $i]: ((k2_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 2.04/2.29      inference('cnf', [status(esa)], [t1_boole])).
% 2.04/2.29  thf('56', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 2.04/2.29      inference('sup+', [status(thm)], ['54', '55'])).
% 2.04/2.29  thf('57', plain,
% 2.04/2.29      (((k4_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 2.04/2.29      inference('demod', [status(thm)], ['51', '56'])).
% 2.04/2.29  thf('58', plain,
% 2.04/2.29      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.04/2.29         (k3_subset_1 @ sk_A @ sk_B_1))
% 2.04/2.29        | (r1_tarski @ sk_B_1 @ sk_C_2))),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('59', plain,
% 2.04/2.29      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.04/2.29         (k3_subset_1 @ sk_A @ sk_B_1)))
% 2.04/2.29         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.04/2.29               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 2.04/2.29      inference('split', [status(esa)], ['58'])).
% 2.04/2.29  thf(t85_xboole_1, axiom,
% 2.04/2.29    (![A:$i,B:$i,C:$i]:
% 2.04/2.29     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 2.04/2.29  thf('60', plain,
% 2.04/2.29      (![X33 : $i, X34 : $i, X35 : $i]:
% 2.04/2.29         (~ (r1_tarski @ X33 @ X34)
% 2.04/2.29          | (r1_xboole_0 @ X33 @ (k4_xboole_0 @ X35 @ X34)))),
% 2.04/2.29      inference('cnf', [status(esa)], [t85_xboole_1])).
% 2.04/2.29  thf('61', plain,
% 2.04/2.29      ((![X0 : $i]:
% 2.04/2.29          (r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.04/2.29           (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1))))
% 2.04/2.29         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.04/2.29               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 2.04/2.29      inference('sup-', [status(thm)], ['59', '60'])).
% 2.04/2.29  thf('62', plain,
% 2.04/2.29      (((k3_subset_1 @ sk_A @ sk_C_2) = (k5_xboole_0 @ sk_A @ sk_C_2))),
% 2.04/2.29      inference('sup+', [status(thm)], ['15', '18'])).
% 2.04/2.29  thf('63', plain,
% 2.04/2.29      (((k3_subset_1 @ sk_A @ sk_B_1) = (k5_xboole_0 @ sk_A @ sk_B_1))),
% 2.04/2.29      inference('sup+', [status(thm)], ['30', '33'])).
% 2.04/2.29  thf('64', plain,
% 2.04/2.29      ((![X0 : $i]:
% 2.04/2.29          (r1_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_C_2) @ 
% 2.04/2.29           (k4_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_B_1))))
% 2.04/2.29         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.04/2.29               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 2.04/2.29      inference('demod', [status(thm)], ['61', '62', '63'])).
% 2.04/2.29  thf('65', plain,
% 2.04/2.29      (((r1_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_C_2) @ sk_B_1))
% 2.04/2.29         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.04/2.29               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 2.04/2.29      inference('sup+', [status(thm)], ['57', '64'])).
% 2.04/2.29  thf(symmetry_r1_xboole_0, axiom,
% 2.04/2.29    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 2.04/2.29  thf('66', plain,
% 2.04/2.29      (![X6 : $i, X7 : $i]:
% 2.04/2.29         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 2.04/2.29      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.04/2.29  thf('67', plain,
% 2.04/2.29      (((r1_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_A @ sk_C_2)))
% 2.04/2.29         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.04/2.29               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 2.04/2.29      inference('sup-', [status(thm)], ['65', '66'])).
% 2.04/2.29  thf('68', plain,
% 2.04/2.29      (((k4_xboole_0 @ sk_A @ sk_C_2) = (k5_xboole_0 @ sk_A @ sk_C_2))),
% 2.04/2.29      inference('sup+', [status(thm)], ['11', '14'])).
% 2.04/2.29  thf(t39_xboole_1, axiom,
% 2.04/2.29    (![A:$i,B:$i]:
% 2.04/2.29     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.04/2.29  thf('69', plain,
% 2.04/2.29      (![X25 : $i, X26 : $i]:
% 2.04/2.29         ((k2_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25))
% 2.04/2.29           = (k2_xboole_0 @ X25 @ X26))),
% 2.04/2.29      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.04/2.29  thf('70', plain,
% 2.04/2.29      (((k2_xboole_0 @ sk_C_2 @ (k5_xboole_0 @ sk_A @ sk_C_2))
% 2.04/2.29         = (k2_xboole_0 @ sk_C_2 @ sk_A))),
% 2.04/2.29      inference('sup+', [status(thm)], ['68', '69'])).
% 2.04/2.29  thf('71', plain, (((k3_xboole_0 @ sk_C_2 @ sk_A) = (sk_C_2))),
% 2.04/2.29      inference('sup-', [status(thm)], ['9', '10'])).
% 2.04/2.29  thf('72', plain,
% 2.04/2.29      (![X12 : $i, X13 : $i]:
% 2.04/2.29         ((k4_xboole_0 @ X12 @ X13)
% 2.04/2.29           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 2.04/2.29      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.04/2.29  thf('73', plain,
% 2.04/2.29      (((k4_xboole_0 @ sk_C_2 @ sk_A) = (k5_xboole_0 @ sk_C_2 @ sk_C_2))),
% 2.04/2.29      inference('sup+', [status(thm)], ['71', '72'])).
% 2.04/2.29  thf(commutativity_k2_tarski, axiom,
% 2.04/2.29    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 2.04/2.29  thf('74', plain,
% 2.04/2.29      (![X41 : $i, X42 : $i]:
% 2.04/2.29         ((k2_tarski @ X42 @ X41) = (k2_tarski @ X41 @ X42))),
% 2.04/2.29      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 2.04/2.29  thf(l51_zfmisc_1, axiom,
% 2.04/2.29    (![A:$i,B:$i]:
% 2.04/2.29     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.04/2.29  thf('75', plain,
% 2.04/2.29      (![X50 : $i, X51 : $i]:
% 2.04/2.29         ((k3_tarski @ (k2_tarski @ X50 @ X51)) = (k2_xboole_0 @ X50 @ X51))),
% 2.04/2.29      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.04/2.29  thf('76', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i]:
% 2.04/2.29         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 2.04/2.29      inference('sup+', [status(thm)], ['74', '75'])).
% 2.04/2.29  thf('77', plain,
% 2.04/2.29      (![X50 : $i, X51 : $i]:
% 2.04/2.29         ((k3_tarski @ (k2_tarski @ X50 @ X51)) = (k2_xboole_0 @ X50 @ X51))),
% 2.04/2.29      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.04/2.29  thf('78', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.04/2.29      inference('sup+', [status(thm)], ['76', '77'])).
% 2.04/2.29  thf('79', plain, (![X17 : $i]: ((k2_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 2.04/2.29      inference('cnf', [status(esa)], [t1_boole])).
% 2.04/2.29  thf('80', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.04/2.29      inference('sup+', [status(thm)], ['78', '79'])).
% 2.04/2.29  thf('81', plain,
% 2.04/2.29      (![X25 : $i, X26 : $i]:
% 2.04/2.29         ((k2_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25))
% 2.04/2.29           = (k2_xboole_0 @ X25 @ X26))),
% 2.04/2.29      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.04/2.29  thf('82', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 2.04/2.29      inference('sup+', [status(thm)], ['80', '81'])).
% 2.04/2.29  thf('83', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.04/2.29      inference('sup+', [status(thm)], ['78', '79'])).
% 2.04/2.29  thf('84', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 2.04/2.29      inference('demod', [status(thm)], ['82', '83'])).
% 2.04/2.29  thf(t36_xboole_1, axiom,
% 2.04/2.29    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 2.04/2.29  thf('85', plain,
% 2.04/2.29      (![X23 : $i, X24 : $i]: (r1_tarski @ (k4_xboole_0 @ X23 @ X24) @ X23)),
% 2.04/2.29      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.04/2.29  thf('86', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 2.04/2.29      inference('sup+', [status(thm)], ['84', '85'])).
% 2.04/2.29  thf('87', plain,
% 2.04/2.29      (![X45 : $i, X46 : $i, X47 : $i]:
% 2.04/2.29         (~ (r1_tarski @ X45 @ X46)
% 2.04/2.29          | (r2_hidden @ X45 @ X47)
% 2.04/2.29          | ((X47) != (k1_zfmisc_1 @ X46)))),
% 2.04/2.29      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 2.04/2.29  thf('88', plain,
% 2.04/2.29      (![X45 : $i, X46 : $i]:
% 2.04/2.29         ((r2_hidden @ X45 @ (k1_zfmisc_1 @ X46)) | ~ (r1_tarski @ X45 @ X46))),
% 2.04/2.29      inference('simplify', [status(thm)], ['87'])).
% 2.04/2.29  thf('89', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.04/2.29      inference('sup-', [status(thm)], ['86', '88'])).
% 2.04/2.29  thf('90', plain,
% 2.04/2.29      (![X52 : $i, X53 : $i]:
% 2.04/2.29         (~ (r2_hidden @ X52 @ X53)
% 2.04/2.29          | (m1_subset_1 @ X52 @ X53)
% 2.04/2.29          | (v1_xboole_0 @ X53))),
% 2.04/2.29      inference('cnf', [status(esa)], [d2_subset_1])).
% 2.04/2.29  thf('91', plain,
% 2.04/2.29      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 2.04/2.29      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.04/2.29  thf('92', plain,
% 2.04/2.29      (![X52 : $i, X53 : $i]:
% 2.04/2.29         ((m1_subset_1 @ X52 @ X53) | ~ (r2_hidden @ X52 @ X53))),
% 2.04/2.29      inference('clc', [status(thm)], ['90', '91'])).
% 2.04/2.29  thf('93', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.04/2.29      inference('sup-', [status(thm)], ['89', '92'])).
% 2.04/2.29  thf('94', plain,
% 2.04/2.29      (![X55 : $i, X56 : $i]:
% 2.04/2.29         (((k3_subset_1 @ X55 @ X56) = (k4_xboole_0 @ X55 @ X56))
% 2.04/2.29          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ X55)))),
% 2.04/2.29      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.04/2.29  thf('95', plain,
% 2.04/2.29      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 2.04/2.29      inference('sup-', [status(thm)], ['93', '94'])).
% 2.04/2.29  thf('96', plain,
% 2.04/2.29      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 2.04/2.29      inference('sup-', [status(thm)], ['93', '94'])).
% 2.04/2.29  thf('97', plain,
% 2.04/2.29      (![X31 : $i, X32 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X31 @ X32) @ X32)),
% 2.04/2.29      inference('cnf', [status(esa)], [t79_xboole_1])).
% 2.04/2.29  thf('98', plain, (![X0 : $i]: (r1_xboole_0 @ (k3_subset_1 @ X0 @ X0) @ X0)),
% 2.04/2.29      inference('sup+', [status(thm)], ['96', '97'])).
% 2.04/2.29  thf('99', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.04/2.29      inference('sup+', [status(thm)], ['78', '79'])).
% 2.04/2.29  thf(t73_xboole_1, axiom,
% 2.04/2.29    (![A:$i,B:$i,C:$i]:
% 2.04/2.29     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 2.04/2.29       ( r1_tarski @ A @ B ) ))).
% 2.04/2.29  thf('100', plain,
% 2.04/2.29      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.04/2.29         ((r1_tarski @ X28 @ X29)
% 2.04/2.29          | ~ (r1_tarski @ X28 @ (k2_xboole_0 @ X29 @ X30))
% 2.04/2.29          | ~ (r1_xboole_0 @ X28 @ X30))),
% 2.04/2.29      inference('cnf', [status(esa)], [t73_xboole_1])).
% 2.04/2.29  thf('101', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i]:
% 2.04/2.29         (~ (r1_tarski @ X1 @ X0)
% 2.04/2.29          | ~ (r1_xboole_0 @ X1 @ X0)
% 2.04/2.29          | (r1_tarski @ X1 @ k1_xboole_0))),
% 2.04/2.29      inference('sup-', [status(thm)], ['99', '100'])).
% 2.04/2.29  thf('102', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         ((r1_tarski @ (k3_subset_1 @ X0 @ X0) @ k1_xboole_0)
% 2.04/2.29          | ~ (r1_tarski @ (k3_subset_1 @ X0 @ X0) @ X0))),
% 2.04/2.29      inference('sup-', [status(thm)], ['98', '101'])).
% 2.04/2.29  thf('103', plain,
% 2.04/2.29      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 2.04/2.29      inference('sup-', [status(thm)], ['93', '94'])).
% 2.04/2.29  thf('104', plain,
% 2.04/2.29      (![X23 : $i, X24 : $i]: (r1_tarski @ (k4_xboole_0 @ X23 @ X24) @ X23)),
% 2.04/2.29      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.04/2.29  thf('105', plain, (![X0 : $i]: (r1_tarski @ (k3_subset_1 @ X0 @ X0) @ X0)),
% 2.04/2.29      inference('sup+', [status(thm)], ['103', '104'])).
% 2.04/2.29  thf('106', plain,
% 2.04/2.29      (![X0 : $i]: (r1_tarski @ (k3_subset_1 @ X0 @ X0) @ k1_xboole_0)),
% 2.04/2.29      inference('demod', [status(thm)], ['102', '105'])).
% 2.04/2.29  thf('107', plain,
% 2.04/2.29      (![X21 : $i, X22 : $i]:
% 2.04/2.29         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 2.04/2.29      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.04/2.29  thf('108', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         ((k3_xboole_0 @ (k3_subset_1 @ X0 @ X0) @ k1_xboole_0)
% 2.04/2.29           = (k3_subset_1 @ X0 @ X0))),
% 2.04/2.29      inference('sup-', [status(thm)], ['106', '107'])).
% 2.04/2.29  thf('109', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 2.04/2.29      inference('demod', [status(thm)], ['82', '83'])).
% 2.04/2.29  thf('110', plain,
% 2.04/2.29      (![X39 : $i, X40 : $i]:
% 2.04/2.29         ((k2_xboole_0 @ X39 @ X40)
% 2.04/2.29           = (k5_xboole_0 @ X39 @ (k4_xboole_0 @ X40 @ X39)))),
% 2.04/2.29      inference('cnf', [status(esa)], [t98_xboole_1])).
% 2.04/2.29  thf('111', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 2.04/2.29      inference('sup+', [status(thm)], ['109', '110'])).
% 2.04/2.29  thf('112', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.04/2.29      inference('sup+', [status(thm)], ['78', '79'])).
% 2.04/2.29  thf('113', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.04/2.29      inference('sup+', [status(thm)], ['111', '112'])).
% 2.04/2.29  thf('114', plain,
% 2.04/2.29      (![X12 : $i, X13 : $i]:
% 2.04/2.29         ((k4_xboole_0 @ X12 @ X13)
% 2.04/2.29           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 2.04/2.29      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.04/2.29  thf('115', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 2.04/2.29      inference('sup+', [status(thm)], ['113', '114'])).
% 2.04/2.29  thf('116', plain,
% 2.04/2.29      (![X27 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X27) = (k1_xboole_0))),
% 2.04/2.29      inference('cnf', [status(esa)], [t4_boole])).
% 2.04/2.29  thf('117', plain,
% 2.04/2.29      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.04/2.29      inference('sup+', [status(thm)], ['115', '116'])).
% 2.04/2.29  thf('118', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.04/2.29      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.04/2.29  thf('119', plain,
% 2.04/2.29      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.04/2.29      inference('sup+', [status(thm)], ['117', '118'])).
% 2.04/2.29  thf('120', plain, (![X0 : $i]: ((k1_xboole_0) = (k3_subset_1 @ X0 @ X0))),
% 2.04/2.29      inference('demod', [status(thm)], ['108', '119'])).
% 2.04/2.29  thf('121', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 2.04/2.29      inference('demod', [status(thm)], ['95', '120'])).
% 2.04/2.29  thf('122', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 2.04/2.29      inference('sup+', [status(thm)], ['84', '85'])).
% 2.04/2.29  thf('123', plain,
% 2.04/2.29      (![X21 : $i, X22 : $i]:
% 2.04/2.29         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 2.04/2.29      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.04/2.29  thf('124', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 2.04/2.29      inference('sup-', [status(thm)], ['122', '123'])).
% 2.04/2.29  thf('125', plain,
% 2.04/2.29      (![X12 : $i, X13 : $i]:
% 2.04/2.29         ((k4_xboole_0 @ X12 @ X13)
% 2.04/2.29           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 2.04/2.29      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.04/2.29  thf('126', plain,
% 2.04/2.29      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 2.04/2.29      inference('sup+', [status(thm)], ['124', '125'])).
% 2.04/2.29  thf('127', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 2.04/2.29      inference('sup+', [status(thm)], ['121', '126'])).
% 2.04/2.29  thf('128', plain, (((k4_xboole_0 @ sk_C_2 @ sk_A) = (k1_xboole_0))),
% 2.04/2.29      inference('demod', [status(thm)], ['73', '127'])).
% 2.04/2.29  thf('129', plain,
% 2.04/2.29      (![X25 : $i, X26 : $i]:
% 2.04/2.29         ((k2_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25))
% 2.04/2.29           = (k2_xboole_0 @ X25 @ X26))),
% 2.04/2.29      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.04/2.29  thf('130', plain,
% 2.04/2.29      (((k2_xboole_0 @ sk_A @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_C_2))),
% 2.04/2.29      inference('sup+', [status(thm)], ['128', '129'])).
% 2.04/2.29  thf('131', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.04/2.29      inference('sup+', [status(thm)], ['76', '77'])).
% 2.04/2.29  thf('132', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.04/2.29      inference('sup+', [status(thm)], ['78', '79'])).
% 2.04/2.29  thf('133', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.04/2.29      inference('sup+', [status(thm)], ['76', '77'])).
% 2.04/2.29  thf('134', plain, (((sk_A) = (k2_xboole_0 @ sk_C_2 @ sk_A))),
% 2.04/2.29      inference('demod', [status(thm)], ['130', '131', '132', '133'])).
% 2.04/2.29  thf('135', plain,
% 2.04/2.29      (((k2_xboole_0 @ sk_C_2 @ (k5_xboole_0 @ sk_A @ sk_C_2)) = (sk_A))),
% 2.04/2.29      inference('demod', [status(thm)], ['70', '134'])).
% 2.04/2.29  thf('136', plain,
% 2.04/2.29      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.04/2.29         ((r1_tarski @ X28 @ X29)
% 2.04/2.29          | ~ (r1_tarski @ X28 @ (k2_xboole_0 @ X29 @ X30))
% 2.04/2.29          | ~ (r1_xboole_0 @ X28 @ X30))),
% 2.04/2.29      inference('cnf', [status(esa)], [t73_xboole_1])).
% 2.04/2.29  thf('137', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         (~ (r1_tarski @ X0 @ sk_A)
% 2.04/2.29          | ~ (r1_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_C_2))
% 2.04/2.29          | (r1_tarski @ X0 @ sk_C_2))),
% 2.04/2.29      inference('sup-', [status(thm)], ['135', '136'])).
% 2.04/2.29  thf('138', plain,
% 2.04/2.29      ((((r1_tarski @ sk_B_1 @ sk_C_2) | ~ (r1_tarski @ sk_B_1 @ sk_A)))
% 2.04/2.29         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.04/2.29               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 2.04/2.29      inference('sup-', [status(thm)], ['67', '137'])).
% 2.04/2.29  thf('139', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 2.04/2.29      inference('sup-', [status(thm)], ['24', '25'])).
% 2.04/2.29  thf('140', plain,
% 2.04/2.29      (((r1_tarski @ sk_B_1 @ sk_C_2))
% 2.04/2.29         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.04/2.29               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 2.04/2.29      inference('demod', [status(thm)], ['138', '139'])).
% 2.04/2.29  thf('141', plain,
% 2.04/2.29      ((~ (r1_tarski @ sk_B_1 @ sk_C_2)) <= (~ ((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 2.04/2.29      inference('split', [status(esa)], ['0'])).
% 2.04/2.29  thf('142', plain,
% 2.04/2.29      (((r1_tarski @ sk_B_1 @ sk_C_2)) | 
% 2.04/2.29       ~
% 2.04/2.29       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.04/2.29         (k3_subset_1 @ sk_A @ sk_B_1)))),
% 2.04/2.29      inference('sup-', [status(thm)], ['140', '141'])).
% 2.04/2.29  thf('143', plain,
% 2.04/2.29      (~
% 2.04/2.29       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.04/2.29         (k3_subset_1 @ sk_A @ sk_B_1)))),
% 2.04/2.29      inference('sat_resolution*', [status(thm)], ['36', '142'])).
% 2.04/2.29  thf('144', plain,
% 2.04/2.29      (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_2) @ 
% 2.04/2.29          (k5_xboole_0 @ sk_A @ sk_B_1))),
% 2.04/2.29      inference('simpl_trail', [status(thm)], ['35', '143'])).
% 2.04/2.29  thf('145', plain,
% 2.04/2.29      (((k4_xboole_0 @ sk_A @ sk_C_2) = (k5_xboole_0 @ sk_A @ sk_C_2))),
% 2.04/2.29      inference('sup+', [status(thm)], ['11', '14'])).
% 2.04/2.29  thf('146', plain,
% 2.04/2.29      (![X23 : $i, X24 : $i]: (r1_tarski @ (k4_xboole_0 @ X23 @ X24) @ X23)),
% 2.04/2.29      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.04/2.29  thf('147', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_2) @ sk_A)),
% 2.04/2.29      inference('sup+', [status(thm)], ['145', '146'])).
% 2.04/2.29  thf('148', plain,
% 2.04/2.29      (((k3_subset_1 @ sk_A @ sk_C_2) = (k4_xboole_0 @ sk_A @ sk_C_2))),
% 2.04/2.29      inference('sup-', [status(thm)], ['16', '17'])).
% 2.04/2.29  thf('149', plain,
% 2.04/2.29      (((r1_tarski @ sk_B_1 @ sk_C_2)) <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 2.04/2.29      inference('split', [status(esa)], ['58'])).
% 2.04/2.29  thf('150', plain,
% 2.04/2.29      (![X33 : $i, X34 : $i, X35 : $i]:
% 2.04/2.29         (~ (r1_tarski @ X33 @ X34)
% 2.04/2.29          | (r1_xboole_0 @ X33 @ (k4_xboole_0 @ X35 @ X34)))),
% 2.04/2.29      inference('cnf', [status(esa)], [t85_xboole_1])).
% 2.04/2.29  thf('151', plain,
% 2.04/2.29      ((![X0 : $i]: (r1_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ X0 @ sk_C_2)))
% 2.04/2.29         <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 2.04/2.29      inference('sup-', [status(thm)], ['149', '150'])).
% 2.04/2.29  thf('152', plain,
% 2.04/2.29      (![X6 : $i, X7 : $i]:
% 2.04/2.29         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 2.04/2.29      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.04/2.29  thf('153', plain,
% 2.04/2.29      ((![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_2) @ sk_B_1))
% 2.04/2.29         <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 2.04/2.29      inference('sup-', [status(thm)], ['151', '152'])).
% 2.04/2.29  thf('154', plain,
% 2.04/2.29      (((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_2) @ sk_B_1))
% 2.04/2.29         <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 2.04/2.29      inference('sup+', [status(thm)], ['148', '153'])).
% 2.04/2.29  thf(t86_xboole_1, axiom,
% 2.04/2.29    (![A:$i,B:$i,C:$i]:
% 2.04/2.29     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 2.04/2.29       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 2.04/2.29  thf('155', plain,
% 2.04/2.29      (![X36 : $i, X37 : $i, X38 : $i]:
% 2.04/2.29         (~ (r1_tarski @ X36 @ X37)
% 2.04/2.29          | ~ (r1_xboole_0 @ X36 @ X38)
% 2.04/2.29          | (r1_tarski @ X36 @ (k4_xboole_0 @ X37 @ X38)))),
% 2.04/2.29      inference('cnf', [status(esa)], [t86_xboole_1])).
% 2.04/2.29  thf('156', plain,
% 2.04/2.29      ((![X0 : $i]:
% 2.04/2.29          ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.04/2.29            (k4_xboole_0 @ X0 @ sk_B_1))
% 2.04/2.29           | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ X0)))
% 2.04/2.29         <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 2.04/2.29      inference('sup-', [status(thm)], ['154', '155'])).
% 2.04/2.29  thf('157', plain,
% 2.04/2.29      (((k3_subset_1 @ sk_A @ sk_C_2) = (k5_xboole_0 @ sk_A @ sk_C_2))),
% 2.04/2.29      inference('sup+', [status(thm)], ['15', '18'])).
% 2.04/2.29  thf('158', plain,
% 2.04/2.29      (((k3_subset_1 @ sk_A @ sk_C_2) = (k5_xboole_0 @ sk_A @ sk_C_2))),
% 2.04/2.29      inference('sup+', [status(thm)], ['15', '18'])).
% 2.04/2.29  thf('159', plain,
% 2.04/2.29      ((![X0 : $i]:
% 2.04/2.29          ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_2) @ 
% 2.04/2.29            (k4_xboole_0 @ X0 @ sk_B_1))
% 2.04/2.29           | ~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_2) @ X0)))
% 2.04/2.29         <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 2.04/2.29      inference('demod', [status(thm)], ['156', '157', '158'])).
% 2.04/2.29  thf('160', plain,
% 2.04/2.29      (((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_2) @ 
% 2.04/2.29         (k4_xboole_0 @ sk_A @ sk_B_1))) <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 2.04/2.29      inference('sup-', [status(thm)], ['147', '159'])).
% 2.04/2.29  thf('161', plain,
% 2.04/2.29      (((k4_xboole_0 @ sk_A @ sk_B_1) = (k5_xboole_0 @ sk_A @ sk_B_1))),
% 2.04/2.29      inference('sup+', [status(thm)], ['28', '29'])).
% 2.04/2.29  thf('162', plain,
% 2.04/2.29      (((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_2) @ 
% 2.04/2.29         (k5_xboole_0 @ sk_A @ sk_B_1))) <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 2.04/2.29      inference('demod', [status(thm)], ['160', '161'])).
% 2.04/2.29  thf('163', plain,
% 2.04/2.29      (((r1_tarski @ sk_B_1 @ sk_C_2)) | 
% 2.04/2.29       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 2.04/2.29         (k3_subset_1 @ sk_A @ sk_B_1)))),
% 2.04/2.29      inference('split', [status(esa)], ['58'])).
% 2.04/2.29  thf('164', plain, (((r1_tarski @ sk_B_1 @ sk_C_2))),
% 2.04/2.29      inference('sat_resolution*', [status(thm)], ['36', '142', '163'])).
% 2.04/2.29  thf('165', plain,
% 2.04/2.29      ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_2) @ 
% 2.04/2.29        (k5_xboole_0 @ sk_A @ sk_B_1))),
% 2.04/2.29      inference('simpl_trail', [status(thm)], ['162', '164'])).
% 2.04/2.29  thf('166', plain, ($false), inference('demod', [status(thm)], ['144', '165'])).
% 2.04/2.29  
% 2.04/2.29  % SZS output end Refutation
% 2.04/2.29  
% 2.12/2.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
