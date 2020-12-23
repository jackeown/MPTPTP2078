%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YCg21S9LV6

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:04 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 164 expanded)
%              Number of leaves         :   26 (  56 expanded)
%              Depth                    :   22
%              Number of atoms          :  603 (1457 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t44_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) )
          <=> ( r1_tarski @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) )
            <=> ( r1_tarski @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_subset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_5 )
    | ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_5 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_5 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_5 )
    | ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    m1_subset_1 @ sk_C_5 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k3_subset_1 @ X43 @ X44 )
        = ( k4_xboole_0 @ X43 @ X44 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_5 )
    = ( k4_xboole_0 @ sk_A @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('6',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X29 @ X30 ) @ X30 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('11',plain,
    ( ( r1_tarski @ sk_B @ sk_C_5 )
    | ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r1_tarski @ sk_B @ sk_C_5 )
   <= ( r1_tarski @ sk_B @ sk_C_5 ) ),
    inference(split,[status(esa)],['11'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_C_5 )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ! [X0: $i] :
        ( ( r1_xboole_0 @ sk_B @ X0 )
        | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ sk_C_5 ) )
   <= ( r1_tarski @ sk_B @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_xboole_0 @ sk_B @ X0 )
        | ~ ( r1_xboole_0 @ sk_C_5 @ X1 )
        | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ X1 ) )
   <= ( r1_tarski @ sk_B @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ( r1_xboole_0 @ sk_B @ X0 )
        | ~ ( r1_xboole_0 @ sk_C_5 @ X0 )
        | ( r1_xboole_0 @ sk_B @ X0 ) )
   <= ( r1_tarski @ sk_B @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ sk_C_5 @ X0 )
        | ( r1_xboole_0 @ sk_B @ X0 ) )
   <= ( r1_tarski @ sk_B @ sk_C_5 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_5 ) )
   <= ( r1_tarski @ sk_B @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['8','19'])).

thf('21',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_5 ) )
   <= ( r1_tarski @ sk_B @ sk_C_5 ) ),
    inference('sup+',[status(thm)],['5','20'])).

thf('22',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_5 ) )
   <= ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_5 ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C_5 ) ),
    inference('sat_resolution*',[status(thm)],['2','23'])).

thf('25',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C_5 ) ),
    inference(simpl_trail,[status(thm)],['1','24'])).

thf('26',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_5 ) )
   <= ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ) ),
    inference(split,[status(esa)],['11'])).

thf('27',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_5 ) )
    | ( r1_tarski @ sk_B @ sk_C_5 ) ),
    inference(split,[status(esa)],['11'])).

thf('28',plain,(
    r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ),
    inference('sat_resolution*',[status(thm)],['2','23','27'])).

thf('29',plain,(
    r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_5 ) ),
    inference(simpl_trail,[status(thm)],['26','28'])).

thf('30',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_5 )
    = ( k4_xboole_0 @ sk_A @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t81_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('31',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( r1_xboole_0 @ X31 @ ( k4_xboole_0 @ X32 @ X33 ) )
      | ~ ( r1_xboole_0 @ X32 @ ( k4_xboole_0 @ X31 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_5 ) )
      | ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C_5 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('35',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C_5 ) @ sk_A ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('38',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ X45 @ X46 )
      | ( r2_hidden @ X45 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('42',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ sk_A )
      | ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_A )
      | ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['35','45'])).

thf('47',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('48',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C_5 ) @ sk_B ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('49',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X37 @ X38 ) @ X38 )
        = X37 )
      | ~ ( r1_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('50',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C_5 ) @ sk_B ) @ sk_B )
    = ( k4_xboole_0 @ sk_B @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('51',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X25 @ X26 ) @ X25 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('52',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_xboole_0 @ X21 @ X20 )
        = X20 )
      | ~ ( r1_tarski @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('55',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('58',plain,(
    ! [X17: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ X17 @ X19 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_B @ sk_C_5 ) ),
    inference(demod,[status(thm)],['50','53','59'])).

thf('61',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ( ( k4_xboole_0 @ X17 @ X18 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('62',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    r1_tarski @ sk_B @ sk_C_5 ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['25','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YCg21S9LV6
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:58:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.61/0.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.61/0.82  % Solved by: fo/fo7.sh
% 0.61/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.82  % done 877 iterations in 0.364s
% 0.61/0.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.61/0.82  % SZS output start Refutation
% 0.61/0.82  thf(sk_C_5_type, type, sk_C_5: $i).
% 0.61/0.82  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.61/0.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.61/0.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.61/0.82  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.61/0.82  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.61/0.82  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.61/0.82  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.61/0.82  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.61/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.82  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.61/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.61/0.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.82  thf(t44_subset_1, conjecture,
% 0.61/0.82    (![A:$i,B:$i]:
% 0.61/0.82     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.61/0.82       ( ![C:$i]:
% 0.61/0.82         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.61/0.82           ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 0.61/0.82             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.61/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.82    (~( ![A:$i,B:$i]:
% 0.61/0.82        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.61/0.82          ( ![C:$i]:
% 0.61/0.82            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.61/0.82              ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 0.61/0.82                ( r1_tarski @ B @ C ) ) ) ) ) )),
% 0.61/0.82    inference('cnf.neg', [status(esa)], [t44_subset_1])).
% 0.61/0.82  thf('0', plain,
% 0.61/0.82      ((~ (r1_tarski @ sk_B @ sk_C_5)
% 0.61/0.82        | ~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('1', plain,
% 0.61/0.82      ((~ (r1_tarski @ sk_B @ sk_C_5)) <= (~ ((r1_tarski @ sk_B @ sk_C_5)))),
% 0.61/0.82      inference('split', [status(esa)], ['0'])).
% 0.61/0.82  thf('2', plain,
% 0.61/0.82      (~ ((r1_tarski @ sk_B @ sk_C_5)) | 
% 0.61/0.82       ~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)))),
% 0.61/0.82      inference('split', [status(esa)], ['0'])).
% 0.61/0.82  thf('3', plain, ((m1_subset_1 @ sk_C_5 @ (k1_zfmisc_1 @ sk_A))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf(d5_subset_1, axiom,
% 0.61/0.82    (![A:$i,B:$i]:
% 0.61/0.82     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.61/0.82       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.61/0.82  thf('4', plain,
% 0.61/0.82      (![X43 : $i, X44 : $i]:
% 0.61/0.82         (((k3_subset_1 @ X43 @ X44) = (k4_xboole_0 @ X43 @ X44))
% 0.61/0.82          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X43)))),
% 0.61/0.82      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.61/0.82  thf('5', plain,
% 0.61/0.82      (((k3_subset_1 @ sk_A @ sk_C_5) = (k4_xboole_0 @ sk_A @ sk_C_5))),
% 0.61/0.82      inference('sup-', [status(thm)], ['3', '4'])).
% 0.61/0.82  thf(t79_xboole_1, axiom,
% 0.61/0.82    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.61/0.82  thf('6', plain,
% 0.61/0.82      (![X29 : $i, X30 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X29 @ X30) @ X30)),
% 0.61/0.82      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.61/0.82  thf(symmetry_r1_xboole_0, axiom,
% 0.61/0.82    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.61/0.82  thf('7', plain,
% 0.61/0.82      (![X7 : $i, X8 : $i]:
% 0.61/0.82         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 0.61/0.82      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.61/0.82  thf('8', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.61/0.82      inference('sup-', [status(thm)], ['6', '7'])).
% 0.61/0.82  thf(t3_xboole_0, axiom,
% 0.61/0.82    (![A:$i,B:$i]:
% 0.61/0.82     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.61/0.82            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.61/0.82       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.61/0.82            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.61/0.82  thf('9', plain,
% 0.61/0.82      (![X9 : $i, X10 : $i]:
% 0.61/0.82         ((r1_xboole_0 @ X9 @ X10) | (r2_hidden @ (sk_C_1 @ X10 @ X9) @ X10))),
% 0.61/0.82      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.61/0.82  thf('10', plain,
% 0.61/0.82      (![X9 : $i, X10 : $i]:
% 0.61/0.82         ((r1_xboole_0 @ X9 @ X10) | (r2_hidden @ (sk_C_1 @ X10 @ X9) @ X9))),
% 0.61/0.82      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.61/0.82  thf('11', plain,
% 0.61/0.82      (((r1_tarski @ sk_B @ sk_C_5)
% 0.61/0.82        | (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('12', plain,
% 0.61/0.82      (((r1_tarski @ sk_B @ sk_C_5)) <= (((r1_tarski @ sk_B @ sk_C_5)))),
% 0.61/0.82      inference('split', [status(esa)], ['11'])).
% 0.61/0.82  thf(d3_tarski, axiom,
% 0.61/0.82    (![A:$i,B:$i]:
% 0.61/0.82     ( ( r1_tarski @ A @ B ) <=>
% 0.61/0.82       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.61/0.82  thf('13', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.82         (~ (r2_hidden @ X0 @ X1)
% 0.61/0.82          | (r2_hidden @ X0 @ X2)
% 0.61/0.82          | ~ (r1_tarski @ X1 @ X2))),
% 0.61/0.82      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.82  thf('14', plain,
% 0.61/0.82      ((![X0 : $i]: ((r2_hidden @ X0 @ sk_C_5) | ~ (r2_hidden @ X0 @ sk_B)))
% 0.61/0.82         <= (((r1_tarski @ sk_B @ sk_C_5)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['12', '13'])).
% 0.61/0.82  thf('15', plain,
% 0.61/0.82      ((![X0 : $i]:
% 0.61/0.82          ((r1_xboole_0 @ sk_B @ X0)
% 0.61/0.82           | (r2_hidden @ (sk_C_1 @ X0 @ sk_B) @ sk_C_5)))
% 0.61/0.82         <= (((r1_tarski @ sk_B @ sk_C_5)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['10', '14'])).
% 0.61/0.82  thf('16', plain,
% 0.61/0.82      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.61/0.82         (~ (r2_hidden @ X11 @ X9)
% 0.61/0.82          | ~ (r2_hidden @ X11 @ X12)
% 0.61/0.82          | ~ (r1_xboole_0 @ X9 @ X12))),
% 0.61/0.82      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.61/0.82  thf('17', plain,
% 0.61/0.82      ((![X0 : $i, X1 : $i]:
% 0.61/0.82          ((r1_xboole_0 @ sk_B @ X0)
% 0.61/0.82           | ~ (r1_xboole_0 @ sk_C_5 @ X1)
% 0.61/0.82           | ~ (r2_hidden @ (sk_C_1 @ X0 @ sk_B) @ X1)))
% 0.61/0.82         <= (((r1_tarski @ sk_B @ sk_C_5)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['15', '16'])).
% 0.61/0.82  thf('18', plain,
% 0.61/0.82      ((![X0 : $i]:
% 0.61/0.82          ((r1_xboole_0 @ sk_B @ X0)
% 0.61/0.82           | ~ (r1_xboole_0 @ sk_C_5 @ X0)
% 0.61/0.82           | (r1_xboole_0 @ sk_B @ X0)))
% 0.61/0.82         <= (((r1_tarski @ sk_B @ sk_C_5)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['9', '17'])).
% 0.61/0.82  thf('19', plain,
% 0.61/0.82      ((![X0 : $i]: (~ (r1_xboole_0 @ sk_C_5 @ X0) | (r1_xboole_0 @ sk_B @ X0)))
% 0.61/0.82         <= (((r1_tarski @ sk_B @ sk_C_5)))),
% 0.61/0.82      inference('simplify', [status(thm)], ['18'])).
% 0.61/0.82  thf('20', plain,
% 0.61/0.82      ((![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_5)))
% 0.61/0.82         <= (((r1_tarski @ sk_B @ sk_C_5)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['8', '19'])).
% 0.61/0.82  thf('21', plain,
% 0.61/0.82      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)))
% 0.61/0.82         <= (((r1_tarski @ sk_B @ sk_C_5)))),
% 0.61/0.82      inference('sup+', [status(thm)], ['5', '20'])).
% 0.61/0.82  thf('22', plain,
% 0.61/0.82      ((~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)))
% 0.61/0.82         <= (~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5))))),
% 0.61/0.82      inference('split', [status(esa)], ['0'])).
% 0.61/0.82  thf('23', plain,
% 0.61/0.82      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5))) | 
% 0.61/0.82       ~ ((r1_tarski @ sk_B @ sk_C_5))),
% 0.61/0.82      inference('sup-', [status(thm)], ['21', '22'])).
% 0.61/0.82  thf('24', plain, (~ ((r1_tarski @ sk_B @ sk_C_5))),
% 0.61/0.82      inference('sat_resolution*', [status(thm)], ['2', '23'])).
% 0.61/0.82  thf('25', plain, (~ (r1_tarski @ sk_B @ sk_C_5)),
% 0.61/0.82      inference('simpl_trail', [status(thm)], ['1', '24'])).
% 0.61/0.82  thf('26', plain,
% 0.61/0.82      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)))
% 0.61/0.82         <= (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5))))),
% 0.61/0.82      inference('split', [status(esa)], ['11'])).
% 0.61/0.82  thf('27', plain,
% 0.61/0.82      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5))) | 
% 0.61/0.82       ((r1_tarski @ sk_B @ sk_C_5))),
% 0.61/0.82      inference('split', [status(esa)], ['11'])).
% 0.61/0.82  thf('28', plain, (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5)))),
% 0.61/0.82      inference('sat_resolution*', [status(thm)], ['2', '23', '27'])).
% 0.61/0.82  thf('29', plain, ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_5))),
% 0.61/0.82      inference('simpl_trail', [status(thm)], ['26', '28'])).
% 0.61/0.82  thf('30', plain,
% 0.61/0.82      (((k3_subset_1 @ sk_A @ sk_C_5) = (k4_xboole_0 @ sk_A @ sk_C_5))),
% 0.61/0.82      inference('sup-', [status(thm)], ['3', '4'])).
% 0.61/0.82  thf(t81_xboole_1, axiom,
% 0.61/0.82    (![A:$i,B:$i,C:$i]:
% 0.61/0.82     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.61/0.82       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.61/0.82  thf('31', plain,
% 0.61/0.82      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.61/0.82         ((r1_xboole_0 @ X31 @ (k4_xboole_0 @ X32 @ X33))
% 0.61/0.82          | ~ (r1_xboole_0 @ X32 @ (k4_xboole_0 @ X31 @ X33)))),
% 0.61/0.82      inference('cnf', [status(esa)], [t81_xboole_1])).
% 0.61/0.82  thf('32', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         (~ (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_5))
% 0.61/0.82          | (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C_5)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['30', '31'])).
% 0.61/0.82  thf('33', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_5))),
% 0.61/0.82      inference('sup-', [status(thm)], ['29', '32'])).
% 0.61/0.82  thf('34', plain,
% 0.61/0.82      (![X7 : $i, X8 : $i]:
% 0.61/0.82         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 0.61/0.82      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.61/0.82  thf('35', plain, ((r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C_5) @ sk_A)),
% 0.61/0.82      inference('sup-', [status(thm)], ['33', '34'])).
% 0.61/0.82  thf('36', plain,
% 0.61/0.82      (![X9 : $i, X10 : $i]:
% 0.61/0.82         ((r1_xboole_0 @ X9 @ X10) | (r2_hidden @ (sk_C_1 @ X10 @ X9) @ X9))),
% 0.61/0.82      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.61/0.82  thf('37', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf(l3_subset_1, axiom,
% 0.61/0.82    (![A:$i,B:$i]:
% 0.61/0.82     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.61/0.82       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.61/0.82  thf('38', plain,
% 0.61/0.82      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.61/0.82         (~ (r2_hidden @ X45 @ X46)
% 0.61/0.82          | (r2_hidden @ X45 @ X47)
% 0.61/0.82          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47)))),
% 0.61/0.82      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.61/0.82  thf('39', plain,
% 0.61/0.82      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.61/0.82      inference('sup-', [status(thm)], ['37', '38'])).
% 0.61/0.82  thf('40', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         ((r1_xboole_0 @ sk_B @ X0) | (r2_hidden @ (sk_C_1 @ X0 @ sk_B) @ sk_A))),
% 0.61/0.82      inference('sup-', [status(thm)], ['36', '39'])).
% 0.61/0.82  thf('41', plain,
% 0.61/0.82      (![X9 : $i, X10 : $i]:
% 0.61/0.82         ((r1_xboole_0 @ X9 @ X10) | (r2_hidden @ (sk_C_1 @ X10 @ X9) @ X10))),
% 0.61/0.82      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.61/0.82  thf('42', plain,
% 0.61/0.82      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.61/0.82         (~ (r2_hidden @ X11 @ X9)
% 0.61/0.82          | ~ (r2_hidden @ X11 @ X12)
% 0.61/0.82          | ~ (r1_xboole_0 @ X9 @ X12))),
% 0.61/0.82      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.61/0.82  thf('43', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.82         ((r1_xboole_0 @ X1 @ X0)
% 0.61/0.82          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.61/0.82          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 0.61/0.82      inference('sup-', [status(thm)], ['41', '42'])).
% 0.61/0.82  thf('44', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         ((r1_xboole_0 @ sk_B @ X0)
% 0.61/0.82          | ~ (r1_xboole_0 @ X0 @ sk_A)
% 0.61/0.82          | (r1_xboole_0 @ sk_B @ X0))),
% 0.61/0.82      inference('sup-', [status(thm)], ['40', '43'])).
% 0.61/0.82  thf('45', plain,
% 0.61/0.82      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ sk_A) | (r1_xboole_0 @ sk_B @ X0))),
% 0.61/0.82      inference('simplify', [status(thm)], ['44'])).
% 0.61/0.82  thf('46', plain, ((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C_5))),
% 0.61/0.82      inference('sup-', [status(thm)], ['35', '45'])).
% 0.61/0.82  thf('47', plain,
% 0.61/0.82      (![X7 : $i, X8 : $i]:
% 0.61/0.82         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 0.61/0.82      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.61/0.82  thf('48', plain, ((r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C_5) @ sk_B)),
% 0.61/0.82      inference('sup-', [status(thm)], ['46', '47'])).
% 0.61/0.82  thf(t88_xboole_1, axiom,
% 0.61/0.82    (![A:$i,B:$i]:
% 0.61/0.82     ( ( r1_xboole_0 @ A @ B ) =>
% 0.61/0.82       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 0.61/0.82  thf('49', plain,
% 0.61/0.82      (![X37 : $i, X38 : $i]:
% 0.61/0.82         (((k4_xboole_0 @ (k2_xboole_0 @ X37 @ X38) @ X38) = (X37))
% 0.61/0.82          | ~ (r1_xboole_0 @ X37 @ X38))),
% 0.61/0.82      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.61/0.82  thf('50', plain,
% 0.61/0.82      (((k4_xboole_0 @ (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C_5) @ sk_B) @ 
% 0.61/0.82         sk_B) = (k4_xboole_0 @ sk_B @ sk_C_5))),
% 0.61/0.82      inference('sup-', [status(thm)], ['48', '49'])).
% 0.61/0.82  thf(t36_xboole_1, axiom,
% 0.61/0.82    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.61/0.82  thf('51', plain,
% 0.61/0.82      (![X25 : $i, X26 : $i]: (r1_tarski @ (k4_xboole_0 @ X25 @ X26) @ X25)),
% 0.61/0.82      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.61/0.82  thf(t12_xboole_1, axiom,
% 0.61/0.82    (![A:$i,B:$i]:
% 0.61/0.82     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.61/0.82  thf('52', plain,
% 0.61/0.82      (![X20 : $i, X21 : $i]:
% 0.61/0.82         (((k2_xboole_0 @ X21 @ X20) = (X20)) | ~ (r1_tarski @ X21 @ X20))),
% 0.61/0.82      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.61/0.82  thf('53', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.61/0.82      inference('sup-', [status(thm)], ['51', '52'])).
% 0.61/0.82  thf('54', plain,
% 0.61/0.82      (![X1 : $i, X3 : $i]:
% 0.61/0.82         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.61/0.82      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.82  thf('55', plain,
% 0.61/0.82      (![X1 : $i, X3 : $i]:
% 0.61/0.82         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.61/0.82      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.82  thf('56', plain,
% 0.61/0.82      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.61/0.82      inference('sup-', [status(thm)], ['54', '55'])).
% 0.61/0.82  thf('57', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.61/0.82      inference('simplify', [status(thm)], ['56'])).
% 0.61/0.82  thf(l32_xboole_1, axiom,
% 0.61/0.82    (![A:$i,B:$i]:
% 0.61/0.82     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.61/0.82  thf('58', plain,
% 0.61/0.82      (![X17 : $i, X19 : $i]:
% 0.61/0.82         (((k4_xboole_0 @ X17 @ X19) = (k1_xboole_0))
% 0.61/0.82          | ~ (r1_tarski @ X17 @ X19))),
% 0.61/0.82      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.61/0.82  thf('59', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.61/0.82      inference('sup-', [status(thm)], ['57', '58'])).
% 0.61/0.82  thf('60', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_C_5))),
% 0.61/0.82      inference('demod', [status(thm)], ['50', '53', '59'])).
% 0.61/0.82  thf('61', plain,
% 0.61/0.82      (![X17 : $i, X18 : $i]:
% 0.61/0.82         ((r1_tarski @ X17 @ X18)
% 0.61/0.82          | ((k4_xboole_0 @ X17 @ X18) != (k1_xboole_0)))),
% 0.61/0.82      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.61/0.82  thf('62', plain,
% 0.61/0.82      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_B @ sk_C_5))),
% 0.61/0.82      inference('sup-', [status(thm)], ['60', '61'])).
% 0.61/0.82  thf('63', plain, ((r1_tarski @ sk_B @ sk_C_5)),
% 0.61/0.82      inference('simplify', [status(thm)], ['62'])).
% 0.61/0.82  thf('64', plain, ($false), inference('demod', [status(thm)], ['25', '63'])).
% 0.61/0.82  
% 0.61/0.82  % SZS output end Refutation
% 0.61/0.82  
% 0.61/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
