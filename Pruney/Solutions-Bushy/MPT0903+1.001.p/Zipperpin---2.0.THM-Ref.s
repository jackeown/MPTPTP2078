%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0903+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oQ19b055QI

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:41 EST 2020

% Result     : Theorem 3.47s
% Output     : Refutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :  197 (1360 expanded)
%              Number of leaves         :   34 ( 433 expanded)
%              Depth                    :   45
%              Number of atoms          : 2064 (17336 expanded)
%              Number of equality atoms :  223 (1480 expanded)
%              Maximal formula depth    :   23 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t63_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ~ ( ~ ( r1_tarski @ A @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
          & ~ ( r1_tarski @ A @ ( k4_zfmisc_1 @ B @ C @ D @ A ) )
          & ~ ( r1_tarski @ A @ ( k4_zfmisc_1 @ C @ D @ A @ B ) )
          & ~ ( r1_tarski @ A @ ( k4_zfmisc_1 @ D @ A @ B @ C ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ~ ( ~ ( r1_tarski @ A @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
            & ~ ( r1_tarski @ A @ ( k4_zfmisc_1 @ B @ C @ D @ A ) )
            & ~ ( r1_tarski @ A @ ( k4_zfmisc_1 @ C @ D @ A @ B ) )
            & ~ ( r1_tarski @ A @ ( k4_zfmisc_1 @ D @ A @ B @ C ) ) )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t63_mcart_1])).

thf('0',plain,
    ( ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) )
    | ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_B_1 @ sk_C @ sk_D @ sk_A ) )
    | ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_C @ sk_D @ sk_A @ sk_B_1 ) )
    | ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_C @ sk_D @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_C @ sk_D @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t54_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C @ D )
      = ( k4_zfmisc_1 @ A @ B @ C @ D ) ) )).

thf('3',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) @ X38 @ X39 )
      = ( k4_zfmisc_1 @ X36 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t54_mcart_1])).

thf(t49_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ A @ B @ C ) )
          & ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ B @ C @ A ) )
          & ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ C @ A @ B ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X30 = k1_xboole_0 )
      | ~ ( r1_tarski @ X30 @ ( k3_zfmisc_1 @ X32 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t49_mcart_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('5',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('6',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X30 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X30 @ ( k3_zfmisc_1 @ X32 @ X30 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X1 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,
    ( ( sk_A = o_0_0_xboole_0 )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_C @ sk_D @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('11',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_C @ sk_D @ sk_A @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['8','11'])).

thf('13',plain,
    ( ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_B_1 @ sk_C @ sk_D @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_B_1 @ sk_C @ sk_D @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) @ X38 @ X39 )
      = ( k4_zfmisc_1 @ X36 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t54_mcart_1])).

thf('15',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X30 = k1_xboole_0 )
      | ~ ( r1_tarski @ X30 @ ( k3_zfmisc_1 @ X31 @ X32 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t49_mcart_1])).

thf('16',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('17',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X30 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X30 @ ( k3_zfmisc_1 @ X31 @ X32 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X0 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,
    ( ( sk_A = o_0_0_xboole_0 )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_B_1 @ sk_C @ sk_D @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('21',plain,(
    ~ ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_B_1 @ sk_C @ sk_D @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t34_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) )).

thf('23',plain,(
    ! [X21: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X21 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf('24',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('25',plain,(
    ! [X21: $i] :
      ( ( X21 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X21 ) @ X21 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('27',plain,(
    ! [X26: $i,X28: $i] :
      ( ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( r1_tarski @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('29',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ( m1_subset_1 @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ X0 @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) )
        | ~ ( r2_hidden @ X0 @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( sk_A = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('33',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

thf(dt_k8_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ A ) ) )).

thf('34',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k8_mcart_1 @ X7 @ X8 @ X9 @ X10 @ X11 ) @ X7 )
      | ~ ( m1_subset_1 @ X11 @ ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_mcart_1])).

thf('35',plain,
    ( ( m1_subset_1 @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ ( sk_B @ sk_A ) ) @ sk_A )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('36',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('37',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ ( sk_B @ sk_A ) ) @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

thf(t60_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 )
        & ~ ! [E: $i] :
              ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
             => ( E
                = ( k4_mcart_1 @ ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ ( k11_mcart_1 @ A @ B @ C @ D @ E ) ) ) ) ) )).

thf('39',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( X45 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( X49
        = ( k4_mcart_1 @ ( k8_mcart_1 @ X45 @ X46 @ X47 @ X48 @ X49 ) @ ( k9_mcart_1 @ X45 @ X46 @ X47 @ X48 @ X49 ) @ ( k10_mcart_1 @ X45 @ X46 @ X47 @ X48 @ X49 ) @ ( k11_mcart_1 @ X45 @ X46 @ X47 @ X48 @ X49 ) ) )
      | ~ ( m1_subset_1 @ X49 @ ( k4_zfmisc_1 @ X45 @ X46 @ X47 @ X48 ) )
      | ( X48 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t60_mcart_1])).

thf('40',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('41',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('42',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('43',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('44',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( X45 = o_0_0_xboole_0 )
      | ( X46 = o_0_0_xboole_0 )
      | ( X47 = o_0_0_xboole_0 )
      | ( X49
        = ( k4_mcart_1 @ ( k8_mcart_1 @ X45 @ X46 @ X47 @ X48 @ X49 ) @ ( k9_mcart_1 @ X45 @ X46 @ X47 @ X48 @ X49 ) @ ( k10_mcart_1 @ X45 @ X46 @ X47 @ X48 @ X49 ) @ ( k11_mcart_1 @ X45 @ X46 @ X47 @ X48 @ X49 ) ) )
      | ~ ( m1_subset_1 @ X49 @ ( k4_zfmisc_1 @ X45 @ X46 @ X47 @ X48 ) )
      | ( X48 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('45',plain,
    ( ( ( sk_D = o_0_0_xboole_0 )
      | ( ( sk_B @ sk_A )
        = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ ( sk_B @ sk_A ) ) @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ ( sk_B @ sk_A ) ) @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ ( sk_B @ sk_A ) ) @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ ( sk_B @ sk_A ) ) ) )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['38','44'])).

thf('46',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('47',plain,
    ( ( ( sk_D = o_0_0_xboole_0 )
      | ( ( sk_B @ sk_A )
        = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ ( sk_B @ sk_A ) ) @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ ( sk_B @ sk_A ) ) @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ ( sk_B @ sk_A ) ) @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ ( sk_B @ sk_A ) ) ) )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X21 = k1_xboole_0 )
      | ~ ( r2_hidden @ X23 @ X21 )
      | ( ( sk_B @ X21 )
       != ( k4_mcart_1 @ X23 @ X22 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf('49',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('50',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X21 = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X23 @ X21 )
      | ( ( sk_B @ X21 )
       != ( k4_mcart_1 @ X23 @ X22 @ X24 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != ( sk_B @ sk_A ) )
        | ( sk_B_1 = o_0_0_xboole_0 )
        | ( sk_C = o_0_0_xboole_0 )
        | ( sk_D = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ ( sk_B @ sk_A ) ) @ X0 )
        | ( X0 = o_0_0_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( sk_A = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( ( sk_B @ sk_A )
       != ( sk_B @ sk_A ) ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['37','51'])).

thf('53',plain,
    ( ( ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('55',plain,
    ( ( ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('56',plain,(
    ! [X50: $i] :
      ( ( X50 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('57',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('58',plain,(
    ! [X50: $i] :
      ( ( X50 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X50 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( sk_D = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('61',plain,
    ( ( ( sk_D = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('63',plain,
    ( ( ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ o_0_0_xboole_0 ) )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf('64',plain,(
    ! [X40: $i,X41: $i,X42: $i,X44: $i] :
      ( ( X44 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X40 @ X41 @ X42 @ X44 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('65',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k4_zfmisc_1 @ X40 @ X41 @ X42 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('67',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('68',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k4_zfmisc_1 @ X40 @ X41 @ X42 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ( ( r1_tarski @ sk_A @ o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['63','68'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('70',plain,(
    ! [X29: $i] :
      ( ( X29 = k1_xboole_0 )
      | ~ ( r1_tarski @ X29 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('71',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('72',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('73',plain,(
    ! [X29: $i] :
      ( ( X29 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X29 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ( ( sk_C = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['69','73'])).

thf('75',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('76',plain,
    ( ( ( sk_C = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('78',plain,
    ( ( ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ o_0_0_xboole_0 @ sk_D ) )
      | ( sk_B_1 = o_0_0_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X40: $i,X41: $i,X42: $i,X44: $i] :
      ( ( X42 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X40 @ X41 @ X42 @ X44 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('80',plain,(
    ! [X40: $i,X41: $i,X44: $i] :
      ( ( k4_zfmisc_1 @ X40 @ X41 @ k1_xboole_0 @ X44 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('82',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('83',plain,(
    ! [X40: $i,X41: $i,X44: $i] :
      ( ( k4_zfmisc_1 @ X40 @ X41 @ o_0_0_xboole_0 @ X44 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ( ( r1_tarski @ sk_A @ o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['78','83'])).

thf('85',plain,(
    ! [X29: $i] :
      ( ( X29 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X29 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('86',plain,
    ( ( ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('88',plain,
    ( ( sk_B_1 = o_0_0_xboole_0 )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X40: $i,X41: $i,X42: $i,X44: $i] :
      ( ( X41 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X40 @ X41 @ X42 @ X44 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('90',plain,(
    ! [X40: $i,X42: $i,X44: $i] :
      ( ( k4_zfmisc_1 @ X40 @ k1_xboole_0 @ X42 @ X44 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('92',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('93',plain,(
    ! [X40: $i,X42: $i,X44: $i] :
      ( ( k4_zfmisc_1 @ X40 @ o_0_0_xboole_0 @ X42 @ X44 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,
    ( ( r1_tarski @ sk_A @ o_0_0_xboole_0 )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['22','88','93'])).

thf('95',plain,(
    ! [X29: $i] :
      ( ( X29 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X29 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('96',plain,
    ( ( sk_A = o_0_0_xboole_0 )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('98',plain,(
    ~ ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) )
    | ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_B_1 @ sk_C @ sk_D @ sk_A ) )
    | ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_C @ sk_D @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('100',plain,(
    r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['12','21','98','99'])).

thf('101',plain,(
    r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','100'])).

thf('102',plain,(
    ! [X21: $i] :
      ( ( X21 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X21 ) @ X21 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('103',plain,
    ( ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('104',plain,(
    ! [X26: $i,X28: $i] :
      ( ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( r1_tarski @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('105',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C ) ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ( m1_subset_1 @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('107',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ X0 @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C ) )
        | ~ ( r2_hidden @ X0 @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( sk_A = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C ) ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['102','107'])).

thf('109',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('110',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['108','109'])).

thf(dt_k9_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ B ) ) )).

thf('111',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k9_mcart_1 @ X12 @ X13 @ X14 @ X15 @ X16 ) @ X13 )
      | ~ ( m1_subset_1 @ X16 @ ( k4_zfmisc_1 @ X12 @ X13 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_mcart_1])).

thf('112',plain,
    ( ( m1_subset_1 @ ( k9_mcart_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C @ ( sk_B @ sk_A ) ) @ sk_A )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('114',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ ( k9_mcart_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C @ ( sk_B @ sk_A ) ) @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['12','21','98','99'])).

thf('116',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( k9_mcart_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C @ ( sk_B @ sk_A ) ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['108','109'])).

thf('118',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( X45 = o_0_0_xboole_0 )
      | ( X46 = o_0_0_xboole_0 )
      | ( X47 = o_0_0_xboole_0 )
      | ( X49
        = ( k4_mcart_1 @ ( k8_mcart_1 @ X45 @ X46 @ X47 @ X48 @ X49 ) @ ( k9_mcart_1 @ X45 @ X46 @ X47 @ X48 @ X49 ) @ ( k10_mcart_1 @ X45 @ X46 @ X47 @ X48 @ X49 ) @ ( k11_mcart_1 @ X45 @ X46 @ X47 @ X48 @ X49 ) ) )
      | ~ ( m1_subset_1 @ X49 @ ( k4_zfmisc_1 @ X45 @ X46 @ X47 @ X48 ) )
      | ( X48 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('119',plain,
    ( ( ( sk_C = o_0_0_xboole_0 )
      | ( ( sk_B @ sk_A )
        = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C @ ( sk_B @ sk_A ) ) @ ( k9_mcart_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C @ ( sk_B @ sk_A ) ) @ ( k10_mcart_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C @ ( sk_B @ sk_A ) ) @ ( k11_mcart_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C @ ( sk_B @ sk_A ) ) ) )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('121',plain,
    ( ( ( sk_C = o_0_0_xboole_0 )
      | ( ( sk_B @ sk_A )
        = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C @ ( sk_B @ sk_A ) ) @ ( k9_mcart_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C @ ( sk_B @ sk_A ) ) @ ( k10_mcart_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C @ ( sk_B @ sk_A ) ) @ ( k11_mcart_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C @ ( sk_B @ sk_A ) ) ) )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['119','120'])).

thf('122',plain,(
    r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['12','21','98','99'])).

thf('123',plain,
    ( ( sk_C = o_0_0_xboole_0 )
    | ( ( sk_B @ sk_A )
      = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C @ ( sk_B @ sk_A ) ) @ ( k9_mcart_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C @ ( sk_B @ sk_A ) ) @ ( k10_mcart_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C @ ( sk_B @ sk_A ) ) @ ( k11_mcart_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C @ ( sk_B @ sk_A ) ) ) )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X21 = k1_xboole_0 )
      | ~ ( r2_hidden @ X22 @ X21 )
      | ( ( sk_B @ X21 )
       != ( k4_mcart_1 @ X23 @ X22 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf('125',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('126',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X21 = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X22 @ X21 )
      | ( ( sk_B @ X21 )
       != ( k4_mcart_1 @ X23 @ X22 @ X24 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != ( sk_B @ sk_A ) )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ ( k9_mcart_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C @ ( sk_B @ sk_A ) ) @ X0 )
      | ( X0 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['123','126'])).

thf('128',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_A = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 )
    | ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['116','127'])).

thf('129',plain,
    ( ( sk_D = o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('131',plain,
    ( ( sk_D = o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X50: $i] :
      ( ( X50 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X50 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('133',plain,
    ( ( sk_C = o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('135',plain,
    ( ( sk_C = o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['133','134'])).

thf('136',plain,(
    r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','100'])).

thf('137',plain,
    ( ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ o_0_0_xboole_0 @ sk_A @ sk_B_1 @ sk_C ) )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X40: $i,X41: $i,X42: $i,X44: $i] :
      ( ( X40 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X40 @ X41 @ X42 @ X44 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('139',plain,(
    ! [X41: $i,X42: $i,X44: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X41 @ X42 @ X44 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('141',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('142',plain,(
    ! [X41: $i,X42: $i,X44: $i] :
      ( ( k4_zfmisc_1 @ o_0_0_xboole_0 @ X41 @ X42 @ X44 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['139','140','141'])).

thf('143',plain,
    ( ( r1_tarski @ sk_A @ o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['137','142'])).

thf('144',plain,(
    ! [X29: $i] :
      ( ( X29 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X29 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('145',plain,
    ( ( sk_C = o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('147',plain,
    ( ( sk_C = o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['145','146'])).

thf('148',plain,(
    r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','100'])).

thf('149',plain,
    ( ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_1 @ o_0_0_xboole_0 ) )
    | ( sk_B_1 = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k4_zfmisc_1 @ X40 @ X41 @ X42 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('151',plain,
    ( ( r1_tarski @ sk_A @ o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X29: $i] :
      ( ( X29 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X29 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('153',plain,
    ( ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('155',plain,(
    sk_B_1 = o_0_0_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X40: $i,X41: $i,X44: $i] :
      ( ( k4_zfmisc_1 @ X40 @ X41 @ o_0_0_xboole_0 @ X44 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('157',plain,(
    r1_tarski @ sk_A @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['101','155','156'])).

thf('158',plain,(
    ! [X29: $i] :
      ( ( X29 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X29 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('159',plain,(
    sk_A = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('161',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['159','160'])).


%------------------------------------------------------------------------------
