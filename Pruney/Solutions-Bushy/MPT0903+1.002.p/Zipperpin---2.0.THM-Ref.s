%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0903+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pkLS9LeK38

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:41 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  208 (1426 expanded)
%              Number of leaves         :   36 ( 455 expanded)
%              Depth                    :   45
%              Number of atoms          : 2167 (18196 expanded)
%              Number of equality atoms :  223 (1469 expanded)
%              Maximal formula depth    :   23 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

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
    ( ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) )
    | ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_B_2 @ sk_C @ sk_D @ sk_A ) )
    | ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_C @ sk_D @ sk_A @ sk_B_2 ) )
    | ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_C @ sk_D @ sk_A @ sk_B_2 ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_C @ sk_D @ sk_A @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t54_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C @ D )
      = ( k4_zfmisc_1 @ A @ B @ C @ D ) ) )).

thf('3',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) @ X37 @ X38 )
      = ( k4_zfmisc_1 @ X35 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t54_mcart_1])).

thf(t49_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ A @ B @ C ) )
          & ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ B @ C @ A ) )
          & ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ C @ A @ B ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29 = k1_xboole_0 )
      | ~ ( r1_tarski @ X29 @ ( k3_zfmisc_1 @ X31 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t49_mcart_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('5',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('6',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X29 @ ( k3_zfmisc_1 @ X31 @ X29 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X1 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,
    ( ( sk_A = o_0_0_xboole_0 )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_C @ sk_D @ sk_A @ sk_B_2 ) ) ),
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
    ~ ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_C @ sk_D @ sk_A @ sk_B_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['8','11'])).

thf('13',plain,
    ( ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_B_2 @ sk_C @ sk_D @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_B_2 @ sk_C @ sk_D @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) @ X37 @ X38 )
      = ( k4_zfmisc_1 @ X35 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t54_mcart_1])).

thf('15',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29 = k1_xboole_0 )
      | ~ ( r1_tarski @ X29 @ ( k3_zfmisc_1 @ X30 @ X31 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t49_mcart_1])).

thf('16',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('17',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X29 @ ( k3_zfmisc_1 @ X30 @ X31 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X0 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,
    ( ( sk_A = o_0_0_xboole_0 )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_B_2 @ sk_C @ sk_D @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('21',plain,(
    ~ ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_B_2 @ sk_C @ sk_D @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) ),
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
    ! [X20: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X20 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf('24',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('25',plain,(
    ! [X20: $i] :
      ( ( X20 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X20 ) @ X20 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X20: $i] :
      ( ( X20 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X20 ) @ X20 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('27',plain,(
    ! [X20: $i] :
      ( ( X20 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X20 ) @ X20 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('28',plain,
    ( ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X25: $i,X27: $i] :
      ( ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( r1_tarski @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('31',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ( m1_subset_1 @ X32 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ X0 @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) )
        | ~ ( r2_hidden @ X0 @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( sk_A = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_B_1 @ sk_A ) @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('35',plain,
    ( ( m1_subset_1 @ ( sk_B_1 @ sk_A ) @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf(dt_k8_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ A ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k8_mcart_1 @ X7 @ X8 @ X9 @ X10 @ X11 ) @ X7 )
      | ~ ( m1_subset_1 @ X11 @ ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_mcart_1])).

thf('37',plain,
    ( ( m1_subset_1 @ ( k8_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D @ ( sk_B_1 @ sk_A ) ) @ sk_A )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('38',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r2_hidden @ X18 @ X19 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('39',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D @ ( sk_B_1 @ sk_A ) ) @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( m1_subset_1 @ ( sk_B_1 @ sk_A ) @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

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

thf('41',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( X49 = k1_xboole_0 )
      | ( X51
        = ( k4_mcart_1 @ ( k8_mcart_1 @ X47 @ X48 @ X49 @ X50 @ X51 ) @ ( k9_mcart_1 @ X47 @ X48 @ X49 @ X50 @ X51 ) @ ( k10_mcart_1 @ X47 @ X48 @ X49 @ X50 @ X51 ) @ ( k11_mcart_1 @ X47 @ X48 @ X49 @ X50 @ X51 ) ) )
      | ~ ( m1_subset_1 @ X51 @ ( k4_zfmisc_1 @ X47 @ X48 @ X49 @ X50 ) )
      | ( X50 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t60_mcart_1])).

thf('42',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('43',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('44',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('45',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('46',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( X47 = o_0_0_xboole_0 )
      | ( X48 = o_0_0_xboole_0 )
      | ( X49 = o_0_0_xboole_0 )
      | ( X51
        = ( k4_mcart_1 @ ( k8_mcart_1 @ X47 @ X48 @ X49 @ X50 @ X51 ) @ ( k9_mcart_1 @ X47 @ X48 @ X49 @ X50 @ X51 ) @ ( k10_mcart_1 @ X47 @ X48 @ X49 @ X50 @ X51 ) @ ( k11_mcart_1 @ X47 @ X48 @ X49 @ X50 @ X51 ) ) )
      | ~ ( m1_subset_1 @ X51 @ ( k4_zfmisc_1 @ X47 @ X48 @ X49 @ X50 ) )
      | ( X50 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['41','42','43','44','45'])).

thf('47',plain,
    ( ( ( sk_D = o_0_0_xboole_0 )
      | ( ( sk_B_1 @ sk_A )
        = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D @ ( sk_B_1 @ sk_A ) ) @ ( k9_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D @ ( sk_B_1 @ sk_A ) ) @ ( k10_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D @ ( sk_B_1 @ sk_A ) ) @ ( k11_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D @ ( sk_B_1 @ sk_A ) ) ) )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_B_2 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('49',plain,
    ( ( ( sk_D = o_0_0_xboole_0 )
      | ( ( sk_B_1 @ sk_A )
        = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D @ ( sk_B_1 @ sk_A ) ) @ ( k9_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D @ ( sk_B_1 @ sk_A ) ) @ ( k10_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D @ ( sk_B_1 @ sk_A ) ) @ ( k11_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D @ ( sk_B_1 @ sk_A ) ) ) )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_B_2 = o_0_0_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X20 = k1_xboole_0 )
      | ~ ( r2_hidden @ X22 @ X20 )
      | ( ( sk_B_1 @ X20 )
       != ( k4_mcart_1 @ X22 @ X21 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf('51',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('52',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X20 = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X22 @ X20 )
      | ( ( sk_B_1 @ X20 )
       != ( k4_mcart_1 @ X22 @ X21 @ X23 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B_1 @ X0 )
         != ( sk_B_1 @ sk_A ) )
        | ( sk_B_2 = o_0_0_xboole_0 )
        | ( sk_C = o_0_0_xboole_0 )
        | ( sk_D = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D @ ( sk_B_1 @ sk_A ) ) @ X0 )
        | ( X0 = o_0_0_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( sk_A = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_B_2 = o_0_0_xboole_0 )
      | ( ( sk_B_1 @ sk_A )
       != ( sk_B_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['39','53'])).

thf('55',plain,
    ( ( ( sk_B_2 = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('57',plain,
    ( ( ( sk_B_2 = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['55','56'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('58',plain,(
    ! [X52: $i] :
      ( ( X52 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('59',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('60',plain,(
    ! [X52: $i] :
      ( ( X52 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X52 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( sk_D = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_B_2 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('63',plain,
    ( ( ( sk_D = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_B_2 = o_0_0_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('65',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ X44 @ X45 )
      | ~ ( v1_xboole_0 @ X46 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) )
        | ~ ( r2_hidden @ X0 @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ o_0_0_xboole_0 ) )
        | ( sk_B_2 = o_0_0_xboole_0 )
        | ( sk_C = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf('68',plain,(
    ! [X39: $i,X40: $i,X41: $i,X43: $i] :
      ( ( X43 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X39 @ X40 @ X41 @ X43 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('69',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( k4_zfmisc_1 @ X39 @ X40 @ X41 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('71',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('72',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( k4_zfmisc_1 @ X39 @ X40 @ X41 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('73',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ( sk_B_2 = o_0_0_xboole_0 )
        | ( sk_C = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['67','72','73'])).

thf('75',plain,
    ( ( ( sk_A = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_B_2 = o_0_0_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['26','74'])).

thf('76',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('77',plain,
    ( ( ( sk_C = o_0_0_xboole_0 )
      | ( sk_B_2 = o_0_0_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) )
        | ~ ( r2_hidden @ X0 @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ o_0_0_xboole_0 @ sk_D ) )
        | ( sk_B_2 = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X39: $i,X40: $i,X41: $i,X43: $i] :
      ( ( X41 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X39 @ X40 @ X41 @ X43 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('81',plain,(
    ! [X39: $i,X40: $i,X43: $i] :
      ( ( k4_zfmisc_1 @ X39 @ X40 @ k1_xboole_0 @ X43 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('83',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('84',plain,(
    ! [X39: $i,X40: $i,X43: $i] :
      ( ( k4_zfmisc_1 @ X39 @ X40 @ o_0_0_xboole_0 @ X43 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('86',plain,
    ( ! [X0: $i] :
        ( ( sk_B_2 = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['79','84','85'])).

thf('87',plain,
    ( ( ( sk_A = o_0_0_xboole_0 )
      | ( sk_B_2 = o_0_0_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['25','86'])).

thf('88',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('89',plain,
    ( ( sk_B_2 = o_0_0_xboole_0 )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X39: $i,X40: $i,X41: $i,X43: $i] :
      ( ( X40 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X39 @ X40 @ X41 @ X43 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('91',plain,(
    ! [X39: $i,X41: $i,X43: $i] :
      ( ( k4_zfmisc_1 @ X39 @ k1_xboole_0 @ X41 @ X43 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('93',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('94',plain,(
    ! [X39: $i,X41: $i,X43: $i] :
      ( ( k4_zfmisc_1 @ X39 @ o_0_0_xboole_0 @ X41 @ X43 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ( r1_tarski @ sk_A @ o_0_0_xboole_0 )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['22','89','94'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('96',plain,(
    ! [X28: $i] :
      ( ( X28 = k1_xboole_0 )
      | ~ ( r1_tarski @ X28 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('97',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('98',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('99',plain,(
    ! [X28: $i] :
      ( ( X28 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X28 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ( sk_A = o_0_0_xboole_0 )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['95','99'])).

thf('101',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('102',plain,(
    ~ ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) )
    | ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_B_2 @ sk_C @ sk_D @ sk_A ) )
    | ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_C @ sk_D @ sk_A @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('104',plain,(
    r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['12','21','102','103'])).

thf('105',plain,(
    r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','104'])).

thf('106',plain,(
    ! [X20: $i] :
      ( ( X20 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X20 ) @ X20 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('107',plain,(
    ! [X20: $i] :
      ( ( X20 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X20 ) @ X20 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('108',plain,
    ( ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('109',plain,(
    ! [X25: $i,X27: $i] :
      ( ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( r1_tarski @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('110',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C ) ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ( m1_subset_1 @ X32 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('112',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ X0 @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C ) )
        | ~ ( r2_hidden @ X0 @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( ( sk_A = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( sk_B_1 @ sk_A ) @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C ) ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['107','112'])).

thf('114',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('115',plain,
    ( ( m1_subset_1 @ ( sk_B_1 @ sk_A ) @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['113','114'])).

thf(dt_k9_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ B ) ) )).

thf('116',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k9_mcart_1 @ X12 @ X13 @ X14 @ X15 @ X16 ) @ X13 )
      | ~ ( m1_subset_1 @ X16 @ ( k4_zfmisc_1 @ X12 @ X13 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_mcart_1])).

thf('117',plain,
    ( ( m1_subset_1 @ ( k9_mcart_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C @ ( sk_B_1 @ sk_A ) ) @ sk_A )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r2_hidden @ X18 @ X19 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('119',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ ( k9_mcart_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C @ ( sk_B_1 @ sk_A ) ) @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['12','21','102','103'])).

thf('121',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( k9_mcart_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C @ ( sk_B_1 @ sk_A ) ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( m1_subset_1 @ ( sk_B_1 @ sk_A ) @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['113','114'])).

thf('123',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( X47 = o_0_0_xboole_0 )
      | ( X48 = o_0_0_xboole_0 )
      | ( X49 = o_0_0_xboole_0 )
      | ( X51
        = ( k4_mcart_1 @ ( k8_mcart_1 @ X47 @ X48 @ X49 @ X50 @ X51 ) @ ( k9_mcart_1 @ X47 @ X48 @ X49 @ X50 @ X51 ) @ ( k10_mcart_1 @ X47 @ X48 @ X49 @ X50 @ X51 ) @ ( k11_mcart_1 @ X47 @ X48 @ X49 @ X50 @ X51 ) ) )
      | ~ ( m1_subset_1 @ X51 @ ( k4_zfmisc_1 @ X47 @ X48 @ X49 @ X50 ) )
      | ( X50 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['41','42','43','44','45'])).

thf('124',plain,
    ( ( ( sk_C = o_0_0_xboole_0 )
      | ( ( sk_B_1 @ sk_A )
        = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C @ ( sk_B_1 @ sk_A ) ) @ ( k9_mcart_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C @ ( sk_B_1 @ sk_A ) ) @ ( k10_mcart_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C @ ( sk_B_1 @ sk_A ) ) @ ( k11_mcart_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C @ ( sk_B_1 @ sk_A ) ) ) )
      | ( sk_B_2 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('126',plain,
    ( ( ( sk_C = o_0_0_xboole_0 )
      | ( ( sk_B_1 @ sk_A )
        = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C @ ( sk_B_1 @ sk_A ) ) @ ( k9_mcart_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C @ ( sk_B_1 @ sk_A ) ) @ ( k10_mcart_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C @ ( sk_B_1 @ sk_A ) ) @ ( k11_mcart_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C @ ( sk_B_1 @ sk_A ) ) ) )
      | ( sk_B_2 = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['124','125'])).

thf('127',plain,(
    r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['12','21','102','103'])).

thf('128',plain,
    ( ( sk_C = o_0_0_xboole_0 )
    | ( ( sk_B_1 @ sk_A )
      = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C @ ( sk_B_1 @ sk_A ) ) @ ( k9_mcart_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C @ ( sk_B_1 @ sk_A ) ) @ ( k10_mcart_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C @ ( sk_B_1 @ sk_A ) ) @ ( k11_mcart_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C @ ( sk_B_1 @ sk_A ) ) ) )
    | ( sk_B_2 = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X20 = k1_xboole_0 )
      | ~ ( r2_hidden @ X21 @ X20 )
      | ( ( sk_B_1 @ X20 )
       != ( k4_mcart_1 @ X22 @ X21 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf('130',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('131',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X20 = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X21 @ X20 )
      | ( ( sk_B_1 @ X20 )
       != ( k4_mcart_1 @ X22 @ X21 @ X23 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( ( sk_B_1 @ X0 )
       != ( sk_B_1 @ sk_A ) )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_B_2 = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ ( k9_mcart_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C @ ( sk_B_1 @ sk_A ) ) @ X0 )
      | ( X0 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['128','131'])).

thf('133',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_A = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 )
    | ( sk_B_2 = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 )
    | ( ( sk_B_1 @ sk_A )
     != ( sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['121','132'])).

thf('134',plain,
    ( ( sk_D = o_0_0_xboole_0 )
    | ( sk_B_2 = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('136',plain,
    ( ( sk_D = o_0_0_xboole_0 )
    | ( sk_B_2 = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X52: $i] :
      ( ( X52 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X52 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('138',plain,
    ( ( sk_C = o_0_0_xboole_0 )
    | ( sk_B_2 = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('140',plain,
    ( ( sk_C = o_0_0_xboole_0 )
    | ( sk_B_2 = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['138','139'])).

thf('141',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C ) ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('142',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ X44 @ X45 )
      | ~ ( v1_xboole_0 @ X46 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('143',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C ) )
        | ~ ( r2_hidden @ X0 @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['12','21','102','103'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ o_0_0_xboole_0 @ sk_A @ sk_B_2 @ sk_C ) )
      | ( sk_B_2 = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['140','145'])).

thf('147',plain,(
    ! [X39: $i,X40: $i,X41: $i,X43: $i] :
      ( ( X39 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X39 @ X40 @ X41 @ X43 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('148',plain,(
    ! [X40: $i,X41: $i,X43: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X40 @ X41 @ X43 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('150',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('151',plain,(
    ! [X40: $i,X41: $i,X43: $i] :
      ( ( k4_zfmisc_1 @ o_0_0_xboole_0 @ X40 @ X41 @ X43 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['148','149','150'])).

thf('152',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( sk_B_2 = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['146','151','152'])).

thf('154',plain,
    ( ( sk_A = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 )
    | ( sk_B_2 = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['106','153'])).

thf('155',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('156',plain,
    ( ( sk_C = o_0_0_xboole_0 )
    | ( sk_B_2 = o_0_0_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['154','155'])).

thf('157',plain,(
    r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','104'])).

thf('158',plain,
    ( ( r1_tarski @ sk_A @ ( k4_zfmisc_1 @ sk_D @ sk_A @ sk_B_2 @ o_0_0_xboole_0 ) )
    | ( sk_B_2 = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( k4_zfmisc_1 @ X39 @ X40 @ X41 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('160',plain,
    ( ( r1_tarski @ sk_A @ o_0_0_xboole_0 )
    | ( sk_B_2 = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X28: $i] :
      ( ( X28 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X28 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('162',plain,
    ( ( sk_B_2 = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('164',plain,(
    sk_B_2 = o_0_0_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X39: $i,X40: $i,X43: $i] :
      ( ( k4_zfmisc_1 @ X39 @ X40 @ o_0_0_xboole_0 @ X43 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('166',plain,(
    r1_tarski @ sk_A @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['105','164','165'])).

thf('167',plain,(
    ! [X28: $i] :
      ( ( X28 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X28 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('168',plain,(
    sk_A = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('170',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['168','169'])).


%------------------------------------------------------------------------------
