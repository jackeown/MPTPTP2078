%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0766+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cIuU3mJ8sf

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:27 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 156 expanded)
%              Number of leaves         :   29 (  58 expanded)
%              Depth                    :   19
%              Number of atoms          :  819 (2352 expanded)
%              Number of equality atoms :   28 (  61 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf(t12_wellord1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ? [C: $i] :
                  ( ~ ( r2_hidden @ ( k4_tarski @ C @ B ) @ A )
                  & ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) )
              & ! [C: $i] :
                  ~ ( ( r2_hidden @ C @ ( k3_relat_1 @ A ) )
                    & ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
                    & ! [D: $i] :
                        ~ ( ( r2_hidden @ D @ ( k3_relat_1 @ A ) )
                          & ( r2_hidden @ ( k4_tarski @ B @ D ) @ A )
                          & ( D != B )
                          & ~ ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( v2_wellord1 @ A )
         => ! [B: $i] :
              ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
                & ? [C: $i] :
                    ( ~ ( r2_hidden @ ( k4_tarski @ C @ B ) @ A )
                    & ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) )
                & ! [C: $i] :
                    ~ ( ( r2_hidden @ C @ ( k3_relat_1 @ A ) )
                      & ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
                      & ! [D: $i] :
                          ~ ( ( r2_hidden @ D @ ( k3_relat_1 @ A ) )
                            & ( r2_hidden @ ( k4_tarski @ B @ D ) @ A )
                            & ( D != B )
                            & ~ ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_wellord1])).

thf('1',plain,(
    r2_hidden @ sk_C_3 @ ( k3_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(s1_xboole_0__e7_18__wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ? [C: $i] :
        ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ ( k3_relat_1 @ A ) )
            & ~ ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( r2_hidden @ X6 @ ( sk_C_1 @ X7 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k3_relat_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[s1_xboole_0__e7_18__wellord1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_C_3 @ X0 ) @ sk_A )
      | ( r2_hidden @ sk_C_3 @ ( sk_C_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_C_3 @ X0 ) @ sk_A )
      | ( r2_hidden @ sk_C_3 @ ( sk_C_1 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_C_3 @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ sk_C_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( r2_hidden @ X8 @ ( k3_relat_1 @ X5 ) )
      | ~ ( r2_hidden @ X8 @ ( sk_C_1 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[s1_xboole_0__e7_18__wellord1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( sk_C_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( sk_C_1 @ X1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ ( sk_C_1 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_C_1 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t10_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r1_tarski @ B @ ( k3_relat_1 @ A ) )
              & ( B != k1_xboole_0 )
              & ! [C: $i] :
                  ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( r2_hidden @ D @ B )
                       => ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X11: $i] :
      ( ~ ( v2_wellord1 @ X9 )
      | ( r2_hidden @ ( sk_C_2 @ X11 @ X9 ) @ X11 )
      | ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ ( k3_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('15',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('16',plain,(
    ! [X9: $i,X11: $i] :
      ( ~ ( v2_wellord1 @ X9 )
      | ( r2_hidden @ ( sk_C_2 @ X11 @ X9 ) @ X11 )
      | ( X11 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X11 @ ( k3_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( sk_C_1 @ X1 @ X0 )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ ( sk_C_1 @ X1 @ X0 ) @ X0 ) @ ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( v2_wellord1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ ( sk_C_1 @ X1 @ X0 ) @ X0 ) @ ( sk_C_1 @ X1 @ X0 ) )
      | ( ( sk_C_1 @ X1 @ X0 )
        = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    r2_hidden @ sk_B_1 @ ( k3_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r2_hidden @ sk_B_1 @ ( k3_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( r2_hidden @ X6 @ ( sk_C_1 @ X7 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k3_relat_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[s1_xboole_0__e7_18__wellord1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_B_1 @ X0 ) @ sk_A )
      | ( r2_hidden @ sk_B_1 @ ( sk_C_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_B_1 @ X0 ) @ sk_A )
      | ( r2_hidden @ sk_B_1 @ ( sk_C_1 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X18: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k3_relat_1 @ sk_A ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_B_1 @ X18 ) @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ sk_B_1 @ ( sk_D @ X18 ) ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B_1 @ ( sk_C_1 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B_1 @ ( sk_D @ X0 ) ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B_1 @ ( sk_D @ sk_B_1 ) ) @ sk_A )
    | ( r2_hidden @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_B_1 @ X0 ) @ sk_A )
      | ( r2_hidden @ sk_B_1 @ ( sk_C_1 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('29',plain,(
    ! [X18: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k3_relat_1 @ sk_A ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_B_1 @ X18 ) @ sk_A )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ ( sk_D @ X18 ) ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B_1 @ ( sk_C_1 @ X0 @ sk_A ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D @ X0 ) ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r2_hidden @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( k3_relat_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    r2_hidden @ sk_B_1 @ ( k3_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( r2_hidden @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_C_1 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('36',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v2_wellord1 @ X9 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X11 @ X9 ) @ X10 ) @ X9 )
      | ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ ( k3_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord1])).

thf('37',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('38',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v2_wellord1 @ X9 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X11 @ X9 ) @ X10 ) @ X9 )
      | ( X11 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X11 @ ( k3_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( sk_C_1 @ X1 @ X0 )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ ( sk_C_1 @ X1 @ X0 ) @ X0 ) @ X2 ) @ X0 )
      | ~ ( r2_hidden @ X2 @ ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( v2_wellord1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( sk_C_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ ( sk_C_1 @ X1 @ X0 ) @ X0 ) @ X2 ) @ X0 )
      | ( ( sk_C_1 @ X1 @ X0 )
        = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( sk_C_1 @ sk_B_1 @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v2_wellord1 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( sk_C_1 @ sk_B_1 @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X7 ) @ X5 )
      | ~ ( r2_hidden @ X8 @ ( sk_C_1 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[s1_xboole_0__e7_18__wellord1])).

thf('46',plain,
    ( ( ( sk_C_1 @ sk_B_1 @ sk_A )
      = o_0_0_xboole_0 )
    | ~ ( r2_hidden @ ( sk_C_2 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( sk_C_1 @ sk_B_1 @ sk_A )
      = o_0_0_xboole_0 )
    | ~ ( r2_hidden @ ( sk_C_2 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( sk_C_1 @ sk_B_1 @ sk_A )
      = o_0_0_xboole_0 )
    | ~ ( v2_wellord1 @ sk_A )
    | ( ( sk_C_1 @ sk_B_1 @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( sk_C_1 @ sk_B_1 @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_C_1 @ sk_B_1 @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( sk_C_1 @ sk_B_1 @ sk_A )
    = o_0_0_xboole_0 ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    r2_hidden @ sk_C_3 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['7','53'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('55',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( sk_B @ X4 ) @ X4 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('56',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( sk_B @ X4 ) @ X4 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('59',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('62',plain,(
    ! [X17: $i] :
      ( ( X17 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('63',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('64',plain,(
    ! [X17: $i] :
      ( ( X17 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X17 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_B @ ( k1_zfmisc_1 @ X0 ) )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ o_0_0_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['54','68'])).

thf('70',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','69'])).


%------------------------------------------------------------------------------
