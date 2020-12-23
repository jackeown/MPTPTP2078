%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.99cAnDJL2B

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:50 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 562 expanded)
%              Number of leaves         :   40 ( 193 expanded)
%              Depth                    :   21
%              Number of atoms          : 1692 (6714 expanded)
%              Number of equality atoms :  212 ( 757 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(t69_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( ! [F: $i] :
            ( ( m1_subset_1 @ F @ A )
           => ! [G: $i] :
                ( ( m1_subset_1 @ G @ B )
               => ! [H: $i] :
                    ( ( m1_subset_1 @ H @ C )
                   => ( ( E
                        = ( k3_mcart_1 @ F @ G @ H ) )
                     => ( D = F ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D
            = ( k5_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) )
       => ( ! [F: $i] :
              ( ( m1_subset_1 @ F @ A )
             => ! [G: $i] :
                  ( ( m1_subset_1 @ G @ B )
                 => ! [H: $i] :
                      ( ( m1_subset_1 @ H @ C )
                     => ( ( E
                          = ( k3_mcart_1 @ F @ G @ H ) )
                       => ( D = F ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D
              = ( k5_mcart_1 @ A @ B @ C @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t69_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ X18 )
      | ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X39: $i,X40: $i] :
      ( ( X39
        = ( k4_tarski @ ( k1_mcart_1 @ X39 ) @ ( k2_mcart_1 @ X39 ) ) )
      | ~ ( v1_relat_1 @ X40 )
      | ~ ( r2_hidden @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k3_zfmisc_1 @ X29 @ X30 @ X31 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( v1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('10',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X36 ) @ X37 )
      | ~ ( r2_hidden @ X36 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('14',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('15',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('16',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( r1_tarski @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','17'])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X4 = X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
      | ( ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','25'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('27',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k4_zfmisc_1 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X32 @ X33 @ X34 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf('29',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( ( k4_zfmisc_1 @ X45 @ X46 @ X47 @ X48 )
       != k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['31','32','33','34'])).

thf('36',plain,
    ( ( k1_xboole_0 != sk_E )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(eq_fact,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['31','32','33','34'])).

thf('38',plain,
    ( sk_E
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('40',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k3_zfmisc_1 @ X29 @ X30 @ X31 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('41',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X36 ) @ X37 )
      | ~ ( r2_hidden @ X36 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X39: $i,X40: $i] :
      ( ( X39
        = ( k4_tarski @ ( k1_mcart_1 @ X39 ) @ ( k2_mcart_1 @ X39 ) ) )
      | ~ ( v1_relat_1 @ X40 )
      | ~ ( r2_hidden @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X22: $i,X23: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','24'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k1_mcart_1 @ sk_E )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
      | ( ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k4_zfmisc_1 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X32 @ X33 @ X34 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k1_mcart_1 @ sk_E )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( ( k4_zfmisc_1 @ X45 @ X46 @ X47 @ X48 )
       != k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_mcart_1 @ sk_E )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k1_mcart_1 @ sk_E )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_mcart_1 @ sk_E )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['54','55','56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_mcart_1 @ sk_E )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['54','55','56','57'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k1_mcart_1 @ sk_E )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
      | ( ( k1_mcart_1 @ sk_E )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_mcart_1 @ sk_E )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( k1_mcart_1 @ sk_E )
    = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ),
    inference(condensation,[status(thm)],['61'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('63',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k3_mcart_1 @ X26 @ X27 @ X28 )
      = ( k4_tarski @ ( k4_tarski @ X26 @ X27 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('66',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X36 ) @ X38 )
      | ~ ( r2_hidden @ X36 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('67',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','24'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_1 )
      | ( ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k4_zfmisc_1 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X32 @ X33 @ X34 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_1 )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( ( k4_zfmisc_1 @ X45 @ X46 @ X47 @ X48 )
       != k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_1 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['74','75','76','77'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('79',plain,(
    ! [X20: $i,X21: $i] :
      ( ( m1_subset_1 @ X20 @ X21 )
      | ~ ( r2_hidden @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','17'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('83',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 != X6 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k2_tarski @ X9 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('84',plain,(
    ! [X6: $i,X9: $i] :
      ( r2_hidden @ X6 @ ( k2_tarski @ X9 @ X6 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['82','86'])).

thf('88',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X50 @ sk_B_1 )
      | ( sk_D_1 = X51 )
      | ( sk_E
       != ( k3_mcart_1 @ X51 @ X50 @ X52 ) )
      | ~ ( m1_subset_1 @ X52 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X51 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C_1 )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) )
      | ( sk_D_1 = X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( sk_D_1
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','89'])).

thf('91',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('92',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X36 ) @ X37 )
      | ~ ( r2_hidden @ X36 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('93',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','24'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ( ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k4_zfmisc_1 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X32 @ X33 @ X34 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( ( k4_zfmisc_1 @ X45 @ X46 @ X47 @ X48 )
       != k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['100','101','102','103'])).

thf('105',plain,(
    ! [X20: $i,X21: $i] :
      ( ( m1_subset_1 @ X20 @ X21 )
      | ~ ( r2_hidden @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','17'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('110',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( sk_D_1
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['90','110'])).

thf('112',plain,(
    sk_D_1
 != ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( ( ( k5_mcart_1 @ A @ B @ C @ D )
                  = ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k6_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k7_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ D ) ) ) ) ) )).

thf('114',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( X41 = k1_xboole_0 )
      | ( X42 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X41 @ X42 @ X44 @ X43 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X43 ) ) )
      | ~ ( m1_subset_1 @ X43 @ ( k3_zfmisc_1 @ X41 @ X42 @ X44 ) )
      | ( X44 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('115',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['115','116','117','118'])).

thf('120',plain,(
    sk_D_1
 != ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['112','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_C_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['111','120'])).

thf('122',plain,
    ( ( sk_E != sk_E )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['38','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','24'])).

thf('124',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('125',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k3_zfmisc_1 @ X29 @ X30 @ X31 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('126',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X36 ) @ X38 )
      | ~ ( r2_hidden @ X36 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['124','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('130',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C_1 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k4_zfmisc_1 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X32 @ X33 @ X34 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( ( k4_zfmisc_1 @ X45 @ X46 @ X47 @ X48 )
       != k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C_1 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C_1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['134','135','136','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['123','138'])).

thf('140',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','17'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C_1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    ! [X20: $i,X21: $i] :
      ( ( m1_subset_1 @ X20 @ X21 )
      | ~ ( r2_hidden @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','17'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('148',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    sk_E != sk_E ),
    inference(demod,[status(thm)],['122','148'])).

thf('150',plain,(
    $false ),
    inference(simplify,[status(thm)],['149'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.99cAnDJL2B
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:32:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.06/1.24  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.06/1.24  % Solved by: fo/fo7.sh
% 1.06/1.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.24  % done 1323 iterations in 0.773s
% 1.06/1.24  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.06/1.24  % SZS output start Refutation
% 1.06/1.24  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.06/1.24  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.06/1.24  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.06/1.24  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.06/1.24  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.06/1.24  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 1.06/1.24  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 1.06/1.24  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 1.06/1.24  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.06/1.24  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 1.06/1.24  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 1.06/1.24  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.06/1.24  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.06/1.24  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.06/1.24  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 1.06/1.24  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.06/1.24  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.06/1.24  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 1.06/1.24  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 1.06/1.24  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.06/1.24  thf(sk_B_type, type, sk_B: $i > $i).
% 1.06/1.24  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.06/1.24  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.24  thf(sk_E_type, type, sk_E: $i).
% 1.06/1.24  thf(t69_mcart_1, conjecture,
% 1.06/1.24    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.06/1.24     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.06/1.24       ( ( ![F:$i]:
% 1.06/1.24           ( ( m1_subset_1 @ F @ A ) =>
% 1.06/1.24             ( ![G:$i]:
% 1.06/1.24               ( ( m1_subset_1 @ G @ B ) =>
% 1.06/1.24                 ( ![H:$i]:
% 1.06/1.24                   ( ( m1_subset_1 @ H @ C ) =>
% 1.06/1.24                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 1.06/1.24                       ( ( D ) = ( F ) ) ) ) ) ) ) ) ) =>
% 1.06/1.24         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.06/1.24           ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.06/1.24           ( ( D ) = ( k5_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 1.06/1.24  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.24    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.06/1.24        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.06/1.24          ( ( ![F:$i]:
% 1.06/1.24              ( ( m1_subset_1 @ F @ A ) =>
% 1.06/1.24                ( ![G:$i]:
% 1.06/1.24                  ( ( m1_subset_1 @ G @ B ) =>
% 1.06/1.24                    ( ![H:$i]:
% 1.06/1.24                      ( ( m1_subset_1 @ H @ C ) =>
% 1.06/1.24                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 1.06/1.24                          ( ( D ) = ( F ) ) ) ) ) ) ) ) ) =>
% 1.06/1.24            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.06/1.24              ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.06/1.24              ( ( D ) = ( k5_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 1.06/1.24    inference('cnf.neg', [status(esa)], [t69_mcart_1])).
% 1.06/1.24  thf('0', plain,
% 1.06/1.24      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf(d2_subset_1, axiom,
% 1.06/1.24    (![A:$i,B:$i]:
% 1.06/1.24     ( ( ( v1_xboole_0 @ A ) =>
% 1.06/1.24         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.06/1.24       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.06/1.24         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.06/1.24  thf('1', plain,
% 1.06/1.24      (![X17 : $i, X18 : $i]:
% 1.06/1.24         (~ (m1_subset_1 @ X17 @ X18)
% 1.06/1.24          | (r2_hidden @ X17 @ X18)
% 1.06/1.24          | (v1_xboole_0 @ X18))),
% 1.06/1.24      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.06/1.24  thf('2', plain,
% 1.06/1.24      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 1.06/1.24        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['0', '1'])).
% 1.06/1.24  thf(t23_mcart_1, axiom,
% 1.06/1.24    (![A:$i,B:$i]:
% 1.06/1.24     ( ( v1_relat_1 @ B ) =>
% 1.06/1.24       ( ( r2_hidden @ A @ B ) =>
% 1.06/1.24         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 1.06/1.24  thf('3', plain,
% 1.06/1.24      (![X39 : $i, X40 : $i]:
% 1.06/1.24         (((X39) = (k4_tarski @ (k1_mcart_1 @ X39) @ (k2_mcart_1 @ X39)))
% 1.06/1.24          | ~ (v1_relat_1 @ X40)
% 1.06/1.24          | ~ (r2_hidden @ X39 @ X40))),
% 1.06/1.24      inference('cnf', [status(esa)], [t23_mcart_1])).
% 1.06/1.24  thf('4', plain,
% 1.06/1.24      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 1.06/1.24        | ~ (v1_relat_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 1.06/1.24        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 1.06/1.24      inference('sup-', [status(thm)], ['2', '3'])).
% 1.06/1.24  thf(d3_zfmisc_1, axiom,
% 1.06/1.24    (![A:$i,B:$i,C:$i]:
% 1.06/1.24     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 1.06/1.24       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 1.06/1.24  thf('5', plain,
% 1.06/1.24      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.06/1.24         ((k3_zfmisc_1 @ X29 @ X30 @ X31)
% 1.06/1.24           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30) @ X31))),
% 1.06/1.24      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.06/1.24  thf(fc6_relat_1, axiom,
% 1.06/1.24    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.06/1.24  thf('6', plain,
% 1.06/1.24      (![X22 : $i, X23 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X22 @ X23))),
% 1.06/1.24      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.06/1.24  thf('7', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.24         (v1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))),
% 1.06/1.24      inference('sup+', [status(thm)], ['5', '6'])).
% 1.06/1.24  thf('8', plain,
% 1.06/1.24      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 1.06/1.24        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 1.06/1.24      inference('demod', [status(thm)], ['4', '7'])).
% 1.06/1.24  thf(d1_xboole_0, axiom,
% 1.06/1.24    (![A:$i]:
% 1.06/1.24     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.06/1.24  thf('9', plain,
% 1.06/1.24      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.06/1.24      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.06/1.24  thf(t10_mcart_1, axiom,
% 1.06/1.24    (![A:$i,B:$i,C:$i]:
% 1.06/1.24     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 1.06/1.24       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 1.06/1.24         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 1.06/1.24  thf('10', plain,
% 1.06/1.24      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.06/1.24         ((r2_hidden @ (k1_mcart_1 @ X36) @ X37)
% 1.06/1.24          | ~ (r2_hidden @ X36 @ (k2_zfmisc_1 @ X37 @ X38)))),
% 1.06/1.24      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.06/1.24  thf('11', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]:
% 1.06/1.24         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 1.06/1.24          | (r2_hidden @ (k1_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 1.06/1.24      inference('sup-', [status(thm)], ['9', '10'])).
% 1.06/1.24  thf('12', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.06/1.24      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.06/1.24  thf('13', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]:
% 1.06/1.24         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 1.06/1.24      inference('sup-', [status(thm)], ['11', '12'])).
% 1.06/1.24  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.06/1.24  thf('14', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 1.06/1.24      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.06/1.24  thf('15', plain,
% 1.06/1.24      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.06/1.24      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.06/1.24  thf(t7_ordinal1, axiom,
% 1.06/1.24    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.06/1.24  thf('16', plain,
% 1.06/1.24      (![X24 : $i, X25 : $i]:
% 1.06/1.24         (~ (r2_hidden @ X24 @ X25) | ~ (r1_tarski @ X25 @ X24))),
% 1.06/1.24      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.06/1.24  thf('17', plain,
% 1.06/1.24      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['15', '16'])).
% 1.06/1.24  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.06/1.24      inference('sup-', [status(thm)], ['14', '17'])).
% 1.06/1.24  thf(t2_tarski, axiom,
% 1.06/1.24    (![A:$i,B:$i]:
% 1.06/1.24     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 1.06/1.24       ( ( A ) = ( B ) ) ))).
% 1.06/1.24  thf('19', plain,
% 1.06/1.24      (![X3 : $i, X4 : $i]:
% 1.06/1.24         (((X4) = (X3))
% 1.06/1.24          | (r2_hidden @ (sk_C @ X3 @ X4) @ X3)
% 1.06/1.24          | (r2_hidden @ (sk_C @ X3 @ X4) @ X4))),
% 1.06/1.24      inference('cnf', [status(esa)], [t2_tarski])).
% 1.06/1.24  thf('20', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.06/1.24      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.06/1.24  thf('21', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]:
% 1.06/1.24         ((r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 1.06/1.24          | ((X1) = (X0))
% 1.06/1.24          | ~ (v1_xboole_0 @ X0))),
% 1.06/1.24      inference('sup-', [status(thm)], ['19', '20'])).
% 1.06/1.24  thf('22', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.06/1.24      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.06/1.24  thf('23', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]:
% 1.06/1.24         (~ (v1_xboole_0 @ X1) | ((X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 1.06/1.24      inference('sup-', [status(thm)], ['21', '22'])).
% 1.06/1.24  thf('24', plain,
% 1.06/1.24      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['18', '23'])).
% 1.06/1.24  thf('25', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]:
% 1.06/1.24         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['13', '24'])).
% 1.06/1.24  thf('26', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 1.06/1.24          | ((k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1) @ X0)
% 1.06/1.24              = (k1_xboole_0)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['8', '25'])).
% 1.06/1.24  thf(d4_zfmisc_1, axiom,
% 1.06/1.24    (![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.24     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 1.06/1.24       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 1.06/1.24  thf('27', plain,
% 1.06/1.24      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.06/1.24         ((k4_zfmisc_1 @ X32 @ X33 @ X34 @ X35)
% 1.06/1.24           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X32 @ X33 @ X34) @ X35))),
% 1.06/1.24      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.06/1.24  thf('28', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 1.06/1.24          | ((k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0) = (k1_xboole_0)))),
% 1.06/1.24      inference('demod', [status(thm)], ['26', '27'])).
% 1.06/1.24  thf(t55_mcart_1, axiom,
% 1.06/1.24    (![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.24     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.06/1.24         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 1.06/1.24       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 1.06/1.24  thf('29', plain,
% 1.06/1.24      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 1.06/1.24         (((k4_zfmisc_1 @ X45 @ X46 @ X47 @ X48) != (k1_xboole_0))
% 1.06/1.24          | ((X48) = (k1_xboole_0))
% 1.06/1.24          | ((X47) = (k1_xboole_0))
% 1.06/1.24          | ((X46) = (k1_xboole_0))
% 1.06/1.24          | ((X45) = (k1_xboole_0)))),
% 1.06/1.24      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.06/1.24  thf('30', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (((k1_xboole_0) != (k1_xboole_0))
% 1.06/1.24          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 1.06/1.24          | ((sk_A) = (k1_xboole_0))
% 1.06/1.24          | ((sk_B_1) = (k1_xboole_0))
% 1.06/1.24          | ((sk_C_1) = (k1_xboole_0))
% 1.06/1.24          | ((X0) = (k1_xboole_0)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['28', '29'])).
% 1.06/1.24  thf('31', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (((X0) = (k1_xboole_0))
% 1.06/1.24          | ((sk_C_1) = (k1_xboole_0))
% 1.06/1.24          | ((sk_B_1) = (k1_xboole_0))
% 1.06/1.24          | ((sk_A) = (k1_xboole_0))
% 1.06/1.24          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 1.06/1.24      inference('simplify', [status(thm)], ['30'])).
% 1.06/1.24  thf('32', plain, (((sk_A) != (k1_xboole_0))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('33', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('34', plain, (((sk_C_1) != (k1_xboole_0))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('35', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (((X0) = (k1_xboole_0))
% 1.06/1.24          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 1.06/1.24      inference('simplify_reflect-', [status(thm)], ['31', '32', '33', '34'])).
% 1.06/1.24  thf('36', plain,
% 1.06/1.24      ((((k1_xboole_0) != (sk_E))
% 1.06/1.24        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 1.06/1.24      inference('eq_fact', [status(thm)], ['35'])).
% 1.06/1.24  thf('37', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (((X0) = (k1_xboole_0))
% 1.06/1.24          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 1.06/1.24      inference('simplify_reflect-', [status(thm)], ['31', '32', '33', '34'])).
% 1.06/1.24  thf('38', plain,
% 1.06/1.24      (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))),
% 1.06/1.24      inference('clc', [status(thm)], ['36', '37'])).
% 1.06/1.24  thf('39', plain,
% 1.06/1.24      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 1.06/1.24        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['0', '1'])).
% 1.06/1.24  thf('40', plain,
% 1.06/1.24      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.06/1.24         ((k3_zfmisc_1 @ X29 @ X30 @ X31)
% 1.06/1.24           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30) @ X31))),
% 1.06/1.24      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.06/1.24  thf('41', plain,
% 1.06/1.24      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.06/1.24         ((r2_hidden @ (k1_mcart_1 @ X36) @ X37)
% 1.06/1.24          | ~ (r2_hidden @ X36 @ (k2_zfmisc_1 @ X37 @ X38)))),
% 1.06/1.24      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.06/1.24  thf('42', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.06/1.24         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.06/1.24          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['40', '41'])).
% 1.06/1.24  thf('43', plain,
% 1.06/1.24      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 1.06/1.24        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['39', '42'])).
% 1.06/1.24  thf('44', plain,
% 1.06/1.24      (![X39 : $i, X40 : $i]:
% 1.06/1.24         (((X39) = (k4_tarski @ (k1_mcart_1 @ X39) @ (k2_mcart_1 @ X39)))
% 1.06/1.24          | ~ (v1_relat_1 @ X40)
% 1.06/1.24          | ~ (r2_hidden @ X39 @ X40))),
% 1.06/1.24      inference('cnf', [status(esa)], [t23_mcart_1])).
% 1.06/1.24  thf('45', plain,
% 1.06/1.24      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 1.06/1.24        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 1.06/1.24        | ((k1_mcart_1 @ sk_E)
% 1.06/1.24            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.06/1.24               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 1.06/1.24      inference('sup-', [status(thm)], ['43', '44'])).
% 1.06/1.24  thf('46', plain,
% 1.06/1.24      (![X22 : $i, X23 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X22 @ X23))),
% 1.06/1.24      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.06/1.24  thf('47', plain,
% 1.06/1.24      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 1.06/1.24        | ((k1_mcart_1 @ sk_E)
% 1.06/1.24            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.06/1.24               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 1.06/1.24      inference('demod', [status(thm)], ['45', '46'])).
% 1.06/1.24  thf('48', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]:
% 1.06/1.24         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['13', '24'])).
% 1.06/1.24  thf('49', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (((k1_mcart_1 @ sk_E)
% 1.06/1.24            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.06/1.24               (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 1.06/1.24          | ((k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1) @ X0)
% 1.06/1.24              = (k1_xboole_0)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['47', '48'])).
% 1.06/1.24  thf('50', plain,
% 1.06/1.24      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.06/1.24         ((k4_zfmisc_1 @ X32 @ X33 @ X34 @ X35)
% 1.06/1.24           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X32 @ X33 @ X34) @ X35))),
% 1.06/1.24      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.06/1.24  thf('51', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (((k1_mcart_1 @ sk_E)
% 1.06/1.24            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.06/1.24               (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 1.06/1.24          | ((k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0) = (k1_xboole_0)))),
% 1.06/1.24      inference('demod', [status(thm)], ['49', '50'])).
% 1.06/1.24  thf('52', plain,
% 1.06/1.24      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 1.06/1.24         (((k4_zfmisc_1 @ X45 @ X46 @ X47 @ X48) != (k1_xboole_0))
% 1.06/1.24          | ((X48) = (k1_xboole_0))
% 1.06/1.24          | ((X47) = (k1_xboole_0))
% 1.06/1.24          | ((X46) = (k1_xboole_0))
% 1.06/1.24          | ((X45) = (k1_xboole_0)))),
% 1.06/1.24      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.06/1.24  thf('53', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (((k1_xboole_0) != (k1_xboole_0))
% 1.06/1.24          | ((k1_mcart_1 @ sk_E)
% 1.06/1.24              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.06/1.24                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 1.06/1.24          | ((sk_A) = (k1_xboole_0))
% 1.06/1.24          | ((sk_B_1) = (k1_xboole_0))
% 1.06/1.24          | ((sk_C_1) = (k1_xboole_0))
% 1.06/1.24          | ((X0) = (k1_xboole_0)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['51', '52'])).
% 1.06/1.24  thf('54', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (((X0) = (k1_xboole_0))
% 1.06/1.24          | ((sk_C_1) = (k1_xboole_0))
% 1.06/1.24          | ((sk_B_1) = (k1_xboole_0))
% 1.06/1.24          | ((sk_A) = (k1_xboole_0))
% 1.06/1.24          | ((k1_mcart_1 @ sk_E)
% 1.06/1.24              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.06/1.24                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 1.06/1.24      inference('simplify', [status(thm)], ['53'])).
% 1.06/1.24  thf('55', plain, (((sk_A) != (k1_xboole_0))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('56', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('57', plain, (((sk_C_1) != (k1_xboole_0))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('58', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (((X0) = (k1_xboole_0))
% 1.06/1.24          | ((k1_mcart_1 @ sk_E)
% 1.06/1.24              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.06/1.24                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 1.06/1.24      inference('simplify_reflect-', [status(thm)], ['54', '55', '56', '57'])).
% 1.06/1.24  thf('59', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (((X0) = (k1_xboole_0))
% 1.06/1.24          | ((k1_mcart_1 @ sk_E)
% 1.06/1.24              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.06/1.24                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 1.06/1.24      inference('simplify_reflect-', [status(thm)], ['54', '55', '56', '57'])).
% 1.06/1.24  thf('60', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]:
% 1.06/1.24         (((X1) = (X0))
% 1.06/1.24          | ((k1_mcart_1 @ sk_E)
% 1.06/1.24              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.06/1.24                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 1.06/1.24          | ((k1_mcart_1 @ sk_E)
% 1.06/1.24              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.06/1.24                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 1.06/1.24      inference('sup+', [status(thm)], ['58', '59'])).
% 1.06/1.24  thf('61', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]:
% 1.06/1.24         (((k1_mcart_1 @ sk_E)
% 1.06/1.24            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.06/1.24               (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 1.06/1.24          | ((X1) = (X0)))),
% 1.06/1.24      inference('simplify', [status(thm)], ['60'])).
% 1.06/1.24  thf('62', plain,
% 1.06/1.24      (((k1_mcart_1 @ sk_E)
% 1.06/1.24         = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.06/1.24            (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 1.06/1.24      inference('condensation', [status(thm)], ['61'])).
% 1.06/1.24  thf(d3_mcart_1, axiom,
% 1.06/1.24    (![A:$i,B:$i,C:$i]:
% 1.06/1.24     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 1.06/1.24  thf('63', plain,
% 1.06/1.24      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.06/1.24         ((k3_mcart_1 @ X26 @ X27 @ X28)
% 1.06/1.24           = (k4_tarski @ (k4_tarski @ X26 @ X27) @ X28))),
% 1.06/1.24      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.06/1.24  thf('64', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.06/1.24           (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 1.06/1.24           = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))),
% 1.06/1.24      inference('sup+', [status(thm)], ['62', '63'])).
% 1.06/1.24  thf('65', plain,
% 1.06/1.24      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 1.06/1.24        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['39', '42'])).
% 1.06/1.24  thf('66', plain,
% 1.06/1.24      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.06/1.24         ((r2_hidden @ (k2_mcart_1 @ X36) @ X38)
% 1.06/1.24          | ~ (r2_hidden @ X36 @ (k2_zfmisc_1 @ X37 @ X38)))),
% 1.06/1.24      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.06/1.24  thf('67', plain,
% 1.06/1.24      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 1.06/1.24        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_1))),
% 1.06/1.24      inference('sup-', [status(thm)], ['65', '66'])).
% 1.06/1.24  thf('68', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]:
% 1.06/1.24         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['13', '24'])).
% 1.06/1.24  thf('69', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_1)
% 1.06/1.24          | ((k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1) @ X0)
% 1.06/1.24              = (k1_xboole_0)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['67', '68'])).
% 1.06/1.24  thf('70', plain,
% 1.06/1.24      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.06/1.24         ((k4_zfmisc_1 @ X32 @ X33 @ X34 @ X35)
% 1.06/1.24           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X32 @ X33 @ X34) @ X35))),
% 1.06/1.24      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.06/1.24  thf('71', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_1)
% 1.06/1.24          | ((k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0) = (k1_xboole_0)))),
% 1.06/1.24      inference('demod', [status(thm)], ['69', '70'])).
% 1.06/1.24  thf('72', plain,
% 1.06/1.24      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 1.06/1.24         (((k4_zfmisc_1 @ X45 @ X46 @ X47 @ X48) != (k1_xboole_0))
% 1.06/1.24          | ((X48) = (k1_xboole_0))
% 1.06/1.24          | ((X47) = (k1_xboole_0))
% 1.06/1.24          | ((X46) = (k1_xboole_0))
% 1.06/1.24          | ((X45) = (k1_xboole_0)))),
% 1.06/1.24      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.06/1.24  thf('73', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (((k1_xboole_0) != (k1_xboole_0))
% 1.06/1.24          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_1)
% 1.06/1.24          | ((sk_A) = (k1_xboole_0))
% 1.06/1.24          | ((sk_B_1) = (k1_xboole_0))
% 1.06/1.24          | ((sk_C_1) = (k1_xboole_0))
% 1.06/1.24          | ((X0) = (k1_xboole_0)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['71', '72'])).
% 1.06/1.24  thf('74', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (((X0) = (k1_xboole_0))
% 1.06/1.24          | ((sk_C_1) = (k1_xboole_0))
% 1.06/1.24          | ((sk_B_1) = (k1_xboole_0))
% 1.06/1.24          | ((sk_A) = (k1_xboole_0))
% 1.06/1.24          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_1))),
% 1.06/1.24      inference('simplify', [status(thm)], ['73'])).
% 1.06/1.24  thf('75', plain, (((sk_A) != (k1_xboole_0))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('76', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('77', plain, (((sk_C_1) != (k1_xboole_0))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('78', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (((X0) = (k1_xboole_0))
% 1.06/1.24          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_1))),
% 1.06/1.24      inference('simplify_reflect-', [status(thm)], ['74', '75', '76', '77'])).
% 1.06/1.24  thf(t1_subset, axiom,
% 1.06/1.24    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.06/1.24  thf('79', plain,
% 1.06/1.24      (![X20 : $i, X21 : $i]:
% 1.06/1.24         ((m1_subset_1 @ X20 @ X21) | ~ (r2_hidden @ X20 @ X21))),
% 1.06/1.24      inference('cnf', [status(esa)], [t1_subset])).
% 1.06/1.24  thf('80', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (((X0) = (k1_xboole_0))
% 1.06/1.24          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_1))),
% 1.06/1.24      inference('sup-', [status(thm)], ['78', '79'])).
% 1.06/1.24  thf('81', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.06/1.24      inference('sup-', [status(thm)], ['14', '17'])).
% 1.06/1.24  thf('82', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         ((v1_xboole_0 @ X0)
% 1.06/1.24          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_1))),
% 1.06/1.24      inference('sup+', [status(thm)], ['80', '81'])).
% 1.06/1.24  thf(d2_tarski, axiom,
% 1.06/1.24    (![A:$i,B:$i,C:$i]:
% 1.06/1.24     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 1.06/1.24       ( ![D:$i]:
% 1.06/1.24         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 1.06/1.24  thf('83', plain,
% 1.06/1.24      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 1.06/1.24         (((X7) != (X6))
% 1.06/1.24          | (r2_hidden @ X7 @ X8)
% 1.06/1.24          | ((X8) != (k2_tarski @ X9 @ X6)))),
% 1.06/1.24      inference('cnf', [status(esa)], [d2_tarski])).
% 1.06/1.24  thf('84', plain,
% 1.06/1.24      (![X6 : $i, X9 : $i]: (r2_hidden @ X6 @ (k2_tarski @ X9 @ X6))),
% 1.06/1.24      inference('simplify', [status(thm)], ['83'])).
% 1.06/1.24  thf('85', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.06/1.24      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.06/1.24  thf('86', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 1.06/1.24      inference('sup-', [status(thm)], ['84', '85'])).
% 1.06/1.24  thf('87', plain,
% 1.06/1.24      ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_1)),
% 1.06/1.24      inference('sup-', [status(thm)], ['82', '86'])).
% 1.06/1.24  thf('88', plain,
% 1.06/1.24      (![X50 : $i, X51 : $i, X52 : $i]:
% 1.06/1.24         (~ (m1_subset_1 @ X50 @ sk_B_1)
% 1.06/1.24          | ((sk_D_1) = (X51))
% 1.06/1.24          | ((sk_E) != (k3_mcart_1 @ X51 @ X50 @ X52))
% 1.06/1.24          | ~ (m1_subset_1 @ X52 @ sk_C_1)
% 1.06/1.24          | ~ (m1_subset_1 @ X51 @ sk_A))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('89', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]:
% 1.06/1.24         (~ (m1_subset_1 @ X0 @ sk_A)
% 1.06/1.24          | ~ (m1_subset_1 @ X1 @ sk_C_1)
% 1.06/1.24          | ((sk_E)
% 1.06/1.24              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1))
% 1.06/1.24          | ((sk_D_1) = (X0)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['87', '88'])).
% 1.06/1.24  thf('90', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 1.06/1.24          | ((sk_D_1) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 1.06/1.24          | ~ (m1_subset_1 @ X0 @ sk_C_1)
% 1.06/1.24          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 1.06/1.24      inference('sup-', [status(thm)], ['64', '89'])).
% 1.06/1.24  thf('91', plain,
% 1.06/1.24      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 1.06/1.24        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['39', '42'])).
% 1.06/1.24  thf('92', plain,
% 1.06/1.24      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.06/1.24         ((r2_hidden @ (k1_mcart_1 @ X36) @ X37)
% 1.06/1.24          | ~ (r2_hidden @ X36 @ (k2_zfmisc_1 @ X37 @ X38)))),
% 1.06/1.24      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.06/1.24  thf('93', plain,
% 1.06/1.24      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 1.06/1.24        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 1.06/1.24      inference('sup-', [status(thm)], ['91', '92'])).
% 1.06/1.24  thf('94', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]:
% 1.06/1.24         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['13', '24'])).
% 1.06/1.24  thf('95', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 1.06/1.24          | ((k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1) @ X0)
% 1.06/1.24              = (k1_xboole_0)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['93', '94'])).
% 1.06/1.24  thf('96', plain,
% 1.06/1.24      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.06/1.24         ((k4_zfmisc_1 @ X32 @ X33 @ X34 @ X35)
% 1.06/1.24           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X32 @ X33 @ X34) @ X35))),
% 1.06/1.24      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.06/1.24  thf('97', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 1.06/1.24          | ((k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0) = (k1_xboole_0)))),
% 1.06/1.24      inference('demod', [status(thm)], ['95', '96'])).
% 1.06/1.24  thf('98', plain,
% 1.06/1.24      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 1.06/1.24         (((k4_zfmisc_1 @ X45 @ X46 @ X47 @ X48) != (k1_xboole_0))
% 1.06/1.24          | ((X48) = (k1_xboole_0))
% 1.06/1.24          | ((X47) = (k1_xboole_0))
% 1.06/1.24          | ((X46) = (k1_xboole_0))
% 1.06/1.24          | ((X45) = (k1_xboole_0)))),
% 1.06/1.24      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.06/1.24  thf('99', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (((k1_xboole_0) != (k1_xboole_0))
% 1.06/1.24          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 1.06/1.24          | ((sk_A) = (k1_xboole_0))
% 1.06/1.24          | ((sk_B_1) = (k1_xboole_0))
% 1.06/1.24          | ((sk_C_1) = (k1_xboole_0))
% 1.06/1.24          | ((X0) = (k1_xboole_0)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['97', '98'])).
% 1.06/1.24  thf('100', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (((X0) = (k1_xboole_0))
% 1.06/1.24          | ((sk_C_1) = (k1_xboole_0))
% 1.06/1.24          | ((sk_B_1) = (k1_xboole_0))
% 1.06/1.24          | ((sk_A) = (k1_xboole_0))
% 1.06/1.24          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 1.06/1.24      inference('simplify', [status(thm)], ['99'])).
% 1.06/1.24  thf('101', plain, (((sk_A) != (k1_xboole_0))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('102', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('103', plain, (((sk_C_1) != (k1_xboole_0))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('104', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (((X0) = (k1_xboole_0))
% 1.06/1.24          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 1.06/1.24      inference('simplify_reflect-', [status(thm)],
% 1.06/1.24                ['100', '101', '102', '103'])).
% 1.06/1.24  thf('105', plain,
% 1.06/1.24      (![X20 : $i, X21 : $i]:
% 1.06/1.24         ((m1_subset_1 @ X20 @ X21) | ~ (r2_hidden @ X20 @ X21))),
% 1.06/1.24      inference('cnf', [status(esa)], [t1_subset])).
% 1.06/1.24  thf('106', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (((X0) = (k1_xboole_0))
% 1.06/1.24          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 1.06/1.24      inference('sup-', [status(thm)], ['104', '105'])).
% 1.06/1.24  thf('107', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.06/1.24      inference('sup-', [status(thm)], ['14', '17'])).
% 1.06/1.24  thf('108', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         ((v1_xboole_0 @ X0)
% 1.06/1.24          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 1.06/1.24      inference('sup+', [status(thm)], ['106', '107'])).
% 1.06/1.24  thf('109', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 1.06/1.24      inference('sup-', [status(thm)], ['84', '85'])).
% 1.06/1.24  thf('110', plain,
% 1.06/1.24      ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)),
% 1.06/1.24      inference('sup-', [status(thm)], ['108', '109'])).
% 1.06/1.24  thf('111', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 1.06/1.24          | ((sk_D_1) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 1.06/1.24          | ~ (m1_subset_1 @ X0 @ sk_C_1))),
% 1.06/1.24      inference('demod', [status(thm)], ['90', '110'])).
% 1.06/1.24  thf('112', plain,
% 1.06/1.24      (((sk_D_1) != (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('113', plain,
% 1.06/1.24      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf(t50_mcart_1, axiom,
% 1.06/1.24    (![A:$i,B:$i,C:$i]:
% 1.06/1.24     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.06/1.24          ( ( C ) != ( k1_xboole_0 ) ) & 
% 1.06/1.24          ( ~( ![D:$i]:
% 1.06/1.24               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.06/1.24                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 1.06/1.24                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 1.06/1.24                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 1.06/1.24                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 1.06/1.24                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 1.06/1.24  thf('114', plain,
% 1.06/1.24      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 1.06/1.24         (((X41) = (k1_xboole_0))
% 1.06/1.24          | ((X42) = (k1_xboole_0))
% 1.06/1.24          | ((k5_mcart_1 @ X41 @ X42 @ X44 @ X43)
% 1.06/1.24              = (k1_mcart_1 @ (k1_mcart_1 @ X43)))
% 1.06/1.24          | ~ (m1_subset_1 @ X43 @ (k3_zfmisc_1 @ X41 @ X42 @ X44))
% 1.06/1.24          | ((X44) = (k1_xboole_0)))),
% 1.06/1.24      inference('cnf', [status(esa)], [t50_mcart_1])).
% 1.06/1.24  thf('115', plain,
% 1.06/1.24      ((((sk_C_1) = (k1_xboole_0))
% 1.06/1.24        | ((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E)
% 1.06/1.24            = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 1.06/1.24        | ((sk_B_1) = (k1_xboole_0))
% 1.06/1.24        | ((sk_A) = (k1_xboole_0)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['113', '114'])).
% 1.06/1.24  thf('116', plain, (((sk_A) != (k1_xboole_0))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('117', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('118', plain, (((sk_C_1) != (k1_xboole_0))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('119', plain,
% 1.06/1.24      (((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E)
% 1.06/1.24         = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 1.06/1.24      inference('simplify_reflect-', [status(thm)],
% 1.06/1.24                ['115', '116', '117', '118'])).
% 1.06/1.24  thf('120', plain, (((sk_D_1) != (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 1.06/1.24      inference('demod', [status(thm)], ['112', '119'])).
% 1.06/1.24  thf('121', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 1.06/1.24          | ~ (m1_subset_1 @ X0 @ sk_C_1))),
% 1.06/1.24      inference('simplify_reflect-', [status(thm)], ['111', '120'])).
% 1.06/1.24  thf('122', plain,
% 1.06/1.24      ((((sk_E) != (sk_E)) | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C_1))),
% 1.06/1.24      inference('sup-', [status(thm)], ['38', '121'])).
% 1.06/1.24  thf('123', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]:
% 1.06/1.24         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['13', '24'])).
% 1.06/1.24  thf('124', plain,
% 1.06/1.24      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 1.06/1.24        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['0', '1'])).
% 1.06/1.24  thf('125', plain,
% 1.06/1.24      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.06/1.24         ((k3_zfmisc_1 @ X29 @ X30 @ X31)
% 1.06/1.24           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30) @ X31))),
% 1.06/1.24      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.06/1.24  thf('126', plain,
% 1.06/1.24      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.06/1.24         ((r2_hidden @ (k2_mcart_1 @ X36) @ X38)
% 1.06/1.24          | ~ (r2_hidden @ X36 @ (k2_zfmisc_1 @ X37 @ X38)))),
% 1.06/1.24      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.06/1.24  thf('127', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.06/1.24         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.06/1.24          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 1.06/1.24      inference('sup-', [status(thm)], ['125', '126'])).
% 1.06/1.24  thf('128', plain,
% 1.06/1.24      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 1.06/1.24        | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C_1))),
% 1.06/1.24      inference('sup-', [status(thm)], ['124', '127'])).
% 1.06/1.24  thf('129', plain,
% 1.06/1.24      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['18', '23'])).
% 1.06/1.24  thf('130', plain,
% 1.06/1.24      (((r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C_1)
% 1.06/1.24        | ((k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_xboole_0)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['128', '129'])).
% 1.06/1.24  thf('131', plain,
% 1.06/1.24      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.06/1.24         ((k4_zfmisc_1 @ X32 @ X33 @ X34 @ X35)
% 1.06/1.24           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X32 @ X33 @ X34) @ X35))),
% 1.06/1.24      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.06/1.24  thf('132', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (((k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0)
% 1.06/1.24            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 1.06/1.24          | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C_1))),
% 1.06/1.24      inference('sup+', [status(thm)], ['130', '131'])).
% 1.06/1.24  thf('133', plain,
% 1.06/1.24      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 1.06/1.24         (((k4_zfmisc_1 @ X45 @ X46 @ X47 @ X48) != (k1_xboole_0))
% 1.06/1.24          | ((X48) = (k1_xboole_0))
% 1.06/1.24          | ((X47) = (k1_xboole_0))
% 1.06/1.24          | ((X46) = (k1_xboole_0))
% 1.06/1.24          | ((X45) = (k1_xboole_0)))),
% 1.06/1.24      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.06/1.24  thf('134', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 1.06/1.24          | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C_1)
% 1.06/1.24          | ((sk_A) = (k1_xboole_0))
% 1.06/1.24          | ((sk_B_1) = (k1_xboole_0))
% 1.06/1.24          | ((sk_C_1) = (k1_xboole_0))
% 1.06/1.24          | ((X0) = (k1_xboole_0)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['132', '133'])).
% 1.06/1.24  thf('135', plain, (((sk_C_1) != (k1_xboole_0))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('136', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('137', plain, (((sk_A) != (k1_xboole_0))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('138', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 1.06/1.24          | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C_1)
% 1.06/1.24          | ((X0) = (k1_xboole_0)))),
% 1.06/1.24      inference('simplify_reflect-', [status(thm)],
% 1.06/1.24                ['134', '135', '136', '137'])).
% 1.06/1.24  thf('139', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (((k1_xboole_0) != (k1_xboole_0))
% 1.06/1.24          | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.06/1.24          | ((X0) = (k1_xboole_0))
% 1.06/1.24          | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C_1))),
% 1.06/1.24      inference('sup-', [status(thm)], ['123', '138'])).
% 1.06/1.24  thf('140', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.06/1.24      inference('sup-', [status(thm)], ['14', '17'])).
% 1.06/1.24  thf('141', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (((k1_xboole_0) != (k1_xboole_0))
% 1.06/1.24          | ((X0) = (k1_xboole_0))
% 1.06/1.24          | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C_1))),
% 1.06/1.24      inference('demod', [status(thm)], ['139', '140'])).
% 1.06/1.24  thf('142', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         ((r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C_1) | ((X0) = (k1_xboole_0)))),
% 1.06/1.24      inference('simplify', [status(thm)], ['141'])).
% 1.06/1.24  thf('143', plain,
% 1.06/1.24      (![X20 : $i, X21 : $i]:
% 1.06/1.24         ((m1_subset_1 @ X20 @ X21) | ~ (r2_hidden @ X20 @ X21))),
% 1.06/1.24      inference('cnf', [status(esa)], [t1_subset])).
% 1.06/1.24  thf('144', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C_1))),
% 1.06/1.24      inference('sup-', [status(thm)], ['142', '143'])).
% 1.06/1.24  thf('145', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.06/1.24      inference('sup-', [status(thm)], ['14', '17'])).
% 1.06/1.24  thf('146', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         ((v1_xboole_0 @ X0) | (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C_1))),
% 1.06/1.24      inference('sup+', [status(thm)], ['144', '145'])).
% 1.06/1.24  thf('147', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 1.06/1.24      inference('sup-', [status(thm)], ['84', '85'])).
% 1.06/1.24  thf('148', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C_1)),
% 1.06/1.24      inference('sup-', [status(thm)], ['146', '147'])).
% 1.06/1.24  thf('149', plain, (((sk_E) != (sk_E))),
% 1.06/1.24      inference('demod', [status(thm)], ['122', '148'])).
% 1.06/1.24  thf('150', plain, ($false), inference('simplify', [status(thm)], ['149'])).
% 1.06/1.24  
% 1.06/1.24  % SZS output end Refutation
% 1.06/1.24  
% 1.06/1.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
