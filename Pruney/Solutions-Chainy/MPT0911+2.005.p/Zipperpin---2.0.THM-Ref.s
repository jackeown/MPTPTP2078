%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vnlAWcGgnz

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:56 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 570 expanded)
%              Number of leaves         :   37 ( 185 expanded)
%              Depth                    :   24
%              Number of atoms          : 1011 (8236 expanded)
%              Number of equality atoms :  112 (1112 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t71_mcart_1,conjecture,(
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
                     => ( D = H ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D
            = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )).

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
                       => ( D = H ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D
              = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t71_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_E_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
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
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ X29 )
      | ( r2_hidden @ X28 @ X29 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ sk_E_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X52: $i,X53: $i] :
      ( ( X52
        = ( k4_tarski @ ( k1_mcart_1 @ X52 ) @ ( k2_mcart_1 @ X52 ) ) )
      | ~ ( v1_relat_1 @ X53 )
      | ~ ( r2_hidden @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( sk_E_2
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( k3_zfmisc_1 @ X38 @ X39 @ X40 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) @ X40 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('6',plain,(
    ! [X33: $i,X34: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( v1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( sk_E_2
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X4 = X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('10',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k2_zfmisc_1 @ X24 @ X25 )
        = k1_xboole_0 )
      | ( X25 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('11',plain,(
    ! [X24: $i] :
      ( ( k2_zfmisc_1 @ X24 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('12',plain,(
    ! [X26: $i,X27: $i] :
      ~ ( r2_hidden @ X26 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_E_2
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('18',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k4_zfmisc_1 @ X41 @ X42 @ X43 @ X44 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X41 @ X42 @ X43 ) @ X44 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_E_2
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k2_zfmisc_1 @ X24 @ X25 )
        = k1_xboole_0 )
      | ( X24 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('21',plain,(
    ! [X25: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X25 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0 )
        = k1_xboole_0 )
      | ( sk_E_2
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) ) ) ),
    inference(demod,[status(thm)],['19','21'])).

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ( ( k4_zfmisc_1 @ X58 @ X59 @ X60 @ X61 )
       != k1_xboole_0 )
      | ( X61 = k1_xboole_0 )
      | ( X60 = k1_xboole_0 )
      | ( X59 = k1_xboole_0 )
      | ( X58 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_E_2
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_E_2
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_E_2
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['25','26','27','28'])).

thf('30',plain,
    ( ( k1_xboole_0 != sk_E_2 )
    | ( sk_E_2
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) ) ),
    inference(eq_fact,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_E_2
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['25','26','27','28'])).

thf('32',plain,
    ( sk_E_2
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ sk_E_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('34',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( k3_zfmisc_1 @ X38 @ X39 @ X40 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) @ X40 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('35',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X49 ) @ X50 )
      | ~ ( r2_hidden @ X49 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_E_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X30 @ X29 )
      | ( v1_xboole_0 @ X30 )
      | ~ ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('40',plain,
    ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( v1_xboole_0 @ sk_E_2 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_E_2 ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,
    ( sk_E_2
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf(fc1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( v1_xboole_0 @ ( k4_tarski @ A @ B ) ) )).

thf('43',plain,(
    ! [X21: $i,X22: $i] :
      ~ ( v1_xboole_0 @ ( k4_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc1_zfmisc_1])).

thf('44',plain,(
    ~ ( v1_xboole_0 @ sk_E_2 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X52: $i,X53: $i] :
      ( ( X52
        = ( k4_tarski @ ( k1_mcart_1 @ X52 ) @ ( k2_mcart_1 @ X52 ) ) )
      | ~ ( v1_relat_1 @ X53 )
      | ~ ( r2_hidden @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( ( k1_mcart_1 @ sk_E_2 )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X33: $i,X34: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('49',plain,
    ( ( k1_mcart_1 @ sk_E_2 )
    = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('50',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k3_mcart_1 @ X35 @ X36 @ X37 )
      = ( k4_tarski @ ( k4_tarski @ X35 @ X36 ) @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['41','44'])).

thf('53',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X49 ) @ X51 )
      | ~ ( r2_hidden @ X49 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('54',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ( m1_subset_1 @ X28 @ X29 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('57',plain,(
    ! [X28: $i,X29: $i] :
      ( ( m1_subset_1 @ X28 @ X29 )
      | ~ ( r2_hidden @ X28 @ X29 ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ~ ( m1_subset_1 @ X63 @ sk_B_1 )
      | ( sk_E_2
       != ( k3_mcart_1 @ X64 @ X63 @ X65 ) )
      | ( sk_D_1 = X65 )
      | ~ ( m1_subset_1 @ X65 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X64 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C_1 )
      | ( sk_D_1 = X1 )
      | ( sk_E_2
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( sk_E_2
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ X0 ) )
      | ( sk_D_1 = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','60'])).

thf('62',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['41','44'])).

thf('63',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X49 ) @ X50 )
      | ~ ( r2_hidden @ X49 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('64',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_A ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X28: $i,X29: $i] :
      ( ( m1_subset_1 @ X28 @ X29 )
      | ~ ( r2_hidden @ X28 @ X29 ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('66',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_A ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( sk_E_2
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ X0 ) )
      | ( sk_D_1 = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['61','66'])).

thf('68',plain,
    ( ( sk_E_2 != sk_E_2 )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E_2 ) @ sk_C_1 )
    | ( sk_D_1
      = ( k2_mcart_1 @ sk_E_2 ) ) ),
    inference('sup-',[status(thm)],['32','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_E_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ) )).

thf('70',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( m1_subset_1 @ ( k7_mcart_1 @ X45 @ X46 @ X47 @ X48 ) @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k3_zfmisc_1 @ X45 @ X46 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_mcart_1])).

thf('71',plain,(
    m1_subset_1 @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_2 ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_E_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
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

thf('73',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( X54 = k1_xboole_0 )
      | ( X55 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X54 @ X55 @ X57 @ X56 )
        = ( k2_mcart_1 @ X56 ) )
      | ~ ( m1_subset_1 @ X56 @ ( k3_zfmisc_1 @ X54 @ X55 @ X57 ) )
      | ( X57 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('74',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_2 )
      = ( k2_mcart_1 @ sk_E_2 ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_2 )
    = ( k2_mcart_1 @ sk_E_2 ) ),
    inference('simplify_reflect-',[status(thm)],['74','75','76','77'])).

thf('79',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E_2 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['71','78'])).

thf('80',plain,
    ( ( sk_E_2 != sk_E_2 )
    | ( sk_D_1
      = ( k2_mcart_1 @ sk_E_2 ) ) ),
    inference(demod,[status(thm)],['68','79'])).

thf('81',plain,
    ( sk_D_1
    = ( k2_mcart_1 @ sk_E_2 ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    sk_D_1
 != ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_2 )
    = ( k2_mcart_1 @ sk_E_2 ) ),
    inference('simplify_reflect-',[status(thm)],['74','75','76','77'])).

thf('84',plain,(
    sk_D_1
 != ( k2_mcart_1 @ sk_E_2 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['81','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vnlAWcGgnz
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:39:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.59/0.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.82  % Solved by: fo/fo7.sh
% 0.59/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.82  % done 667 iterations in 0.366s
% 0.59/0.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.82  % SZS output start Refutation
% 0.59/0.82  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.59/0.82  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.59/0.82  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.59/0.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.82  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.59/0.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.82  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.59/0.82  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.59/0.82  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.59/0.82  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.59/0.82  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.59/0.82  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.59/0.82  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.59/0.82  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.82  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.59/0.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.82  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.82  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.59/0.82  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.59/0.82  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.59/0.82  thf(t71_mcart_1, conjecture,
% 0.59/0.82    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.59/0.82     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.59/0.82       ( ( ![F:$i]:
% 0.59/0.82           ( ( m1_subset_1 @ F @ A ) =>
% 0.59/0.82             ( ![G:$i]:
% 0.59/0.82               ( ( m1_subset_1 @ G @ B ) =>
% 0.59/0.82                 ( ![H:$i]:
% 0.59/0.82                   ( ( m1_subset_1 @ H @ C ) =>
% 0.59/0.82                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.59/0.82                       ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.59/0.82         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.59/0.82           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.59/0.82           ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.59/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.82    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.59/0.82        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.59/0.82          ( ( ![F:$i]:
% 0.59/0.82              ( ( m1_subset_1 @ F @ A ) =>
% 0.59/0.82                ( ![G:$i]:
% 0.59/0.82                  ( ( m1_subset_1 @ G @ B ) =>
% 0.59/0.82                    ( ![H:$i]:
% 0.59/0.82                      ( ( m1_subset_1 @ H @ C ) =>
% 0.59/0.82                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.59/0.82                          ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.59/0.82            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.59/0.82              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.59/0.82              ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.59/0.82    inference('cnf.neg', [status(esa)], [t71_mcart_1])).
% 0.59/0.82  thf('0', plain,
% 0.59/0.82      ((m1_subset_1 @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf(d2_subset_1, axiom,
% 0.59/0.82    (![A:$i,B:$i]:
% 0.59/0.82     ( ( ( v1_xboole_0 @ A ) =>
% 0.59/0.82         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.59/0.82       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.59/0.82         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.59/0.82  thf('1', plain,
% 0.59/0.82      (![X28 : $i, X29 : $i]:
% 0.59/0.82         (~ (m1_subset_1 @ X28 @ X29)
% 0.59/0.82          | (r2_hidden @ X28 @ X29)
% 0.59/0.82          | (v1_xboole_0 @ X29))),
% 0.59/0.82      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.59/0.82  thf('2', plain,
% 0.59/0.82      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.59/0.82        | (r2_hidden @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['0', '1'])).
% 0.59/0.82  thf(t23_mcart_1, axiom,
% 0.59/0.82    (![A:$i,B:$i]:
% 0.59/0.82     ( ( v1_relat_1 @ B ) =>
% 0.59/0.82       ( ( r2_hidden @ A @ B ) =>
% 0.59/0.82         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 0.59/0.82  thf('3', plain,
% 0.59/0.82      (![X52 : $i, X53 : $i]:
% 0.59/0.82         (((X52) = (k4_tarski @ (k1_mcart_1 @ X52) @ (k2_mcart_1 @ X52)))
% 0.59/0.82          | ~ (v1_relat_1 @ X53)
% 0.59/0.82          | ~ (r2_hidden @ X52 @ X53))),
% 0.59/0.82      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.59/0.82  thf('4', plain,
% 0.59/0.82      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.59/0.82        | ~ (v1_relat_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.59/0.82        | ((sk_E_2)
% 0.59/0.82            = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2))))),
% 0.59/0.82      inference('sup-', [status(thm)], ['2', '3'])).
% 0.59/0.82  thf(d3_zfmisc_1, axiom,
% 0.59/0.82    (![A:$i,B:$i,C:$i]:
% 0.59/0.82     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.59/0.82       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.59/0.82  thf('5', plain,
% 0.59/0.82      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.59/0.82         ((k3_zfmisc_1 @ X38 @ X39 @ X40)
% 0.59/0.82           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39) @ X40))),
% 0.59/0.82      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.59/0.82  thf(fc6_relat_1, axiom,
% 0.59/0.82    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.59/0.82  thf('6', plain,
% 0.59/0.82      (![X33 : $i, X34 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X33 @ X34))),
% 0.59/0.82      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.59/0.82  thf('7', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.82         (v1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))),
% 0.59/0.82      inference('sup+', [status(thm)], ['5', '6'])).
% 0.59/0.82  thf('8', plain,
% 0.59/0.82      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.59/0.82        | ((sk_E_2)
% 0.59/0.82            = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2))))),
% 0.59/0.82      inference('demod', [status(thm)], ['4', '7'])).
% 0.59/0.82  thf(t2_tarski, axiom,
% 0.59/0.82    (![A:$i,B:$i]:
% 0.59/0.82     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.59/0.82       ( ( A ) = ( B ) ) ))).
% 0.59/0.82  thf('9', plain,
% 0.59/0.82      (![X3 : $i, X4 : $i]:
% 0.59/0.82         (((X4) = (X3))
% 0.59/0.82          | (r2_hidden @ (sk_C @ X3 @ X4) @ X3)
% 0.59/0.82          | (r2_hidden @ (sk_C @ X3 @ X4) @ X4))),
% 0.59/0.82      inference('cnf', [status(esa)], [t2_tarski])).
% 0.59/0.82  thf(t113_zfmisc_1, axiom,
% 0.59/0.82    (![A:$i,B:$i]:
% 0.59/0.82     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.59/0.82       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.59/0.82  thf('10', plain,
% 0.59/0.82      (![X24 : $i, X25 : $i]:
% 0.59/0.82         (((k2_zfmisc_1 @ X24 @ X25) = (k1_xboole_0))
% 0.59/0.82          | ((X25) != (k1_xboole_0)))),
% 0.59/0.82      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.59/0.82  thf('11', plain,
% 0.59/0.82      (![X24 : $i]: ((k2_zfmisc_1 @ X24 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.82      inference('simplify', [status(thm)], ['10'])).
% 0.59/0.82  thf(t152_zfmisc_1, axiom,
% 0.59/0.82    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.59/0.82  thf('12', plain,
% 0.59/0.82      (![X26 : $i, X27 : $i]: ~ (r2_hidden @ X26 @ (k2_zfmisc_1 @ X26 @ X27))),
% 0.59/0.82      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.59/0.82  thf('13', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.59/0.82      inference('sup-', [status(thm)], ['11', '12'])).
% 0.59/0.82  thf('14', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['9', '13'])).
% 0.59/0.82  thf(d1_xboole_0, axiom,
% 0.59/0.82    (![A:$i]:
% 0.59/0.82     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.59/0.82  thf('15', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.59/0.82      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.59/0.82  thf('16', plain,
% 0.59/0.82      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.82      inference('sup-', [status(thm)], ['14', '15'])).
% 0.59/0.82  thf('17', plain,
% 0.59/0.82      ((((sk_E_2) = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2)))
% 0.59/0.82        | ((k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['8', '16'])).
% 0.59/0.82  thf(d4_zfmisc_1, axiom,
% 0.59/0.82    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.82     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.59/0.82       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.59/0.82  thf('18', plain,
% 0.59/0.82      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.59/0.82         ((k4_zfmisc_1 @ X41 @ X42 @ X43 @ X44)
% 0.59/0.82           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X41 @ X42 @ X43) @ X44))),
% 0.59/0.82      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.59/0.82  thf('19', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0)
% 0.59/0.82            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.59/0.82          | ((sk_E_2)
% 0.59/0.82              = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2))))),
% 0.59/0.82      inference('sup+', [status(thm)], ['17', '18'])).
% 0.59/0.82  thf('20', plain,
% 0.59/0.82      (![X24 : $i, X25 : $i]:
% 0.59/0.82         (((k2_zfmisc_1 @ X24 @ X25) = (k1_xboole_0))
% 0.59/0.82          | ((X24) != (k1_xboole_0)))),
% 0.59/0.82      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.59/0.82  thf('21', plain,
% 0.59/0.82      (![X25 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X25) = (k1_xboole_0))),
% 0.59/0.82      inference('simplify', [status(thm)], ['20'])).
% 0.59/0.82  thf('22', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0) = (k1_xboole_0))
% 0.59/0.82          | ((sk_E_2)
% 0.59/0.82              = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2))))),
% 0.59/0.82      inference('demod', [status(thm)], ['19', '21'])).
% 0.59/0.82  thf(t55_mcart_1, axiom,
% 0.59/0.82    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.82     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.59/0.82         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 0.59/0.82       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 0.59/0.82  thf('23', plain,
% 0.59/0.82      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i]:
% 0.59/0.82         (((k4_zfmisc_1 @ X58 @ X59 @ X60 @ X61) != (k1_xboole_0))
% 0.59/0.82          | ((X61) = (k1_xboole_0))
% 0.59/0.82          | ((X60) = (k1_xboole_0))
% 0.59/0.82          | ((X59) = (k1_xboole_0))
% 0.59/0.82          | ((X58) = (k1_xboole_0)))),
% 0.59/0.82      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.59/0.82  thf('24', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.82          | ((sk_E_2)
% 0.59/0.82              = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2)))
% 0.59/0.82          | ((sk_A) = (k1_xboole_0))
% 0.59/0.82          | ((sk_B_1) = (k1_xboole_0))
% 0.59/0.82          | ((sk_C_1) = (k1_xboole_0))
% 0.59/0.82          | ((X0) = (k1_xboole_0)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['22', '23'])).
% 0.59/0.82  thf('25', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((X0) = (k1_xboole_0))
% 0.59/0.82          | ((sk_C_1) = (k1_xboole_0))
% 0.59/0.82          | ((sk_B_1) = (k1_xboole_0))
% 0.59/0.82          | ((sk_A) = (k1_xboole_0))
% 0.59/0.82          | ((sk_E_2)
% 0.59/0.82              = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2))))),
% 0.59/0.82      inference('simplify', [status(thm)], ['24'])).
% 0.59/0.82  thf('26', plain, (((sk_A) != (k1_xboole_0))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('27', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('28', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('29', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((X0) = (k1_xboole_0))
% 0.59/0.82          | ((sk_E_2)
% 0.59/0.82              = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2))))),
% 0.59/0.82      inference('simplify_reflect-', [status(thm)], ['25', '26', '27', '28'])).
% 0.59/0.82  thf('30', plain,
% 0.59/0.82      ((((k1_xboole_0) != (sk_E_2))
% 0.59/0.82        | ((sk_E_2)
% 0.59/0.82            = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2))))),
% 0.59/0.82      inference('eq_fact', [status(thm)], ['29'])).
% 0.59/0.82  thf('31', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((X0) = (k1_xboole_0))
% 0.59/0.82          | ((sk_E_2)
% 0.59/0.82              = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2))))),
% 0.59/0.82      inference('simplify_reflect-', [status(thm)], ['25', '26', '27', '28'])).
% 0.59/0.82  thf('32', plain,
% 0.59/0.82      (((sk_E_2) = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2)))),
% 0.59/0.82      inference('clc', [status(thm)], ['30', '31'])).
% 0.59/0.82  thf('33', plain,
% 0.59/0.82      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.59/0.82        | (r2_hidden @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['0', '1'])).
% 0.59/0.82  thf('34', plain,
% 0.59/0.82      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.59/0.82         ((k3_zfmisc_1 @ X38 @ X39 @ X40)
% 0.59/0.82           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39) @ X40))),
% 0.59/0.82      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.59/0.82  thf(t10_mcart_1, axiom,
% 0.59/0.82    (![A:$i,B:$i,C:$i]:
% 0.59/0.82     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.59/0.82       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.59/0.82         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.59/0.82  thf('35', plain,
% 0.59/0.82      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.59/0.82         ((r2_hidden @ (k1_mcart_1 @ X49) @ X50)
% 0.59/0.82          | ~ (r2_hidden @ X49 @ (k2_zfmisc_1 @ X50 @ X51)))),
% 0.59/0.82      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.59/0.82  thf('36', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.82         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.59/0.82          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['34', '35'])).
% 0.59/0.82  thf('37', plain,
% 0.59/0.82      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.59/0.82        | (r2_hidden @ (k1_mcart_1 @ sk_E_2) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['33', '36'])).
% 0.59/0.82  thf('38', plain,
% 0.59/0.82      ((m1_subset_1 @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('39', plain,
% 0.59/0.82      (![X29 : $i, X30 : $i]:
% 0.59/0.82         (~ (m1_subset_1 @ X30 @ X29)
% 0.59/0.82          | (v1_xboole_0 @ X30)
% 0.59/0.82          | ~ (v1_xboole_0 @ X29))),
% 0.59/0.82      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.59/0.82  thf('40', plain,
% 0.59/0.82      ((~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.59/0.82        | (v1_xboole_0 @ sk_E_2))),
% 0.59/0.82      inference('sup-', [status(thm)], ['38', '39'])).
% 0.59/0.82  thf('41', plain,
% 0.59/0.82      (((r2_hidden @ (k1_mcart_1 @ sk_E_2) @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.59/0.82        | (v1_xboole_0 @ sk_E_2))),
% 0.59/0.82      inference('sup-', [status(thm)], ['37', '40'])).
% 0.59/0.82  thf('42', plain,
% 0.59/0.82      (((sk_E_2) = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2)))),
% 0.59/0.82      inference('clc', [status(thm)], ['30', '31'])).
% 0.59/0.82  thf(fc1_zfmisc_1, axiom,
% 0.59/0.82    (![A:$i,B:$i]: ( ~( v1_xboole_0 @ ( k4_tarski @ A @ B ) ) ))).
% 0.59/0.82  thf('43', plain,
% 0.59/0.82      (![X21 : $i, X22 : $i]: ~ (v1_xboole_0 @ (k4_tarski @ X21 @ X22))),
% 0.59/0.82      inference('cnf', [status(esa)], [fc1_zfmisc_1])).
% 0.59/0.82  thf('44', plain, (~ (v1_xboole_0 @ sk_E_2)),
% 0.59/0.82      inference('sup-', [status(thm)], ['42', '43'])).
% 0.59/0.82  thf('45', plain,
% 0.59/0.82      ((r2_hidden @ (k1_mcart_1 @ sk_E_2) @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.59/0.82      inference('clc', [status(thm)], ['41', '44'])).
% 0.59/0.82  thf('46', plain,
% 0.59/0.82      (![X52 : $i, X53 : $i]:
% 0.59/0.82         (((X52) = (k4_tarski @ (k1_mcart_1 @ X52) @ (k2_mcart_1 @ X52)))
% 0.59/0.82          | ~ (v1_relat_1 @ X53)
% 0.59/0.82          | ~ (r2_hidden @ X52 @ X53))),
% 0.59/0.82      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.59/0.82  thf('47', plain,
% 0.59/0.82      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.59/0.82        | ((k1_mcart_1 @ sk_E_2)
% 0.59/0.82            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ 
% 0.59/0.82               (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)))))),
% 0.59/0.82      inference('sup-', [status(thm)], ['45', '46'])).
% 0.59/0.82  thf('48', plain,
% 0.59/0.82      (![X33 : $i, X34 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X33 @ X34))),
% 0.59/0.82      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.59/0.82  thf('49', plain,
% 0.59/0.82      (((k1_mcart_1 @ sk_E_2)
% 0.59/0.82         = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ 
% 0.59/0.82            (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2))))),
% 0.59/0.82      inference('demod', [status(thm)], ['47', '48'])).
% 0.59/0.82  thf(d3_mcart_1, axiom,
% 0.59/0.82    (![A:$i,B:$i,C:$i]:
% 0.59/0.82     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.59/0.82  thf('50', plain,
% 0.59/0.82      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.59/0.82         ((k3_mcart_1 @ X35 @ X36 @ X37)
% 0.59/0.82           = (k4_tarski @ (k4_tarski @ X35 @ X36) @ X37))),
% 0.59/0.82      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.59/0.82  thf('51', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ 
% 0.59/0.82           (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ X0)
% 0.59/0.82           = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ X0))),
% 0.59/0.82      inference('sup+', [status(thm)], ['49', '50'])).
% 0.59/0.82  thf('52', plain,
% 0.59/0.82      ((r2_hidden @ (k1_mcart_1 @ sk_E_2) @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.59/0.82      inference('clc', [status(thm)], ['41', '44'])).
% 0.59/0.82  thf('53', plain,
% 0.59/0.82      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.59/0.82         ((r2_hidden @ (k2_mcart_1 @ X49) @ X51)
% 0.59/0.82          | ~ (r2_hidden @ X49 @ (k2_zfmisc_1 @ X50 @ X51)))),
% 0.59/0.82      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.59/0.82  thf('54', plain,
% 0.59/0.82      ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_B_1)),
% 0.59/0.82      inference('sup-', [status(thm)], ['52', '53'])).
% 0.59/0.82  thf('55', plain,
% 0.59/0.82      (![X28 : $i, X29 : $i]:
% 0.59/0.82         (~ (r2_hidden @ X28 @ X29)
% 0.59/0.82          | (m1_subset_1 @ X28 @ X29)
% 0.59/0.82          | (v1_xboole_0 @ X29))),
% 0.59/0.82      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.59/0.82  thf('56', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.59/0.82      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.59/0.82  thf('57', plain,
% 0.59/0.82      (![X28 : $i, X29 : $i]:
% 0.59/0.82         ((m1_subset_1 @ X28 @ X29) | ~ (r2_hidden @ X28 @ X29))),
% 0.59/0.82      inference('clc', [status(thm)], ['55', '56'])).
% 0.59/0.82  thf('58', plain,
% 0.59/0.82      ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_B_1)),
% 0.59/0.82      inference('sup-', [status(thm)], ['54', '57'])).
% 0.59/0.82  thf('59', plain,
% 0.59/0.82      (![X63 : $i, X64 : $i, X65 : $i]:
% 0.59/0.82         (~ (m1_subset_1 @ X63 @ sk_B_1)
% 0.59/0.82          | ((sk_E_2) != (k3_mcart_1 @ X64 @ X63 @ X65))
% 0.59/0.82          | ((sk_D_1) = (X65))
% 0.59/0.82          | ~ (m1_subset_1 @ X65 @ sk_C_1)
% 0.59/0.82          | ~ (m1_subset_1 @ X64 @ sk_A))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('60', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]:
% 0.59/0.82         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.59/0.82          | ~ (m1_subset_1 @ X1 @ sk_C_1)
% 0.59/0.82          | ((sk_D_1) = (X1))
% 0.59/0.82          | ((sk_E_2)
% 0.59/0.82              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ X1)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['58', '59'])).
% 0.59/0.82  thf('61', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((sk_E_2) != (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ X0))
% 0.59/0.82          | ((sk_D_1) = (X0))
% 0.59/0.82          | ~ (m1_subset_1 @ X0 @ sk_C_1)
% 0.59/0.82          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_A))),
% 0.59/0.82      inference('sup-', [status(thm)], ['51', '60'])).
% 0.59/0.82  thf('62', plain,
% 0.59/0.82      ((r2_hidden @ (k1_mcart_1 @ sk_E_2) @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.59/0.82      inference('clc', [status(thm)], ['41', '44'])).
% 0.59/0.82  thf('63', plain,
% 0.59/0.82      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.59/0.82         ((r2_hidden @ (k1_mcart_1 @ X49) @ X50)
% 0.59/0.82          | ~ (r2_hidden @ X49 @ (k2_zfmisc_1 @ X50 @ X51)))),
% 0.59/0.82      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.59/0.82  thf('64', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_A)),
% 0.59/0.82      inference('sup-', [status(thm)], ['62', '63'])).
% 0.59/0.82  thf('65', plain,
% 0.59/0.82      (![X28 : $i, X29 : $i]:
% 0.59/0.82         ((m1_subset_1 @ X28 @ X29) | ~ (r2_hidden @ X28 @ X29))),
% 0.59/0.82      inference('clc', [status(thm)], ['55', '56'])).
% 0.59/0.82  thf('66', plain,
% 0.59/0.82      ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_A)),
% 0.59/0.82      inference('sup-', [status(thm)], ['64', '65'])).
% 0.59/0.82  thf('67', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((sk_E_2) != (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ X0))
% 0.59/0.82          | ((sk_D_1) = (X0))
% 0.59/0.82          | ~ (m1_subset_1 @ X0 @ sk_C_1))),
% 0.59/0.82      inference('demod', [status(thm)], ['61', '66'])).
% 0.59/0.82  thf('68', plain,
% 0.59/0.82      ((((sk_E_2) != (sk_E_2))
% 0.59/0.82        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E_2) @ sk_C_1)
% 0.59/0.82        | ((sk_D_1) = (k2_mcart_1 @ sk_E_2)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['32', '67'])).
% 0.59/0.82  thf('69', plain,
% 0.59/0.82      ((m1_subset_1 @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf(dt_k7_mcart_1, axiom,
% 0.59/0.82    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.82     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.59/0.82       ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ))).
% 0.59/0.82  thf('70', plain,
% 0.59/0.82      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.59/0.82         ((m1_subset_1 @ (k7_mcart_1 @ X45 @ X46 @ X47 @ X48) @ X47)
% 0.59/0.82          | ~ (m1_subset_1 @ X48 @ (k3_zfmisc_1 @ X45 @ X46 @ X47)))),
% 0.59/0.82      inference('cnf', [status(esa)], [dt_k7_mcart_1])).
% 0.59/0.82  thf('71', plain,
% 0.59/0.82      ((m1_subset_1 @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_2) @ sk_C_1)),
% 0.59/0.82      inference('sup-', [status(thm)], ['69', '70'])).
% 0.59/0.82  thf('72', plain,
% 0.59/0.82      ((m1_subset_1 @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf(t50_mcart_1, axiom,
% 0.59/0.82    (![A:$i,B:$i,C:$i]:
% 0.59/0.82     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.59/0.82          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.59/0.82          ( ~( ![D:$i]:
% 0.59/0.82               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.59/0.82                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.59/0.82                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.59/0.82                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.59/0.82                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.59/0.82                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.59/0.82  thf('73', plain,
% 0.59/0.82      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 0.59/0.82         (((X54) = (k1_xboole_0))
% 0.59/0.82          | ((X55) = (k1_xboole_0))
% 0.59/0.82          | ((k7_mcart_1 @ X54 @ X55 @ X57 @ X56) = (k2_mcart_1 @ X56))
% 0.59/0.82          | ~ (m1_subset_1 @ X56 @ (k3_zfmisc_1 @ X54 @ X55 @ X57))
% 0.59/0.82          | ((X57) = (k1_xboole_0)))),
% 0.59/0.82      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.59/0.82  thf('74', plain,
% 0.59/0.82      ((((sk_C_1) = (k1_xboole_0))
% 0.59/0.82        | ((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_2)
% 0.59/0.82            = (k2_mcart_1 @ sk_E_2))
% 0.59/0.82        | ((sk_B_1) = (k1_xboole_0))
% 0.59/0.82        | ((sk_A) = (k1_xboole_0)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['72', '73'])).
% 0.59/0.82  thf('75', plain, (((sk_A) != (k1_xboole_0))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('76', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('77', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('78', plain,
% 0.59/0.82      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_2) = (k2_mcart_1 @ sk_E_2))),
% 0.59/0.82      inference('simplify_reflect-', [status(thm)], ['74', '75', '76', '77'])).
% 0.59/0.82  thf('79', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E_2) @ sk_C_1)),
% 0.59/0.82      inference('demod', [status(thm)], ['71', '78'])).
% 0.59/0.82  thf('80', plain,
% 0.59/0.82      ((((sk_E_2) != (sk_E_2)) | ((sk_D_1) = (k2_mcart_1 @ sk_E_2)))),
% 0.59/0.82      inference('demod', [status(thm)], ['68', '79'])).
% 0.59/0.82  thf('81', plain, (((sk_D_1) = (k2_mcart_1 @ sk_E_2))),
% 0.59/0.82      inference('simplify', [status(thm)], ['80'])).
% 0.59/0.82  thf('82', plain,
% 0.59/0.82      (((sk_D_1) != (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_2))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('83', plain,
% 0.59/0.82      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_2) = (k2_mcart_1 @ sk_E_2))),
% 0.59/0.82      inference('simplify_reflect-', [status(thm)], ['74', '75', '76', '77'])).
% 0.59/0.82  thf('84', plain, (((sk_D_1) != (k2_mcart_1 @ sk_E_2))),
% 0.59/0.82      inference('demod', [status(thm)], ['82', '83'])).
% 0.59/0.82  thf('85', plain, ($false),
% 0.59/0.82      inference('simplify_reflect-', [status(thm)], ['81', '84'])).
% 0.59/0.82  
% 0.59/0.82  % SZS output end Refutation
% 0.59/0.82  
% 0.59/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
