%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8Cqhy7j9NK

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:57 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 555 expanded)
%              Number of leaves         :   37 ( 182 expanded)
%              Depth                    :   23
%              Number of atoms          : 1276 (8774 expanded)
%              Number of equality atoms :  174 (1251 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i > $i )).

thf(sk_E_3_type,type,(
    sk_E_3: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    m1_subset_1 @ sk_E_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r2_hidden @ X29 @ X30 )
      | ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ sk_E_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('3',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k3_zfmisc_1 @ X34 @ X35 @ X36 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ D @ E )
           != A ) ) )).

thf('4',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k4_tarski @ ( sk_D_1 @ X21 ) @ ( sk_E_2 @ X21 ) )
        = X21 )
      | ~ ( r2_hidden @ X21 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_tarski @ ( sk_D_1 @ X3 ) @ ( sk_E_2 @ X3 ) )
        = X3 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( ( k4_tarski @ ( sk_D_1 @ sk_E_3 ) @ ( sk_E_2 @ sk_E_3 ) )
      = sk_E_3 ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('7',plain,(
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

thf('8',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_zfmisc_1 @ X25 @ X26 )
        = k1_xboole_0 )
      | ( X26 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('9',plain,(
    ! [X25: $i] :
      ( ( k2_zfmisc_1 @ X25 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X27: $i,X28: $i] :
      ~ ( r2_hidden @ X27 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k4_tarski @ ( sk_D_1 @ sk_E_3 ) @ ( sk_E_2 @ sk_E_3 ) )
      = sk_E_3 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','14'])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( ( k3_zfmisc_1 @ X52 @ X53 @ X54 )
       != k1_xboole_0 )
      | ( X54 = k1_xboole_0 )
      | ( X53 = k1_xboole_0 )
      | ( X52 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('17',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k4_tarski @ ( sk_D_1 @ sk_E_3 ) @ ( sk_E_2 @ sk_E_3 ) )
      = sk_E_3 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k4_tarski @ ( sk_D_1 @ sk_E_3 ) @ ( sk_E_2 @ sk_E_3 ) )
      = sk_E_3 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k4_tarski @ ( sk_D_1 @ sk_E_3 ) @ ( sk_E_2 @ sk_E_3 ) )
    = sk_E_3 ),
    inference('simplify_reflect-',[status(thm)],['18','19','20','21'])).

thf('23',plain,
    ( ( k4_tarski @ ( sk_D_1 @ sk_E_3 ) @ ( sk_E_2 @ sk_E_3 ) )
    = sk_E_3 ),
    inference('simplify_reflect-',[status(thm)],['18','19','20','21'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('24',plain,(
    ! [X60: $i,X61: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X60 @ X61 ) )
      = X60 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('25',plain,
    ( ( k1_mcart_1 @ sk_E_3 )
    = ( sk_D_1 @ sk_E_3 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_E_3 ) @ ( sk_E_2 @ sk_E_3 ) )
    = sk_E_3 ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ sk_E_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('28',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k3_zfmisc_1 @ X34 @ X35 @ X36 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('29',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X49 ) @ X50 )
      | ~ ( r2_hidden @ X49 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_3 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k4_tarski @ ( sk_D_1 @ X21 ) @ ( sk_E_2 @ X21 ) )
        = X21 )
      | ~ ( r2_hidden @ X21 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( ( k4_tarski @ ( sk_D_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( sk_E_2 @ ( k1_mcart_1 @ sk_E_3 ) ) )
      = ( k1_mcart_1 @ sk_E_3 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('35',plain,
    ( ( ( k4_tarski @ ( sk_D_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( sk_E_2 @ ( k1_mcart_1 @ sk_E_3 ) ) )
      = ( k1_mcart_1 @ sk_E_3 ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k4_tarski @ ( sk_D_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( sk_E_2 @ ( k1_mcart_1 @ sk_E_3 ) ) )
      = ( k1_mcart_1 @ sk_E_3 ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('37',plain,(
    ! [X60: $i,X61: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X60 @ X61 ) )
      = X60 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('38',plain,
    ( ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) )
      = ( sk_D_1 @ ( k1_mcart_1 @ sk_E_3 ) ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( ( k3_zfmisc_1 @ X52 @ X53 @ X54 )
       != k1_xboole_0 )
      | ( X54 = k1_xboole_0 )
      | ( X53 = k1_xboole_0 )
      | ( X52 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('40',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) )
      = ( sk_D_1 @ ( k1_mcart_1 @ sk_E_3 ) ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) )
      = ( sk_D_1 @ ( k1_mcart_1 @ sk_E_3 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) )
    = ( sk_D_1 @ ( k1_mcart_1 @ sk_E_3 ) ) ),
    inference('simplify_reflect-',[status(thm)],['41','42','43','44'])).

thf('46',plain,
    ( ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( sk_E_2 @ ( k1_mcart_1 @ sk_E_3 ) ) )
      = ( k1_mcart_1 @ sk_E_3 ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','45'])).

thf('47',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( ( k3_zfmisc_1 @ X52 @ X53 @ X54 )
       != k1_xboole_0 )
      | ( X54 = k1_xboole_0 )
      | ( X53 = k1_xboole_0 )
      | ( X52 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('48',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( sk_E_2 @ ( k1_mcart_1 @ sk_E_3 ) ) )
      = ( k1_mcart_1 @ sk_E_3 ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( sk_E_2 @ ( k1_mcart_1 @ sk_E_3 ) ) )
      = ( k1_mcart_1 @ sk_E_3 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( sk_E_2 @ ( k1_mcart_1 @ sk_E_3 ) ) )
    = ( k1_mcart_1 @ sk_E_3 ) ),
    inference('simplify_reflect-',[status(thm)],['49','50','51','52'])).

thf('54',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( sk_E_2 @ ( k1_mcart_1 @ sk_E_3 ) ) )
    = ( k1_mcart_1 @ sk_E_3 ) ),
    inference('simplify_reflect-',[status(thm)],['49','50','51','52'])).

thf('55',plain,(
    ! [X60: $i,X62: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X60 @ X62 ) )
      = X62 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('56',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) )
    = ( sk_E_2 @ ( k1_mcart_1 @ sk_E_3 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) )
    = ( k1_mcart_1 @ sk_E_3 ) ),
    inference(demod,[status(thm)],['53','56'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('58',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k3_mcart_1 @ X31 @ X32 @ X33 )
      = ( k4_tarski @ ( k4_tarski @ X31 @ X32 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_3 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_E_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ) )).

thf('61',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( m1_subset_1 @ ( k6_mcart_1 @ X41 @ X42 @ X43 @ X44 ) @ X42 )
      | ~ ( m1_subset_1 @ X44 @ ( k3_zfmisc_1 @ X41 @ X42 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_mcart_1])).

thf('62',plain,(
    m1_subset_1 @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_3 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ~ ( m1_subset_1 @ X63 @ sk_B_1 )
      | ( sk_E_3
       != ( k3_mcart_1 @ X64 @ X63 @ X65 ) )
      | ( sk_D_2 = X65 )
      | ~ ( m1_subset_1 @ X65 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X64 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C_1 )
      | ( sk_D_2 = X1 )
      | ( sk_E_3
       != ( k3_mcart_1 @ X0 @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_3 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_E_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
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

thf('66',plain,(
    ! [X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ( X56 = k1_xboole_0 )
      | ( X57 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X56 @ X57 @ X59 @ X58 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X58 ) ) )
      | ~ ( m1_subset_1 @ X58 @ ( k3_zfmisc_1 @ X56 @ X57 @ X59 ) )
      | ( X59 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('67',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_3 )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_3 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) ),
    inference('simplify_reflect-',[status(thm)],['67','68','69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C_1 )
      | ( sk_D_2 = X1 )
      | ( sk_E_3
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['64','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( sk_E_3
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_3 ) @ X0 ) )
      | ( sk_D_2 = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_E_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ A ) ) )).

thf('75',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( m1_subset_1 @ ( k5_mcart_1 @ X37 @ X38 @ X39 @ X40 ) @ X37 )
      | ~ ( m1_subset_1 @ X40 @ ( k3_zfmisc_1 @ X37 @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_mcart_1])).

thf('76',plain,(
    m1_subset_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_3 ) @ sk_A ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_E_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ( X56 = k1_xboole_0 )
      | ( X57 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X56 @ X57 @ X59 @ X58 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X58 ) ) )
      | ~ ( m1_subset_1 @ X58 @ ( k3_zfmisc_1 @ X56 @ X57 @ X59 ) )
      | ( X59 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('79',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_3 )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_3 )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) ),
    inference('simplify_reflect-',[status(thm)],['79','80','81','82'])).

thf('84',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ sk_A ),
    inference(demod,[status(thm)],['76','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( sk_E_3
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_3 ) @ X0 ) )
      | ( sk_D_2 = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['73','84'])).

thf('86',plain,
    ( ( sk_E_3 != sk_E_3 )
    | ~ ( m1_subset_1 @ ( sk_E_2 @ sk_E_3 ) @ sk_C_1 )
    | ( sk_D_2
      = ( sk_E_2 @ sk_E_3 ) ) ),
    inference('sup-',[status(thm)],['26','85'])).

thf('87',plain,
    ( ( sk_D_2
      = ( sk_E_2 @ sk_E_3 ) )
    | ~ ( m1_subset_1 @ ( sk_E_2 @ sk_E_3 ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_E_3 ) @ ( sk_E_2 @ sk_E_3 ) )
    = sk_E_3 ),
    inference(demod,[status(thm)],['22','25'])).

thf('89',plain,(
    ! [X60: $i,X62: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X60 @ X62 ) )
      = X62 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('90',plain,
    ( ( k2_mcart_1 @ sk_E_3 )
    = ( sk_E_2 @ sk_E_3 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k2_mcart_1 @ sk_E_3 )
    = ( sk_E_2 @ sk_E_3 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('92',plain,(
    m1_subset_1 @ sk_E_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ) )).

thf('93',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( m1_subset_1 @ ( k7_mcart_1 @ X45 @ X46 @ X47 @ X48 ) @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k3_zfmisc_1 @ X45 @ X46 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_mcart_1])).

thf('94',plain,(
    m1_subset_1 @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_3 ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_E_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ( X56 = k1_xboole_0 )
      | ( X57 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X56 @ X57 @ X59 @ X58 )
        = ( k2_mcart_1 @ X58 ) )
      | ~ ( m1_subset_1 @ X58 @ ( k3_zfmisc_1 @ X56 @ X57 @ X59 ) )
      | ( X59 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('97',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_3 )
      = ( k2_mcart_1 @ sk_E_3 ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_3 )
    = ( k2_mcart_1 @ sk_E_3 ) ),
    inference('simplify_reflect-',[status(thm)],['97','98','99','100'])).

thf('102',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E_3 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['94','101'])).

thf('103',plain,
    ( sk_D_2
    = ( k2_mcart_1 @ sk_E_3 ) ),
    inference(demod,[status(thm)],['87','90','91','102'])).

thf('104',plain,(
    sk_D_2
 != ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_3 )
    = ( k2_mcart_1 @ sk_E_3 ) ),
    inference('simplify_reflect-',[status(thm)],['97','98','99','100'])).

thf('106',plain,(
    sk_D_2
 != ( k2_mcart_1 @ sk_E_3 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['103','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8Cqhy7j9NK
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:12:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.58/0.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.79  % Solved by: fo/fo7.sh
% 0.58/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.79  % done 538 iterations in 0.333s
% 0.58/0.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.79  % SZS output start Refutation
% 0.58/0.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.79  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.58/0.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.79  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.58/0.79  thf(sk_D_1_type, type, sk_D_1: $i > $i).
% 0.58/0.79  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.79  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.58/0.79  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.58/0.79  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.58/0.79  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.58/0.79  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.58/0.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.79  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.58/0.79  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.58/0.79  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.58/0.79  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.58/0.79  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.58/0.79  thf(sk_E_2_type, type, sk_E_2: $i > $i).
% 0.58/0.79  thf(sk_E_3_type, type, sk_E_3: $i).
% 0.58/0.79  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.58/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.79  thf(t71_mcart_1, conjecture,
% 0.58/0.79    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.58/0.79     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.58/0.79       ( ( ![F:$i]:
% 0.58/0.79           ( ( m1_subset_1 @ F @ A ) =>
% 0.58/0.79             ( ![G:$i]:
% 0.58/0.79               ( ( m1_subset_1 @ G @ B ) =>
% 0.58/0.79                 ( ![H:$i]:
% 0.58/0.79                   ( ( m1_subset_1 @ H @ C ) =>
% 0.58/0.79                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.58/0.79                       ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.58/0.79         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.58/0.79           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.58/0.79           ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.58/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.79    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.58/0.79        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.58/0.79          ( ( ![F:$i]:
% 0.58/0.79              ( ( m1_subset_1 @ F @ A ) =>
% 0.58/0.79                ( ![G:$i]:
% 0.58/0.79                  ( ( m1_subset_1 @ G @ B ) =>
% 0.58/0.79                    ( ![H:$i]:
% 0.58/0.79                      ( ( m1_subset_1 @ H @ C ) =>
% 0.58/0.79                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.58/0.79                          ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.58/0.79            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.58/0.79              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.58/0.79              ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.58/0.79    inference('cnf.neg', [status(esa)], [t71_mcart_1])).
% 0.58/0.79  thf('0', plain,
% 0.58/0.79      ((m1_subset_1 @ sk_E_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf(t2_subset, axiom,
% 0.58/0.79    (![A:$i,B:$i]:
% 0.58/0.79     ( ( m1_subset_1 @ A @ B ) =>
% 0.58/0.79       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.58/0.79  thf('1', plain,
% 0.58/0.79      (![X29 : $i, X30 : $i]:
% 0.58/0.79         ((r2_hidden @ X29 @ X30)
% 0.58/0.79          | (v1_xboole_0 @ X30)
% 0.58/0.79          | ~ (m1_subset_1 @ X29 @ X30))),
% 0.58/0.79      inference('cnf', [status(esa)], [t2_subset])).
% 0.58/0.79  thf('2', plain,
% 0.58/0.79      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.58/0.79        | (r2_hidden @ sk_E_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['0', '1'])).
% 0.58/0.79  thf(d3_zfmisc_1, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.58/0.79       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.58/0.79  thf('3', plain,
% 0.58/0.79      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.58/0.79         ((k3_zfmisc_1 @ X34 @ X35 @ X36)
% 0.58/0.79           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35) @ X36))),
% 0.58/0.79      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.58/0.79  thf(l139_zfmisc_1, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.58/0.79          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 0.58/0.79  thf('4', plain,
% 0.58/0.79      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.58/0.79         (((k4_tarski @ (sk_D_1 @ X21) @ (sk_E_2 @ X21)) = (X21))
% 0.58/0.79          | ~ (r2_hidden @ X21 @ (k2_zfmisc_1 @ X22 @ X23)))),
% 0.58/0.79      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.58/0.79  thf('5', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.79         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.58/0.79          | ((k4_tarski @ (sk_D_1 @ X3) @ (sk_E_2 @ X3)) = (X3)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['3', '4'])).
% 0.58/0.79  thf('6', plain,
% 0.58/0.79      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.58/0.79        | ((k4_tarski @ (sk_D_1 @ sk_E_3) @ (sk_E_2 @ sk_E_3)) = (sk_E_3)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['2', '5'])).
% 0.58/0.79  thf(t2_tarski, axiom,
% 0.58/0.79    (![A:$i,B:$i]:
% 0.58/0.79     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.58/0.79       ( ( A ) = ( B ) ) ))).
% 0.58/0.79  thf('7', plain,
% 0.58/0.79      (![X3 : $i, X4 : $i]:
% 0.58/0.79         (((X4) = (X3))
% 0.58/0.79          | (r2_hidden @ (sk_C @ X3 @ X4) @ X3)
% 0.58/0.79          | (r2_hidden @ (sk_C @ X3 @ X4) @ X4))),
% 0.58/0.79      inference('cnf', [status(esa)], [t2_tarski])).
% 0.58/0.79  thf(t113_zfmisc_1, axiom,
% 0.58/0.79    (![A:$i,B:$i]:
% 0.58/0.79     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.58/0.79       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.58/0.79  thf('8', plain,
% 0.58/0.79      (![X25 : $i, X26 : $i]:
% 0.58/0.79         (((k2_zfmisc_1 @ X25 @ X26) = (k1_xboole_0))
% 0.58/0.79          | ((X26) != (k1_xboole_0)))),
% 0.58/0.79      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.58/0.79  thf('9', plain,
% 0.58/0.79      (![X25 : $i]: ((k2_zfmisc_1 @ X25 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.79      inference('simplify', [status(thm)], ['8'])).
% 0.58/0.79  thf(t152_zfmisc_1, axiom,
% 0.58/0.79    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.58/0.79  thf('10', plain,
% 0.58/0.79      (![X27 : $i, X28 : $i]: ~ (r2_hidden @ X27 @ (k2_zfmisc_1 @ X27 @ X28))),
% 0.58/0.79      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.58/0.79  thf('11', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.58/0.79      inference('sup-', [status(thm)], ['9', '10'])).
% 0.58/0.79  thf('12', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['7', '11'])).
% 0.58/0.79  thf(d1_xboole_0, axiom,
% 0.58/0.79    (![A:$i]:
% 0.58/0.79     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.58/0.79  thf('13', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.58/0.79      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.58/0.79  thf('14', plain,
% 0.58/0.79      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.58/0.79      inference('sup-', [status(thm)], ['12', '13'])).
% 0.58/0.79  thf('15', plain,
% 0.58/0.79      ((((k4_tarski @ (sk_D_1 @ sk_E_3) @ (sk_E_2 @ sk_E_3)) = (sk_E_3))
% 0.58/0.79        | ((k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['6', '14'])).
% 0.58/0.79  thf(t35_mcart_1, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.58/0.79         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 0.58/0.79       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 0.58/0.79  thf('16', plain,
% 0.58/0.79      (![X52 : $i, X53 : $i, X54 : $i]:
% 0.58/0.79         (((k3_zfmisc_1 @ X52 @ X53 @ X54) != (k1_xboole_0))
% 0.58/0.79          | ((X54) = (k1_xboole_0))
% 0.58/0.79          | ((X53) = (k1_xboole_0))
% 0.58/0.79          | ((X52) = (k1_xboole_0)))),
% 0.58/0.79      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.58/0.79  thf('17', plain,
% 0.58/0.79      ((((k1_xboole_0) != (k1_xboole_0))
% 0.58/0.79        | ((k4_tarski @ (sk_D_1 @ sk_E_3) @ (sk_E_2 @ sk_E_3)) = (sk_E_3))
% 0.58/0.79        | ((sk_A) = (k1_xboole_0))
% 0.58/0.79        | ((sk_B_1) = (k1_xboole_0))
% 0.58/0.79        | ((sk_C_1) = (k1_xboole_0)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['15', '16'])).
% 0.58/0.79  thf('18', plain,
% 0.58/0.79      ((((sk_C_1) = (k1_xboole_0))
% 0.58/0.79        | ((sk_B_1) = (k1_xboole_0))
% 0.58/0.79        | ((sk_A) = (k1_xboole_0))
% 0.58/0.79        | ((k4_tarski @ (sk_D_1 @ sk_E_3) @ (sk_E_2 @ sk_E_3)) = (sk_E_3)))),
% 0.58/0.79      inference('simplify', [status(thm)], ['17'])).
% 0.58/0.79  thf('19', plain, (((sk_A) != (k1_xboole_0))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('20', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('21', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('22', plain,
% 0.58/0.79      (((k4_tarski @ (sk_D_1 @ sk_E_3) @ (sk_E_2 @ sk_E_3)) = (sk_E_3))),
% 0.58/0.79      inference('simplify_reflect-', [status(thm)], ['18', '19', '20', '21'])).
% 0.58/0.79  thf('23', plain,
% 0.58/0.79      (((k4_tarski @ (sk_D_1 @ sk_E_3) @ (sk_E_2 @ sk_E_3)) = (sk_E_3))),
% 0.58/0.79      inference('simplify_reflect-', [status(thm)], ['18', '19', '20', '21'])).
% 0.58/0.79  thf(t7_mcart_1, axiom,
% 0.58/0.79    (![A:$i,B:$i]:
% 0.58/0.79     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.58/0.79       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.58/0.79  thf('24', plain,
% 0.58/0.79      (![X60 : $i, X61 : $i]: ((k1_mcart_1 @ (k4_tarski @ X60 @ X61)) = (X60))),
% 0.58/0.79      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.58/0.79  thf('25', plain, (((k1_mcart_1 @ sk_E_3) = (sk_D_1 @ sk_E_3))),
% 0.58/0.79      inference('sup+', [status(thm)], ['23', '24'])).
% 0.58/0.79  thf('26', plain,
% 0.58/0.79      (((k4_tarski @ (k1_mcart_1 @ sk_E_3) @ (sk_E_2 @ sk_E_3)) = (sk_E_3))),
% 0.58/0.79      inference('demod', [status(thm)], ['22', '25'])).
% 0.58/0.79  thf('27', plain,
% 0.58/0.79      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.58/0.79        | (r2_hidden @ sk_E_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['0', '1'])).
% 0.58/0.79  thf('28', plain,
% 0.58/0.79      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.58/0.79         ((k3_zfmisc_1 @ X34 @ X35 @ X36)
% 0.58/0.79           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35) @ X36))),
% 0.58/0.79      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.58/0.79  thf(t10_mcart_1, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.58/0.79       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.58/0.79         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.58/0.79  thf('29', plain,
% 0.58/0.79      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.58/0.79         ((r2_hidden @ (k1_mcart_1 @ X49) @ X50)
% 0.58/0.79          | ~ (r2_hidden @ X49 @ (k2_zfmisc_1 @ X50 @ X51)))),
% 0.58/0.79      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.58/0.79  thf('30', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.79         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.58/0.79          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['28', '29'])).
% 0.58/0.79  thf('31', plain,
% 0.58/0.79      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.58/0.79        | (r2_hidden @ (k1_mcart_1 @ sk_E_3) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['27', '30'])).
% 0.58/0.79  thf('32', plain,
% 0.58/0.79      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.58/0.79         (((k4_tarski @ (sk_D_1 @ X21) @ (sk_E_2 @ X21)) = (X21))
% 0.58/0.79          | ~ (r2_hidden @ X21 @ (k2_zfmisc_1 @ X22 @ X23)))),
% 0.58/0.79      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.58/0.79  thf('33', plain,
% 0.58/0.79      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.58/0.79        | ((k4_tarski @ (sk_D_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 0.58/0.79            (sk_E_2 @ (k1_mcart_1 @ sk_E_3))) = (k1_mcart_1 @ sk_E_3)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['31', '32'])).
% 0.58/0.79  thf('34', plain,
% 0.58/0.79      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.58/0.79      inference('sup-', [status(thm)], ['12', '13'])).
% 0.58/0.79  thf('35', plain,
% 0.58/0.79      ((((k4_tarski @ (sk_D_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 0.58/0.79          (sk_E_2 @ (k1_mcart_1 @ sk_E_3))) = (k1_mcart_1 @ sk_E_3))
% 0.58/0.79        | ((k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['33', '34'])).
% 0.58/0.79  thf('36', plain,
% 0.58/0.79      ((((k4_tarski @ (sk_D_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 0.58/0.79          (sk_E_2 @ (k1_mcart_1 @ sk_E_3))) = (k1_mcart_1 @ sk_E_3))
% 0.58/0.79        | ((k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['33', '34'])).
% 0.58/0.79  thf('37', plain,
% 0.58/0.79      (![X60 : $i, X61 : $i]: ((k1_mcart_1 @ (k4_tarski @ X60 @ X61)) = (X60))),
% 0.58/0.79      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.58/0.79  thf('38', plain,
% 0.58/0.79      ((((k1_mcart_1 @ (k1_mcart_1 @ sk_E_3))
% 0.58/0.79          = (sk_D_1 @ (k1_mcart_1 @ sk_E_3)))
% 0.58/0.79        | ((k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.58/0.79      inference('sup+', [status(thm)], ['36', '37'])).
% 0.58/0.79  thf('39', plain,
% 0.58/0.79      (![X52 : $i, X53 : $i, X54 : $i]:
% 0.58/0.79         (((k3_zfmisc_1 @ X52 @ X53 @ X54) != (k1_xboole_0))
% 0.58/0.79          | ((X54) = (k1_xboole_0))
% 0.58/0.79          | ((X53) = (k1_xboole_0))
% 0.58/0.79          | ((X52) = (k1_xboole_0)))),
% 0.58/0.79      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.58/0.79  thf('40', plain,
% 0.58/0.79      ((((k1_xboole_0) != (k1_xboole_0))
% 0.58/0.79        | ((k1_mcart_1 @ (k1_mcart_1 @ sk_E_3))
% 0.58/0.79            = (sk_D_1 @ (k1_mcart_1 @ sk_E_3)))
% 0.58/0.79        | ((sk_A) = (k1_xboole_0))
% 0.58/0.79        | ((sk_B_1) = (k1_xboole_0))
% 0.58/0.79        | ((sk_C_1) = (k1_xboole_0)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['38', '39'])).
% 0.58/0.79  thf('41', plain,
% 0.58/0.79      ((((sk_C_1) = (k1_xboole_0))
% 0.58/0.79        | ((sk_B_1) = (k1_xboole_0))
% 0.58/0.79        | ((sk_A) = (k1_xboole_0))
% 0.58/0.79        | ((k1_mcart_1 @ (k1_mcart_1 @ sk_E_3))
% 0.58/0.79            = (sk_D_1 @ (k1_mcart_1 @ sk_E_3))))),
% 0.58/0.79      inference('simplify', [status(thm)], ['40'])).
% 0.58/0.79  thf('42', plain, (((sk_A) != (k1_xboole_0))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('43', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('44', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('45', plain,
% 0.58/0.79      (((k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) = (sk_D_1 @ (k1_mcart_1 @ sk_E_3)))),
% 0.58/0.79      inference('simplify_reflect-', [status(thm)], ['41', '42', '43', '44'])).
% 0.58/0.79  thf('46', plain,
% 0.58/0.79      ((((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 0.58/0.79          (sk_E_2 @ (k1_mcart_1 @ sk_E_3))) = (k1_mcart_1 @ sk_E_3))
% 0.58/0.79        | ((k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.58/0.79      inference('demod', [status(thm)], ['35', '45'])).
% 0.58/0.79  thf('47', plain,
% 0.58/0.79      (![X52 : $i, X53 : $i, X54 : $i]:
% 0.58/0.79         (((k3_zfmisc_1 @ X52 @ X53 @ X54) != (k1_xboole_0))
% 0.58/0.79          | ((X54) = (k1_xboole_0))
% 0.58/0.79          | ((X53) = (k1_xboole_0))
% 0.58/0.79          | ((X52) = (k1_xboole_0)))),
% 0.58/0.79      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.58/0.79  thf('48', plain,
% 0.58/0.79      ((((k1_xboole_0) != (k1_xboole_0))
% 0.58/0.79        | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 0.58/0.79            (sk_E_2 @ (k1_mcart_1 @ sk_E_3))) = (k1_mcart_1 @ sk_E_3))
% 0.58/0.79        | ((sk_A) = (k1_xboole_0))
% 0.58/0.79        | ((sk_B_1) = (k1_xboole_0))
% 0.58/0.79        | ((sk_C_1) = (k1_xboole_0)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['46', '47'])).
% 0.58/0.79  thf('49', plain,
% 0.58/0.79      ((((sk_C_1) = (k1_xboole_0))
% 0.58/0.79        | ((sk_B_1) = (k1_xboole_0))
% 0.58/0.79        | ((sk_A) = (k1_xboole_0))
% 0.58/0.79        | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 0.58/0.79            (sk_E_2 @ (k1_mcart_1 @ sk_E_3))) = (k1_mcart_1 @ sk_E_3)))),
% 0.58/0.79      inference('simplify', [status(thm)], ['48'])).
% 0.58/0.79  thf('50', plain, (((sk_A) != (k1_xboole_0))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('51', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('52', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('53', plain,
% 0.58/0.79      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 0.58/0.79         (sk_E_2 @ (k1_mcart_1 @ sk_E_3))) = (k1_mcart_1 @ sk_E_3))),
% 0.58/0.79      inference('simplify_reflect-', [status(thm)], ['49', '50', '51', '52'])).
% 0.58/0.79  thf('54', plain,
% 0.58/0.79      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 0.58/0.79         (sk_E_2 @ (k1_mcart_1 @ sk_E_3))) = (k1_mcart_1 @ sk_E_3))),
% 0.58/0.79      inference('simplify_reflect-', [status(thm)], ['49', '50', '51', '52'])).
% 0.58/0.79  thf('55', plain,
% 0.58/0.79      (![X60 : $i, X62 : $i]: ((k2_mcart_1 @ (k4_tarski @ X60 @ X62)) = (X62))),
% 0.58/0.79      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.58/0.79  thf('56', plain,
% 0.58/0.79      (((k2_mcart_1 @ (k1_mcart_1 @ sk_E_3)) = (sk_E_2 @ (k1_mcart_1 @ sk_E_3)))),
% 0.58/0.79      inference('sup+', [status(thm)], ['54', '55'])).
% 0.58/0.79  thf('57', plain,
% 0.58/0.79      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 0.58/0.79         (k2_mcart_1 @ (k1_mcart_1 @ sk_E_3))) = (k1_mcart_1 @ sk_E_3))),
% 0.58/0.79      inference('demod', [status(thm)], ['53', '56'])).
% 0.58/0.79  thf(d3_mcart_1, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.58/0.79  thf('58', plain,
% 0.58/0.79      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.58/0.79         ((k3_mcart_1 @ X31 @ X32 @ X33)
% 0.58/0.79           = (k4_tarski @ (k4_tarski @ X31 @ X32) @ X33))),
% 0.58/0.79      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.58/0.79  thf('59', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 0.58/0.79           (k2_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ X0)
% 0.58/0.79           = (k4_tarski @ (k1_mcart_1 @ sk_E_3) @ X0))),
% 0.58/0.79      inference('sup+', [status(thm)], ['57', '58'])).
% 0.58/0.79  thf('60', plain,
% 0.58/0.79      ((m1_subset_1 @ sk_E_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf(dt_k6_mcart_1, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.79     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.58/0.79       ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ))).
% 0.58/0.79  thf('61', plain,
% 0.58/0.79      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.58/0.79         ((m1_subset_1 @ (k6_mcart_1 @ X41 @ X42 @ X43 @ X44) @ X42)
% 0.58/0.79          | ~ (m1_subset_1 @ X44 @ (k3_zfmisc_1 @ X41 @ X42 @ X43)))),
% 0.58/0.79      inference('cnf', [status(esa)], [dt_k6_mcart_1])).
% 0.58/0.79  thf('62', plain,
% 0.58/0.79      ((m1_subset_1 @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_3) @ sk_B_1)),
% 0.58/0.79      inference('sup-', [status(thm)], ['60', '61'])).
% 0.58/0.79  thf('63', plain,
% 0.58/0.79      (![X63 : $i, X64 : $i, X65 : $i]:
% 0.58/0.79         (~ (m1_subset_1 @ X63 @ sk_B_1)
% 0.58/0.79          | ((sk_E_3) != (k3_mcart_1 @ X64 @ X63 @ X65))
% 0.58/0.79          | ((sk_D_2) = (X65))
% 0.58/0.79          | ~ (m1_subset_1 @ X65 @ sk_C_1)
% 0.58/0.79          | ~ (m1_subset_1 @ X64 @ sk_A))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('64', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.58/0.79          | ~ (m1_subset_1 @ X1 @ sk_C_1)
% 0.58/0.79          | ((sk_D_2) = (X1))
% 0.58/0.79          | ((sk_E_3)
% 0.58/0.79              != (k3_mcart_1 @ X0 @ 
% 0.58/0.79                  (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_3) @ X1)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['62', '63'])).
% 0.58/0.79  thf('65', plain,
% 0.58/0.79      ((m1_subset_1 @ sk_E_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf(t50_mcart_1, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.58/0.79          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.58/0.79          ( ~( ![D:$i]:
% 0.58/0.79               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.58/0.79                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.58/0.79                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.58/0.79                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.58/0.79                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.58/0.79                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.58/0.79  thf('66', plain,
% 0.58/0.79      (![X56 : $i, X57 : $i, X58 : $i, X59 : $i]:
% 0.58/0.79         (((X56) = (k1_xboole_0))
% 0.58/0.79          | ((X57) = (k1_xboole_0))
% 0.58/0.79          | ((k6_mcart_1 @ X56 @ X57 @ X59 @ X58)
% 0.58/0.79              = (k2_mcart_1 @ (k1_mcart_1 @ X58)))
% 0.58/0.79          | ~ (m1_subset_1 @ X58 @ (k3_zfmisc_1 @ X56 @ X57 @ X59))
% 0.58/0.79          | ((X59) = (k1_xboole_0)))),
% 0.58/0.79      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.58/0.79  thf('67', plain,
% 0.58/0.79      ((((sk_C_1) = (k1_xboole_0))
% 0.58/0.79        | ((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_3)
% 0.58/0.79            = (k2_mcart_1 @ (k1_mcart_1 @ sk_E_3)))
% 0.58/0.79        | ((sk_B_1) = (k1_xboole_0))
% 0.58/0.79        | ((sk_A) = (k1_xboole_0)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['65', '66'])).
% 0.58/0.79  thf('68', plain, (((sk_A) != (k1_xboole_0))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('69', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('70', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('71', plain,
% 0.58/0.79      (((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_3)
% 0.58/0.79         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E_3)))),
% 0.58/0.79      inference('simplify_reflect-', [status(thm)], ['67', '68', '69', '70'])).
% 0.58/0.79  thf('72', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.58/0.79          | ~ (m1_subset_1 @ X1 @ sk_C_1)
% 0.58/0.79          | ((sk_D_2) = (X1))
% 0.58/0.79          | ((sk_E_3)
% 0.58/0.79              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ X1)))),
% 0.58/0.79      inference('demod', [status(thm)], ['64', '71'])).
% 0.58/0.79  thf('73', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         (((sk_E_3) != (k4_tarski @ (k1_mcart_1 @ sk_E_3) @ X0))
% 0.58/0.79          | ((sk_D_2) = (X0))
% 0.58/0.79          | ~ (m1_subset_1 @ X0 @ sk_C_1)
% 0.58/0.79          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ sk_A))),
% 0.58/0.79      inference('sup-', [status(thm)], ['59', '72'])).
% 0.58/0.79  thf('74', plain,
% 0.58/0.79      ((m1_subset_1 @ sk_E_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf(dt_k5_mcart_1, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.79     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.58/0.79       ( m1_subset_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ A ) ))).
% 0.58/0.79  thf('75', plain,
% 0.58/0.79      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.58/0.79         ((m1_subset_1 @ (k5_mcart_1 @ X37 @ X38 @ X39 @ X40) @ X37)
% 0.58/0.79          | ~ (m1_subset_1 @ X40 @ (k3_zfmisc_1 @ X37 @ X38 @ X39)))),
% 0.58/0.79      inference('cnf', [status(esa)], [dt_k5_mcart_1])).
% 0.58/0.79  thf('76', plain,
% 0.58/0.79      ((m1_subset_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_3) @ sk_A)),
% 0.58/0.79      inference('sup-', [status(thm)], ['74', '75'])).
% 0.58/0.79  thf('77', plain,
% 0.58/0.79      ((m1_subset_1 @ sk_E_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('78', plain,
% 0.58/0.79      (![X56 : $i, X57 : $i, X58 : $i, X59 : $i]:
% 0.58/0.79         (((X56) = (k1_xboole_0))
% 0.58/0.79          | ((X57) = (k1_xboole_0))
% 0.58/0.79          | ((k5_mcart_1 @ X56 @ X57 @ X59 @ X58)
% 0.58/0.79              = (k1_mcart_1 @ (k1_mcart_1 @ X58)))
% 0.58/0.79          | ~ (m1_subset_1 @ X58 @ (k3_zfmisc_1 @ X56 @ X57 @ X59))
% 0.58/0.79          | ((X59) = (k1_xboole_0)))),
% 0.58/0.79      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.58/0.79  thf('79', plain,
% 0.58/0.79      ((((sk_C_1) = (k1_xboole_0))
% 0.58/0.79        | ((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_3)
% 0.58/0.79            = (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)))
% 0.58/0.79        | ((sk_B_1) = (k1_xboole_0))
% 0.58/0.79        | ((sk_A) = (k1_xboole_0)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['77', '78'])).
% 0.58/0.79  thf('80', plain, (((sk_A) != (k1_xboole_0))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('81', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('82', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('83', plain,
% 0.58/0.79      (((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_3)
% 0.58/0.79         = (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)))),
% 0.58/0.79      inference('simplify_reflect-', [status(thm)], ['79', '80', '81', '82'])).
% 0.58/0.79  thf('84', plain,
% 0.58/0.79      ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ sk_A)),
% 0.58/0.79      inference('demod', [status(thm)], ['76', '83'])).
% 0.58/0.79  thf('85', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         (((sk_E_3) != (k4_tarski @ (k1_mcart_1 @ sk_E_3) @ X0))
% 0.58/0.79          | ((sk_D_2) = (X0))
% 0.58/0.79          | ~ (m1_subset_1 @ X0 @ sk_C_1))),
% 0.58/0.79      inference('demod', [status(thm)], ['73', '84'])).
% 0.58/0.79  thf('86', plain,
% 0.58/0.79      ((((sk_E_3) != (sk_E_3))
% 0.58/0.79        | ~ (m1_subset_1 @ (sk_E_2 @ sk_E_3) @ sk_C_1)
% 0.58/0.79        | ((sk_D_2) = (sk_E_2 @ sk_E_3)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['26', '85'])).
% 0.58/0.79  thf('87', plain,
% 0.58/0.79      ((((sk_D_2) = (sk_E_2 @ sk_E_3))
% 0.58/0.79        | ~ (m1_subset_1 @ (sk_E_2 @ sk_E_3) @ sk_C_1))),
% 0.58/0.79      inference('simplify', [status(thm)], ['86'])).
% 0.58/0.79  thf('88', plain,
% 0.58/0.79      (((k4_tarski @ (k1_mcart_1 @ sk_E_3) @ (sk_E_2 @ sk_E_3)) = (sk_E_3))),
% 0.58/0.79      inference('demod', [status(thm)], ['22', '25'])).
% 0.58/0.79  thf('89', plain,
% 0.58/0.79      (![X60 : $i, X62 : $i]: ((k2_mcart_1 @ (k4_tarski @ X60 @ X62)) = (X62))),
% 0.58/0.79      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.58/0.79  thf('90', plain, (((k2_mcart_1 @ sk_E_3) = (sk_E_2 @ sk_E_3))),
% 0.58/0.79      inference('sup+', [status(thm)], ['88', '89'])).
% 0.58/0.79  thf('91', plain, (((k2_mcart_1 @ sk_E_3) = (sk_E_2 @ sk_E_3))),
% 0.58/0.79      inference('sup+', [status(thm)], ['88', '89'])).
% 0.58/0.79  thf('92', plain,
% 0.58/0.79      ((m1_subset_1 @ sk_E_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf(dt_k7_mcart_1, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.79     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.58/0.79       ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ))).
% 0.58/0.79  thf('93', plain,
% 0.58/0.79      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.58/0.79         ((m1_subset_1 @ (k7_mcart_1 @ X45 @ X46 @ X47 @ X48) @ X47)
% 0.58/0.79          | ~ (m1_subset_1 @ X48 @ (k3_zfmisc_1 @ X45 @ X46 @ X47)))),
% 0.58/0.79      inference('cnf', [status(esa)], [dt_k7_mcart_1])).
% 0.58/0.79  thf('94', plain,
% 0.58/0.79      ((m1_subset_1 @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_3) @ sk_C_1)),
% 0.58/0.79      inference('sup-', [status(thm)], ['92', '93'])).
% 0.58/0.79  thf('95', plain,
% 0.58/0.79      ((m1_subset_1 @ sk_E_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('96', plain,
% 0.58/0.79      (![X56 : $i, X57 : $i, X58 : $i, X59 : $i]:
% 0.58/0.79         (((X56) = (k1_xboole_0))
% 0.58/0.79          | ((X57) = (k1_xboole_0))
% 0.58/0.79          | ((k7_mcart_1 @ X56 @ X57 @ X59 @ X58) = (k2_mcart_1 @ X58))
% 0.58/0.79          | ~ (m1_subset_1 @ X58 @ (k3_zfmisc_1 @ X56 @ X57 @ X59))
% 0.58/0.79          | ((X59) = (k1_xboole_0)))),
% 0.58/0.79      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.58/0.79  thf('97', plain,
% 0.58/0.79      ((((sk_C_1) = (k1_xboole_0))
% 0.58/0.79        | ((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_3)
% 0.58/0.79            = (k2_mcart_1 @ sk_E_3))
% 0.58/0.79        | ((sk_B_1) = (k1_xboole_0))
% 0.58/0.79        | ((sk_A) = (k1_xboole_0)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['95', '96'])).
% 0.58/0.79  thf('98', plain, (((sk_A) != (k1_xboole_0))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('99', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('100', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('101', plain,
% 0.58/0.79      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_3) = (k2_mcart_1 @ sk_E_3))),
% 0.58/0.79      inference('simplify_reflect-', [status(thm)], ['97', '98', '99', '100'])).
% 0.58/0.79  thf('102', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E_3) @ sk_C_1)),
% 0.58/0.79      inference('demod', [status(thm)], ['94', '101'])).
% 0.58/0.79  thf('103', plain, (((sk_D_2) = (k2_mcart_1 @ sk_E_3))),
% 0.58/0.79      inference('demod', [status(thm)], ['87', '90', '91', '102'])).
% 0.58/0.79  thf('104', plain,
% 0.58/0.79      (((sk_D_2) != (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_3))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('105', plain,
% 0.58/0.79      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_3) = (k2_mcart_1 @ sk_E_3))),
% 0.58/0.79      inference('simplify_reflect-', [status(thm)], ['97', '98', '99', '100'])).
% 0.58/0.79  thf('106', plain, (((sk_D_2) != (k2_mcart_1 @ sk_E_3))),
% 0.58/0.79      inference('demod', [status(thm)], ['104', '105'])).
% 0.58/0.79  thf('107', plain, ($false),
% 0.58/0.79      inference('simplify_reflect-', [status(thm)], ['103', '106'])).
% 0.58/0.79  
% 0.58/0.79  % SZS output end Refutation
% 0.58/0.79  
% 0.58/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
