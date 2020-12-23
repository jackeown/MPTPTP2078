%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.weGhU4IKoc

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:57 EST 2020

% Result     : Theorem 2.43s
% Output     : Refutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 600 expanded)
%              Number of leaves         :   39 ( 197 expanded)
%              Depth                    :   30
%              Number of atoms          : 1447 (9934 expanded)
%              Number of equality atoms :  180 (1375 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_3_type,type,(
    sk_E_3: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    m1_subset_1 @ sk_E_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r2_hidden @ X32 @ X33 )
      | ( v1_xboole_0 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ sk_E_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('3',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k3_zfmisc_1 @ X37 @ X38 @ X39 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ D @ E )
           != A ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k4_tarski @ ( sk_D_1 @ X19 ) @ ( sk_E_2 @ X19 ) )
        = X19 )
      | ~ ( r2_hidden @ X19 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_tarski @ ( sk_D_1 @ X3 ) @ ( sk_E_2 @ X3 ) )
        = X3 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( ( k4_tarski @ ( sk_D_1 @ sk_E_3 ) @ ( sk_E_2 @ sk_E_3 ) )
      = sk_E_3 ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('7',plain,(
    ! [X66: $i] :
      ( ( X66 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X66 ) @ X66 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('10',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ( ( k3_zfmisc_1 @ X55 @ X56 @ X57 )
       != k1_xboole_0 )
      | ( X57 = k1_xboole_0 )
      | ( X56 = k1_xboole_0 )
      | ( X55 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
       != X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( ( k4_tarski @ ( sk_D_1 @ sk_E_3 ) @ ( sk_E_2 @ sk_E_3 ) )
      = sk_E_3 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k4_tarski @ ( sk_D_1 @ sk_E_3 ) @ ( sk_E_2 @ sk_E_3 ) )
    = sk_E_3 ),
    inference('simplify_reflect-',[status(thm)],['13','14','15','16'])).

thf('18',plain,
    ( ( k4_tarski @ ( sk_D_1 @ sk_E_3 ) @ ( sk_E_2 @ sk_E_3 ) )
    = sk_E_3 ),
    inference('simplify_reflect-',[status(thm)],['13','14','15','16'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('19',plain,(
    ! [X63: $i,X64: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X63 @ X64 ) )
      = X63 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('20',plain,
    ( ( k1_mcart_1 @ sk_E_3 )
    = ( sk_D_1 @ sk_E_3 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_E_3 ) @ ( sk_E_2 @ sk_E_3 ) )
    = sk_E_3 ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ sk_E_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('23',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k3_zfmisc_1 @ X37 @ X38 @ X39 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('24',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X52 ) @ X53 )
      | ~ ( r2_hidden @ X52 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_3 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k4_tarski @ ( sk_D_1 @ X19 ) @ ( sk_E_2 @ X19 ) )
        = X19 )
      | ~ ( r2_hidden @ X19 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( ( k4_tarski @ ( sk_D_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( sk_E_2 @ ( k1_mcart_1 @ sk_E_3 ) ) )
      = ( k1_mcart_1 @ sk_E_3 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( ( k4_tarski @ ( sk_D_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( sk_E_2 @ ( k1_mcart_1 @ sk_E_3 ) ) )
      = ( k1_mcart_1 @ sk_E_3 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('30',plain,(
    ! [X63: $i,X64: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X63 @ X64 ) )
      = X63 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('31',plain,
    ( ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) )
      = ( sk_D_1 @ ( k1_mcart_1 @ sk_E_3 ) ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k3_zfmisc_1 @ X37 @ X38 @ X39 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('33',plain,(
    ! [X66: $i] :
      ( ( X66 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X66 ) @ X66 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('34',plain,(
    m1_subset_1 @ sk_E_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ) )).

thf('35',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( m1_subset_1 @ ( k7_mcart_1 @ X48 @ X49 @ X50 @ X51 ) @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k3_zfmisc_1 @ X48 @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_mcart_1])).

thf('36',plain,(
    m1_subset_1 @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3 ) @ sk_C ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r2_hidden @ X32 @ X33 )
      | ( v1_xboole_0 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('38',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('46',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k2_zfmisc_1 @ X28 @ X29 )
        = k1_xboole_0 )
      | ( X29 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('47',plain,(
    ! [X28: $i] :
      ( ( k2_zfmisc_1 @ X28 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('48',plain,(
    ! [X30: $i,X31: $i] :
      ~ ( r2_hidden @ X30 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('49',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','49'])).

thf('51',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['44','50'])).

thf('52',plain,(
    r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3 ) @ sk_C ),
    inference(clc,[status(thm)],['38','51'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('53',plain,(
    ! [X22: $i,X23: $i,X24: $i,X26: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X22 @ X24 ) @ ( k2_zfmisc_1 @ X23 @ X26 ) )
      | ~ ( r2_hidden @ X24 @ X26 )
      | ~ ( r2_hidden @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3 ) ) @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_E_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
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

thf('56',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ( X59 = k1_xboole_0 )
      | ( X60 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X59 @ X60 @ X62 @ X61 )
        = ( k2_mcart_1 @ X61 ) )
      | ~ ( m1_subset_1 @ X61 @ ( k3_zfmisc_1 @ X59 @ X60 @ X62 ) )
      | ( X62 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('57',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3 )
      = ( k2_mcart_1 @ sk_E_3 ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3 )
    = ( k2_mcart_1 @ sk_E_3 ) ),
    inference('simplify_reflect-',[status(thm)],['57','58','59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( k2_mcart_1 @ sk_E_3 ) ) @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['54','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X0 ) @ ( k2_mcart_1 @ sk_E_3 ) ) @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['33','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X1 @ X0 @ sk_C ) )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','65'])).

thf('67',plain,
    ( ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) )
      = ( sk_D_1 @ ( k1_mcart_1 @ sk_E_3 ) ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','66'])).

thf('68',plain,(
    ! [X27: $i,X28: $i] :
      ( ( X27 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X28 @ X27 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('69',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) )
      = ( sk_D_1 @ ( k1_mcart_1 @ sk_E_3 ) ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) )
      = ( sk_D_1 @ ( k1_mcart_1 @ sk_E_3 ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) )
    = ( sk_D_1 @ ( k1_mcart_1 @ sk_E_3 ) ) ),
    inference('simplify_reflect-',[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( sk_E_2 @ ( k1_mcart_1 @ sk_E_3 ) ) )
      = ( k1_mcart_1 @ sk_E_3 ) ) ),
    inference(demod,[status(thm)],['28','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('76',plain,
    ( ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( sk_E_2 @ ( k1_mcart_1 @ sk_E_3 ) ) )
      = ( k1_mcart_1 @ sk_E_3 ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ( ( k3_zfmisc_1 @ X55 @ X56 @ X57 )
       != k1_xboole_0 )
      | ( X57 = k1_xboole_0 )
      | ( X56 = k1_xboole_0 )
      | ( X55 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('78',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( sk_E_2 @ ( k1_mcart_1 @ sk_E_3 ) ) )
      = ( k1_mcart_1 @ sk_E_3 ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( sk_E_2 @ ( k1_mcart_1 @ sk_E_3 ) ) )
      = ( k1_mcart_1 @ sk_E_3 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( sk_E_2 @ ( k1_mcart_1 @ sk_E_3 ) ) )
    = ( k1_mcart_1 @ sk_E_3 ) ),
    inference('simplify_reflect-',[status(thm)],['79','80','81','82'])).

thf('84',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( sk_E_2 @ ( k1_mcart_1 @ sk_E_3 ) ) )
    = ( k1_mcart_1 @ sk_E_3 ) ),
    inference('simplify_reflect-',[status(thm)],['79','80','81','82'])).

thf('85',plain,(
    ! [X63: $i,X65: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X63 @ X65 ) )
      = X65 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('86',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) )
    = ( sk_E_2 @ ( k1_mcart_1 @ sk_E_3 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) )
    = ( k1_mcart_1 @ sk_E_3 ) ),
    inference(demod,[status(thm)],['83','86'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('88',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k3_mcart_1 @ X34 @ X35 @ X36 )
      = ( k4_tarski @ ( k4_tarski @ X34 @ X35 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_3 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_E_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ) )).

thf('91',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( m1_subset_1 @ ( k6_mcart_1 @ X44 @ X45 @ X46 @ X47 ) @ X45 )
      | ~ ( m1_subset_1 @ X47 @ ( k3_zfmisc_1 @ X44 @ X45 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_mcart_1])).

thf('92',plain,(
    m1_subset_1 @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3 ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X69: $i,X70: $i,X71: $i] :
      ( ~ ( m1_subset_1 @ X69 @ sk_B_2 )
      | ( sk_E_3
       != ( k3_mcart_1 @ X70 @ X69 @ X71 ) )
      | ( sk_D_2 = X71 )
      | ~ ( m1_subset_1 @ X71 @ sk_C )
      | ~ ( m1_subset_1 @ X70 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_D_2 = X1 )
      | ( sk_E_3
       != ( k3_mcart_1 @ X0 @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_E_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ( X59 = k1_xboole_0 )
      | ( X60 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X59 @ X60 @ X62 @ X61 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X61 ) ) )
      | ~ ( m1_subset_1 @ X61 @ ( k3_zfmisc_1 @ X59 @ X60 @ X62 ) )
      | ( X62 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('97',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3 )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) ),
    inference('simplify_reflect-',[status(thm)],['97','98','99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_D_2 = X1 )
      | ( sk_E_3
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['94','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( sk_E_3
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_3 ) @ X0 ) )
      | ( sk_D_2 = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_E_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ A ) ) )).

thf('105',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( m1_subset_1 @ ( k5_mcart_1 @ X40 @ X41 @ X42 @ X43 ) @ X40 )
      | ~ ( m1_subset_1 @ X43 @ ( k3_zfmisc_1 @ X40 @ X41 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_mcart_1])).

thf('106',plain,(
    m1_subset_1 @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3 ) @ sk_A ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_E_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ( X59 = k1_xboole_0 )
      | ( X60 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X59 @ X60 @ X62 @ X61 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X61 ) ) )
      | ~ ( m1_subset_1 @ X61 @ ( k3_zfmisc_1 @ X59 @ X60 @ X62 ) )
      | ( X62 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('109',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3 )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3 )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) ),
    inference('simplify_reflect-',[status(thm)],['109','110','111','112'])).

thf('114',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ sk_A ),
    inference(demod,[status(thm)],['106','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( sk_E_3
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_3 ) @ X0 ) )
      | ( sk_D_2 = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['103','114'])).

thf('116',plain,
    ( ( sk_E_3 != sk_E_3 )
    | ~ ( m1_subset_1 @ ( sk_E_2 @ sk_E_3 ) @ sk_C )
    | ( sk_D_2
      = ( sk_E_2 @ sk_E_3 ) ) ),
    inference('sup-',[status(thm)],['21','115'])).

thf('117',plain,
    ( ( sk_D_2
      = ( sk_E_2 @ sk_E_3 ) )
    | ~ ( m1_subset_1 @ ( sk_E_2 @ sk_E_3 ) @ sk_C ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_E_3 ) @ ( sk_E_2 @ sk_E_3 ) )
    = sk_E_3 ),
    inference(demod,[status(thm)],['17','20'])).

thf('119',plain,(
    ! [X63: $i,X65: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X63 @ X65 ) )
      = X65 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('120',plain,
    ( ( k2_mcart_1 @ sk_E_3 )
    = ( sk_E_2 @ sk_E_3 ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( k2_mcart_1 @ sk_E_3 )
    = ( sk_E_2 @ sk_E_3 ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('122',plain,(
    m1_subset_1 @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3 ) @ sk_C ),
    inference('sup-',[status(thm)],['34','35'])).

thf('123',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3 )
    = ( k2_mcart_1 @ sk_E_3 ) ),
    inference('simplify_reflect-',[status(thm)],['57','58','59','60'])).

thf('124',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E_3 ) @ sk_C ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( sk_D_2
    = ( k2_mcart_1 @ sk_E_3 ) ),
    inference(demod,[status(thm)],['117','120','121','124'])).

thf('126',plain,(
    sk_D_2
 != ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3 )
    = ( k2_mcart_1 @ sk_E_3 ) ),
    inference('simplify_reflect-',[status(thm)],['57','58','59','60'])).

thf('128',plain,(
    sk_D_2
 != ( k2_mcart_1 @ sk_E_3 ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['125','128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.weGhU4IKoc
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:30:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.43/2.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.43/2.60  % Solved by: fo/fo7.sh
% 2.43/2.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.43/2.60  % done 3857 iterations in 2.140s
% 2.43/2.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.43/2.60  % SZS output start Refutation
% 2.43/2.60  thf(sk_E_3_type, type, sk_E_3: $i).
% 2.43/2.60  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 2.43/2.60  thf(sk_B_type, type, sk_B: $i > $i).
% 2.43/2.60  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 2.43/2.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.43/2.60  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 2.43/2.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.43/2.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.43/2.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.43/2.60  thf(sk_D_1_type, type, sk_D_1: $i > $i).
% 2.43/2.60  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 2.43/2.60  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 2.43/2.60  thf(sk_D_2_type, type, sk_D_2: $i).
% 2.43/2.60  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 2.43/2.60  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 2.43/2.60  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 2.43/2.60  thf(sk_E_2_type, type, sk_E_2: $i > $i).
% 2.43/2.60  thf(sk_C_type, type, sk_C: $i).
% 2.43/2.60  thf(sk_B_2_type, type, sk_B_2: $i).
% 2.43/2.60  thf(sk_A_type, type, sk_A: $i).
% 2.43/2.60  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 2.43/2.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.43/2.60  thf(t71_mcart_1, conjecture,
% 2.43/2.60    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 2.43/2.60     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 2.43/2.60       ( ( ![F:$i]:
% 2.43/2.60           ( ( m1_subset_1 @ F @ A ) =>
% 2.43/2.60             ( ![G:$i]:
% 2.43/2.60               ( ( m1_subset_1 @ G @ B ) =>
% 2.43/2.60                 ( ![H:$i]:
% 2.43/2.60                   ( ( m1_subset_1 @ H @ C ) =>
% 2.43/2.60                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 2.43/2.60                       ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 2.43/2.60         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.43/2.60           ( ( C ) = ( k1_xboole_0 ) ) | 
% 2.43/2.60           ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 2.43/2.60  thf(zf_stmt_0, negated_conjecture,
% 2.43/2.60    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 2.43/2.60        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 2.43/2.60          ( ( ![F:$i]:
% 2.43/2.60              ( ( m1_subset_1 @ F @ A ) =>
% 2.43/2.60                ( ![G:$i]:
% 2.43/2.60                  ( ( m1_subset_1 @ G @ B ) =>
% 2.43/2.60                    ( ![H:$i]:
% 2.43/2.60                      ( ( m1_subset_1 @ H @ C ) =>
% 2.43/2.60                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 2.43/2.60                          ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 2.43/2.60            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.43/2.60              ( ( C ) = ( k1_xboole_0 ) ) | 
% 2.43/2.60              ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 2.43/2.60    inference('cnf.neg', [status(esa)], [t71_mcart_1])).
% 2.43/2.60  thf('0', plain,
% 2.43/2.60      ((m1_subset_1 @ sk_E_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 2.43/2.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.60  thf(t2_subset, axiom,
% 2.43/2.60    (![A:$i,B:$i]:
% 2.43/2.60     ( ( m1_subset_1 @ A @ B ) =>
% 2.43/2.60       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 2.43/2.60  thf('1', plain,
% 2.43/2.60      (![X32 : $i, X33 : $i]:
% 2.43/2.60         ((r2_hidden @ X32 @ X33)
% 2.43/2.60          | (v1_xboole_0 @ X33)
% 2.43/2.60          | ~ (m1_subset_1 @ X32 @ X33))),
% 2.43/2.60      inference('cnf', [status(esa)], [t2_subset])).
% 2.43/2.60  thf('2', plain,
% 2.43/2.60      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 2.43/2.60        | (r2_hidden @ sk_E_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 2.43/2.60      inference('sup-', [status(thm)], ['0', '1'])).
% 2.43/2.60  thf(d3_zfmisc_1, axiom,
% 2.43/2.60    (![A:$i,B:$i,C:$i]:
% 2.43/2.60     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 2.43/2.60       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 2.43/2.60  thf('3', plain,
% 2.43/2.60      (![X37 : $i, X38 : $i, X39 : $i]:
% 2.43/2.60         ((k3_zfmisc_1 @ X37 @ X38 @ X39)
% 2.43/2.60           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38) @ X39))),
% 2.43/2.60      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 2.43/2.60  thf(l139_zfmisc_1, axiom,
% 2.43/2.60    (![A:$i,B:$i,C:$i]:
% 2.43/2.60     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 2.43/2.60          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 2.43/2.60  thf('4', plain,
% 2.43/2.60      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.43/2.60         (((k4_tarski @ (sk_D_1 @ X19) @ (sk_E_2 @ X19)) = (X19))
% 2.43/2.60          | ~ (r2_hidden @ X19 @ (k2_zfmisc_1 @ X20 @ X21)))),
% 2.43/2.60      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 2.43/2.60  thf('5', plain,
% 2.43/2.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.43/2.60         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 2.43/2.60          | ((k4_tarski @ (sk_D_1 @ X3) @ (sk_E_2 @ X3)) = (X3)))),
% 2.43/2.60      inference('sup-', [status(thm)], ['3', '4'])).
% 2.43/2.60  thf('6', plain,
% 2.43/2.60      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 2.43/2.60        | ((k4_tarski @ (sk_D_1 @ sk_E_3) @ (sk_E_2 @ sk_E_3)) = (sk_E_3)))),
% 2.43/2.60      inference('sup-', [status(thm)], ['2', '5'])).
% 2.43/2.60  thf(t9_mcart_1, axiom,
% 2.43/2.60    (![A:$i]:
% 2.43/2.60     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.43/2.60          ( ![B:$i]:
% 2.43/2.60            ( ~( ( r2_hidden @ B @ A ) & 
% 2.43/2.60                 ( ![C:$i,D:$i]:
% 2.43/2.60                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 2.43/2.60                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 2.43/2.60  thf('7', plain,
% 2.43/2.60      (![X66 : $i]:
% 2.43/2.60         (((X66) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X66) @ X66))),
% 2.43/2.60      inference('cnf', [status(esa)], [t9_mcart_1])).
% 2.43/2.60  thf(d1_xboole_0, axiom,
% 2.43/2.60    (![A:$i]:
% 2.43/2.60     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.43/2.60  thf('8', plain,
% 2.43/2.60      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.43/2.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.43/2.60  thf('9', plain,
% 2.43/2.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.43/2.60      inference('sup-', [status(thm)], ['7', '8'])).
% 2.43/2.60  thf(t35_mcart_1, axiom,
% 2.43/2.60    (![A:$i,B:$i,C:$i]:
% 2.43/2.60     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 2.43/2.60         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 2.43/2.60       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 2.43/2.60  thf('10', plain,
% 2.43/2.60      (![X55 : $i, X56 : $i, X57 : $i]:
% 2.43/2.60         (((k3_zfmisc_1 @ X55 @ X56 @ X57) != (k1_xboole_0))
% 2.43/2.60          | ((X57) = (k1_xboole_0))
% 2.43/2.60          | ((X56) = (k1_xboole_0))
% 2.43/2.60          | ((X55) = (k1_xboole_0)))),
% 2.43/2.60      inference('cnf', [status(esa)], [t35_mcart_1])).
% 2.43/2.60  thf('11', plain,
% 2.43/2.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.43/2.60         (((k3_zfmisc_1 @ X3 @ X2 @ X1) != (X0))
% 2.43/2.60          | ~ (v1_xboole_0 @ X0)
% 2.43/2.60          | ((X3) = (k1_xboole_0))
% 2.43/2.60          | ((X2) = (k1_xboole_0))
% 2.43/2.60          | ((X1) = (k1_xboole_0)))),
% 2.43/2.60      inference('sup-', [status(thm)], ['9', '10'])).
% 2.43/2.60  thf('12', plain,
% 2.43/2.60      (![X1 : $i, X2 : $i, X3 : $i]:
% 2.43/2.60         (((X1) = (k1_xboole_0))
% 2.43/2.60          | ((X2) = (k1_xboole_0))
% 2.43/2.60          | ((X3) = (k1_xboole_0))
% 2.43/2.60          | ~ (v1_xboole_0 @ (k3_zfmisc_1 @ X3 @ X2 @ X1)))),
% 2.43/2.60      inference('simplify', [status(thm)], ['11'])).
% 2.43/2.60  thf('13', plain,
% 2.43/2.60      ((((k4_tarski @ (sk_D_1 @ sk_E_3) @ (sk_E_2 @ sk_E_3)) = (sk_E_3))
% 2.43/2.60        | ((sk_A) = (k1_xboole_0))
% 2.43/2.60        | ((sk_B_2) = (k1_xboole_0))
% 2.43/2.60        | ((sk_C) = (k1_xboole_0)))),
% 2.43/2.60      inference('sup-', [status(thm)], ['6', '12'])).
% 2.43/2.60  thf('14', plain, (((sk_C) != (k1_xboole_0))),
% 2.43/2.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.60  thf('15', plain, (((sk_B_2) != (k1_xboole_0))),
% 2.43/2.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.60  thf('16', plain, (((sk_A) != (k1_xboole_0))),
% 2.43/2.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.60  thf('17', plain,
% 2.43/2.60      (((k4_tarski @ (sk_D_1 @ sk_E_3) @ (sk_E_2 @ sk_E_3)) = (sk_E_3))),
% 2.43/2.60      inference('simplify_reflect-', [status(thm)], ['13', '14', '15', '16'])).
% 2.43/2.60  thf('18', plain,
% 2.43/2.60      (((k4_tarski @ (sk_D_1 @ sk_E_3) @ (sk_E_2 @ sk_E_3)) = (sk_E_3))),
% 2.43/2.60      inference('simplify_reflect-', [status(thm)], ['13', '14', '15', '16'])).
% 2.43/2.60  thf(t7_mcart_1, axiom,
% 2.43/2.60    (![A:$i,B:$i]:
% 2.43/2.60     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 2.43/2.60       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 2.43/2.60  thf('19', plain,
% 2.43/2.60      (![X63 : $i, X64 : $i]: ((k1_mcart_1 @ (k4_tarski @ X63 @ X64)) = (X63))),
% 2.43/2.60      inference('cnf', [status(esa)], [t7_mcart_1])).
% 2.43/2.60  thf('20', plain, (((k1_mcart_1 @ sk_E_3) = (sk_D_1 @ sk_E_3))),
% 2.43/2.60      inference('sup+', [status(thm)], ['18', '19'])).
% 2.43/2.60  thf('21', plain,
% 2.43/2.60      (((k4_tarski @ (k1_mcart_1 @ sk_E_3) @ (sk_E_2 @ sk_E_3)) = (sk_E_3))),
% 2.43/2.60      inference('demod', [status(thm)], ['17', '20'])).
% 2.43/2.60  thf('22', plain,
% 2.43/2.60      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 2.43/2.60        | (r2_hidden @ sk_E_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 2.43/2.60      inference('sup-', [status(thm)], ['0', '1'])).
% 2.43/2.60  thf('23', plain,
% 2.43/2.60      (![X37 : $i, X38 : $i, X39 : $i]:
% 2.43/2.60         ((k3_zfmisc_1 @ X37 @ X38 @ X39)
% 2.43/2.60           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38) @ X39))),
% 2.43/2.60      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 2.43/2.60  thf(t10_mcart_1, axiom,
% 2.43/2.60    (![A:$i,B:$i,C:$i]:
% 2.43/2.60     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 2.43/2.60       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 2.43/2.60         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 2.43/2.60  thf('24', plain,
% 2.43/2.60      (![X52 : $i, X53 : $i, X54 : $i]:
% 2.43/2.60         ((r2_hidden @ (k1_mcart_1 @ X52) @ X53)
% 2.43/2.60          | ~ (r2_hidden @ X52 @ (k2_zfmisc_1 @ X53 @ X54)))),
% 2.43/2.60      inference('cnf', [status(esa)], [t10_mcart_1])).
% 2.43/2.60  thf('25', plain,
% 2.43/2.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.43/2.60         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 2.43/2.60          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 2.43/2.60      inference('sup-', [status(thm)], ['23', '24'])).
% 2.43/2.60  thf('26', plain,
% 2.43/2.60      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 2.43/2.60        | (r2_hidden @ (k1_mcart_1 @ sk_E_3) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.43/2.60      inference('sup-', [status(thm)], ['22', '25'])).
% 2.43/2.60  thf('27', plain,
% 2.43/2.60      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.43/2.60         (((k4_tarski @ (sk_D_1 @ X19) @ (sk_E_2 @ X19)) = (X19))
% 2.43/2.60          | ~ (r2_hidden @ X19 @ (k2_zfmisc_1 @ X20 @ X21)))),
% 2.43/2.60      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 2.43/2.60  thf('28', plain,
% 2.43/2.60      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 2.43/2.60        | ((k4_tarski @ (sk_D_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 2.43/2.60            (sk_E_2 @ (k1_mcart_1 @ sk_E_3))) = (k1_mcart_1 @ sk_E_3)))),
% 2.43/2.60      inference('sup-', [status(thm)], ['26', '27'])).
% 2.43/2.60  thf('29', plain,
% 2.43/2.60      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 2.43/2.60        | ((k4_tarski @ (sk_D_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 2.43/2.60            (sk_E_2 @ (k1_mcart_1 @ sk_E_3))) = (k1_mcart_1 @ sk_E_3)))),
% 2.43/2.60      inference('sup-', [status(thm)], ['26', '27'])).
% 2.43/2.60  thf('30', plain,
% 2.43/2.60      (![X63 : $i, X64 : $i]: ((k1_mcart_1 @ (k4_tarski @ X63 @ X64)) = (X63))),
% 2.43/2.60      inference('cnf', [status(esa)], [t7_mcart_1])).
% 2.43/2.60  thf('31', plain,
% 2.43/2.60      ((((k1_mcart_1 @ (k1_mcart_1 @ sk_E_3))
% 2.43/2.60          = (sk_D_1 @ (k1_mcart_1 @ sk_E_3)))
% 2.43/2.60        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 2.43/2.60      inference('sup+', [status(thm)], ['29', '30'])).
% 2.43/2.60  thf('32', plain,
% 2.43/2.60      (![X37 : $i, X38 : $i, X39 : $i]:
% 2.43/2.60         ((k3_zfmisc_1 @ X37 @ X38 @ X39)
% 2.43/2.60           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38) @ X39))),
% 2.43/2.60      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 2.43/2.60  thf('33', plain,
% 2.43/2.60      (![X66 : $i]:
% 2.43/2.60         (((X66) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X66) @ X66))),
% 2.43/2.60      inference('cnf', [status(esa)], [t9_mcart_1])).
% 2.43/2.60  thf('34', plain,
% 2.43/2.60      ((m1_subset_1 @ sk_E_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 2.43/2.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.60  thf(dt_k7_mcart_1, axiom,
% 2.43/2.60    (![A:$i,B:$i,C:$i,D:$i]:
% 2.43/2.60     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 2.43/2.60       ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ))).
% 2.43/2.60  thf('35', plain,
% 2.43/2.60      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 2.43/2.60         ((m1_subset_1 @ (k7_mcart_1 @ X48 @ X49 @ X50 @ X51) @ X50)
% 2.43/2.60          | ~ (m1_subset_1 @ X51 @ (k3_zfmisc_1 @ X48 @ X49 @ X50)))),
% 2.43/2.60      inference('cnf', [status(esa)], [dt_k7_mcart_1])).
% 2.43/2.60  thf('36', plain,
% 2.43/2.60      ((m1_subset_1 @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3) @ sk_C)),
% 2.43/2.61      inference('sup-', [status(thm)], ['34', '35'])).
% 2.43/2.61  thf('37', plain,
% 2.43/2.61      (![X32 : $i, X33 : $i]:
% 2.43/2.61         ((r2_hidden @ X32 @ X33)
% 2.43/2.61          | (v1_xboole_0 @ X33)
% 2.43/2.61          | ~ (m1_subset_1 @ X32 @ X33))),
% 2.43/2.61      inference('cnf', [status(esa)], [t2_subset])).
% 2.43/2.61  thf('38', plain,
% 2.43/2.61      (((v1_xboole_0 @ sk_C)
% 2.43/2.61        | (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3) @ sk_C))),
% 2.43/2.61      inference('sup-', [status(thm)], ['36', '37'])).
% 2.43/2.61  thf('39', plain,
% 2.43/2.61      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.43/2.61      inference('sup-', [status(thm)], ['7', '8'])).
% 2.43/2.61  thf('40', plain,
% 2.43/2.61      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.43/2.61      inference('sup-', [status(thm)], ['7', '8'])).
% 2.43/2.61  thf('41', plain,
% 2.43/2.61      (![X0 : $i, X1 : $i]:
% 2.43/2.61         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 2.43/2.61      inference('sup+', [status(thm)], ['39', '40'])).
% 2.43/2.61  thf('42', plain, (((sk_C) != (k1_xboole_0))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('43', plain,
% 2.43/2.61      (![X0 : $i]:
% 2.43/2.61         (((X0) != (k1_xboole_0))
% 2.43/2.61          | ~ (v1_xboole_0 @ X0)
% 2.43/2.61          | ~ (v1_xboole_0 @ sk_C))),
% 2.43/2.61      inference('sup-', [status(thm)], ['41', '42'])).
% 2.43/2.61  thf('44', plain, ((~ (v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 2.43/2.61      inference('simplify', [status(thm)], ['43'])).
% 2.43/2.61  thf('45', plain,
% 2.43/2.61      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.43/2.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.43/2.61  thf(t113_zfmisc_1, axiom,
% 2.43/2.61    (![A:$i,B:$i]:
% 2.43/2.61     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.43/2.61       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.43/2.61  thf('46', plain,
% 2.43/2.61      (![X28 : $i, X29 : $i]:
% 2.43/2.61         (((k2_zfmisc_1 @ X28 @ X29) = (k1_xboole_0))
% 2.43/2.61          | ((X29) != (k1_xboole_0)))),
% 2.43/2.61      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.43/2.61  thf('47', plain,
% 2.43/2.61      (![X28 : $i]: ((k2_zfmisc_1 @ X28 @ k1_xboole_0) = (k1_xboole_0))),
% 2.43/2.61      inference('simplify', [status(thm)], ['46'])).
% 2.43/2.61  thf(t152_zfmisc_1, axiom,
% 2.43/2.61    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 2.43/2.61  thf('48', plain,
% 2.43/2.61      (![X30 : $i, X31 : $i]: ~ (r2_hidden @ X30 @ (k2_zfmisc_1 @ X30 @ X31))),
% 2.43/2.61      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 2.43/2.61  thf('49', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 2.43/2.61      inference('sup-', [status(thm)], ['47', '48'])).
% 2.43/2.61  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.43/2.61      inference('sup-', [status(thm)], ['45', '49'])).
% 2.43/2.61  thf('51', plain, (~ (v1_xboole_0 @ sk_C)),
% 2.43/2.61      inference('demod', [status(thm)], ['44', '50'])).
% 2.43/2.61  thf('52', plain,
% 2.43/2.61      ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3) @ sk_C)),
% 2.43/2.61      inference('clc', [status(thm)], ['38', '51'])).
% 2.43/2.61  thf(l54_zfmisc_1, axiom,
% 2.43/2.61    (![A:$i,B:$i,C:$i,D:$i]:
% 2.43/2.61     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 2.43/2.61       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 2.43/2.61  thf('53', plain,
% 2.43/2.61      (![X22 : $i, X23 : $i, X24 : $i, X26 : $i]:
% 2.43/2.61         ((r2_hidden @ (k4_tarski @ X22 @ X24) @ (k2_zfmisc_1 @ X23 @ X26))
% 2.43/2.61          | ~ (r2_hidden @ X24 @ X26)
% 2.43/2.61          | ~ (r2_hidden @ X22 @ X23))),
% 2.43/2.61      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 2.43/2.61  thf('54', plain,
% 2.43/2.61      (![X0 : $i, X1 : $i]:
% 2.43/2.61         (~ (r2_hidden @ X1 @ X0)
% 2.43/2.61          | (r2_hidden @ 
% 2.43/2.61             (k4_tarski @ X1 @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3)) @ 
% 2.43/2.61             (k2_zfmisc_1 @ X0 @ sk_C)))),
% 2.43/2.61      inference('sup-', [status(thm)], ['52', '53'])).
% 2.43/2.61  thf('55', plain,
% 2.43/2.61      ((m1_subset_1 @ sk_E_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf(t50_mcart_1, axiom,
% 2.43/2.61    (![A:$i,B:$i,C:$i]:
% 2.43/2.61     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 2.43/2.61          ( ( C ) != ( k1_xboole_0 ) ) & 
% 2.43/2.61          ( ~( ![D:$i]:
% 2.43/2.61               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 2.43/2.61                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 2.43/2.61                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 2.43/2.61                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 2.43/2.61                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 2.43/2.61                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 2.43/2.61  thf('56', plain,
% 2.43/2.61      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 2.43/2.61         (((X59) = (k1_xboole_0))
% 2.43/2.61          | ((X60) = (k1_xboole_0))
% 2.43/2.61          | ((k7_mcart_1 @ X59 @ X60 @ X62 @ X61) = (k2_mcart_1 @ X61))
% 2.43/2.61          | ~ (m1_subset_1 @ X61 @ (k3_zfmisc_1 @ X59 @ X60 @ X62))
% 2.43/2.61          | ((X62) = (k1_xboole_0)))),
% 2.43/2.61      inference('cnf', [status(esa)], [t50_mcart_1])).
% 2.43/2.61  thf('57', plain,
% 2.43/2.61      ((((sk_C) = (k1_xboole_0))
% 2.43/2.61        | ((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3) = (k2_mcart_1 @ sk_E_3))
% 2.43/2.61        | ((sk_B_2) = (k1_xboole_0))
% 2.43/2.61        | ((sk_A) = (k1_xboole_0)))),
% 2.43/2.61      inference('sup-', [status(thm)], ['55', '56'])).
% 2.43/2.61  thf('58', plain, (((sk_A) != (k1_xboole_0))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('59', plain, (((sk_B_2) != (k1_xboole_0))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('60', plain, (((sk_C) != (k1_xboole_0))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('61', plain,
% 2.43/2.61      (((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3) = (k2_mcart_1 @ sk_E_3))),
% 2.43/2.61      inference('simplify_reflect-', [status(thm)], ['57', '58', '59', '60'])).
% 2.43/2.61  thf('62', plain,
% 2.43/2.61      (![X0 : $i, X1 : $i]:
% 2.43/2.61         (~ (r2_hidden @ X1 @ X0)
% 2.43/2.61          | (r2_hidden @ (k4_tarski @ X1 @ (k2_mcart_1 @ sk_E_3)) @ 
% 2.43/2.61             (k2_zfmisc_1 @ X0 @ sk_C)))),
% 2.43/2.61      inference('demod', [status(thm)], ['54', '61'])).
% 2.43/2.61  thf('63', plain,
% 2.43/2.61      (![X0 : $i]:
% 2.43/2.61         (((X0) = (k1_xboole_0))
% 2.43/2.61          | (r2_hidden @ (k4_tarski @ (sk_B_1 @ X0) @ (k2_mcart_1 @ sk_E_3)) @ 
% 2.43/2.61             (k2_zfmisc_1 @ X0 @ sk_C)))),
% 2.43/2.61      inference('sup-', [status(thm)], ['33', '62'])).
% 2.43/2.61  thf('64', plain,
% 2.43/2.61      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.43/2.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.43/2.61  thf('65', plain,
% 2.43/2.61      (![X0 : $i]:
% 2.43/2.61         (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_C)))),
% 2.43/2.61      inference('sup-', [status(thm)], ['63', '64'])).
% 2.43/2.61  thf('66', plain,
% 2.43/2.61      (![X0 : $i, X1 : $i]:
% 2.43/2.61         (~ (v1_xboole_0 @ (k3_zfmisc_1 @ X1 @ X0 @ sk_C))
% 2.43/2.61          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 2.43/2.61      inference('sup-', [status(thm)], ['32', '65'])).
% 2.43/2.61  thf('67', plain,
% 2.43/2.61      ((((k1_mcart_1 @ (k1_mcart_1 @ sk_E_3))
% 2.43/2.61          = (sk_D_1 @ (k1_mcart_1 @ sk_E_3)))
% 2.43/2.61        | ((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 2.43/2.61      inference('sup-', [status(thm)], ['31', '66'])).
% 2.43/2.61  thf('68', plain,
% 2.43/2.61      (![X27 : $i, X28 : $i]:
% 2.43/2.61         (((X27) = (k1_xboole_0))
% 2.43/2.61          | ((X28) = (k1_xboole_0))
% 2.43/2.61          | ((k2_zfmisc_1 @ X28 @ X27) != (k1_xboole_0)))),
% 2.43/2.61      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.43/2.61  thf('69', plain,
% 2.43/2.61      ((((k1_xboole_0) != (k1_xboole_0))
% 2.43/2.61        | ((k1_mcart_1 @ (k1_mcart_1 @ sk_E_3))
% 2.43/2.61            = (sk_D_1 @ (k1_mcart_1 @ sk_E_3)))
% 2.43/2.61        | ((sk_A) = (k1_xboole_0))
% 2.43/2.61        | ((sk_B_2) = (k1_xboole_0)))),
% 2.43/2.61      inference('sup-', [status(thm)], ['67', '68'])).
% 2.43/2.61  thf('70', plain,
% 2.43/2.61      ((((sk_B_2) = (k1_xboole_0))
% 2.43/2.61        | ((sk_A) = (k1_xboole_0))
% 2.43/2.61        | ((k1_mcart_1 @ (k1_mcart_1 @ sk_E_3))
% 2.43/2.61            = (sk_D_1 @ (k1_mcart_1 @ sk_E_3))))),
% 2.43/2.61      inference('simplify', [status(thm)], ['69'])).
% 2.43/2.61  thf('71', plain, (((sk_A) != (k1_xboole_0))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('72', plain, (((sk_B_2) != (k1_xboole_0))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('73', plain,
% 2.43/2.61      (((k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) = (sk_D_1 @ (k1_mcart_1 @ sk_E_3)))),
% 2.43/2.61      inference('simplify_reflect-', [status(thm)], ['70', '71', '72'])).
% 2.43/2.61  thf('74', plain,
% 2.43/2.61      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 2.43/2.61        | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 2.43/2.61            (sk_E_2 @ (k1_mcart_1 @ sk_E_3))) = (k1_mcart_1 @ sk_E_3)))),
% 2.43/2.61      inference('demod', [status(thm)], ['28', '73'])).
% 2.43/2.61  thf('75', plain,
% 2.43/2.61      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.43/2.61      inference('sup-', [status(thm)], ['7', '8'])).
% 2.43/2.61  thf('76', plain,
% 2.43/2.61      ((((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 2.43/2.61          (sk_E_2 @ (k1_mcart_1 @ sk_E_3))) = (k1_mcart_1 @ sk_E_3))
% 2.43/2.61        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 2.43/2.61      inference('sup-', [status(thm)], ['74', '75'])).
% 2.43/2.61  thf('77', plain,
% 2.43/2.61      (![X55 : $i, X56 : $i, X57 : $i]:
% 2.43/2.61         (((k3_zfmisc_1 @ X55 @ X56 @ X57) != (k1_xboole_0))
% 2.43/2.61          | ((X57) = (k1_xboole_0))
% 2.43/2.61          | ((X56) = (k1_xboole_0))
% 2.43/2.61          | ((X55) = (k1_xboole_0)))),
% 2.43/2.61      inference('cnf', [status(esa)], [t35_mcart_1])).
% 2.43/2.61  thf('78', plain,
% 2.43/2.61      ((((k1_xboole_0) != (k1_xboole_0))
% 2.43/2.61        | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 2.43/2.61            (sk_E_2 @ (k1_mcart_1 @ sk_E_3))) = (k1_mcart_1 @ sk_E_3))
% 2.43/2.61        | ((sk_A) = (k1_xboole_0))
% 2.43/2.61        | ((sk_B_2) = (k1_xboole_0))
% 2.43/2.61        | ((sk_C) = (k1_xboole_0)))),
% 2.43/2.61      inference('sup-', [status(thm)], ['76', '77'])).
% 2.43/2.61  thf('79', plain,
% 2.43/2.61      ((((sk_C) = (k1_xboole_0))
% 2.43/2.61        | ((sk_B_2) = (k1_xboole_0))
% 2.43/2.61        | ((sk_A) = (k1_xboole_0))
% 2.43/2.61        | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 2.43/2.61            (sk_E_2 @ (k1_mcart_1 @ sk_E_3))) = (k1_mcart_1 @ sk_E_3)))),
% 2.43/2.61      inference('simplify', [status(thm)], ['78'])).
% 2.43/2.61  thf('80', plain, (((sk_A) != (k1_xboole_0))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('81', plain, (((sk_B_2) != (k1_xboole_0))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('82', plain, (((sk_C) != (k1_xboole_0))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('83', plain,
% 2.43/2.61      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 2.43/2.61         (sk_E_2 @ (k1_mcart_1 @ sk_E_3))) = (k1_mcart_1 @ sk_E_3))),
% 2.43/2.61      inference('simplify_reflect-', [status(thm)], ['79', '80', '81', '82'])).
% 2.43/2.61  thf('84', plain,
% 2.43/2.61      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 2.43/2.61         (sk_E_2 @ (k1_mcart_1 @ sk_E_3))) = (k1_mcart_1 @ sk_E_3))),
% 2.43/2.61      inference('simplify_reflect-', [status(thm)], ['79', '80', '81', '82'])).
% 2.43/2.61  thf('85', plain,
% 2.43/2.61      (![X63 : $i, X65 : $i]: ((k2_mcart_1 @ (k4_tarski @ X63 @ X65)) = (X65))),
% 2.43/2.61      inference('cnf', [status(esa)], [t7_mcart_1])).
% 2.43/2.61  thf('86', plain,
% 2.43/2.61      (((k2_mcart_1 @ (k1_mcart_1 @ sk_E_3)) = (sk_E_2 @ (k1_mcart_1 @ sk_E_3)))),
% 2.43/2.61      inference('sup+', [status(thm)], ['84', '85'])).
% 2.43/2.61  thf('87', plain,
% 2.43/2.61      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 2.43/2.61         (k2_mcart_1 @ (k1_mcart_1 @ sk_E_3))) = (k1_mcart_1 @ sk_E_3))),
% 2.43/2.61      inference('demod', [status(thm)], ['83', '86'])).
% 2.43/2.61  thf(d3_mcart_1, axiom,
% 2.43/2.61    (![A:$i,B:$i,C:$i]:
% 2.43/2.61     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 2.43/2.61  thf('88', plain,
% 2.43/2.61      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.43/2.61         ((k3_mcart_1 @ X34 @ X35 @ X36)
% 2.43/2.61           = (k4_tarski @ (k4_tarski @ X34 @ X35) @ X36))),
% 2.43/2.61      inference('cnf', [status(esa)], [d3_mcart_1])).
% 2.43/2.61  thf('89', plain,
% 2.43/2.61      (![X0 : $i]:
% 2.43/2.61         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 2.43/2.61           (k2_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ X0)
% 2.43/2.61           = (k4_tarski @ (k1_mcart_1 @ sk_E_3) @ X0))),
% 2.43/2.61      inference('sup+', [status(thm)], ['87', '88'])).
% 2.43/2.61  thf('90', plain,
% 2.43/2.61      ((m1_subset_1 @ sk_E_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf(dt_k6_mcart_1, axiom,
% 2.43/2.61    (![A:$i,B:$i,C:$i,D:$i]:
% 2.43/2.61     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 2.43/2.61       ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ))).
% 2.43/2.61  thf('91', plain,
% 2.43/2.61      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 2.43/2.61         ((m1_subset_1 @ (k6_mcart_1 @ X44 @ X45 @ X46 @ X47) @ X45)
% 2.43/2.61          | ~ (m1_subset_1 @ X47 @ (k3_zfmisc_1 @ X44 @ X45 @ X46)))),
% 2.43/2.61      inference('cnf', [status(esa)], [dt_k6_mcart_1])).
% 2.43/2.61  thf('92', plain,
% 2.43/2.61      ((m1_subset_1 @ (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3) @ sk_B_2)),
% 2.43/2.61      inference('sup-', [status(thm)], ['90', '91'])).
% 2.43/2.61  thf('93', plain,
% 2.43/2.61      (![X69 : $i, X70 : $i, X71 : $i]:
% 2.43/2.61         (~ (m1_subset_1 @ X69 @ sk_B_2)
% 2.43/2.61          | ((sk_E_3) != (k3_mcart_1 @ X70 @ X69 @ X71))
% 2.43/2.61          | ((sk_D_2) = (X71))
% 2.43/2.61          | ~ (m1_subset_1 @ X71 @ sk_C)
% 2.43/2.61          | ~ (m1_subset_1 @ X70 @ sk_A))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('94', plain,
% 2.43/2.61      (![X0 : $i, X1 : $i]:
% 2.43/2.61         (~ (m1_subset_1 @ X0 @ sk_A)
% 2.43/2.61          | ~ (m1_subset_1 @ X1 @ sk_C)
% 2.43/2.61          | ((sk_D_2) = (X1))
% 2.43/2.61          | ((sk_E_3)
% 2.43/2.61              != (k3_mcart_1 @ X0 @ 
% 2.43/2.61                  (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3) @ X1)))),
% 2.43/2.61      inference('sup-', [status(thm)], ['92', '93'])).
% 2.43/2.61  thf('95', plain,
% 2.43/2.61      ((m1_subset_1 @ sk_E_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('96', plain,
% 2.43/2.61      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 2.43/2.61         (((X59) = (k1_xboole_0))
% 2.43/2.61          | ((X60) = (k1_xboole_0))
% 2.43/2.61          | ((k6_mcart_1 @ X59 @ X60 @ X62 @ X61)
% 2.43/2.61              = (k2_mcart_1 @ (k1_mcart_1 @ X61)))
% 2.43/2.61          | ~ (m1_subset_1 @ X61 @ (k3_zfmisc_1 @ X59 @ X60 @ X62))
% 2.43/2.61          | ((X62) = (k1_xboole_0)))),
% 2.43/2.61      inference('cnf', [status(esa)], [t50_mcart_1])).
% 2.43/2.61  thf('97', plain,
% 2.43/2.61      ((((sk_C) = (k1_xboole_0))
% 2.43/2.61        | ((k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3)
% 2.43/2.61            = (k2_mcart_1 @ (k1_mcart_1 @ sk_E_3)))
% 2.43/2.61        | ((sk_B_2) = (k1_xboole_0))
% 2.43/2.61        | ((sk_A) = (k1_xboole_0)))),
% 2.43/2.61      inference('sup-', [status(thm)], ['95', '96'])).
% 2.43/2.61  thf('98', plain, (((sk_A) != (k1_xboole_0))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('99', plain, (((sk_B_2) != (k1_xboole_0))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('100', plain, (((sk_C) != (k1_xboole_0))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('101', plain,
% 2.43/2.61      (((k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3)
% 2.43/2.61         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E_3)))),
% 2.43/2.61      inference('simplify_reflect-', [status(thm)], ['97', '98', '99', '100'])).
% 2.43/2.61  thf('102', plain,
% 2.43/2.61      (![X0 : $i, X1 : $i]:
% 2.43/2.61         (~ (m1_subset_1 @ X0 @ sk_A)
% 2.43/2.61          | ~ (m1_subset_1 @ X1 @ sk_C)
% 2.43/2.61          | ((sk_D_2) = (X1))
% 2.43/2.61          | ((sk_E_3)
% 2.43/2.61              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ X1)))),
% 2.43/2.61      inference('demod', [status(thm)], ['94', '101'])).
% 2.43/2.61  thf('103', plain,
% 2.43/2.61      (![X0 : $i]:
% 2.43/2.61         (((sk_E_3) != (k4_tarski @ (k1_mcart_1 @ sk_E_3) @ X0))
% 2.43/2.61          | ((sk_D_2) = (X0))
% 2.43/2.61          | ~ (m1_subset_1 @ X0 @ sk_C)
% 2.43/2.61          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ sk_A))),
% 2.43/2.61      inference('sup-', [status(thm)], ['89', '102'])).
% 2.43/2.61  thf('104', plain,
% 2.43/2.61      ((m1_subset_1 @ sk_E_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf(dt_k5_mcart_1, axiom,
% 2.43/2.61    (![A:$i,B:$i,C:$i,D:$i]:
% 2.43/2.61     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 2.43/2.61       ( m1_subset_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ A ) ))).
% 2.43/2.61  thf('105', plain,
% 2.43/2.61      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 2.43/2.61         ((m1_subset_1 @ (k5_mcart_1 @ X40 @ X41 @ X42 @ X43) @ X40)
% 2.43/2.61          | ~ (m1_subset_1 @ X43 @ (k3_zfmisc_1 @ X40 @ X41 @ X42)))),
% 2.43/2.61      inference('cnf', [status(esa)], [dt_k5_mcart_1])).
% 2.43/2.61  thf('106', plain,
% 2.43/2.61      ((m1_subset_1 @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3) @ sk_A)),
% 2.43/2.61      inference('sup-', [status(thm)], ['104', '105'])).
% 2.43/2.61  thf('107', plain,
% 2.43/2.61      ((m1_subset_1 @ sk_E_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('108', plain,
% 2.43/2.61      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 2.43/2.61         (((X59) = (k1_xboole_0))
% 2.43/2.61          | ((X60) = (k1_xboole_0))
% 2.43/2.61          | ((k5_mcart_1 @ X59 @ X60 @ X62 @ X61)
% 2.43/2.61              = (k1_mcart_1 @ (k1_mcart_1 @ X61)))
% 2.43/2.61          | ~ (m1_subset_1 @ X61 @ (k3_zfmisc_1 @ X59 @ X60 @ X62))
% 2.43/2.61          | ((X62) = (k1_xboole_0)))),
% 2.43/2.61      inference('cnf', [status(esa)], [t50_mcart_1])).
% 2.43/2.61  thf('109', plain,
% 2.43/2.61      ((((sk_C) = (k1_xboole_0))
% 2.43/2.61        | ((k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3)
% 2.43/2.61            = (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)))
% 2.43/2.61        | ((sk_B_2) = (k1_xboole_0))
% 2.43/2.61        | ((sk_A) = (k1_xboole_0)))),
% 2.43/2.61      inference('sup-', [status(thm)], ['107', '108'])).
% 2.43/2.61  thf('110', plain, (((sk_A) != (k1_xboole_0))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('111', plain, (((sk_B_2) != (k1_xboole_0))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('112', plain, (((sk_C) != (k1_xboole_0))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('113', plain,
% 2.43/2.61      (((k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3)
% 2.43/2.61         = (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)))),
% 2.43/2.61      inference('simplify_reflect-', [status(thm)],
% 2.43/2.61                ['109', '110', '111', '112'])).
% 2.43/2.61  thf('114', plain,
% 2.43/2.61      ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ sk_A)),
% 2.43/2.61      inference('demod', [status(thm)], ['106', '113'])).
% 2.43/2.61  thf('115', plain,
% 2.43/2.61      (![X0 : $i]:
% 2.43/2.61         (((sk_E_3) != (k4_tarski @ (k1_mcart_1 @ sk_E_3) @ X0))
% 2.43/2.61          | ((sk_D_2) = (X0))
% 2.43/2.61          | ~ (m1_subset_1 @ X0 @ sk_C))),
% 2.43/2.61      inference('demod', [status(thm)], ['103', '114'])).
% 2.43/2.61  thf('116', plain,
% 2.43/2.61      ((((sk_E_3) != (sk_E_3))
% 2.43/2.61        | ~ (m1_subset_1 @ (sk_E_2 @ sk_E_3) @ sk_C)
% 2.43/2.61        | ((sk_D_2) = (sk_E_2 @ sk_E_3)))),
% 2.43/2.61      inference('sup-', [status(thm)], ['21', '115'])).
% 2.43/2.61  thf('117', plain,
% 2.43/2.61      ((((sk_D_2) = (sk_E_2 @ sk_E_3))
% 2.43/2.61        | ~ (m1_subset_1 @ (sk_E_2 @ sk_E_3) @ sk_C))),
% 2.43/2.61      inference('simplify', [status(thm)], ['116'])).
% 2.43/2.61  thf('118', plain,
% 2.43/2.61      (((k4_tarski @ (k1_mcart_1 @ sk_E_3) @ (sk_E_2 @ sk_E_3)) = (sk_E_3))),
% 2.43/2.61      inference('demod', [status(thm)], ['17', '20'])).
% 2.43/2.61  thf('119', plain,
% 2.43/2.61      (![X63 : $i, X65 : $i]: ((k2_mcart_1 @ (k4_tarski @ X63 @ X65)) = (X65))),
% 2.43/2.61      inference('cnf', [status(esa)], [t7_mcart_1])).
% 2.43/2.61  thf('120', plain, (((k2_mcart_1 @ sk_E_3) = (sk_E_2 @ sk_E_3))),
% 2.43/2.61      inference('sup+', [status(thm)], ['118', '119'])).
% 2.43/2.61  thf('121', plain, (((k2_mcart_1 @ sk_E_3) = (sk_E_2 @ sk_E_3))),
% 2.43/2.61      inference('sup+', [status(thm)], ['118', '119'])).
% 2.43/2.61  thf('122', plain,
% 2.43/2.61      ((m1_subset_1 @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3) @ sk_C)),
% 2.43/2.61      inference('sup-', [status(thm)], ['34', '35'])).
% 2.43/2.61  thf('123', plain,
% 2.43/2.61      (((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3) = (k2_mcart_1 @ sk_E_3))),
% 2.43/2.61      inference('simplify_reflect-', [status(thm)], ['57', '58', '59', '60'])).
% 2.43/2.61  thf('124', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E_3) @ sk_C)),
% 2.43/2.61      inference('demod', [status(thm)], ['122', '123'])).
% 2.43/2.61  thf('125', plain, (((sk_D_2) = (k2_mcart_1 @ sk_E_3))),
% 2.43/2.61      inference('demod', [status(thm)], ['117', '120', '121', '124'])).
% 2.43/2.61  thf('126', plain,
% 2.43/2.61      (((sk_D_2) != (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('127', plain,
% 2.43/2.61      (((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3) = (k2_mcart_1 @ sk_E_3))),
% 2.43/2.61      inference('simplify_reflect-', [status(thm)], ['57', '58', '59', '60'])).
% 2.43/2.61  thf('128', plain, (((sk_D_2) != (k2_mcart_1 @ sk_E_3))),
% 2.43/2.61      inference('demod', [status(thm)], ['126', '127'])).
% 2.43/2.61  thf('129', plain, ($false),
% 2.43/2.61      inference('simplify_reflect-', [status(thm)], ['125', '128'])).
% 2.43/2.61  
% 2.43/2.61  % SZS output end Refutation
% 2.43/2.61  
% 2.43/2.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
