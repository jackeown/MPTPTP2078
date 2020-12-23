%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8X2X8CmLFE

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:53 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 386 expanded)
%              Number of leaves         :   42 ( 134 expanded)
%              Depth                    :   28
%              Number of atoms          : 1566 (5492 expanded)
%              Number of equality atoms :  205 ( 712 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t70_mcart_1,conjecture,(
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
                     => ( D = G ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D
            = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )).

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
                       => ( D = G ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D
              = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t70_mcart_1])).

thf('0',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r2_hidden @ X18 @ X19 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X39: $i,X40: $i] :
      ( ( X39
        = ( k4_tarski @ ( k1_mcart_1 @ X39 ) @ ( k2_mcart_1 @ X39 ) ) )
      | ~ ( v1_relat_1 @ X40 )
      | ~ ( r2_hidden @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('6',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k3_zfmisc_1 @ X25 @ X26 @ X27 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( v1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['5','8'])).

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

thf('10',plain,(
    ! [X41: $i] :
      ( ( X41 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X41 ) @ X41 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('14',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k4_zfmisc_1 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X28 @ X29 @ X30 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X41: $i] :
      ( ( X41 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X41 ) @ X41 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('17',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X36 ) @ X37 )
      | ~ ( r2_hidden @ X36 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('19',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X12 @ X14 ) @ X13 )
       != ( k2_tarski @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X1 @ X0 )
       != ( k2_tarski @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ) ),
    inference(demod,[status(thm)],['15','23'])).

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf('25',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( ( k4_zfmisc_1 @ X50 @ X51 @ X52 @ X53 )
       != k1_xboole_0 )
      | ( X53 = k1_xboole_0 )
      | ( X52 = k1_xboole_0 )
      | ( X51 = k1_xboole_0 )
      | ( X50 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['27','28','29','30'])).

thf('32',plain,
    ( ( k1_xboole_0 != sk_E )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(eq_fact,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['27','28','29','30'])).

thf('34',plain,
    ( sk_E
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('36',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k3_zfmisc_1 @ X25 @ X26 @ X27 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('37',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X36 ) @ X37 )
      | ~ ( r2_hidden @ X36 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X39: $i,X40: $i] :
      ( ( X39
        = ( k4_tarski @ ( k1_mcart_1 @ X39 ) @ ( k2_mcart_1 @ X39 ) ) )
      | ~ ( v1_relat_1 @ X40 )
      | ~ ( r2_hidden @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('45',plain,
    ( ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('46',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_mcart_1 @ X22 @ X23 @ X24 )
      = ( k4_tarski @ ( k4_tarski @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('49',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X36 ) @ X38 )
      | ~ ( r2_hidden @ X36 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('52',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k4_zfmisc_1 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X28 @ X29 @ X30 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( ( k4_zfmisc_1 @ X50 @ X51 @ X52 @ X53 )
       != k1_xboole_0 )
      | ( X53 = k1_xboole_0 )
      | ( X52 = k1_xboole_0 )
      | ( X51 = k1_xboole_0 )
      | ( X50 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['59','60','61','62'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('64',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ X16 @ X17 )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('67',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('68',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['65','68'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('70',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ( r2_hidden @ X5 @ X6 )
      | ( X6
       != ( k2_tarski @ X7 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('71',plain,(
    ! [X4: $i,X7: $i] :
      ( r2_hidden @ X4 @ ( k2_tarski @ X7 @ X4 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['69','73'])).

thf('75',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X55 @ sk_B_2 )
      | ( sk_D_1 = X55 )
      | ( sk_E
       != ( k3_mcart_1 @ X56 @ X55 @ X57 ) )
      | ~ ( m1_subset_1 @ X57 @ sk_C )
      | ~ ( m1_subset_1 @ X56 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) )
      | ( sk_D_1
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    sk_D_1
 != ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
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

thf('79',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( X46 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X46 @ X47 @ X49 @ X48 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X48 ) ) )
      | ~ ( m1_subset_1 @ X48 @ ( k3_zfmisc_1 @ X46 @ X47 @ X49 ) )
      | ( X49 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('80',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['80','81','82','83'])).

thf('85',plain,(
    sk_D_1
 != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['77','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['76','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
        = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','86'])).

thf('88',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('89',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X36 ) @ X37 )
      | ~ ( r2_hidden @ X36 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('90',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('92',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k4_zfmisc_1 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X28 @ X29 @ X30 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( ( k4_zfmisc_1 @ X50 @ X51 @ X52 @ X53 )
       != k1_xboole_0 )
      | ( X53 = k1_xboole_0 )
      | ( X52 = k1_xboole_0 )
      | ( X51 = k1_xboole_0 )
      | ( X50 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['99','100','101','102'])).

thf('104',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ X16 @ X17 )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['66','67'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('109',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
        = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['87','109'])).

thf('111',plain,
    ( ( sk_E != sk_E )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ) )).

thf('113',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( m1_subset_1 @ ( k7_mcart_1 @ X32 @ X33 @ X34 @ X35 ) @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k3_zfmisc_1 @ X32 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_mcart_1])).

thf('114',plain,(
    m1_subset_1 @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E ) @ sk_C ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( X46 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X46 @ X47 @ X49 @ X48 )
        = ( k2_mcart_1 @ X48 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k3_zfmisc_1 @ X46 @ X47 @ X49 ) )
      | ( X49 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('117',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E )
      = ( k2_mcart_1 @ sk_E ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['117','118','119','120'])).

thf('122',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['114','121'])).

thf('123',plain,
    ( ( sk_E != sk_E )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['111','122'])).

thf('124',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k4_zfmisc_1 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X28 @ X29 @ X30 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( ( k4_zfmisc_1 @ X50 @ X51 @ X52 @ X53 )
       != k1_xboole_0 )
      | ( X53 = k1_xboole_0 )
      | ( X52 = k1_xboole_0 )
      | ( X51 = k1_xboole_0 )
      | ( X50 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['131','132','133','134'])).

thf('136',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','135'])).

thf('137',plain,(
    $false ),
    inference(simplify,[status(thm)],['136'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8X2X8CmLFE
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:39:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.77/1.00  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.77/1.00  % Solved by: fo/fo7.sh
% 0.77/1.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/1.00  % done 939 iterations in 0.544s
% 0.77/1.00  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.77/1.00  % SZS output start Refutation
% 0.77/1.00  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.77/1.00  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.77/1.00  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.77/1.00  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.77/1.00  thf(sk_E_type, type, sk_E: $i).
% 0.77/1.00  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.77/1.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.77/1.00  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.77/1.00  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.77/1.00  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.77/1.00  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.77/1.00  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.77/1.00  thf(sk_C_type, type, sk_C: $i).
% 0.77/1.00  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.77/1.00  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.77/1.00  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.77/1.00  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.77/1.00  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.77/1.00  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.77/1.00  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.77/1.00  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.77/1.00  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.77/1.00  thf(sk_A_type, type, sk_A: $i).
% 0.77/1.00  thf(sk_B_type, type, sk_B: $i > $i).
% 0.77/1.00  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.77/1.00  thf(t70_mcart_1, conjecture,
% 0.77/1.00    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.77/1.00     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.77/1.00       ( ( ![F:$i]:
% 0.77/1.00           ( ( m1_subset_1 @ F @ A ) =>
% 0.77/1.00             ( ![G:$i]:
% 0.77/1.00               ( ( m1_subset_1 @ G @ B ) =>
% 0.77/1.00                 ( ![H:$i]:
% 0.77/1.00                   ( ( m1_subset_1 @ H @ C ) =>
% 0.77/1.00                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.77/1.00                       ( ( D ) = ( G ) ) ) ) ) ) ) ) ) =>
% 0.77/1.00         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.77/1.00           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.77/1.00           ( ( D ) = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.77/1.00  thf(zf_stmt_0, negated_conjecture,
% 0.77/1.00    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.77/1.00        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.77/1.00          ( ( ![F:$i]:
% 0.77/1.00              ( ( m1_subset_1 @ F @ A ) =>
% 0.77/1.00                ( ![G:$i]:
% 0.77/1.00                  ( ( m1_subset_1 @ G @ B ) =>
% 0.77/1.00                    ( ![H:$i]:
% 0.77/1.00                      ( ( m1_subset_1 @ H @ C ) =>
% 0.77/1.00                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.77/1.00                          ( ( D ) = ( G ) ) ) ) ) ) ) ) ) =>
% 0.77/1.00            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.77/1.00              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.77/1.00              ( ( D ) = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.77/1.00    inference('cnf.neg', [status(esa)], [t70_mcart_1])).
% 0.77/1.00  thf('0', plain, (((sk_C) != (k1_xboole_0))),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf('1', plain,
% 0.77/1.00      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf(t2_subset, axiom,
% 0.77/1.00    (![A:$i,B:$i]:
% 0.77/1.00     ( ( m1_subset_1 @ A @ B ) =>
% 0.77/1.00       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.77/1.00  thf('2', plain,
% 0.77/1.00      (![X18 : $i, X19 : $i]:
% 0.77/1.00         ((r2_hidden @ X18 @ X19)
% 0.77/1.00          | (v1_xboole_0 @ X19)
% 0.77/1.00          | ~ (m1_subset_1 @ X18 @ X19))),
% 0.77/1.00      inference('cnf', [status(esa)], [t2_subset])).
% 0.77/1.00  thf('3', plain,
% 0.77/1.00      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.77/1.00        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.77/1.00      inference('sup-', [status(thm)], ['1', '2'])).
% 0.77/1.00  thf(t23_mcart_1, axiom,
% 0.77/1.00    (![A:$i,B:$i]:
% 0.77/1.00     ( ( v1_relat_1 @ B ) =>
% 0.77/1.00       ( ( r2_hidden @ A @ B ) =>
% 0.77/1.00         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 0.77/1.00  thf('4', plain,
% 0.77/1.00      (![X39 : $i, X40 : $i]:
% 0.77/1.00         (((X39) = (k4_tarski @ (k1_mcart_1 @ X39) @ (k2_mcart_1 @ X39)))
% 0.77/1.00          | ~ (v1_relat_1 @ X40)
% 0.77/1.00          | ~ (r2_hidden @ X39 @ X40))),
% 0.77/1.00      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.77/1.00  thf('5', plain,
% 0.77/1.00      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.77/1.00        | ~ (v1_relat_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.77/1.00        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.77/1.00      inference('sup-', [status(thm)], ['3', '4'])).
% 0.77/1.00  thf(d3_zfmisc_1, axiom,
% 0.77/1.00    (![A:$i,B:$i,C:$i]:
% 0.77/1.00     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.77/1.00       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.77/1.00  thf('6', plain,
% 0.77/1.00      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.77/1.00         ((k3_zfmisc_1 @ X25 @ X26 @ X27)
% 0.77/1.00           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26) @ X27))),
% 0.77/1.00      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.77/1.00  thf(fc6_relat_1, axiom,
% 0.77/1.00    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.77/1.00  thf('7', plain,
% 0.77/1.00      (![X20 : $i, X21 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21))),
% 0.77/1.00      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.77/1.00  thf('8', plain,
% 0.77/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/1.00         (v1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))),
% 0.77/1.00      inference('sup+', [status(thm)], ['6', '7'])).
% 0.77/1.00  thf('9', plain,
% 0.77/1.00      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.77/1.00        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.77/1.00      inference('demod', [status(thm)], ['5', '8'])).
% 0.77/1.00  thf(t34_mcart_1, axiom,
% 0.77/1.00    (![A:$i]:
% 0.77/1.00     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.77/1.00          ( ![B:$i]:
% 0.77/1.00            ( ~( ( r2_hidden @ B @ A ) & 
% 0.77/1.00                 ( ![C:$i,D:$i,E:$i,F:$i]:
% 0.77/1.00                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.77/1.00                        ( ( B ) = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) ) ) ) ) ))).
% 0.77/1.00  thf('10', plain,
% 0.77/1.00      (![X41 : $i]:
% 0.77/1.00         (((X41) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X41) @ X41))),
% 0.77/1.00      inference('cnf', [status(esa)], [t34_mcart_1])).
% 0.77/1.00  thf(d1_xboole_0, axiom,
% 0.77/1.00    (![A:$i]:
% 0.77/1.00     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.77/1.00  thf('11', plain,
% 0.77/1.00      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.77/1.00      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.77/1.00  thf('12', plain,
% 0.77/1.00      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.77/1.00      inference('sup-', [status(thm)], ['10', '11'])).
% 0.77/1.00  thf('13', plain,
% 0.77/1.00      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.77/1.00        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 0.77/1.00      inference('sup-', [status(thm)], ['9', '12'])).
% 0.77/1.00  thf(d4_zfmisc_1, axiom,
% 0.77/1.00    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/1.00     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.77/1.00       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.77/1.00  thf('14', plain,
% 0.77/1.00      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.77/1.00         ((k4_zfmisc_1 @ X28 @ X29 @ X30 @ X31)
% 0.77/1.00           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X28 @ X29 @ X30) @ X31))),
% 0.77/1.00      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.77/1.00  thf('15', plain,
% 0.77/1.00      (![X0 : $i]:
% 0.77/1.00         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 0.77/1.00            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.77/1.00          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.77/1.00      inference('sup+', [status(thm)], ['13', '14'])).
% 0.77/1.00  thf('16', plain,
% 0.77/1.00      (![X41 : $i]:
% 0.77/1.00         (((X41) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X41) @ X41))),
% 0.77/1.00      inference('cnf', [status(esa)], [t34_mcart_1])).
% 0.77/1.00  thf(t10_mcart_1, axiom,
% 0.77/1.00    (![A:$i,B:$i,C:$i]:
% 0.77/1.00     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.77/1.00       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.77/1.00         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.77/1.00  thf('17', plain,
% 0.77/1.00      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.77/1.00         ((r2_hidden @ (k1_mcart_1 @ X36) @ X37)
% 0.77/1.00          | ~ (r2_hidden @ X36 @ (k2_zfmisc_1 @ X37 @ X38)))),
% 0.77/1.00      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.77/1.00  thf('18', plain,
% 0.77/1.00      (![X0 : $i, X1 : $i]:
% 0.77/1.00         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 0.77/1.00          | (r2_hidden @ (k1_mcart_1 @ (sk_B_1 @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 0.77/1.00      inference('sup-', [status(thm)], ['16', '17'])).
% 0.77/1.00  thf(t3_boole, axiom,
% 0.77/1.00    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.77/1.00  thf('19', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.77/1.00      inference('cnf', [status(esa)], [t3_boole])).
% 0.77/1.00  thf(t72_zfmisc_1, axiom,
% 0.77/1.00    (![A:$i,B:$i,C:$i]:
% 0.77/1.00     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.77/1.00       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 0.77/1.00  thf('20', plain,
% 0.77/1.00      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.77/1.00         (~ (r2_hidden @ X12 @ X13)
% 0.77/1.00          | ((k4_xboole_0 @ (k2_tarski @ X12 @ X14) @ X13)
% 0.77/1.00              != (k2_tarski @ X12 @ X14)))),
% 0.77/1.00      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.77/1.00  thf('21', plain,
% 0.77/1.00      (![X0 : $i, X1 : $i]:
% 0.77/1.00         (((k2_tarski @ X1 @ X0) != (k2_tarski @ X1 @ X0))
% 0.77/1.00          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.77/1.00      inference('sup-', [status(thm)], ['19', '20'])).
% 0.77/1.00  thf('22', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.77/1.00      inference('simplify', [status(thm)], ['21'])).
% 0.77/1.00  thf('23', plain,
% 0.77/1.00      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.77/1.00      inference('sup-', [status(thm)], ['18', '22'])).
% 0.77/1.00  thf('24', plain,
% 0.77/1.00      (![X0 : $i]:
% 0.77/1.00         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))
% 0.77/1.00          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.77/1.00      inference('demod', [status(thm)], ['15', '23'])).
% 0.77/1.00  thf(t55_mcart_1, axiom,
% 0.77/1.00    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/1.00     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.77/1.00         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 0.77/1.00       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 0.77/1.00  thf('25', plain,
% 0.77/1.00      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.77/1.00         (((k4_zfmisc_1 @ X50 @ X51 @ X52 @ X53) != (k1_xboole_0))
% 0.77/1.00          | ((X53) = (k1_xboole_0))
% 0.77/1.00          | ((X52) = (k1_xboole_0))
% 0.77/1.00          | ((X51) = (k1_xboole_0))
% 0.77/1.00          | ((X50) = (k1_xboole_0)))),
% 0.77/1.00      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.77/1.00  thf('26', plain,
% 0.77/1.00      (![X0 : $i]:
% 0.77/1.00         (((k1_xboole_0) != (k1_xboole_0))
% 0.77/1.00          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.77/1.00          | ((sk_A) = (k1_xboole_0))
% 0.77/1.00          | ((sk_B_2) = (k1_xboole_0))
% 0.77/1.00          | ((sk_C) = (k1_xboole_0))
% 0.77/1.00          | ((X0) = (k1_xboole_0)))),
% 0.77/1.00      inference('sup-', [status(thm)], ['24', '25'])).
% 0.77/1.00  thf('27', plain,
% 0.77/1.00      (![X0 : $i]:
% 0.77/1.00         (((X0) = (k1_xboole_0))
% 0.77/1.00          | ((sk_C) = (k1_xboole_0))
% 0.77/1.00          | ((sk_B_2) = (k1_xboole_0))
% 0.77/1.00          | ((sk_A) = (k1_xboole_0))
% 0.77/1.00          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.77/1.00      inference('simplify', [status(thm)], ['26'])).
% 0.77/1.00  thf('28', plain, (((sk_A) != (k1_xboole_0))),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf('29', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf('30', plain, (((sk_C) != (k1_xboole_0))),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf('31', plain,
% 0.77/1.00      (![X0 : $i]:
% 0.77/1.00         (((X0) = (k1_xboole_0))
% 0.77/1.00          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.77/1.00      inference('simplify_reflect-', [status(thm)], ['27', '28', '29', '30'])).
% 0.77/1.00  thf('32', plain,
% 0.77/1.00      ((((k1_xboole_0) != (sk_E))
% 0.77/1.00        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.77/1.00      inference('eq_fact', [status(thm)], ['31'])).
% 0.77/1.00  thf('33', plain,
% 0.77/1.00      (![X0 : $i]:
% 0.77/1.00         (((X0) = (k1_xboole_0))
% 0.77/1.00          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.77/1.00      inference('simplify_reflect-', [status(thm)], ['27', '28', '29', '30'])).
% 0.77/1.00  thf('34', plain,
% 0.77/1.00      (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))),
% 0.77/1.00      inference('clc', [status(thm)], ['32', '33'])).
% 0.77/1.00  thf('35', plain,
% 0.77/1.00      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.77/1.00        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.77/1.00      inference('sup-', [status(thm)], ['1', '2'])).
% 0.77/1.00  thf('36', plain,
% 0.77/1.00      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.77/1.00         ((k3_zfmisc_1 @ X25 @ X26 @ X27)
% 0.77/1.00           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26) @ X27))),
% 0.77/1.00      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.77/1.00  thf('37', plain,
% 0.77/1.00      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.77/1.00         ((r2_hidden @ (k1_mcart_1 @ X36) @ X37)
% 0.77/1.00          | ~ (r2_hidden @ X36 @ (k2_zfmisc_1 @ X37 @ X38)))),
% 0.77/1.00      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.77/1.00  thf('38', plain,
% 0.77/1.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.77/1.00         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.77/1.00          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.77/1.00      inference('sup-', [status(thm)], ['36', '37'])).
% 0.77/1.00  thf('39', plain,
% 0.77/1.00      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.77/1.00        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.77/1.00      inference('sup-', [status(thm)], ['35', '38'])).
% 0.77/1.00  thf('40', plain,
% 0.77/1.00      (![X39 : $i, X40 : $i]:
% 0.77/1.00         (((X39) = (k4_tarski @ (k1_mcart_1 @ X39) @ (k2_mcart_1 @ X39)))
% 0.77/1.00          | ~ (v1_relat_1 @ X40)
% 0.77/1.00          | ~ (r2_hidden @ X39 @ X40))),
% 0.77/1.00      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.77/1.00  thf('41', plain,
% 0.77/1.00      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.77/1.00        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 0.77/1.00        | ((k1_mcart_1 @ sk_E)
% 0.77/1.00            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.77/1.00               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.77/1.00      inference('sup-', [status(thm)], ['39', '40'])).
% 0.77/1.00  thf('42', plain,
% 0.77/1.00      (![X20 : $i, X21 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21))),
% 0.77/1.00      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.77/1.00  thf('43', plain,
% 0.77/1.00      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.77/1.00        | ((k1_mcart_1 @ sk_E)
% 0.77/1.00            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.77/1.00               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.77/1.00      inference('demod', [status(thm)], ['41', '42'])).
% 0.77/1.00  thf('44', plain,
% 0.77/1.00      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.77/1.00      inference('sup-', [status(thm)], ['10', '11'])).
% 0.77/1.00  thf('45', plain,
% 0.77/1.00      ((((k1_mcart_1 @ sk_E)
% 0.77/1.00          = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.77/1.00             (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.77/1.00        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 0.77/1.00      inference('sup-', [status(thm)], ['43', '44'])).
% 0.77/1.00  thf(d3_mcart_1, axiom,
% 0.77/1.00    (![A:$i,B:$i,C:$i]:
% 0.77/1.00     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.77/1.00  thf('46', plain,
% 0.77/1.00      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.77/1.00         ((k3_mcart_1 @ X22 @ X23 @ X24)
% 0.77/1.00           = (k4_tarski @ (k4_tarski @ X22 @ X23) @ X24))),
% 0.77/1.00      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.77/1.00  thf('47', plain,
% 0.77/1.00      (![X0 : $i]:
% 0.77/1.00         (((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.77/1.00            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 0.77/1.00            = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.77/1.00          | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 0.77/1.00      inference('sup+', [status(thm)], ['45', '46'])).
% 0.77/1.00  thf('48', plain,
% 0.77/1.00      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.77/1.00        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.77/1.00      inference('sup-', [status(thm)], ['35', '38'])).
% 0.77/1.00  thf('49', plain,
% 0.77/1.00      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.77/1.00         ((r2_hidden @ (k2_mcart_1 @ X36) @ X38)
% 0.77/1.00          | ~ (r2_hidden @ X36 @ (k2_zfmisc_1 @ X37 @ X38)))),
% 0.77/1.00      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.77/1.00  thf('50', plain,
% 0.77/1.00      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.77/1.00        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 0.77/1.00      inference('sup-', [status(thm)], ['48', '49'])).
% 0.77/1.00  thf('51', plain,
% 0.77/1.00      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.77/1.00      inference('sup-', [status(thm)], ['10', '11'])).
% 0.77/1.00  thf('52', plain,
% 0.77/1.00      (((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2)
% 0.77/1.00        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 0.77/1.00      inference('sup-', [status(thm)], ['50', '51'])).
% 0.77/1.00  thf('53', plain,
% 0.77/1.00      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.77/1.00         ((k4_zfmisc_1 @ X28 @ X29 @ X30 @ X31)
% 0.77/1.00           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X28 @ X29 @ X30) @ X31))),
% 0.77/1.00      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.77/1.00  thf('54', plain,
% 0.77/1.00      (![X0 : $i]:
% 0.77/1.00         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 0.77/1.00            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.77/1.00          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 0.77/1.00      inference('sup+', [status(thm)], ['52', '53'])).
% 0.77/1.00  thf('55', plain,
% 0.77/1.00      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.77/1.00      inference('sup-', [status(thm)], ['18', '22'])).
% 0.77/1.00  thf('56', plain,
% 0.77/1.00      (![X0 : $i]:
% 0.77/1.00         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))
% 0.77/1.00          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 0.77/1.00      inference('demod', [status(thm)], ['54', '55'])).
% 0.77/1.00  thf('57', plain,
% 0.77/1.00      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.77/1.00         (((k4_zfmisc_1 @ X50 @ X51 @ X52 @ X53) != (k1_xboole_0))
% 0.77/1.00          | ((X53) = (k1_xboole_0))
% 0.77/1.00          | ((X52) = (k1_xboole_0))
% 0.77/1.00          | ((X51) = (k1_xboole_0))
% 0.77/1.00          | ((X50) = (k1_xboole_0)))),
% 0.77/1.00      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.77/1.00  thf('58', plain,
% 0.77/1.00      (![X0 : $i]:
% 0.77/1.00         (((k1_xboole_0) != (k1_xboole_0))
% 0.77/1.00          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2)
% 0.77/1.00          | ((sk_A) = (k1_xboole_0))
% 0.77/1.00          | ((sk_B_2) = (k1_xboole_0))
% 0.77/1.00          | ((sk_C) = (k1_xboole_0))
% 0.77/1.00          | ((X0) = (k1_xboole_0)))),
% 0.77/1.00      inference('sup-', [status(thm)], ['56', '57'])).
% 0.77/1.00  thf('59', plain,
% 0.77/1.00      (![X0 : $i]:
% 0.77/1.00         (((X0) = (k1_xboole_0))
% 0.77/1.00          | ((sk_C) = (k1_xboole_0))
% 0.77/1.00          | ((sk_B_2) = (k1_xboole_0))
% 0.77/1.00          | ((sk_A) = (k1_xboole_0))
% 0.77/1.00          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 0.77/1.00      inference('simplify', [status(thm)], ['58'])).
% 0.77/1.00  thf('60', plain, (((sk_A) != (k1_xboole_0))),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf('61', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf('62', plain, (((sk_C) != (k1_xboole_0))),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf('63', plain,
% 0.77/1.00      (![X0 : $i]:
% 0.77/1.00         (((X0) = (k1_xboole_0))
% 0.77/1.00          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 0.77/1.00      inference('simplify_reflect-', [status(thm)], ['59', '60', '61', '62'])).
% 0.77/1.00  thf(t1_subset, axiom,
% 0.77/1.00    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.77/1.00  thf('64', plain,
% 0.77/1.00      (![X16 : $i, X17 : $i]:
% 0.77/1.00         ((m1_subset_1 @ X16 @ X17) | ~ (r2_hidden @ X16 @ X17))),
% 0.77/1.00      inference('cnf', [status(esa)], [t1_subset])).
% 0.77/1.00  thf('65', plain,
% 0.77/1.00      (![X0 : $i]:
% 0.77/1.00         (((X0) = (k1_xboole_0))
% 0.77/1.00          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 0.77/1.00      inference('sup-', [status(thm)], ['63', '64'])).
% 0.77/1.00  thf('66', plain,
% 0.77/1.00      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.77/1.00      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.77/1.00  thf('67', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.77/1.00      inference('simplify', [status(thm)], ['21'])).
% 0.77/1.00  thf('68', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.77/1.00      inference('sup-', [status(thm)], ['66', '67'])).
% 0.77/1.00  thf('69', plain,
% 0.77/1.00      (![X0 : $i]:
% 0.77/1.00         ((v1_xboole_0 @ X0)
% 0.77/1.00          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 0.77/1.00      inference('sup+', [status(thm)], ['65', '68'])).
% 0.77/1.00  thf(d2_tarski, axiom,
% 0.77/1.00    (![A:$i,B:$i,C:$i]:
% 0.77/1.00     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.77/1.00       ( ![D:$i]:
% 0.77/1.00         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.77/1.00  thf('70', plain,
% 0.77/1.00      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.77/1.00         (((X5) != (X4))
% 0.77/1.00          | (r2_hidden @ X5 @ X6)
% 0.77/1.00          | ((X6) != (k2_tarski @ X7 @ X4)))),
% 0.77/1.00      inference('cnf', [status(esa)], [d2_tarski])).
% 0.77/1.00  thf('71', plain,
% 0.77/1.00      (![X4 : $i, X7 : $i]: (r2_hidden @ X4 @ (k2_tarski @ X7 @ X4))),
% 0.77/1.00      inference('simplify', [status(thm)], ['70'])).
% 0.77/1.00  thf('72', plain,
% 0.77/1.00      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.77/1.00      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.77/1.00  thf('73', plain,
% 0.77/1.00      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 0.77/1.00      inference('sup-', [status(thm)], ['71', '72'])).
% 0.77/1.00  thf('74', plain,
% 0.77/1.00      ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2)),
% 0.77/1.00      inference('sup-', [status(thm)], ['69', '73'])).
% 0.77/1.00  thf('75', plain,
% 0.77/1.00      (![X55 : $i, X56 : $i, X57 : $i]:
% 0.77/1.00         (~ (m1_subset_1 @ X55 @ sk_B_2)
% 0.77/1.00          | ((sk_D_1) = (X55))
% 0.77/1.00          | ((sk_E) != (k3_mcart_1 @ X56 @ X55 @ X57))
% 0.77/1.00          | ~ (m1_subset_1 @ X57 @ sk_C)
% 0.77/1.00          | ~ (m1_subset_1 @ X56 @ sk_A))),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf('76', plain,
% 0.77/1.00      (![X0 : $i, X1 : $i]:
% 0.77/1.00         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.77/1.00          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.77/1.00          | ((sk_E)
% 0.77/1.00              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1))
% 0.77/1.00          | ((sk_D_1) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.77/1.00      inference('sup-', [status(thm)], ['74', '75'])).
% 0.77/1.00  thf('77', plain, (((sk_D_1) != (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E))),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf('78', plain,
% 0.77/1.00      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf(t50_mcart_1, axiom,
% 0.77/1.00    (![A:$i,B:$i,C:$i]:
% 0.77/1.00     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.77/1.00          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.77/1.00          ( ~( ![D:$i]:
% 0.77/1.00               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.77/1.00                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.77/1.00                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.77/1.00                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.77/1.00                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.77/1.00                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.77/1.00  thf('79', plain,
% 0.77/1.00      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.77/1.00         (((X46) = (k1_xboole_0))
% 0.77/1.00          | ((X47) = (k1_xboole_0))
% 0.77/1.00          | ((k6_mcart_1 @ X46 @ X47 @ X49 @ X48)
% 0.77/1.00              = (k2_mcart_1 @ (k1_mcart_1 @ X48)))
% 0.77/1.00          | ~ (m1_subset_1 @ X48 @ (k3_zfmisc_1 @ X46 @ X47 @ X49))
% 0.77/1.00          | ((X49) = (k1_xboole_0)))),
% 0.77/1.00      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.77/1.00  thf('80', plain,
% 0.77/1.00      ((((sk_C) = (k1_xboole_0))
% 0.77/1.00        | ((k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E)
% 0.77/1.00            = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.77/1.00        | ((sk_B_2) = (k1_xboole_0))
% 0.77/1.00        | ((sk_A) = (k1_xboole_0)))),
% 0.77/1.00      inference('sup-', [status(thm)], ['78', '79'])).
% 0.77/1.00  thf('81', plain, (((sk_A) != (k1_xboole_0))),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf('82', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf('83', plain, (((sk_C) != (k1_xboole_0))),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf('84', plain,
% 0.77/1.00      (((k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E)
% 0.77/1.00         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.77/1.00      inference('simplify_reflect-', [status(thm)], ['80', '81', '82', '83'])).
% 0.77/1.00  thf('85', plain, (((sk_D_1) != (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.77/1.00      inference('demod', [status(thm)], ['77', '84'])).
% 0.77/1.00  thf('86', plain,
% 0.77/1.00      (![X0 : $i, X1 : $i]:
% 0.77/1.00         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.77/1.00          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.77/1.00          | ((sk_E)
% 0.77/1.00              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1)))),
% 0.77/1.00      inference('simplify_reflect-', [status(thm)], ['76', '85'])).
% 0.77/1.00  thf('87', plain,
% 0.77/1.00      (![X0 : $i]:
% 0.77/1.00         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.77/1.00          | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0))
% 0.77/1.00          | ~ (m1_subset_1 @ X0 @ sk_C)
% 0.77/1.00          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.77/1.00      inference('sup-', [status(thm)], ['47', '86'])).
% 0.77/1.00  thf('88', plain,
% 0.77/1.00      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.77/1.00        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.77/1.00      inference('sup-', [status(thm)], ['35', '38'])).
% 0.77/1.00  thf('89', plain,
% 0.77/1.00      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.77/1.00         ((r2_hidden @ (k1_mcart_1 @ X36) @ X37)
% 0.77/1.00          | ~ (r2_hidden @ X36 @ (k2_zfmisc_1 @ X37 @ X38)))),
% 0.77/1.00      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.77/1.00  thf('90', plain,
% 0.77/1.00      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.77/1.00        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.77/1.00      inference('sup-', [status(thm)], ['88', '89'])).
% 0.77/1.00  thf('91', plain,
% 0.77/1.00      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.77/1.00      inference('sup-', [status(thm)], ['10', '11'])).
% 0.77/1.00  thf('92', plain,
% 0.77/1.00      (((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 0.77/1.00        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 0.77/1.00      inference('sup-', [status(thm)], ['90', '91'])).
% 0.77/1.00  thf('93', plain,
% 0.77/1.00      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.77/1.00         ((k4_zfmisc_1 @ X28 @ X29 @ X30 @ X31)
% 0.77/1.00           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X28 @ X29 @ X30) @ X31))),
% 0.77/1.00      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.77/1.00  thf('94', plain,
% 0.77/1.00      (![X0 : $i]:
% 0.77/1.00         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 0.77/1.00            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.77/1.00          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.77/1.00      inference('sup+', [status(thm)], ['92', '93'])).
% 0.77/1.00  thf('95', plain,
% 0.77/1.00      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.77/1.00      inference('sup-', [status(thm)], ['18', '22'])).
% 0.77/1.00  thf('96', plain,
% 0.77/1.00      (![X0 : $i]:
% 0.77/1.00         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))
% 0.77/1.00          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.77/1.00      inference('demod', [status(thm)], ['94', '95'])).
% 0.77/1.00  thf('97', plain,
% 0.77/1.00      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.77/1.00         (((k4_zfmisc_1 @ X50 @ X51 @ X52 @ X53) != (k1_xboole_0))
% 0.77/1.00          | ((X53) = (k1_xboole_0))
% 0.77/1.00          | ((X52) = (k1_xboole_0))
% 0.77/1.00          | ((X51) = (k1_xboole_0))
% 0.77/1.00          | ((X50) = (k1_xboole_0)))),
% 0.77/1.00      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.77/1.00  thf('98', plain,
% 0.77/1.00      (![X0 : $i]:
% 0.77/1.00         (((k1_xboole_0) != (k1_xboole_0))
% 0.77/1.00          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 0.77/1.00          | ((sk_A) = (k1_xboole_0))
% 0.77/1.00          | ((sk_B_2) = (k1_xboole_0))
% 0.77/1.00          | ((sk_C) = (k1_xboole_0))
% 0.77/1.00          | ((X0) = (k1_xboole_0)))),
% 0.77/1.00      inference('sup-', [status(thm)], ['96', '97'])).
% 0.77/1.00  thf('99', plain,
% 0.77/1.00      (![X0 : $i]:
% 0.77/1.00         (((X0) = (k1_xboole_0))
% 0.77/1.00          | ((sk_C) = (k1_xboole_0))
% 0.77/1.00          | ((sk_B_2) = (k1_xboole_0))
% 0.77/1.00          | ((sk_A) = (k1_xboole_0))
% 0.77/1.00          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.77/1.00      inference('simplify', [status(thm)], ['98'])).
% 0.77/1.00  thf('100', plain, (((sk_A) != (k1_xboole_0))),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf('101', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf('102', plain, (((sk_C) != (k1_xboole_0))),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf('103', plain,
% 0.77/1.00      (![X0 : $i]:
% 0.77/1.00         (((X0) = (k1_xboole_0))
% 0.77/1.00          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.77/1.00      inference('simplify_reflect-', [status(thm)], ['99', '100', '101', '102'])).
% 0.77/1.00  thf('104', plain,
% 0.77/1.00      (![X16 : $i, X17 : $i]:
% 0.77/1.00         ((m1_subset_1 @ X16 @ X17) | ~ (r2_hidden @ X16 @ X17))),
% 0.77/1.00      inference('cnf', [status(esa)], [t1_subset])).
% 0.77/1.00  thf('105', plain,
% 0.77/1.00      (![X0 : $i]:
% 0.77/1.00         (((X0) = (k1_xboole_0))
% 0.77/1.00          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.77/1.00      inference('sup-', [status(thm)], ['103', '104'])).
% 0.77/1.00  thf('106', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.77/1.00      inference('sup-', [status(thm)], ['66', '67'])).
% 0.77/1.00  thf('107', plain,
% 0.77/1.00      (![X0 : $i]:
% 0.77/1.00         ((v1_xboole_0 @ X0)
% 0.77/1.00          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.77/1.00      inference('sup+', [status(thm)], ['105', '106'])).
% 0.77/1.00  thf('108', plain,
% 0.77/1.00      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 0.77/1.00      inference('sup-', [status(thm)], ['71', '72'])).
% 0.77/1.00  thf('109', plain,
% 0.77/1.00      ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)),
% 0.77/1.00      inference('sup-', [status(thm)], ['107', '108'])).
% 0.77/1.00  thf('110', plain,
% 0.77/1.00      (![X0 : $i]:
% 0.77/1.00         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.77/1.00          | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0))
% 0.77/1.00          | ~ (m1_subset_1 @ X0 @ sk_C))),
% 0.77/1.00      inference('demod', [status(thm)], ['87', '109'])).
% 0.77/1.00  thf('111', plain,
% 0.77/1.00      ((((sk_E) != (sk_E))
% 0.77/1.00        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)
% 0.77/1.00        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 0.77/1.00      inference('sup-', [status(thm)], ['34', '110'])).
% 0.77/1.00  thf('112', plain,
% 0.77/1.00      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf(dt_k7_mcart_1, axiom,
% 0.77/1.00    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/1.00     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.77/1.00       ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ))).
% 0.77/1.00  thf('113', plain,
% 0.77/1.00      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.77/1.00         ((m1_subset_1 @ (k7_mcart_1 @ X32 @ X33 @ X34 @ X35) @ X34)
% 0.77/1.00          | ~ (m1_subset_1 @ X35 @ (k3_zfmisc_1 @ X32 @ X33 @ X34)))),
% 0.77/1.00      inference('cnf', [status(esa)], [dt_k7_mcart_1])).
% 0.77/1.00  thf('114', plain,
% 0.77/1.00      ((m1_subset_1 @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E) @ sk_C)),
% 0.77/1.00      inference('sup-', [status(thm)], ['112', '113'])).
% 0.77/1.00  thf('115', plain,
% 0.77/1.00      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf('116', plain,
% 0.77/1.00      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.77/1.00         (((X46) = (k1_xboole_0))
% 0.77/1.00          | ((X47) = (k1_xboole_0))
% 0.77/1.00          | ((k7_mcart_1 @ X46 @ X47 @ X49 @ X48) = (k2_mcart_1 @ X48))
% 0.77/1.00          | ~ (m1_subset_1 @ X48 @ (k3_zfmisc_1 @ X46 @ X47 @ X49))
% 0.77/1.00          | ((X49) = (k1_xboole_0)))),
% 0.77/1.00      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.77/1.00  thf('117', plain,
% 0.77/1.00      ((((sk_C) = (k1_xboole_0))
% 0.77/1.00        | ((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))
% 0.77/1.00        | ((sk_B_2) = (k1_xboole_0))
% 0.77/1.00        | ((sk_A) = (k1_xboole_0)))),
% 0.77/1.00      inference('sup-', [status(thm)], ['115', '116'])).
% 0.77/1.00  thf('118', plain, (((sk_A) != (k1_xboole_0))),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf('119', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf('120', plain, (((sk_C) != (k1_xboole_0))),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf('121', plain,
% 0.77/1.00      (((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 0.77/1.00      inference('simplify_reflect-', [status(thm)],
% 0.77/1.00                ['117', '118', '119', '120'])).
% 0.77/1.00  thf('122', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)),
% 0.77/1.00      inference('demod', [status(thm)], ['114', '121'])).
% 0.77/1.00  thf('123', plain,
% 0.77/1.00      ((((sk_E) != (sk_E))
% 0.77/1.00        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 0.77/1.00      inference('demod', [status(thm)], ['111', '122'])).
% 0.77/1.00  thf('124', plain, (((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0))),
% 0.77/1.00      inference('simplify', [status(thm)], ['123'])).
% 0.77/1.00  thf('125', plain,
% 0.77/1.00      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.77/1.00         ((k4_zfmisc_1 @ X28 @ X29 @ X30 @ X31)
% 0.77/1.00           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X28 @ X29 @ X30) @ X31))),
% 0.77/1.00      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.77/1.00  thf('126', plain,
% 0.77/1.00      (![X0 : $i]:
% 0.77/1.00         ((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 0.77/1.00           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.77/1.00      inference('sup+', [status(thm)], ['124', '125'])).
% 0.77/1.00  thf('127', plain,
% 0.77/1.00      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.77/1.00      inference('sup-', [status(thm)], ['18', '22'])).
% 0.77/1.00  thf('128', plain,
% 0.77/1.00      (![X0 : $i]: ((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))),
% 0.77/1.00      inference('demod', [status(thm)], ['126', '127'])).
% 0.77/1.00  thf('129', plain,
% 0.77/1.00      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.77/1.00         (((k4_zfmisc_1 @ X50 @ X51 @ X52 @ X53) != (k1_xboole_0))
% 0.77/1.00          | ((X53) = (k1_xboole_0))
% 0.77/1.00          | ((X52) = (k1_xboole_0))
% 0.77/1.00          | ((X51) = (k1_xboole_0))
% 0.77/1.00          | ((X50) = (k1_xboole_0)))),
% 0.77/1.00      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.77/1.00  thf('130', plain,
% 0.77/1.00      (![X0 : $i]:
% 0.77/1.00         (((k1_xboole_0) != (k1_xboole_0))
% 0.77/1.00          | ((sk_A) = (k1_xboole_0))
% 0.77/1.00          | ((sk_B_2) = (k1_xboole_0))
% 0.77/1.00          | ((sk_C) = (k1_xboole_0))
% 0.77/1.00          | ((X0) = (k1_xboole_0)))),
% 0.77/1.00      inference('sup-', [status(thm)], ['128', '129'])).
% 0.77/1.00  thf('131', plain,
% 0.77/1.00      (![X0 : $i]:
% 0.77/1.00         (((X0) = (k1_xboole_0))
% 0.77/1.00          | ((sk_C) = (k1_xboole_0))
% 0.77/1.00          | ((sk_B_2) = (k1_xboole_0))
% 0.77/1.00          | ((sk_A) = (k1_xboole_0)))),
% 0.77/1.00      inference('simplify', [status(thm)], ['130'])).
% 0.77/1.00  thf('132', plain, (((sk_A) != (k1_xboole_0))),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf('133', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf('134', plain, (((sk_C) != (k1_xboole_0))),
% 0.77/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.00  thf('135', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 0.77/1.00      inference('simplify_reflect-', [status(thm)],
% 0.77/1.00                ['131', '132', '133', '134'])).
% 0.77/1.00  thf('136', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.77/1.00      inference('demod', [status(thm)], ['0', '135'])).
% 0.77/1.00  thf('137', plain, ($false), inference('simplify', [status(thm)], ['136'])).
% 0.77/1.00  
% 0.77/1.00  % SZS output end Refutation
% 0.77/1.00  
% 0.77/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
