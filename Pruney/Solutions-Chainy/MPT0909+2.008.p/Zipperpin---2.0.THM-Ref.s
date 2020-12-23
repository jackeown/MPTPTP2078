%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KOujgaCoof

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:50 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 367 expanded)
%              Number of leaves         :   37 ( 125 expanded)
%              Depth                    :   22
%              Number of atoms          : 1424 (6008 expanded)
%              Number of equality atoms :  179 ( 835 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    m1_subset_1 @ sk_E_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r2_hidden @ X21 @ X22 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ sk_E_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X50: $i,X51: $i] :
      ( ( X50
        = ( k4_tarski @ ( k1_mcart_1 @ X50 ) @ ( k2_mcart_1 @ X50 ) ) )
      | ~ ( v1_relat_1 @ X51 )
      | ~ ( r2_hidden @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( sk_E_2
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k3_zfmisc_1 @ X28 @ X29 @ X30 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( v1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( sk_E_2
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) ) ),
    inference(demod,[status(thm)],['4','7'])).

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

thf('9',plain,(
    ! [X52: $i] :
      ( ( X52 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X52 ) @ X52 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_E_2
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('13',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X31 @ X32 @ X33 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_E_2
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X61: $i,X62: $i,X63: $i,X65: $i] :
      ( ( X63 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X61 @ X62 @ X63 @ X65 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('16',plain,(
    ! [X61: $i,X62: $i,X65: $i] :
      ( ( k4_zfmisc_1 @ X61 @ X62 @ k1_xboole_0 @ X65 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k3_zfmisc_1 @ X28 @ X29 @ X30 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('18',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k3_zfmisc_1 @ X28 @ X29 @ X30 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X31 @ X32 @ X33 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X31 @ X32 @ X33 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 @ X4 )
      = ( k2_zfmisc_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) @ X4 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','23'])).

thf('25',plain,(
    ! [X61: $i,X62: $i,X63: $i,X65: $i] :
      ( ( X65 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X61 @ X62 @ X63 @ X65 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('26',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ( k4_zfmisc_1 @ X61 @ X62 @ X63 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( sk_E_2
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) ) ) ),
    inference(demod,[status(thm)],['14','27'])).

thf('29',plain,(
    ! [X61: $i,X62: $i,X63: $i,X64: $i] :
      ( ( ( k4_zfmisc_1 @ X61 @ X62 @ X63 @ X64 )
       != k1_xboole_0 )
      | ( X64 = k1_xboole_0 )
      | ( X63 = k1_xboole_0 )
      | ( X62 = k1_xboole_0 )
      | ( X61 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_E_2
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_E_2
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_E_2
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['31','32','33','34'])).

thf('36',plain,
    ( ( k1_xboole_0 != sk_E_2 )
    | ( sk_E_2
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) ) ),
    inference(eq_fact,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_E_2
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['31','32','33','34'])).

thf('38',plain,
    ( sk_E_2
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_mcart_1 @ sk_E_2 ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ sk_E_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('40',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k3_zfmisc_1 @ X28 @ X29 @ X30 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('41',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X47 ) @ X48 )
      | ~ ( r2_hidden @ X47 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_2 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X50: $i,X51: $i] :
      ( ( X50
        = ( k4_tarski @ ( k1_mcart_1 @ X50 ) @ ( k2_mcart_1 @ X50 ) ) )
      | ~ ( v1_relat_1 @ X51 )
      | ~ ( r2_hidden @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( ( k1_mcart_1 @ sk_E_2 )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X23: $i,X24: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( ( k1_mcart_1 @ sk_E_2 )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('49',plain,
    ( ( ( k1_mcart_1 @ sk_E_2 )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X31 @ X32 @ X33 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( ( k1_mcart_1 @ sk_E_2 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','26'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( ( k1_mcart_1 @ sk_E_2 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X61: $i,X62: $i,X63: $i,X64: $i] :
      ( ( ( k4_zfmisc_1 @ X61 @ X62 @ X63 @ X64 )
       != k1_xboole_0 )
      | ( X64 = k1_xboole_0 )
      | ( X63 = k1_xboole_0 )
      | ( X62 = k1_xboole_0 )
      | ( X61 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_mcart_1 @ sk_E_2 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k1_mcart_1 @ sk_E_2 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_mcart_1 @ sk_E_2 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['56','57','58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_mcart_1 @ sk_E_2 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['56','57','58','59'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k1_mcart_1 @ sk_E_2 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ) )
      | ( ( k1_mcart_1 @ sk_E_2 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_mcart_1 @ sk_E_2 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ) )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( k1_mcart_1 @ sk_E_2 )
    = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ) ),
    inference(condensation,[status(thm)],['63'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('65',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k3_mcart_1 @ X25 @ X26 @ X27 )
      = ( k4_tarski @ ( k4_tarski @ X25 @ X26 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_E_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ) )).

thf('68',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( m1_subset_1 @ ( k6_mcart_1 @ X39 @ X40 @ X41 @ X42 ) @ X40 )
      | ~ ( m1_subset_1 @ X42 @ ( k3_zfmisc_1 @ X39 @ X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_mcart_1])).

thf('69',plain,(
    m1_subset_1 @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ~ ( m1_subset_1 @ X66 @ sk_B_2 )
      | ( sk_D_1 = X67 )
      | ( sk_E_2
       != ( k3_mcart_1 @ X67 @ X66 @ X68 ) )
      | ~ ( m1_subset_1 @ X68 @ sk_C )
      | ~ ( m1_subset_1 @ X67 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E_2
       != ( k3_mcart_1 @ X0 @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 ) @ X1 ) )
      | ( sk_D_1 = X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_E_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
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
    ! [X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ( X57 = k1_xboole_0 )
      | ( X58 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X57 @ X58 @ X60 @ X59 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X59 ) ) )
      | ~ ( m1_subset_1 @ X59 @ ( k3_zfmisc_1 @ X57 @ X58 @ X60 ) )
      | ( X60 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('74',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['74','75','76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E_2
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ X1 ) )
      | ( sk_D_1 = X0 ) ) ),
    inference(demod,[status(thm)],['71','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( sk_E_2
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ X0 ) )
      | ( sk_D_1
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_E_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ A ) ) )).

thf('82',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( m1_subset_1 @ ( k5_mcart_1 @ X35 @ X36 @ X37 @ X38 ) @ X35 )
      | ~ ( m1_subset_1 @ X38 @ ( k3_zfmisc_1 @ X35 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_mcart_1])).

thf('83',plain,(
    m1_subset_1 @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_E_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ( X57 = k1_xboole_0 )
      | ( X58 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X57 @ X58 @ X60 @ X59 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X59 ) ) )
      | ~ ( m1_subset_1 @ X59 @ ( k3_zfmisc_1 @ X57 @ X58 @ X60 ) )
      | ( X60 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('86',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['86','87','88','89'])).

thf('91',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) @ sk_A ),
    inference(demod,[status(thm)],['83','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( sk_E_2
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ X0 ) )
      | ( sk_D_1
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['80','91'])).

thf('93',plain,(
    sk_D_1
 != ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['86','87','88','89'])).

thf('95',plain,(
    sk_D_1
 != ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_2 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( sk_E_2
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_2 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['92','95'])).

thf('97',plain,
    ( ( sk_E_2 != sk_E_2 )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E_2 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['38','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_E_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ) )).

thf('99',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( m1_subset_1 @ ( k7_mcart_1 @ X43 @ X44 @ X45 @ X46 ) @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k3_zfmisc_1 @ X43 @ X44 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_mcart_1])).

thf('100',plain,(
    m1_subset_1 @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 ) @ sk_C ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_E_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ( X57 = k1_xboole_0 )
      | ( X58 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X57 @ X58 @ X60 @ X59 )
        = ( k2_mcart_1 @ X59 ) )
      | ~ ( m1_subset_1 @ X59 @ ( k3_zfmisc_1 @ X57 @ X58 @ X60 ) )
      | ( X60 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('103',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 )
      = ( k2_mcart_1 @ sk_E_2 ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2 )
    = ( k2_mcart_1 @ sk_E_2 ) ),
    inference('simplify_reflect-',[status(thm)],['103','104','105','106'])).

thf('108',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E_2 ) @ sk_C ),
    inference(demod,[status(thm)],['100','107'])).

thf('109',plain,(
    sk_E_2 != sk_E_2 ),
    inference(demod,[status(thm)],['97','108'])).

thf('110',plain,(
    $false ),
    inference(simplify,[status(thm)],['109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KOujgaCoof
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:26:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.69/0.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.69/0.89  % Solved by: fo/fo7.sh
% 0.69/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.89  % done 665 iterations in 0.421s
% 0.69/0.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.69/0.89  % SZS output start Refutation
% 0.69/0.89  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.69/0.89  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.69/0.89  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.69/0.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.69/0.89  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.69/0.89  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.69/0.89  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.69/0.89  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.69/0.89  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.69/0.89  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.69/0.89  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.69/0.89  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.69/0.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.69/0.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.89  thf(sk_C_type, type, sk_C: $i).
% 0.69/0.89  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.69/0.89  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.69/0.89  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.69/0.89  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.69/0.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.69/0.89  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.69/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.89  thf(t69_mcart_1, conjecture,
% 0.69/0.89    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.69/0.89     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.69/0.89       ( ( ![F:$i]:
% 0.69/0.89           ( ( m1_subset_1 @ F @ A ) =>
% 0.69/0.89             ( ![G:$i]:
% 0.69/0.89               ( ( m1_subset_1 @ G @ B ) =>
% 0.69/0.89                 ( ![H:$i]:
% 0.69/0.89                   ( ( m1_subset_1 @ H @ C ) =>
% 0.69/0.89                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.69/0.89                       ( ( D ) = ( F ) ) ) ) ) ) ) ) ) =>
% 0.69/0.89         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.69/0.89           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.69/0.89           ( ( D ) = ( k5_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.69/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.89    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.69/0.89        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.69/0.89          ( ( ![F:$i]:
% 0.69/0.89              ( ( m1_subset_1 @ F @ A ) =>
% 0.69/0.89                ( ![G:$i]:
% 0.69/0.89                  ( ( m1_subset_1 @ G @ B ) =>
% 0.69/0.89                    ( ![H:$i]:
% 0.69/0.89                      ( ( m1_subset_1 @ H @ C ) =>
% 0.69/0.89                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.69/0.89                          ( ( D ) = ( F ) ) ) ) ) ) ) ) ) =>
% 0.69/0.89            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.69/0.89              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.69/0.89              ( ( D ) = ( k5_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.69/0.89    inference('cnf.neg', [status(esa)], [t69_mcart_1])).
% 0.69/0.89  thf('0', plain,
% 0.69/0.89      ((m1_subset_1 @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf(t2_subset, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( m1_subset_1 @ A @ B ) =>
% 0.69/0.89       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.69/0.89  thf('1', plain,
% 0.69/0.89      (![X21 : $i, X22 : $i]:
% 0.69/0.89         ((r2_hidden @ X21 @ X22)
% 0.69/0.89          | (v1_xboole_0 @ X22)
% 0.69/0.89          | ~ (m1_subset_1 @ X21 @ X22))),
% 0.69/0.89      inference('cnf', [status(esa)], [t2_subset])).
% 0.69/0.89  thf('2', plain,
% 0.69/0.89      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.69/0.89        | (r2_hidden @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['0', '1'])).
% 0.69/0.89  thf(t23_mcart_1, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( v1_relat_1 @ B ) =>
% 0.69/0.89       ( ( r2_hidden @ A @ B ) =>
% 0.69/0.89         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 0.69/0.89  thf('3', plain,
% 0.69/0.89      (![X50 : $i, X51 : $i]:
% 0.69/0.89         (((X50) = (k4_tarski @ (k1_mcart_1 @ X50) @ (k2_mcart_1 @ X50)))
% 0.69/0.89          | ~ (v1_relat_1 @ X51)
% 0.69/0.89          | ~ (r2_hidden @ X50 @ X51))),
% 0.69/0.89      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.69/0.89  thf('4', plain,
% 0.69/0.89      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.69/0.89        | ~ (v1_relat_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.69/0.89        | ((sk_E_2)
% 0.69/0.89            = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2))))),
% 0.69/0.89      inference('sup-', [status(thm)], ['2', '3'])).
% 0.69/0.89  thf(d3_zfmisc_1, axiom,
% 0.69/0.89    (![A:$i,B:$i,C:$i]:
% 0.69/0.89     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.69/0.89       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.69/0.89  thf('5', plain,
% 0.69/0.89      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.69/0.89         ((k3_zfmisc_1 @ X28 @ X29 @ X30)
% 0.69/0.89           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29) @ X30))),
% 0.69/0.89      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.69/0.89  thf(fc6_relat_1, axiom,
% 0.69/0.89    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.69/0.89  thf('6', plain,
% 0.69/0.89      (![X23 : $i, X24 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X23 @ X24))),
% 0.69/0.89      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.69/0.89  thf('7', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.89         (v1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))),
% 0.69/0.89      inference('sup+', [status(thm)], ['5', '6'])).
% 0.69/0.89  thf('8', plain,
% 0.69/0.89      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.69/0.89        | ((sk_E_2)
% 0.69/0.89            = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2))))),
% 0.69/0.89      inference('demod', [status(thm)], ['4', '7'])).
% 0.69/0.89  thf(t34_mcart_1, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.69/0.89          ( ![B:$i]:
% 0.69/0.89            ( ~( ( r2_hidden @ B @ A ) & 
% 0.69/0.89                 ( ![C:$i,D:$i,E:$i,F:$i]:
% 0.69/0.89                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.69/0.89                        ( ( B ) = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) ) ) ) ) ))).
% 0.69/0.89  thf('9', plain,
% 0.69/0.89      (![X52 : $i]:
% 0.69/0.89         (((X52) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X52) @ X52))),
% 0.69/0.89      inference('cnf', [status(esa)], [t34_mcart_1])).
% 0.69/0.89  thf(d1_xboole_0, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.69/0.89  thf('10', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.69/0.89      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.69/0.89  thf('11', plain,
% 0.69/0.89      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.69/0.89      inference('sup-', [status(thm)], ['9', '10'])).
% 0.69/0.89  thf('12', plain,
% 0.69/0.89      ((((sk_E_2) = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2)))
% 0.69/0.89        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['8', '11'])).
% 0.69/0.89  thf(d4_zfmisc_1, axiom,
% 0.69/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.69/0.89     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.69/0.89       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.69/0.89  thf('13', plain,
% 0.69/0.89      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.69/0.89         ((k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34)
% 0.69/0.89           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X31 @ X32 @ X33) @ X34))),
% 0.69/0.89      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.69/0.89  thf('14', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 0.69/0.89            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.69/0.89          | ((sk_E_2)
% 0.69/0.89              = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2))))),
% 0.69/0.89      inference('sup+', [status(thm)], ['12', '13'])).
% 0.69/0.89  thf(t55_mcart_1, axiom,
% 0.69/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.69/0.89     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.69/0.89         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 0.69/0.89       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 0.69/0.89  thf('15', plain,
% 0.69/0.89      (![X61 : $i, X62 : $i, X63 : $i, X65 : $i]:
% 0.69/0.89         (((X63) != (k1_xboole_0))
% 0.69/0.89          | ((k4_zfmisc_1 @ X61 @ X62 @ X63 @ X65) = (k1_xboole_0)))),
% 0.69/0.89      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.69/0.89  thf('16', plain,
% 0.69/0.89      (![X61 : $i, X62 : $i, X65 : $i]:
% 0.69/0.89         ((k4_zfmisc_1 @ X61 @ X62 @ k1_xboole_0 @ X65) = (k1_xboole_0))),
% 0.69/0.89      inference('simplify', [status(thm)], ['15'])).
% 0.69/0.89  thf('17', plain,
% 0.69/0.89      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.69/0.89         ((k3_zfmisc_1 @ X28 @ X29 @ X30)
% 0.69/0.89           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29) @ X30))),
% 0.69/0.89      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.69/0.89  thf('18', plain,
% 0.69/0.89      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.69/0.89         ((k3_zfmisc_1 @ X28 @ X29 @ X30)
% 0.69/0.89           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29) @ X30))),
% 0.69/0.89      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.69/0.89  thf('19', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.69/0.89         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.69/0.89           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.69/0.89      inference('sup+', [status(thm)], ['17', '18'])).
% 0.69/0.89  thf('20', plain,
% 0.69/0.89      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.69/0.89         ((k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34)
% 0.69/0.89           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X31 @ X32 @ X33) @ X34))),
% 0.69/0.89      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.69/0.89  thf('21', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.69/0.89         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.69/0.89           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.69/0.89      inference('demod', [status(thm)], ['19', '20'])).
% 0.69/0.89  thf('22', plain,
% 0.69/0.89      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.69/0.89         ((k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34)
% 0.69/0.89           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X31 @ X32 @ X33) @ X34))),
% 0.69/0.89      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.69/0.89  thf('23', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.69/0.89         ((k4_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0 @ X4)
% 0.69/0.89           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) @ X4))),
% 0.69/0.89      inference('sup+', [status(thm)], ['21', '22'])).
% 0.69/0.89  thf('24', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.69/0.89         ((k1_xboole_0)
% 0.69/0.89           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ k1_xboole_0) @ X0))),
% 0.69/0.89      inference('sup+', [status(thm)], ['16', '23'])).
% 0.69/0.89  thf('25', plain,
% 0.69/0.89      (![X61 : $i, X62 : $i, X63 : $i, X65 : $i]:
% 0.69/0.89         (((X65) != (k1_xboole_0))
% 0.69/0.89          | ((k4_zfmisc_1 @ X61 @ X62 @ X63 @ X65) = (k1_xboole_0)))),
% 0.69/0.89      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.69/0.89  thf('26', plain,
% 0.69/0.89      (![X61 : $i, X62 : $i, X63 : $i]:
% 0.69/0.89         ((k4_zfmisc_1 @ X61 @ X62 @ X63 @ k1_xboole_0) = (k1_xboole_0))),
% 0.69/0.89      inference('simplify', [status(thm)], ['25'])).
% 0.69/0.89  thf('27', plain,
% 0.69/0.89      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.69/0.89      inference('demod', [status(thm)], ['24', '26'])).
% 0.69/0.89  thf('28', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))
% 0.69/0.89          | ((sk_E_2)
% 0.69/0.89              = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2))))),
% 0.69/0.89      inference('demod', [status(thm)], ['14', '27'])).
% 0.69/0.89  thf('29', plain,
% 0.69/0.89      (![X61 : $i, X62 : $i, X63 : $i, X64 : $i]:
% 0.69/0.89         (((k4_zfmisc_1 @ X61 @ X62 @ X63 @ X64) != (k1_xboole_0))
% 0.69/0.89          | ((X64) = (k1_xboole_0))
% 0.69/0.89          | ((X63) = (k1_xboole_0))
% 0.69/0.89          | ((X62) = (k1_xboole_0))
% 0.69/0.89          | ((X61) = (k1_xboole_0)))),
% 0.69/0.89      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.69/0.89  thf('30', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.89          | ((sk_E_2)
% 0.69/0.89              = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2)))
% 0.69/0.89          | ((sk_A) = (k1_xboole_0))
% 0.69/0.89          | ((sk_B_2) = (k1_xboole_0))
% 0.69/0.89          | ((sk_C) = (k1_xboole_0))
% 0.69/0.89          | ((X0) = (k1_xboole_0)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['28', '29'])).
% 0.69/0.89  thf('31', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((X0) = (k1_xboole_0))
% 0.69/0.89          | ((sk_C) = (k1_xboole_0))
% 0.69/0.89          | ((sk_B_2) = (k1_xboole_0))
% 0.69/0.89          | ((sk_A) = (k1_xboole_0))
% 0.69/0.89          | ((sk_E_2)
% 0.69/0.89              = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2))))),
% 0.69/0.89      inference('simplify', [status(thm)], ['30'])).
% 0.69/0.89  thf('32', plain, (((sk_A) != (k1_xboole_0))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('33', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('34', plain, (((sk_C) != (k1_xboole_0))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('35', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((X0) = (k1_xboole_0))
% 0.69/0.89          | ((sk_E_2)
% 0.69/0.89              = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2))))),
% 0.69/0.89      inference('simplify_reflect-', [status(thm)], ['31', '32', '33', '34'])).
% 0.69/0.89  thf('36', plain,
% 0.69/0.89      ((((k1_xboole_0) != (sk_E_2))
% 0.69/0.89        | ((sk_E_2)
% 0.69/0.89            = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2))))),
% 0.69/0.89      inference('eq_fact', [status(thm)], ['35'])).
% 0.69/0.89  thf('37', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((X0) = (k1_xboole_0))
% 0.69/0.89          | ((sk_E_2)
% 0.69/0.89              = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2))))),
% 0.69/0.89      inference('simplify_reflect-', [status(thm)], ['31', '32', '33', '34'])).
% 0.69/0.89  thf('38', plain,
% 0.69/0.89      (((sk_E_2) = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ (k2_mcart_1 @ sk_E_2)))),
% 0.69/0.89      inference('clc', [status(thm)], ['36', '37'])).
% 0.69/0.89  thf('39', plain,
% 0.69/0.89      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.69/0.89        | (r2_hidden @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['0', '1'])).
% 0.69/0.89  thf('40', plain,
% 0.69/0.89      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.69/0.89         ((k3_zfmisc_1 @ X28 @ X29 @ X30)
% 0.69/0.89           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29) @ X30))),
% 0.69/0.89      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.69/0.89  thf(t10_mcart_1, axiom,
% 0.69/0.89    (![A:$i,B:$i,C:$i]:
% 0.69/0.89     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.69/0.89       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.69/0.89         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.69/0.89  thf('41', plain,
% 0.69/0.89      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.69/0.89         ((r2_hidden @ (k1_mcart_1 @ X47) @ X48)
% 0.69/0.89          | ~ (r2_hidden @ X47 @ (k2_zfmisc_1 @ X48 @ X49)))),
% 0.69/0.89      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.69/0.89  thf('42', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.69/0.89         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.69/0.89          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['40', '41'])).
% 0.69/0.89  thf('43', plain,
% 0.69/0.89      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.69/0.89        | (r2_hidden @ (k1_mcart_1 @ sk_E_2) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['39', '42'])).
% 0.69/0.89  thf('44', plain,
% 0.69/0.89      (![X50 : $i, X51 : $i]:
% 0.69/0.89         (((X50) = (k4_tarski @ (k1_mcart_1 @ X50) @ (k2_mcart_1 @ X50)))
% 0.69/0.89          | ~ (v1_relat_1 @ X51)
% 0.69/0.89          | ~ (r2_hidden @ X50 @ X51))),
% 0.69/0.89      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.69/0.89  thf('45', plain,
% 0.69/0.89      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.69/0.89        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 0.69/0.89        | ((k1_mcart_1 @ sk_E_2)
% 0.69/0.89            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ 
% 0.69/0.89               (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)))))),
% 0.69/0.89      inference('sup-', [status(thm)], ['43', '44'])).
% 0.69/0.89  thf('46', plain,
% 0.69/0.89      (![X23 : $i, X24 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X23 @ X24))),
% 0.69/0.89      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.69/0.89  thf('47', plain,
% 0.69/0.89      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.69/0.89        | ((k1_mcart_1 @ sk_E_2)
% 0.69/0.89            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ 
% 0.69/0.89               (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)))))),
% 0.69/0.89      inference('demod', [status(thm)], ['45', '46'])).
% 0.69/0.89  thf('48', plain,
% 0.69/0.89      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.69/0.89      inference('sup-', [status(thm)], ['9', '10'])).
% 0.69/0.89  thf('49', plain,
% 0.69/0.89      ((((k1_mcart_1 @ sk_E_2)
% 0.69/0.89          = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ 
% 0.69/0.89             (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2))))
% 0.69/0.89        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['47', '48'])).
% 0.69/0.89  thf('50', plain,
% 0.69/0.89      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.69/0.89         ((k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34)
% 0.69/0.89           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X31 @ X32 @ X33) @ X34))),
% 0.69/0.89      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.69/0.89  thf('51', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 0.69/0.89            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.69/0.89          | ((k1_mcart_1 @ sk_E_2)
% 0.69/0.89              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ 
% 0.69/0.89                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)))))),
% 0.69/0.89      inference('sup+', [status(thm)], ['49', '50'])).
% 0.69/0.89  thf('52', plain,
% 0.69/0.89      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.69/0.89      inference('demod', [status(thm)], ['24', '26'])).
% 0.69/0.89  thf('53', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))
% 0.69/0.89          | ((k1_mcart_1 @ sk_E_2)
% 0.69/0.89              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ 
% 0.69/0.89                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)))))),
% 0.69/0.89      inference('demod', [status(thm)], ['51', '52'])).
% 0.69/0.89  thf('54', plain,
% 0.69/0.89      (![X61 : $i, X62 : $i, X63 : $i, X64 : $i]:
% 0.69/0.89         (((k4_zfmisc_1 @ X61 @ X62 @ X63 @ X64) != (k1_xboole_0))
% 0.69/0.89          | ((X64) = (k1_xboole_0))
% 0.69/0.89          | ((X63) = (k1_xboole_0))
% 0.69/0.89          | ((X62) = (k1_xboole_0))
% 0.69/0.89          | ((X61) = (k1_xboole_0)))),
% 0.69/0.89      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.69/0.89  thf('55', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.89          | ((k1_mcart_1 @ sk_E_2)
% 0.69/0.89              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ 
% 0.69/0.89                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2))))
% 0.69/0.89          | ((sk_A) = (k1_xboole_0))
% 0.69/0.89          | ((sk_B_2) = (k1_xboole_0))
% 0.69/0.89          | ((sk_C) = (k1_xboole_0))
% 0.69/0.89          | ((X0) = (k1_xboole_0)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['53', '54'])).
% 0.69/0.89  thf('56', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((X0) = (k1_xboole_0))
% 0.69/0.89          | ((sk_C) = (k1_xboole_0))
% 0.69/0.89          | ((sk_B_2) = (k1_xboole_0))
% 0.69/0.89          | ((sk_A) = (k1_xboole_0))
% 0.69/0.89          | ((k1_mcart_1 @ sk_E_2)
% 0.69/0.89              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ 
% 0.69/0.89                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)))))),
% 0.69/0.89      inference('simplify', [status(thm)], ['55'])).
% 0.69/0.89  thf('57', plain, (((sk_A) != (k1_xboole_0))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('58', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('59', plain, (((sk_C) != (k1_xboole_0))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('60', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((X0) = (k1_xboole_0))
% 0.69/0.89          | ((k1_mcart_1 @ sk_E_2)
% 0.69/0.89              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ 
% 0.69/0.89                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)))))),
% 0.69/0.89      inference('simplify_reflect-', [status(thm)], ['56', '57', '58', '59'])).
% 0.69/0.89  thf('61', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((X0) = (k1_xboole_0))
% 0.69/0.89          | ((k1_mcart_1 @ sk_E_2)
% 0.69/0.89              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ 
% 0.69/0.89                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)))))),
% 0.69/0.89      inference('simplify_reflect-', [status(thm)], ['56', '57', '58', '59'])).
% 0.69/0.89  thf('62', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (((X1) = (X0))
% 0.69/0.89          | ((k1_mcart_1 @ sk_E_2)
% 0.69/0.89              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ 
% 0.69/0.89                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2))))
% 0.69/0.89          | ((k1_mcart_1 @ sk_E_2)
% 0.69/0.89              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ 
% 0.69/0.89                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)))))),
% 0.69/0.89      inference('sup+', [status(thm)], ['60', '61'])).
% 0.69/0.89  thf('63', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (((k1_mcart_1 @ sk_E_2)
% 0.69/0.89            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ 
% 0.69/0.89               (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2))))
% 0.69/0.89          | ((X1) = (X0)))),
% 0.69/0.89      inference('simplify', [status(thm)], ['62'])).
% 0.69/0.89  thf('64', plain,
% 0.69/0.89      (((k1_mcart_1 @ sk_E_2)
% 0.69/0.89         = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ 
% 0.69/0.89            (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2))))),
% 0.69/0.89      inference('condensation', [status(thm)], ['63'])).
% 0.69/0.89  thf(d3_mcart_1, axiom,
% 0.69/0.89    (![A:$i,B:$i,C:$i]:
% 0.69/0.89     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.69/0.89  thf('65', plain,
% 0.69/0.89      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.69/0.89         ((k3_mcart_1 @ X25 @ X26 @ X27)
% 0.69/0.89           = (k4_tarski @ (k4_tarski @ X25 @ X26) @ X27))),
% 0.69/0.89      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.69/0.89  thf('66', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ 
% 0.69/0.89           (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ X0)
% 0.69/0.89           = (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ X0))),
% 0.69/0.89      inference('sup+', [status(thm)], ['64', '65'])).
% 0.69/0.89  thf('67', plain,
% 0.69/0.89      ((m1_subset_1 @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf(dt_k6_mcart_1, axiom,
% 0.69/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.69/0.89     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.69/0.89       ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ))).
% 0.69/0.89  thf('68', plain,
% 0.69/0.89      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.69/0.89         ((m1_subset_1 @ (k6_mcart_1 @ X39 @ X40 @ X41 @ X42) @ X40)
% 0.69/0.89          | ~ (m1_subset_1 @ X42 @ (k3_zfmisc_1 @ X39 @ X40 @ X41)))),
% 0.69/0.89      inference('cnf', [status(esa)], [dt_k6_mcart_1])).
% 0.69/0.89  thf('69', plain,
% 0.69/0.89      ((m1_subset_1 @ (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2) @ sk_B_2)),
% 0.69/0.89      inference('sup-', [status(thm)], ['67', '68'])).
% 0.69/0.89  thf('70', plain,
% 0.69/0.89      (![X66 : $i, X67 : $i, X68 : $i]:
% 0.69/0.89         (~ (m1_subset_1 @ X66 @ sk_B_2)
% 0.69/0.89          | ((sk_D_1) = (X67))
% 0.69/0.89          | ((sk_E_2) != (k3_mcart_1 @ X67 @ X66 @ X68))
% 0.69/0.89          | ~ (m1_subset_1 @ X68 @ sk_C)
% 0.69/0.89          | ~ (m1_subset_1 @ X67 @ sk_A))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('71', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.69/0.89          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.69/0.89          | ((sk_E_2)
% 0.69/0.89              != (k3_mcart_1 @ X0 @ 
% 0.69/0.89                  (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2) @ X1))
% 0.69/0.89          | ((sk_D_1) = (X0)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['69', '70'])).
% 0.69/0.89  thf('72', plain,
% 0.69/0.89      ((m1_subset_1 @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf(t50_mcart_1, axiom,
% 0.69/0.89    (![A:$i,B:$i,C:$i]:
% 0.69/0.89     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.69/0.89          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.69/0.89          ( ~( ![D:$i]:
% 0.69/0.89               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.69/0.89                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.69/0.89                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.69/0.89                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.69/0.89                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.69/0.89                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.69/0.89  thf('73', plain,
% 0.69/0.89      (![X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 0.69/0.89         (((X57) = (k1_xboole_0))
% 0.69/0.89          | ((X58) = (k1_xboole_0))
% 0.69/0.89          | ((k6_mcart_1 @ X57 @ X58 @ X60 @ X59)
% 0.69/0.89              = (k2_mcart_1 @ (k1_mcart_1 @ X59)))
% 0.69/0.89          | ~ (m1_subset_1 @ X59 @ (k3_zfmisc_1 @ X57 @ X58 @ X60))
% 0.69/0.89          | ((X60) = (k1_xboole_0)))),
% 0.69/0.89      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.69/0.89  thf('74', plain,
% 0.69/0.89      ((((sk_C) = (k1_xboole_0))
% 0.69/0.89        | ((k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2)
% 0.69/0.89            = (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)))
% 0.69/0.89        | ((sk_B_2) = (k1_xboole_0))
% 0.69/0.89        | ((sk_A) = (k1_xboole_0)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['72', '73'])).
% 0.69/0.89  thf('75', plain, (((sk_A) != (k1_xboole_0))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('76', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('77', plain, (((sk_C) != (k1_xboole_0))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('78', plain,
% 0.69/0.89      (((k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2)
% 0.69/0.89         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)))),
% 0.69/0.89      inference('simplify_reflect-', [status(thm)], ['74', '75', '76', '77'])).
% 0.69/0.89  thf('79', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.69/0.89          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.69/0.89          | ((sk_E_2)
% 0.69/0.89              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ X1))
% 0.69/0.89          | ((sk_D_1) = (X0)))),
% 0.69/0.89      inference('demod', [status(thm)], ['71', '78'])).
% 0.69/0.89  thf('80', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((sk_E_2) != (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ X0))
% 0.69/0.89          | ((sk_D_1) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)))
% 0.69/0.89          | ~ (m1_subset_1 @ X0 @ sk_C)
% 0.69/0.89          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_A))),
% 0.69/0.89      inference('sup-', [status(thm)], ['66', '79'])).
% 0.69/0.89  thf('81', plain,
% 0.69/0.89      ((m1_subset_1 @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf(dt_k5_mcart_1, axiom,
% 0.69/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.69/0.89     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.69/0.89       ( m1_subset_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ A ) ))).
% 0.69/0.89  thf('82', plain,
% 0.69/0.89      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.69/0.89         ((m1_subset_1 @ (k5_mcart_1 @ X35 @ X36 @ X37 @ X38) @ X35)
% 0.69/0.89          | ~ (m1_subset_1 @ X38 @ (k3_zfmisc_1 @ X35 @ X36 @ X37)))),
% 0.69/0.89      inference('cnf', [status(esa)], [dt_k5_mcart_1])).
% 0.69/0.89  thf('83', plain,
% 0.69/0.89      ((m1_subset_1 @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2) @ sk_A)),
% 0.69/0.89      inference('sup-', [status(thm)], ['81', '82'])).
% 0.69/0.89  thf('84', plain,
% 0.69/0.89      ((m1_subset_1 @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('85', plain,
% 0.69/0.89      (![X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 0.69/0.89         (((X57) = (k1_xboole_0))
% 0.69/0.89          | ((X58) = (k1_xboole_0))
% 0.69/0.89          | ((k5_mcart_1 @ X57 @ X58 @ X60 @ X59)
% 0.69/0.89              = (k1_mcart_1 @ (k1_mcart_1 @ X59)))
% 0.69/0.89          | ~ (m1_subset_1 @ X59 @ (k3_zfmisc_1 @ X57 @ X58 @ X60))
% 0.69/0.89          | ((X60) = (k1_xboole_0)))),
% 0.69/0.89      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.69/0.89  thf('86', plain,
% 0.69/0.89      ((((sk_C) = (k1_xboole_0))
% 0.69/0.89        | ((k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2)
% 0.69/0.89            = (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)))
% 0.69/0.89        | ((sk_B_2) = (k1_xboole_0))
% 0.69/0.89        | ((sk_A) = (k1_xboole_0)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['84', '85'])).
% 0.69/0.89  thf('87', plain, (((sk_A) != (k1_xboole_0))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('88', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('89', plain, (((sk_C) != (k1_xboole_0))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('90', plain,
% 0.69/0.89      (((k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2)
% 0.69/0.89         = (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)))),
% 0.69/0.89      inference('simplify_reflect-', [status(thm)], ['86', '87', '88', '89'])).
% 0.69/0.89  thf('91', plain,
% 0.69/0.89      ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)) @ sk_A)),
% 0.69/0.89      inference('demod', [status(thm)], ['83', '90'])).
% 0.69/0.89  thf('92', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((sk_E_2) != (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ X0))
% 0.69/0.89          | ((sk_D_1) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)))
% 0.69/0.89          | ~ (m1_subset_1 @ X0 @ sk_C))),
% 0.69/0.89      inference('demod', [status(thm)], ['80', '91'])).
% 0.69/0.89  thf('93', plain,
% 0.69/0.89      (((sk_D_1) != (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('94', plain,
% 0.69/0.89      (((k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2)
% 0.69/0.89         = (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)))),
% 0.69/0.89      inference('simplify_reflect-', [status(thm)], ['86', '87', '88', '89'])).
% 0.69/0.89  thf('95', plain, (((sk_D_1) != (k1_mcart_1 @ (k1_mcart_1 @ sk_E_2)))),
% 0.69/0.89      inference('demod', [status(thm)], ['93', '94'])).
% 0.69/0.89  thf('96', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((sk_E_2) != (k4_tarski @ (k1_mcart_1 @ sk_E_2) @ X0))
% 0.69/0.89          | ~ (m1_subset_1 @ X0 @ sk_C))),
% 0.69/0.89      inference('simplify_reflect-', [status(thm)], ['92', '95'])).
% 0.69/0.89  thf('97', plain,
% 0.69/0.89      ((((sk_E_2) != (sk_E_2)) | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E_2) @ sk_C))),
% 0.69/0.89      inference('sup-', [status(thm)], ['38', '96'])).
% 0.69/0.89  thf('98', plain,
% 0.69/0.89      ((m1_subset_1 @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf(dt_k7_mcart_1, axiom,
% 0.69/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.69/0.89     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.69/0.89       ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ))).
% 0.69/0.89  thf('99', plain,
% 0.69/0.89      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.69/0.89         ((m1_subset_1 @ (k7_mcart_1 @ X43 @ X44 @ X45 @ X46) @ X45)
% 0.69/0.89          | ~ (m1_subset_1 @ X46 @ (k3_zfmisc_1 @ X43 @ X44 @ X45)))),
% 0.69/0.89      inference('cnf', [status(esa)], [dt_k7_mcart_1])).
% 0.69/0.89  thf('100', plain,
% 0.69/0.89      ((m1_subset_1 @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2) @ sk_C)),
% 0.69/0.89      inference('sup-', [status(thm)], ['98', '99'])).
% 0.69/0.89  thf('101', plain,
% 0.69/0.89      ((m1_subset_1 @ sk_E_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('102', plain,
% 0.69/0.89      (![X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 0.69/0.89         (((X57) = (k1_xboole_0))
% 0.69/0.89          | ((X58) = (k1_xboole_0))
% 0.69/0.89          | ((k7_mcart_1 @ X57 @ X58 @ X60 @ X59) = (k2_mcart_1 @ X59))
% 0.69/0.89          | ~ (m1_subset_1 @ X59 @ (k3_zfmisc_1 @ X57 @ X58 @ X60))
% 0.69/0.89          | ((X60) = (k1_xboole_0)))),
% 0.69/0.89      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.69/0.89  thf('103', plain,
% 0.69/0.89      ((((sk_C) = (k1_xboole_0))
% 0.69/0.89        | ((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2) = (k2_mcart_1 @ sk_E_2))
% 0.69/0.89        | ((sk_B_2) = (k1_xboole_0))
% 0.69/0.89        | ((sk_A) = (k1_xboole_0)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['101', '102'])).
% 0.69/0.89  thf('104', plain, (((sk_A) != (k1_xboole_0))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('105', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('106', plain, (((sk_C) != (k1_xboole_0))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('107', plain,
% 0.69/0.89      (((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_2) = (k2_mcart_1 @ sk_E_2))),
% 0.69/0.89      inference('simplify_reflect-', [status(thm)],
% 0.69/0.89                ['103', '104', '105', '106'])).
% 0.69/0.89  thf('108', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E_2) @ sk_C)),
% 0.69/0.89      inference('demod', [status(thm)], ['100', '107'])).
% 0.69/0.89  thf('109', plain, (((sk_E_2) != (sk_E_2))),
% 0.69/0.89      inference('demod', [status(thm)], ['97', '108'])).
% 0.69/0.89  thf('110', plain, ($false), inference('simplify', [status(thm)], ['109'])).
% 0.69/0.89  
% 0.69/0.89  % SZS output end Refutation
% 0.69/0.89  
% 0.69/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
