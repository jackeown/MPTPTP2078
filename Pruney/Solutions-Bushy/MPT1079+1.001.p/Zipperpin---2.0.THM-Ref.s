%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1079+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yz5wfjzxqg

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 197 expanded)
%              Number of leaves         :   29 (  67 expanded)
%              Depth                    :   22
%              Number of atoms          : 2172 (5892 expanded)
%              Number of equality atoms :   37 ( 105 expanded)
%              Maximal formula depth    :   21 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_funct_2_type,type,(
    k5_funct_2: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_funct_2_type,type,(
    k4_funct_2: $i > $i > $i > $i > $i )).

thf(t196_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ~ ( v1_xboole_0 @ C )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ A @ ( k2_zfmisc_1 @ B @ C ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ A )
                     => ( ( k3_funct_2 @ A @ ( k2_zfmisc_1 @ B @ C ) @ D @ E )
                        = ( k4_tarski @ ( k3_funct_2 @ A @ B @ ( k4_funct_2 @ A @ B @ C @ D ) @ E ) @ ( k3_funct_2 @ A @ C @ ( k5_funct_2 @ A @ B @ C @ D ) @ E ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ~ ( v1_xboole_0 @ C )
               => ! [D: $i] :
                    ( ( ( v1_funct_1 @ D )
                      & ( v1_funct_2 @ D @ A @ ( k2_zfmisc_1 @ B @ C ) )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ A )
                       => ( ( k3_funct_2 @ A @ ( k2_zfmisc_1 @ B @ C ) @ D @ E )
                          = ( k4_tarski @ ( k3_funct_2 @ A @ B @ ( k4_funct_2 @ A @ B @ C @ D ) @ E ) @ ( k3_funct_2 @ A @ C @ ( k5_funct_2 @ A @ B @ C @ D ) @ E ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t196_funct_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( m1_subset_1 @ ( k3_funct_2 @ A @ B @ C @ D ) @ B ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X12 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X12 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ X13 )
      | ( m1_subset_1 @ ( k3_funct_2 @ X13 @ X14 @ X12 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_funct_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ sk_E ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','9'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r2_hidden @ X30 @ X31 )
      | ( v1_xboole_0 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ sk_E ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X28: $i,X29: $i] :
      ( ( X28
        = ( k4_tarski @ ( k1_mcart_1 @ X28 ) @ ( k2_mcart_1 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X29 )
      | ~ ( r2_hidden @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ sk_E ) ) @ ( k2_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X26: $i,X27: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ sk_E ) ) @ ( k2_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ sk_E ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ~ ( v1_xboole_0 @ C )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )
     => ( ( v1_funct_1 @ ( k5_funct_2 @ A @ B @ C @ D ) )
        & ( v1_funct_2 @ ( k5_funct_2 @ A @ B @ C @ D ) @ A @ C )
        & ( m1_subset_1 @ ( k5_funct_2 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) )).

thf('19',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ( v1_xboole_0 @ X21 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ X22 @ ( k2_zfmisc_1 @ X21 @ X20 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) )
      | ( v1_funct_1 @ ( k5_funct_2 @ X22 @ X21 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_funct_2])).

thf('20',plain,
    ( ( v1_funct_1 @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_funct_1 @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ( v1_xboole_0 @ X21 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ X22 @ ( k2_zfmisc_1 @ X21 @ X20 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) )
      | ( v1_funct_2 @ ( k5_funct_2 @ X22 @ X21 @ X20 @ X23 ) @ X22 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_funct_2])).

thf('26',plain,
    ( ( v1_funct_2 @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_A @ sk_C )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v1_funct_2 @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_A @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ( v1_xboole_0 @ X21 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ X22 @ ( k2_zfmisc_1 @ X21 @ X20 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) )
      | ( m1_subset_1 @ ( k5_funct_2 @ X22 @ X21 @ X20 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_funct_2])).

thf('32',plain,
    ( ( m1_subset_1 @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( m1_subset_1 @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf(d7_funct_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ~ ( v1_xboole_0 @ C )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ A @ ( k2_zfmisc_1 @ B @ C ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ A @ C )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) )
                     => ( ( E
                          = ( k5_funct_2 @ A @ B @ C @ D ) )
                      <=> ! [F: $i] :
                            ( ( m1_subset_1 @ F @ A )
                           => ( ( k3_funct_2 @ A @ C @ E @ F )
                              = ( k2_mcart_1 @ ( k3_funct_2 @ A @ ( k2_zfmisc_1 @ B @ C ) @ D @ F ) ) ) ) ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_funct_2 @ X7 @ X8 @ ( k2_zfmisc_1 @ X6 @ X9 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ ( k2_zfmisc_1 @ X6 @ X9 ) ) ) )
      | ( X10
       != ( k5_funct_2 @ X8 @ X6 @ X9 @ X7 ) )
      | ( ( k3_funct_2 @ X8 @ X9 @ X10 @ X11 )
        = ( k2_mcart_1 @ ( k3_funct_2 @ X8 @ ( k2_zfmisc_1 @ X6 @ X9 ) @ X7 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X11 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X8 @ X9 )
      | ~ ( v1_funct_1 @ X10 )
      | ( v1_xboole_0 @ X9 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d7_funct_2])).

thf('37',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X11: $i] :
      ( ( v1_xboole_0 @ X8 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v1_funct_1 @ ( k5_funct_2 @ X8 @ X6 @ X9 @ X7 ) )
      | ~ ( v1_funct_2 @ ( k5_funct_2 @ X8 @ X6 @ X9 @ X7 ) @ X8 @ X9 )
      | ~ ( m1_subset_1 @ ( k5_funct_2 @ X8 @ X6 @ X9 @ X7 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X11 @ X8 )
      | ( ( k3_funct_2 @ X8 @ X9 @ ( k5_funct_2 @ X8 @ X6 @ X9 @ X7 ) @ X11 )
        = ( k2_mcart_1 @ ( k3_funct_2 @ X8 @ ( k2_zfmisc_1 @ X6 @ X9 ) @ X7 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ ( k2_zfmisc_1 @ X6 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ X8 @ ( k2_zfmisc_1 @ X6 @ X9 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) )
      | ( ( k3_funct_2 @ sk_A @ sk_C @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
        = ( k2_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( v1_funct_2 @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_A @ sk_C )
      | ~ ( v1_funct_1 @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( ( k3_funct_2 @ sk_A @ sk_C @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
        = ( k2_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( v1_funct_2 @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_A @ sk_C )
      | ~ ( v1_funct_1 @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ~ ( v1_funct_2 @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_A @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_C @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
        = ( k2_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_C @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
        = ( k2_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( v1_funct_1 @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['29','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_C @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
        = ( k2_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_C @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
        = ( k2_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_C @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
        = ( k2_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k3_funct_2 @ sk_A @ sk_C @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E )
      = ( k2_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['17','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ~ ( v1_xboole_0 @ C )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )
     => ( ( v1_funct_1 @ ( k4_funct_2 @ A @ B @ C @ D ) )
        & ( v1_funct_2 @ ( k4_funct_2 @ A @ B @ C @ D ) @ A @ B )
        & ( m1_subset_1 @ ( k4_funct_2 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('51',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ( v1_xboole_0 @ X17 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ ( k2_zfmisc_1 @ X17 @ X16 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) )
      | ( v1_funct_1 @ ( k4_funct_2 @ X18 @ X17 @ X16 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_funct_2])).

thf('52',plain,
    ( ( v1_funct_1 @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v1_funct_1 @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ( v1_xboole_0 @ X17 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ ( k2_zfmisc_1 @ X17 @ X16 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) )
      | ( v1_funct_2 @ ( k4_funct_2 @ X18 @ X17 @ X16 @ X19 ) @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_funct_2])).

thf('58',plain,
    ( ( v1_funct_2 @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v1_funct_2 @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_A @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ( v1_xboole_0 @ X17 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ ( k2_zfmisc_1 @ X17 @ X16 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) )
      | ( m1_subset_1 @ ( k4_funct_2 @ X18 @ X17 @ X16 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_funct_2])).

thf('64',plain,
    ( ( m1_subset_1 @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( m1_subset_1 @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf(d6_funct_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ~ ( v1_xboole_0 @ C )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ A @ ( k2_zfmisc_1 @ B @ C ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ A @ B )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
                     => ( ( E
                          = ( k4_funct_2 @ A @ B @ C @ D ) )
                      <=> ! [F: $i] :
                            ( ( m1_subset_1 @ F @ A )
                           => ( ( k3_funct_2 @ A @ B @ E @ F )
                              = ( k1_mcart_1 @ ( k3_funct_2 @ A @ ( k2_zfmisc_1 @ B @ C ) @ D @ F ) ) ) ) ) ) ) ) ) ) )).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ X2 @ ( k2_zfmisc_1 @ X0 @ X3 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ ( k2_zfmisc_1 @ X0 @ X3 ) ) ) )
      | ( X4
       != ( k4_funct_2 @ X2 @ X0 @ X3 @ X1 ) )
      | ( ( k3_funct_2 @ X2 @ X0 @ X4 @ X5 )
        = ( k1_mcart_1 @ ( k3_funct_2 @ X2 @ ( k2_zfmisc_1 @ X0 @ X3 ) @ X1 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X5 @ X2 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X4 @ X2 @ X0 )
      | ~ ( v1_funct_1 @ X4 )
      | ( v1_xboole_0 @ X3 )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d6_funct_2])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( v1_funct_1 @ ( k4_funct_2 @ X2 @ X0 @ X3 @ X1 ) )
      | ~ ( v1_funct_2 @ ( k4_funct_2 @ X2 @ X0 @ X3 @ X1 ) @ X2 @ X0 )
      | ~ ( m1_subset_1 @ ( k4_funct_2 @ X2 @ X0 @ X3 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X5 @ X2 )
      | ( ( k3_funct_2 @ X2 @ X0 @ ( k4_funct_2 @ X2 @ X0 @ X3 @ X1 ) @ X5 )
        = ( k1_mcart_1 @ ( k3_funct_2 @ X2 @ ( k2_zfmisc_1 @ X0 @ X3 ) @ X1 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ ( k2_zfmisc_1 @ X0 @ X3 ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ X2 @ ( k2_zfmisc_1 @ X0 @ X3 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) )
      | ( ( k3_funct_2 @ sk_A @ sk_B @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
        = ( k1_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( v1_funct_2 @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( ( k3_funct_2 @ sk_A @ sk_B @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
        = ( k1_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( v1_funct_2 @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ~ ( v1_funct_2 @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_B @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
        = ( k1_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_B @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
        = ( k1_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['61','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_B @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
        = ( k1_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_B @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
        = ( k1_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_B @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
        = ( k1_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k3_funct_2 @ sk_A @ sk_B @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E )
      = ( k1_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['49','79'])).

thf('81',plain,(
    ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ sk_E )
 != ( k4_tarski @ ( k3_funct_2 @ sk_A @ sk_B @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) @ ( k3_funct_2 @ sk_A @ sk_C @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ sk_E )
     != ( k4_tarski @ ( k1_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ sk_E ) ) @ ( k3_funct_2 @ sk_A @ sk_C @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ sk_E )
     != ( k4_tarski @ ( k1_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ sk_E ) ) @ ( k2_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ sk_E ) ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','82'])).

thf('84',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ sk_E )
     != ( k4_tarski @ ( k1_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ sk_E ) ) @ ( k2_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ sk_E ) ) ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ sk_E )
     != ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ sk_E ) )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','84'])).

thf('86',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf(fc10_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('87',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ( v1_xboole_0 @ X25 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[fc10_subset_1])).

thf('88',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    $false ),
    inference(demod,[status(thm)],['0','93'])).


%------------------------------------------------------------------------------
