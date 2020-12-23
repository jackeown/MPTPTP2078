%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eYJPYHE4TW

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:40 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 123 expanded)
%              Number of leaves         :   20 (  44 expanded)
%              Depth                    :   19
%              Number of atoms          :  857 (1254 expanded)
%              Number of equality atoms :   44 (  81 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('1',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d8_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( C
                  = ( k5_relat_1 @ A @ B ) )
              <=> ! [D: $i,E: $i] :
                    ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
                  <=> ? [F: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B )
                        & ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X16 @ X14 @ X15 ) @ ( sk_E @ X16 @ X14 @ X15 ) ) @ X16 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X16 @ X14 @ X15 ) @ ( sk_E @ X16 @ X14 @ X15 ) ) @ X14 )
      | ( X16
        = ( k5_relat_1 @ X15 @ X14 ) )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X3 )
      | ~ ( r1_tarski @ X0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X0 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X2 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ k1_xboole_0 @ X2 @ X1 ) @ ( sk_E @ k1_xboole_0 @ X2 @ X1 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ k1_xboole_0 @ X2 @ X1 ) @ ( sk_E @ k1_xboole_0 @ X2 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf(t62_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
          = k1_xboole_0 )
        & ( ( k5_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
            = k1_xboole_0 )
          & ( ( k5_relat_1 @ A @ k1_xboole_0 )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_relat_1])).

thf('7',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ k1_xboole_0 @ X2 @ X1 ) @ ( sk_E @ k1_xboole_0 @ X2 @ X1 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ k1_xboole_0 @ X2 @ X1 ) @ ( sk_E @ k1_xboole_0 @ X2 @ X1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X1: $i,X2: $i] :
      ~ ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('14',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ k1_xboole_0 @ X2 @ X1 ) @ ( sk_E @ k1_xboole_0 @ X2 @ X1 ) ) @ X2 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ k1_xboole_0 @ X0 @ X1 ) @ ( sk_E @ k1_xboole_0 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ k1_xboole_0 @ X0 @ X1 ) @ ( sk_E @ k1_xboole_0 @ X0 @ X1 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ k1_xboole_0 @ k1_xboole_0 @ X1 ) @ ( sk_E @ k1_xboole_0 @ k1_xboole_0 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','17'])).

thf('19',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','10'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ k1_xboole_0 @ k1_xboole_0 @ X1 ) @ ( sk_E @ k1_xboole_0 @ k1_xboole_0 @ X1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X1: $i,X2: $i] :
      ~ ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('22',plain,(
    ! [X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('27',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X16 @ X14 @ X15 ) @ ( sk_E @ X16 @ X14 @ X15 ) ) @ X16 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X16 @ X14 @ X15 ) @ ( sk_F @ X16 @ X14 @ X15 ) ) @ X15 )
      | ( X16
        = ( k5_relat_1 @ X15 @ X14 ) )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('28',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X0 @ X2 @ X1 ) @ ( sk_F @ X0 @ X2 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X3 )
      | ~ ( r1_tarski @ X0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X0 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X0 @ X2 @ X1 ) @ ( sk_F @ X0 @ X2 @ X1 ) ) @ X1 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ k1_xboole_0 @ X2 @ X1 ) @ ( sk_F @ k1_xboole_0 @ X2 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ k1_xboole_0 @ X2 @ X1 ) @ ( sk_E @ k1_xboole_0 @ X2 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','10'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ k1_xboole_0 @ X2 @ X1 ) @ ( sk_F @ k1_xboole_0 @ X2 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ k1_xboole_0 @ X2 @ X1 ) @ ( sk_E @ k1_xboole_0 @ X2 @ X1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X1: $i,X2: $i] :
      ~ ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('35',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ k1_xboole_0 @ X2 @ X1 ) @ ( sk_F @ k1_xboole_0 @ X2 @ X1 ) ) @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ k1_xboole_0 @ X1 @ X0 ) @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ k1_xboole_0 @ X1 @ X0 ) @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ k1_xboole_0 @ X1 @ k1_xboole_0 ) @ ( sk_F @ k1_xboole_0 @ X1 @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','38'])).

thf('40',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','10'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ k1_xboole_0 @ X1 @ k1_xboole_0 ) @ ( sk_F @ k1_xboole_0 @ X1 @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X1: $i,X2: $i] :
      ~ ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('43',plain,(
    ! [X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('45',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('50',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['48','49'])).

thf('51',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['24','50'])).

thf('52',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    $false ),
    inference(simplify,[status(thm)],['54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eYJPYHE4TW
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:19:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.50/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.73  % Solved by: fo/fo7.sh
% 0.50/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.73  % done 152 iterations in 0.275s
% 0.50/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.73  % SZS output start Refutation
% 0.50/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.73  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.50/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.73  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.50/0.73  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.50/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.73  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.50/0.73  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.50/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.50/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.50/0.73  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.50/0.73  thf('0', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.50/0.73      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.50/0.73  thf('1', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.50/0.73      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.50/0.73  thf(d8_relat_1, axiom,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( v1_relat_1 @ A ) =>
% 0.50/0.73       ( ![B:$i]:
% 0.50/0.73         ( ( v1_relat_1 @ B ) =>
% 0.50/0.73           ( ![C:$i]:
% 0.50/0.73             ( ( v1_relat_1 @ C ) =>
% 0.50/0.73               ( ( ( C ) = ( k5_relat_1 @ A @ B ) ) <=>
% 0.50/0.73                 ( ![D:$i,E:$i]:
% 0.50/0.73                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.50/0.73                     ( ?[F:$i]:
% 0.50/0.73                       ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B ) & 
% 0.50/0.73                         ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.50/0.73  thf('2', plain,
% 0.50/0.73      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X14)
% 0.50/0.73          | (r2_hidden @ 
% 0.50/0.73             (k4_tarski @ (sk_D_1 @ X16 @ X14 @ X15) @ (sk_E @ X16 @ X14 @ X15)) @ 
% 0.50/0.73             X16)
% 0.50/0.73          | (r2_hidden @ 
% 0.50/0.73             (k4_tarski @ (sk_F @ X16 @ X14 @ X15) @ (sk_E @ X16 @ X14 @ X15)) @ 
% 0.50/0.73             X14)
% 0.50/0.73          | ((X16) = (k5_relat_1 @ X15 @ X14))
% 0.50/0.73          | ~ (v1_relat_1 @ X16)
% 0.50/0.73          | ~ (v1_relat_1 @ X15))),
% 0.50/0.73      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.50/0.73  thf(d3_relat_1, axiom,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( v1_relat_1 @ A ) =>
% 0.50/0.73       ( ![B:$i]:
% 0.50/0.73         ( ( r1_tarski @ A @ B ) <=>
% 0.50/0.73           ( ![C:$i,D:$i]:
% 0.50/0.73             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.50/0.73               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.50/0.73  thf('3', plain,
% 0.50/0.73      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.50/0.73         (~ (r1_tarski @ X10 @ X11)
% 0.50/0.73          | (r2_hidden @ (k4_tarski @ X12 @ X13) @ X11)
% 0.50/0.73          | ~ (r2_hidden @ (k4_tarski @ X12 @ X13) @ X10)
% 0.50/0.73          | ~ (v1_relat_1 @ X10))),
% 0.50/0.73      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.50/0.73  thf('4', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X1)
% 0.50/0.73          | ~ (v1_relat_1 @ X0)
% 0.50/0.73          | ((X0) = (k5_relat_1 @ X1 @ X2))
% 0.50/0.73          | (r2_hidden @ 
% 0.50/0.73             (k4_tarski @ (sk_F @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X2)
% 0.50/0.73          | ~ (v1_relat_1 @ X2)
% 0.50/0.73          | ~ (v1_relat_1 @ X0)
% 0.50/0.73          | (r2_hidden @ 
% 0.50/0.73             (k4_tarski @ (sk_D_1 @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X3)
% 0.50/0.73          | ~ (r1_tarski @ X0 @ X3))),
% 0.50/0.73      inference('sup-', [status(thm)], ['2', '3'])).
% 0.50/0.73  thf('5', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.50/0.73         (~ (r1_tarski @ X0 @ X3)
% 0.50/0.73          | (r2_hidden @ 
% 0.50/0.73             (k4_tarski @ (sk_D_1 @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X3)
% 0.50/0.73          | ~ (v1_relat_1 @ X2)
% 0.50/0.73          | (r2_hidden @ 
% 0.50/0.73             (k4_tarski @ (sk_F @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X2)
% 0.50/0.73          | ((X0) = (k5_relat_1 @ X1 @ X2))
% 0.50/0.73          | ~ (v1_relat_1 @ X0)
% 0.50/0.73          | ~ (v1_relat_1 @ X1))),
% 0.50/0.73      inference('simplify', [status(thm)], ['4'])).
% 0.50/0.73  thf('6', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X1)
% 0.50/0.73          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.50/0.73          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ X2))
% 0.50/0.73          | (r2_hidden @ 
% 0.50/0.73             (k4_tarski @ (sk_F @ k1_xboole_0 @ X2 @ X1) @ 
% 0.50/0.73              (sk_E @ k1_xboole_0 @ X2 @ X1)) @ 
% 0.50/0.73             X2)
% 0.50/0.73          | ~ (v1_relat_1 @ X2)
% 0.50/0.73          | (r2_hidden @ 
% 0.50/0.73             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X2 @ X1) @ 
% 0.50/0.73              (sk_E @ k1_xboole_0 @ X2 @ X1)) @ 
% 0.50/0.73             X0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['1', '5'])).
% 0.50/0.73  thf(t62_relat_1, conjecture,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( v1_relat_1 @ A ) =>
% 0.50/0.73       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.50/0.73         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.50/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.73    (~( ![A:$i]:
% 0.50/0.73        ( ( v1_relat_1 @ A ) =>
% 0.50/0.73          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.50/0.73            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.50/0.73    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.50/0.73  thf('7', plain, ((v1_relat_1 @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf(t4_subset_1, axiom,
% 0.50/0.73    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.50/0.73  thf('8', plain,
% 0.50/0.73      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 0.50/0.73      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.50/0.73  thf(cc2_relat_1, axiom,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( v1_relat_1 @ A ) =>
% 0.50/0.73       ( ![B:$i]:
% 0.50/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.50/0.73  thf('9', plain,
% 0.50/0.73      (![X7 : $i, X8 : $i]:
% 0.50/0.73         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.50/0.73          | (v1_relat_1 @ X7)
% 0.50/0.73          | ~ (v1_relat_1 @ X8))),
% 0.50/0.73      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.50/0.73  thf('10', plain,
% 0.50/0.73      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['8', '9'])).
% 0.50/0.73  thf('11', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.50/0.73      inference('sup-', [status(thm)], ['7', '10'])).
% 0.50/0.73  thf('12', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X1)
% 0.50/0.73          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ X2))
% 0.50/0.73          | (r2_hidden @ 
% 0.50/0.73             (k4_tarski @ (sk_F @ k1_xboole_0 @ X2 @ X1) @ 
% 0.50/0.73              (sk_E @ k1_xboole_0 @ X2 @ X1)) @ 
% 0.50/0.73             X2)
% 0.50/0.73          | ~ (v1_relat_1 @ X2)
% 0.50/0.73          | (r2_hidden @ 
% 0.50/0.73             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X2 @ X1) @ 
% 0.50/0.73              (sk_E @ k1_xboole_0 @ X2 @ X1)) @ 
% 0.50/0.73             X0))),
% 0.50/0.73      inference('demod', [status(thm)], ['6', '11'])).
% 0.50/0.73  thf(t152_zfmisc_1, axiom,
% 0.50/0.73    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.50/0.73  thf('13', plain,
% 0.50/0.73      (![X1 : $i, X2 : $i]: ~ (r2_hidden @ X1 @ (k2_zfmisc_1 @ X1 @ X2))),
% 0.50/0.73      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.50/0.73  thf('14', plain,
% 0.50/0.73      (![X1 : $i, X2 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X2)
% 0.50/0.73          | (r2_hidden @ 
% 0.50/0.73             (k4_tarski @ (sk_F @ k1_xboole_0 @ X2 @ X1) @ 
% 0.50/0.73              (sk_E @ k1_xboole_0 @ X2 @ X1)) @ 
% 0.50/0.73             X2)
% 0.50/0.73          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ X2))
% 0.50/0.73          | ~ (v1_relat_1 @ X1))),
% 0.50/0.73      inference('sup-', [status(thm)], ['12', '13'])).
% 0.50/0.73  thf('15', plain,
% 0.50/0.73      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.50/0.73         (~ (r1_tarski @ X10 @ X11)
% 0.50/0.73          | (r2_hidden @ (k4_tarski @ X12 @ X13) @ X11)
% 0.50/0.73          | ~ (r2_hidden @ (k4_tarski @ X12 @ X13) @ X10)
% 0.50/0.73          | ~ (v1_relat_1 @ X10))),
% 0.50/0.73      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.50/0.73  thf('16', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X1)
% 0.50/0.73          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ X0))
% 0.50/0.73          | ~ (v1_relat_1 @ X0)
% 0.50/0.73          | ~ (v1_relat_1 @ X0)
% 0.50/0.73          | (r2_hidden @ 
% 0.50/0.73             (k4_tarski @ (sk_F @ k1_xboole_0 @ X0 @ X1) @ 
% 0.50/0.73              (sk_E @ k1_xboole_0 @ X0 @ X1)) @ 
% 0.50/0.73             X2)
% 0.50/0.73          | ~ (r1_tarski @ X0 @ X2))),
% 0.50/0.73      inference('sup-', [status(thm)], ['14', '15'])).
% 0.50/0.73  thf('17', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.73         (~ (r1_tarski @ X0 @ X2)
% 0.50/0.73          | (r2_hidden @ 
% 0.50/0.73             (k4_tarski @ (sk_F @ k1_xboole_0 @ X0 @ X1) @ 
% 0.50/0.73              (sk_E @ k1_xboole_0 @ X0 @ X1)) @ 
% 0.50/0.73             X2)
% 0.50/0.73          | ~ (v1_relat_1 @ X0)
% 0.50/0.73          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ X0))
% 0.50/0.73          | ~ (v1_relat_1 @ X1))),
% 0.50/0.73      inference('simplify', [status(thm)], ['16'])).
% 0.50/0.73  thf('18', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X1)
% 0.50/0.73          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ k1_xboole_0))
% 0.50/0.73          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.50/0.73          | (r2_hidden @ 
% 0.50/0.73             (k4_tarski @ (sk_F @ k1_xboole_0 @ k1_xboole_0 @ X1) @ 
% 0.50/0.73              (sk_E @ k1_xboole_0 @ k1_xboole_0 @ X1)) @ 
% 0.50/0.73             X0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['0', '17'])).
% 0.50/0.73  thf('19', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.50/0.73      inference('sup-', [status(thm)], ['7', '10'])).
% 0.50/0.73  thf('20', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X1)
% 0.50/0.73          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ k1_xboole_0))
% 0.50/0.73          | (r2_hidden @ 
% 0.50/0.73             (k4_tarski @ (sk_F @ k1_xboole_0 @ k1_xboole_0 @ X1) @ 
% 0.50/0.73              (sk_E @ k1_xboole_0 @ k1_xboole_0 @ X1)) @ 
% 0.50/0.73             X0))),
% 0.50/0.73      inference('demod', [status(thm)], ['18', '19'])).
% 0.50/0.73  thf('21', plain,
% 0.50/0.73      (![X1 : $i, X2 : $i]: ~ (r2_hidden @ X1 @ (k2_zfmisc_1 @ X1 @ X2))),
% 0.50/0.73      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.50/0.73  thf('22', plain,
% 0.50/0.73      (![X1 : $i]:
% 0.50/0.73         (((k1_xboole_0) = (k5_relat_1 @ X1 @ k1_xboole_0))
% 0.50/0.73          | ~ (v1_relat_1 @ X1))),
% 0.50/0.73      inference('sup-', [status(thm)], ['20', '21'])).
% 0.50/0.73  thf('23', plain,
% 0.50/0.73      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.50/0.73        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('24', plain,
% 0.50/0.73      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.50/0.73         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.50/0.73      inference('split', [status(esa)], ['23'])).
% 0.50/0.73  thf('25', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.50/0.73      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.50/0.73  thf('26', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.50/0.73      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.50/0.73  thf('27', plain,
% 0.50/0.73      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X14)
% 0.50/0.73          | (r2_hidden @ 
% 0.50/0.73             (k4_tarski @ (sk_D_1 @ X16 @ X14 @ X15) @ (sk_E @ X16 @ X14 @ X15)) @ 
% 0.50/0.73             X16)
% 0.50/0.73          | (r2_hidden @ 
% 0.50/0.73             (k4_tarski @ (sk_D_1 @ X16 @ X14 @ X15) @ (sk_F @ X16 @ X14 @ X15)) @ 
% 0.50/0.73             X15)
% 0.50/0.73          | ((X16) = (k5_relat_1 @ X15 @ X14))
% 0.50/0.73          | ~ (v1_relat_1 @ X16)
% 0.50/0.73          | ~ (v1_relat_1 @ X15))),
% 0.50/0.73      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.50/0.73  thf('28', plain,
% 0.50/0.73      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.50/0.73         (~ (r1_tarski @ X10 @ X11)
% 0.50/0.73          | (r2_hidden @ (k4_tarski @ X12 @ X13) @ X11)
% 0.50/0.73          | ~ (r2_hidden @ (k4_tarski @ X12 @ X13) @ X10)
% 0.50/0.73          | ~ (v1_relat_1 @ X10))),
% 0.50/0.73      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.50/0.73  thf('29', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X1)
% 0.50/0.73          | ~ (v1_relat_1 @ X0)
% 0.50/0.73          | ((X0) = (k5_relat_1 @ X1 @ X2))
% 0.50/0.73          | (r2_hidden @ 
% 0.50/0.73             (k4_tarski @ (sk_D_1 @ X0 @ X2 @ X1) @ (sk_F @ X0 @ X2 @ X1)) @ X1)
% 0.50/0.73          | ~ (v1_relat_1 @ X2)
% 0.50/0.73          | ~ (v1_relat_1 @ X0)
% 0.50/0.73          | (r2_hidden @ 
% 0.50/0.73             (k4_tarski @ (sk_D_1 @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X3)
% 0.50/0.73          | ~ (r1_tarski @ X0 @ X3))),
% 0.50/0.73      inference('sup-', [status(thm)], ['27', '28'])).
% 0.50/0.73  thf('30', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.50/0.73         (~ (r1_tarski @ X0 @ X3)
% 0.50/0.73          | (r2_hidden @ 
% 0.50/0.73             (k4_tarski @ (sk_D_1 @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X3)
% 0.50/0.73          | ~ (v1_relat_1 @ X2)
% 0.50/0.73          | (r2_hidden @ 
% 0.50/0.73             (k4_tarski @ (sk_D_1 @ X0 @ X2 @ X1) @ (sk_F @ X0 @ X2 @ X1)) @ X1)
% 0.50/0.73          | ((X0) = (k5_relat_1 @ X1 @ X2))
% 0.50/0.73          | ~ (v1_relat_1 @ X0)
% 0.50/0.73          | ~ (v1_relat_1 @ X1))),
% 0.50/0.73      inference('simplify', [status(thm)], ['29'])).
% 0.50/0.73  thf('31', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X1)
% 0.50/0.73          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.50/0.73          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ X2))
% 0.50/0.73          | (r2_hidden @ 
% 0.50/0.73             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X2 @ X1) @ 
% 0.50/0.73              (sk_F @ k1_xboole_0 @ X2 @ X1)) @ 
% 0.50/0.73             X1)
% 0.50/0.73          | ~ (v1_relat_1 @ X2)
% 0.50/0.73          | (r2_hidden @ 
% 0.50/0.73             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X2 @ X1) @ 
% 0.50/0.73              (sk_E @ k1_xboole_0 @ X2 @ X1)) @ 
% 0.50/0.73             X0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['26', '30'])).
% 0.50/0.73  thf('32', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.50/0.73      inference('sup-', [status(thm)], ['7', '10'])).
% 0.50/0.73  thf('33', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X1)
% 0.50/0.73          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ X2))
% 0.50/0.73          | (r2_hidden @ 
% 0.50/0.73             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X2 @ X1) @ 
% 0.50/0.73              (sk_F @ k1_xboole_0 @ X2 @ X1)) @ 
% 0.50/0.73             X1)
% 0.50/0.73          | ~ (v1_relat_1 @ X2)
% 0.50/0.73          | (r2_hidden @ 
% 0.50/0.73             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X2 @ X1) @ 
% 0.50/0.73              (sk_E @ k1_xboole_0 @ X2 @ X1)) @ 
% 0.50/0.73             X0))),
% 0.50/0.73      inference('demod', [status(thm)], ['31', '32'])).
% 0.50/0.73  thf('34', plain,
% 0.50/0.73      (![X1 : $i, X2 : $i]: ~ (r2_hidden @ X1 @ (k2_zfmisc_1 @ X1 @ X2))),
% 0.50/0.73      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.50/0.73  thf('35', plain,
% 0.50/0.73      (![X1 : $i, X2 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X2)
% 0.50/0.73          | (r2_hidden @ 
% 0.50/0.73             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X2 @ X1) @ 
% 0.50/0.73              (sk_F @ k1_xboole_0 @ X2 @ X1)) @ 
% 0.50/0.73             X1)
% 0.50/0.73          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ X2))
% 0.50/0.73          | ~ (v1_relat_1 @ X1))),
% 0.50/0.73      inference('sup-', [status(thm)], ['33', '34'])).
% 0.50/0.73  thf('36', plain,
% 0.50/0.73      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.50/0.73         (~ (r1_tarski @ X10 @ X11)
% 0.50/0.73          | (r2_hidden @ (k4_tarski @ X12 @ X13) @ X11)
% 0.50/0.73          | ~ (r2_hidden @ (k4_tarski @ X12 @ X13) @ X10)
% 0.50/0.73          | ~ (v1_relat_1 @ X10))),
% 0.50/0.73      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.50/0.73  thf('37', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X0)
% 0.50/0.73          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 0.50/0.73          | ~ (v1_relat_1 @ X1)
% 0.50/0.73          | ~ (v1_relat_1 @ X0)
% 0.50/0.73          | (r2_hidden @ 
% 0.50/0.73             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X1 @ X0) @ 
% 0.50/0.73              (sk_F @ k1_xboole_0 @ X1 @ X0)) @ 
% 0.50/0.73             X2)
% 0.50/0.73          | ~ (r1_tarski @ X0 @ X2))),
% 0.50/0.73      inference('sup-', [status(thm)], ['35', '36'])).
% 0.50/0.73  thf('38', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.73         (~ (r1_tarski @ X0 @ X2)
% 0.50/0.73          | (r2_hidden @ 
% 0.50/0.73             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X1 @ X0) @ 
% 0.50/0.73              (sk_F @ k1_xboole_0 @ X1 @ X0)) @ 
% 0.50/0.73             X2)
% 0.50/0.73          | ~ (v1_relat_1 @ X1)
% 0.50/0.73          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 0.50/0.73          | ~ (v1_relat_1 @ X0))),
% 0.50/0.73      inference('simplify', [status(thm)], ['37'])).
% 0.50/0.73  thf('39', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ k1_xboole_0)
% 0.50/0.73          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X1))
% 0.50/0.73          | ~ (v1_relat_1 @ X1)
% 0.50/0.73          | (r2_hidden @ 
% 0.50/0.73             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X1 @ k1_xboole_0) @ 
% 0.50/0.73              (sk_F @ k1_xboole_0 @ X1 @ k1_xboole_0)) @ 
% 0.50/0.73             X0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['25', '38'])).
% 0.50/0.73  thf('40', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.50/0.73      inference('sup-', [status(thm)], ['7', '10'])).
% 0.50/0.73  thf('41', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X1))
% 0.50/0.73          | ~ (v1_relat_1 @ X1)
% 0.50/0.73          | (r2_hidden @ 
% 0.50/0.73             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X1 @ k1_xboole_0) @ 
% 0.50/0.73              (sk_F @ k1_xboole_0 @ X1 @ k1_xboole_0)) @ 
% 0.50/0.73             X0))),
% 0.50/0.73      inference('demod', [status(thm)], ['39', '40'])).
% 0.50/0.73  thf('42', plain,
% 0.50/0.73      (![X1 : $i, X2 : $i]: ~ (r2_hidden @ X1 @ (k2_zfmisc_1 @ X1 @ X2))),
% 0.50/0.73      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.50/0.73  thf('43', plain,
% 0.50/0.73      (![X1 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X1)
% 0.50/0.73          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X1)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['41', '42'])).
% 0.50/0.73  thf('44', plain,
% 0.50/0.73      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.50/0.73         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.50/0.73      inference('split', [status(esa)], ['23'])).
% 0.50/0.73  thf('45', plain,
% 0.50/0.73      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A)))
% 0.50/0.73         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.50/0.73      inference('sup-', [status(thm)], ['43', '44'])).
% 0.50/0.73  thf('46', plain, ((v1_relat_1 @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('47', plain,
% 0.50/0.73      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.50/0.73         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.50/0.73      inference('demod', [status(thm)], ['45', '46'])).
% 0.50/0.73  thf('48', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.50/0.73      inference('simplify', [status(thm)], ['47'])).
% 0.50/0.73  thf('49', plain,
% 0.50/0.73      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.50/0.73       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.50/0.73      inference('split', [status(esa)], ['23'])).
% 0.50/0.73  thf('50', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.50/0.73      inference('sat_resolution*', [status(thm)], ['48', '49'])).
% 0.50/0.73  thf('51', plain, (((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.50/0.73      inference('simpl_trail', [status(thm)], ['24', '50'])).
% 0.50/0.73  thf('52', plain,
% 0.50/0.73      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.50/0.73      inference('sup-', [status(thm)], ['22', '51'])).
% 0.50/0.73  thf('53', plain, ((v1_relat_1 @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('54', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.50/0.73      inference('demod', [status(thm)], ['52', '53'])).
% 0.50/0.73  thf('55', plain, ($false), inference('simplify', [status(thm)], ['54'])).
% 0.50/0.73  
% 0.50/0.73  % SZS output end Refutation
% 0.50/0.73  
% 0.50/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
