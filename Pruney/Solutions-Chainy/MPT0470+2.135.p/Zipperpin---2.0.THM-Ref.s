%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.es2xkalkaw

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 123 expanded)
%              Number of leaves         :   20 (  44 expanded)
%              Depth                    :   19
%              Number of atoms          :  859 (1262 expanded)
%              Number of equality atoms :   46 (  89 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X12 @ X10 @ X11 ) @ ( sk_E @ X12 @ X10 @ X11 ) ) @ X12 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X12 @ X10 @ X11 ) @ ( sk_E @ X12 @ X10 @ X11 ) ) @ X10 )
      | ( X12
        = ( k5_relat_1 @ X11 @ X10 ) )
      | ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
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

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X2 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(fc2_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k4_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_relat_1])).

thf('10',plain,(
    ! [X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

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
    ! [X3: $i,X4: $i] :
      ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X12 @ X10 @ X11 ) @ ( sk_E @ X12 @ X10 @ X11 ) ) @ X12 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X12 @ X10 @ X11 ) @ ( sk_F @ X12 @ X10 @ X11 ) ) @ X11 )
      | ( X12
        = ( k5_relat_1 @ X11 @ X10 ) )
      | ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('28',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.es2xkalkaw
% 0.13/0.36  % Computer   : n018.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 10:30:57 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.57  % Solved by: fo/fo7.sh
% 0.22/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.57  % done 107 iterations in 0.106s
% 0.22/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.57  % SZS output start Refutation
% 0.22/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.57  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.57  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.22/0.57  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.22/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.57  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.22/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.57  thf('0', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.57  thf('1', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.57  thf(d8_relat_1, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( v1_relat_1 @ A ) =>
% 0.22/0.57       ( ![B:$i]:
% 0.22/0.57         ( ( v1_relat_1 @ B ) =>
% 0.22/0.57           ( ![C:$i]:
% 0.22/0.57             ( ( v1_relat_1 @ C ) =>
% 0.22/0.57               ( ( ( C ) = ( k5_relat_1 @ A @ B ) ) <=>
% 0.22/0.57                 ( ![D:$i,E:$i]:
% 0.22/0.57                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.22/0.57                     ( ?[F:$i]:
% 0.22/0.57                       ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B ) & 
% 0.22/0.57                         ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.57  thf('2', plain,
% 0.22/0.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X10)
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_D_1 @ X12 @ X10 @ X11) @ (sk_E @ X12 @ X10 @ X11)) @ 
% 0.22/0.57             X12)
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_F @ X12 @ X10 @ X11) @ (sk_E @ X12 @ X10 @ X11)) @ 
% 0.22/0.57             X10)
% 0.22/0.57          | ((X12) = (k5_relat_1 @ X11 @ X10))
% 0.22/0.57          | ~ (v1_relat_1 @ X12)
% 0.22/0.57          | ~ (v1_relat_1 @ X11))),
% 0.22/0.57      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.22/0.57  thf(d3_relat_1, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( v1_relat_1 @ A ) =>
% 0.22/0.57       ( ![B:$i]:
% 0.22/0.57         ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.57           ( ![C:$i,D:$i]:
% 0.22/0.57             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.22/0.57               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.22/0.57  thf('3', plain,
% 0.22/0.57      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.57         (~ (r1_tarski @ X6 @ X7)
% 0.22/0.57          | (r2_hidden @ (k4_tarski @ X8 @ X9) @ X7)
% 0.22/0.57          | ~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X6)
% 0.22/0.57          | ~ (v1_relat_1 @ X6))),
% 0.22/0.57      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.22/0.57  thf('4', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X1)
% 0.22/0.57          | ~ (v1_relat_1 @ X0)
% 0.22/0.57          | ((X0) = (k5_relat_1 @ X1 @ X2))
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_F @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X2)
% 0.22/0.57          | ~ (v1_relat_1 @ X2)
% 0.22/0.57          | ~ (v1_relat_1 @ X0)
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_D_1 @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X3)
% 0.22/0.57          | ~ (r1_tarski @ X0 @ X3))),
% 0.22/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.57  thf('5', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.57         (~ (r1_tarski @ X0 @ X3)
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_D_1 @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X3)
% 0.22/0.57          | ~ (v1_relat_1 @ X2)
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_F @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X2)
% 0.22/0.57          | ((X0) = (k5_relat_1 @ X1 @ X2))
% 0.22/0.57          | ~ (v1_relat_1 @ X0)
% 0.22/0.57          | ~ (v1_relat_1 @ X1))),
% 0.22/0.57      inference('simplify', [status(thm)], ['4'])).
% 0.22/0.57  thf('6', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X1)
% 0.22/0.57          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.57          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ X2))
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_F @ k1_xboole_0 @ X2 @ X1) @ 
% 0.22/0.57              (sk_E @ k1_xboole_0 @ X2 @ X1)) @ 
% 0.22/0.57             X2)
% 0.22/0.57          | ~ (v1_relat_1 @ X2)
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X2 @ X1) @ 
% 0.22/0.57              (sk_E @ k1_xboole_0 @ X2 @ X1)) @ 
% 0.22/0.57             X0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['1', '5'])).
% 0.22/0.57  thf(t62_relat_1, conjecture,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( v1_relat_1 @ A ) =>
% 0.22/0.57       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.22/0.57         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.57    (~( ![A:$i]:
% 0.22/0.57        ( ( v1_relat_1 @ A ) =>
% 0.22/0.57          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.22/0.57            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.22/0.57    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.22/0.57  thf('7', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(t46_xboole_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.22/0.57  thf('8', plain,
% 0.22/0.57      (![X1 : $i, X2 : $i]:
% 0.22/0.57         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X2)) = (k1_xboole_0))),
% 0.22/0.57      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.22/0.57  thf(fc2_relat_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ))).
% 0.22/0.57  thf('9', plain,
% 0.22/0.57      (![X18 : $i, X19 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X18) | (v1_relat_1 @ (k4_xboole_0 @ X18 @ X19)))),
% 0.22/0.57      inference('cnf', [status(esa)], [fc2_relat_1])).
% 0.22/0.57  thf('10', plain,
% 0.22/0.57      (![X1 : $i]: ((v1_relat_1 @ k1_xboole_0) | ~ (v1_relat_1 @ X1))),
% 0.22/0.57      inference('sup+', [status(thm)], ['8', '9'])).
% 0.22/0.57  thf('11', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.57      inference('sup-', [status(thm)], ['7', '10'])).
% 0.22/0.57  thf('12', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X1)
% 0.22/0.57          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ X2))
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_F @ k1_xboole_0 @ X2 @ X1) @ 
% 0.22/0.57              (sk_E @ k1_xboole_0 @ X2 @ X1)) @ 
% 0.22/0.57             X2)
% 0.22/0.57          | ~ (v1_relat_1 @ X2)
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X2 @ X1) @ 
% 0.22/0.57              (sk_E @ k1_xboole_0 @ X2 @ X1)) @ 
% 0.22/0.57             X0))),
% 0.22/0.57      inference('demod', [status(thm)], ['6', '11'])).
% 0.22/0.57  thf(t152_zfmisc_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.22/0.57  thf('13', plain,
% 0.22/0.57      (![X3 : $i, X4 : $i]: ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.22/0.57      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.22/0.57  thf('14', plain,
% 0.22/0.57      (![X1 : $i, X2 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X2)
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_F @ k1_xboole_0 @ X2 @ X1) @ 
% 0.22/0.57              (sk_E @ k1_xboole_0 @ X2 @ X1)) @ 
% 0.22/0.57             X2)
% 0.22/0.57          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ X2))
% 0.22/0.57          | ~ (v1_relat_1 @ X1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.57  thf('15', plain,
% 0.22/0.57      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.57         (~ (r1_tarski @ X6 @ X7)
% 0.22/0.57          | (r2_hidden @ (k4_tarski @ X8 @ X9) @ X7)
% 0.22/0.57          | ~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X6)
% 0.22/0.57          | ~ (v1_relat_1 @ X6))),
% 0.22/0.57      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.22/0.57  thf('16', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X1)
% 0.22/0.57          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ X0))
% 0.22/0.57          | ~ (v1_relat_1 @ X0)
% 0.22/0.57          | ~ (v1_relat_1 @ X0)
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_F @ k1_xboole_0 @ X0 @ X1) @ 
% 0.22/0.57              (sk_E @ k1_xboole_0 @ X0 @ X1)) @ 
% 0.22/0.57             X2)
% 0.22/0.57          | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.57  thf('17', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.57         (~ (r1_tarski @ X0 @ X2)
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_F @ k1_xboole_0 @ X0 @ X1) @ 
% 0.22/0.57              (sk_E @ k1_xboole_0 @ X0 @ X1)) @ 
% 0.22/0.57             X2)
% 0.22/0.57          | ~ (v1_relat_1 @ X0)
% 0.22/0.57          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ X0))
% 0.22/0.57          | ~ (v1_relat_1 @ X1))),
% 0.22/0.57      inference('simplify', [status(thm)], ['16'])).
% 0.22/0.57  thf('18', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X1)
% 0.22/0.57          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ k1_xboole_0))
% 0.22/0.57          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_F @ k1_xboole_0 @ k1_xboole_0 @ X1) @ 
% 0.22/0.57              (sk_E @ k1_xboole_0 @ k1_xboole_0 @ X1)) @ 
% 0.22/0.57             X0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['0', '17'])).
% 0.22/0.57  thf('19', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.57      inference('sup-', [status(thm)], ['7', '10'])).
% 0.22/0.57  thf('20', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X1)
% 0.22/0.57          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ k1_xboole_0))
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_F @ k1_xboole_0 @ k1_xboole_0 @ X1) @ 
% 0.22/0.57              (sk_E @ k1_xboole_0 @ k1_xboole_0 @ X1)) @ 
% 0.22/0.57             X0))),
% 0.22/0.57      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.57  thf('21', plain,
% 0.22/0.57      (![X3 : $i, X4 : $i]: ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.22/0.57      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.22/0.57  thf('22', plain,
% 0.22/0.57      (![X1 : $i]:
% 0.22/0.57         (((k1_xboole_0) = (k5_relat_1 @ X1 @ k1_xboole_0))
% 0.22/0.57          | ~ (v1_relat_1 @ X1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.57  thf('23', plain,
% 0.22/0.57      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.22/0.57        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('24', plain,
% 0.22/0.57      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.57         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.22/0.57      inference('split', [status(esa)], ['23'])).
% 0.22/0.57  thf('25', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.57  thf('26', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.57  thf('27', plain,
% 0.22/0.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X10)
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_D_1 @ X12 @ X10 @ X11) @ (sk_E @ X12 @ X10 @ X11)) @ 
% 0.22/0.57             X12)
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_D_1 @ X12 @ X10 @ X11) @ (sk_F @ X12 @ X10 @ X11)) @ 
% 0.22/0.57             X11)
% 0.22/0.57          | ((X12) = (k5_relat_1 @ X11 @ X10))
% 0.22/0.57          | ~ (v1_relat_1 @ X12)
% 0.22/0.57          | ~ (v1_relat_1 @ X11))),
% 0.22/0.57      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.22/0.57  thf('28', plain,
% 0.22/0.57      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.57         (~ (r1_tarski @ X6 @ X7)
% 0.22/0.57          | (r2_hidden @ (k4_tarski @ X8 @ X9) @ X7)
% 0.22/0.57          | ~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X6)
% 0.22/0.57          | ~ (v1_relat_1 @ X6))),
% 0.22/0.57      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.22/0.57  thf('29', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X1)
% 0.22/0.57          | ~ (v1_relat_1 @ X0)
% 0.22/0.57          | ((X0) = (k5_relat_1 @ X1 @ X2))
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_D_1 @ X0 @ X2 @ X1) @ (sk_F @ X0 @ X2 @ X1)) @ X1)
% 0.22/0.57          | ~ (v1_relat_1 @ X2)
% 0.22/0.57          | ~ (v1_relat_1 @ X0)
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_D_1 @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X3)
% 0.22/0.57          | ~ (r1_tarski @ X0 @ X3))),
% 0.22/0.57      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.57  thf('30', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.57         (~ (r1_tarski @ X0 @ X3)
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_D_1 @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X3)
% 0.22/0.57          | ~ (v1_relat_1 @ X2)
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_D_1 @ X0 @ X2 @ X1) @ (sk_F @ X0 @ X2 @ X1)) @ X1)
% 0.22/0.57          | ((X0) = (k5_relat_1 @ X1 @ X2))
% 0.22/0.57          | ~ (v1_relat_1 @ X0)
% 0.22/0.57          | ~ (v1_relat_1 @ X1))),
% 0.22/0.57      inference('simplify', [status(thm)], ['29'])).
% 0.22/0.57  thf('31', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X1)
% 0.22/0.57          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.57          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ X2))
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X2 @ X1) @ 
% 0.22/0.57              (sk_F @ k1_xboole_0 @ X2 @ X1)) @ 
% 0.22/0.57             X1)
% 0.22/0.57          | ~ (v1_relat_1 @ X2)
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X2 @ X1) @ 
% 0.22/0.57              (sk_E @ k1_xboole_0 @ X2 @ X1)) @ 
% 0.22/0.57             X0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['26', '30'])).
% 0.22/0.57  thf('32', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.57      inference('sup-', [status(thm)], ['7', '10'])).
% 0.22/0.57  thf('33', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X1)
% 0.22/0.57          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ X2))
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X2 @ X1) @ 
% 0.22/0.57              (sk_F @ k1_xboole_0 @ X2 @ X1)) @ 
% 0.22/0.57             X1)
% 0.22/0.57          | ~ (v1_relat_1 @ X2)
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X2 @ X1) @ 
% 0.22/0.57              (sk_E @ k1_xboole_0 @ X2 @ X1)) @ 
% 0.22/0.57             X0))),
% 0.22/0.57      inference('demod', [status(thm)], ['31', '32'])).
% 0.22/0.57  thf('34', plain,
% 0.22/0.57      (![X3 : $i, X4 : $i]: ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.22/0.57      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.22/0.57  thf('35', plain,
% 0.22/0.57      (![X1 : $i, X2 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X2)
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X2 @ X1) @ 
% 0.22/0.57              (sk_F @ k1_xboole_0 @ X2 @ X1)) @ 
% 0.22/0.57             X1)
% 0.22/0.57          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ X2))
% 0.22/0.57          | ~ (v1_relat_1 @ X1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.57  thf('36', plain,
% 0.22/0.57      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.57         (~ (r1_tarski @ X6 @ X7)
% 0.22/0.57          | (r2_hidden @ (k4_tarski @ X8 @ X9) @ X7)
% 0.22/0.57          | ~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X6)
% 0.22/0.57          | ~ (v1_relat_1 @ X6))),
% 0.22/0.57      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.22/0.57  thf('37', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X0)
% 0.22/0.57          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 0.22/0.57          | ~ (v1_relat_1 @ X1)
% 0.22/0.57          | ~ (v1_relat_1 @ X0)
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X1 @ X0) @ 
% 0.22/0.57              (sk_F @ k1_xboole_0 @ X1 @ X0)) @ 
% 0.22/0.57             X2)
% 0.22/0.57          | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.57      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.57  thf('38', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.57         (~ (r1_tarski @ X0 @ X2)
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X1 @ X0) @ 
% 0.22/0.57              (sk_F @ k1_xboole_0 @ X1 @ X0)) @ 
% 0.22/0.57             X2)
% 0.22/0.57          | ~ (v1_relat_1 @ X1)
% 0.22/0.57          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 0.22/0.57          | ~ (v1_relat_1 @ X0))),
% 0.22/0.57      inference('simplify', [status(thm)], ['37'])).
% 0.22/0.57  thf('39', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.57          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X1))
% 0.22/0.57          | ~ (v1_relat_1 @ X1)
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X1 @ k1_xboole_0) @ 
% 0.22/0.57              (sk_F @ k1_xboole_0 @ X1 @ k1_xboole_0)) @ 
% 0.22/0.57             X0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['25', '38'])).
% 0.22/0.57  thf('40', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.57      inference('sup-', [status(thm)], ['7', '10'])).
% 0.22/0.57  thf('41', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X1))
% 0.22/0.57          | ~ (v1_relat_1 @ X1)
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X1 @ k1_xboole_0) @ 
% 0.22/0.57              (sk_F @ k1_xboole_0 @ X1 @ k1_xboole_0)) @ 
% 0.22/0.57             X0))),
% 0.22/0.57      inference('demod', [status(thm)], ['39', '40'])).
% 0.22/0.57  thf('42', plain,
% 0.22/0.57      (![X3 : $i, X4 : $i]: ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.22/0.57      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.22/0.57  thf('43', plain,
% 0.22/0.57      (![X1 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X1)
% 0.22/0.57          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X1)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.57  thf('44', plain,
% 0.22/0.57      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.22/0.57         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('split', [status(esa)], ['23'])).
% 0.22/0.57  thf('45', plain,
% 0.22/0.57      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A)))
% 0.22/0.57         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.57  thf('46', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('47', plain,
% 0.22/0.57      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.57         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('demod', [status(thm)], ['45', '46'])).
% 0.22/0.57  thf('48', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.57      inference('simplify', [status(thm)], ['47'])).
% 0.22/0.57  thf('49', plain,
% 0.22/0.57      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.22/0.57       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.57      inference('split', [status(esa)], ['23'])).
% 0.22/0.57  thf('50', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.57      inference('sat_resolution*', [status(thm)], ['48', '49'])).
% 0.22/0.57  thf('51', plain, (((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.57      inference('simpl_trail', [status(thm)], ['24', '50'])).
% 0.22/0.57  thf('52', plain,
% 0.22/0.57      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.22/0.57      inference('sup-', [status(thm)], ['22', '51'])).
% 0.22/0.57  thf('53', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('54', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.57      inference('demod', [status(thm)], ['52', '53'])).
% 0.22/0.57  thf('55', plain, ($false), inference('simplify', [status(thm)], ['54'])).
% 0.22/0.57  
% 0.22/0.57  % SZS output end Refutation
% 0.22/0.57  
% 0.22/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
