%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ae4zuhdN2m

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:59 EST 2020

% Result     : Theorem 0.85s
% Output     : Refutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 593 expanded)
%              Number of leaves         :   21 ( 171 expanded)
%              Depth                    :   25
%              Number of atoms          : 1176 (8708 expanded)
%              Number of equality atoms :  108 ( 799 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t41_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X6 @ X5 ) @ X5 )
      | ( X5
        = ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k11_relat_1 @ X7 @ X8 )
        = ( k9_relat_1 @ X7 @ ( k1_tarski @ X8 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k9_relat_1 @ X12 @ X10 ) )
      | ( r2_hidden @ ( sk_D @ X12 @ X10 @ X11 ) @ X10 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ ( k1_tarski @ X0 ) @ X2 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ ( k1_tarski @ X0 ) @ X2 ) @ ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ ( k1_tarski @ X0 ) @ ( sk_C_1 @ X2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('7',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_D @ X1 @ ( k1_tarski @ X0 ) @ ( sk_C_1 @ X2 @ ( k11_relat_1 @ X1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X6 @ X5 ) @ X5 )
      | ( X5
        = ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k11_relat_1 @ X7 @ X8 )
        = ( k9_relat_1 @ X7 @ ( k1_tarski @ X8 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k9_relat_1 @ X12 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X12 @ X10 @ X11 ) @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ ( k1_tarski @ X0 ) @ X2 ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ ( k1_tarski @ X0 ) @ X2 ) @ X2 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ ( k1_tarski @ X0 ) @ ( sk_C_1 @ X2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ ( sk_C_1 @ X2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C_1 @ X2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C_1 @ X2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X26 @ X28 ) @ X27 )
      | ( X28
        = ( k1_funct_1 @ X27 @ X26 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k11_relat_1 @ X0 @ X1 )
        = ( k1_tarski @ X2 ) )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_C_1 @ X2 @ ( k11_relat_1 @ X0 @ X1 ) )
        = ( k1_funct_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C_1 @ X2 @ ( k11_relat_1 @ X0 @ X1 ) )
        = ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = ( k1_tarski @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( ( sk_C_1 @ X6 @ X5 )
       != X6 )
      | ( X5
        = ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ X1 @ X0 )
       != X2 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t117_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
         => ( ( k11_relat_1 @ B @ A )
            = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t117_funct_1])).

thf('23',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != ( k11_relat_1 @ sk_B @ sk_A ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != ( k11_relat_1 @ sk_B @ sk_A ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X4: $i] :
      ( ( X4
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X4 @ X0 )
        = X0 )
      | ( r2_hidden @ ( sk_C @ X4 @ X0 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ ( k1_tarski @ X0 ) @ X2 ) @ ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ X2 )
        = X2 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ ( k1_tarski @ X0 ) @ ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k11_relat_1 @ X2 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C @ ( k11_relat_1 @ X2 @ X0 ) @ X1 )
        = X1 )
      | ( ( sk_D @ X2 @ ( k1_tarski @ X0 ) @ ( sk_C @ ( k11_relat_1 @ X2 @ X0 ) @ X1 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X4: $i] :
      ( ( X4
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X4 @ X0 )
        = X0 )
      | ( r2_hidden @ ( sk_C @ X4 @ X0 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ ( k1_tarski @ X0 ) @ X2 ) @ X2 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ X2 )
        = X2 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ ( k1_tarski @ X0 ) @ ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X1 )
      | ( ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ X2 )
        = X2 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ X2 )
        = X2 ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ X2 )
        = X2 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ k1_xboole_0 @ X0 ) ) @ sk_B )
      | ( ( sk_C @ ( k11_relat_1 @ sk_B @ sk_A ) @ X0 )
        = X0 )
      | ( ( k11_relat_1 @ sk_B @ sk_A )
        = ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['28','38'])).

thf('40',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['27'])).

thf('41',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['27'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ k1_xboole_0 @ X0 ) ) @ sk_B )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X26 @ X28 ) @ X27 )
      | ( X28
        = ( k1_funct_1 @ X27 @ X26 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ sk_A )
       != X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['48'])).

thf('50',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ( ( sk_C @ k1_xboole_0 @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['27'])).

thf('53',plain,(
    k1_xboole_0
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_C @ k1_xboole_0 @ ( k1_funct_1 @ sk_B @ sk_A ) )
    = ( k1_funct_1 @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i,X4: $i] :
      ( ( X4
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X4 @ X0 )
       != X0 )
      | ~ ( r2_hidden @ ( sk_C @ X4 @ X0 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('56',plain,
    ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ k1_xboole_0 )
    | ( ( sk_C @ k1_xboole_0 @ ( k1_funct_1 @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_B @ sk_A ) )
    | ( k1_xboole_0
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k11_relat_1 @ X7 @ X8 )
        = ( k9_relat_1 @ X7 @ ( k1_tarski @ X8 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('59',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X26 @ ( k1_relat_1 @ X27 ) )
      | ( X28
       != ( k1_funct_1 @ X27 @ X26 ) )
      | ( r2_hidden @ ( k4_tarski @ X26 @ X28 ) @ X27 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('62',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ~ ( v1_funct_1 @ X27 )
      | ( r2_hidden @ ( k4_tarski @ X26 @ ( k1_funct_1 @ X27 @ X26 ) ) @ X27 )
      | ~ ( r2_hidden @ X26 @ ( k1_relat_1 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X11 ) @ X12 )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X12 ) )
      | ( r2_hidden @ X11 @ ( k9_relat_1 @ X12 @ X10 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ X0 ) )
      | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ X0 ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','71'])).

thf('73',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k11_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['57','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k11_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['27'])).

thf('77',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( sk_C @ k1_xboole_0 @ ( k1_funct_1 @ sk_B @ sk_A ) )
    = ( k1_funct_1 @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['50','53'])).

thf('79',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_A )
     != ( k1_funct_1 @ sk_B @ sk_A ) )
    | ( k1_xboole_0
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['56','77','78'])).

thf('80',plain,
    ( k1_xboole_0
    = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    k1_xboole_0
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('82',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['80','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ae4zuhdN2m
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:15:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.85/1.04  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.85/1.04  % Solved by: fo/fo7.sh
% 0.85/1.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.85/1.04  % done 352 iterations in 0.586s
% 0.85/1.04  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.85/1.04  % SZS output start Refutation
% 0.85/1.04  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.85/1.04  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.85/1.04  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.85/1.04  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.85/1.04  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.85/1.04  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.85/1.04  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.85/1.04  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.85/1.04  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.85/1.04  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.85/1.04  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.85/1.04  thf(sk_A_type, type, sk_A: $i).
% 0.85/1.04  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.85/1.04  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.85/1.04  thf(sk_B_type, type, sk_B: $i).
% 0.85/1.04  thf(t41_zfmisc_1, axiom,
% 0.85/1.04    (![A:$i,B:$i]:
% 0.85/1.04     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.85/1.04          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.85/1.04  thf('0', plain,
% 0.85/1.04      (![X5 : $i, X6 : $i]:
% 0.85/1.04         (((X5) = (k1_xboole_0))
% 0.85/1.04          | (r2_hidden @ (sk_C_1 @ X6 @ X5) @ X5)
% 0.85/1.04          | ((X5) = (k1_tarski @ X6)))),
% 0.85/1.04      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.85/1.04  thf(d16_relat_1, axiom,
% 0.85/1.04    (![A:$i]:
% 0.85/1.04     ( ( v1_relat_1 @ A ) =>
% 0.85/1.04       ( ![B:$i]:
% 0.85/1.04         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.85/1.04  thf('1', plain,
% 0.85/1.04      (![X7 : $i, X8 : $i]:
% 0.85/1.04         (((k11_relat_1 @ X7 @ X8) = (k9_relat_1 @ X7 @ (k1_tarski @ X8)))
% 0.85/1.04          | ~ (v1_relat_1 @ X7))),
% 0.85/1.04      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.85/1.04  thf(t143_relat_1, axiom,
% 0.85/1.04    (![A:$i,B:$i,C:$i]:
% 0.85/1.04     ( ( v1_relat_1 @ C ) =>
% 0.85/1.04       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.85/1.04         ( ?[D:$i]:
% 0.85/1.04           ( ( r2_hidden @ D @ B ) & 
% 0.85/1.04             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.85/1.04             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.85/1.04  thf('2', plain,
% 0.85/1.04      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.85/1.04         (~ (r2_hidden @ X11 @ (k9_relat_1 @ X12 @ X10))
% 0.85/1.04          | (r2_hidden @ (sk_D @ X12 @ X10 @ X11) @ X10)
% 0.85/1.04          | ~ (v1_relat_1 @ X12))),
% 0.85/1.04      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.85/1.04  thf('3', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.04         (~ (r2_hidden @ X2 @ (k11_relat_1 @ X1 @ X0))
% 0.85/1.04          | ~ (v1_relat_1 @ X1)
% 0.85/1.04          | ~ (v1_relat_1 @ X1)
% 0.85/1.04          | (r2_hidden @ (sk_D @ X1 @ (k1_tarski @ X0) @ X2) @ (k1_tarski @ X0)))),
% 0.85/1.04      inference('sup-', [status(thm)], ['1', '2'])).
% 0.85/1.04  thf('4', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.04         ((r2_hidden @ (sk_D @ X1 @ (k1_tarski @ X0) @ X2) @ (k1_tarski @ X0))
% 0.85/1.04          | ~ (v1_relat_1 @ X1)
% 0.85/1.04          | ~ (r2_hidden @ X2 @ (k11_relat_1 @ X1 @ X0)))),
% 0.85/1.04      inference('simplify', [status(thm)], ['3'])).
% 0.85/1.04  thf('5', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.04         (((k11_relat_1 @ X1 @ X0) = (k1_tarski @ X2))
% 0.85/1.04          | ((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.85/1.04          | ~ (v1_relat_1 @ X1)
% 0.85/1.04          | (r2_hidden @ 
% 0.85/1.04             (sk_D @ X1 @ (k1_tarski @ X0) @ 
% 0.85/1.04              (sk_C_1 @ X2 @ (k11_relat_1 @ X1 @ X0))) @ 
% 0.85/1.04             (k1_tarski @ X0)))),
% 0.85/1.04      inference('sup-', [status(thm)], ['0', '4'])).
% 0.85/1.04  thf(d1_tarski, axiom,
% 0.85/1.04    (![A:$i,B:$i]:
% 0.85/1.04     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.85/1.04       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.85/1.04  thf('6', plain,
% 0.85/1.04      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.85/1.04         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.85/1.04      inference('cnf', [status(esa)], [d1_tarski])).
% 0.85/1.04  thf('7', plain,
% 0.85/1.04      (![X0 : $i, X3 : $i]:
% 0.85/1.04         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.85/1.04      inference('simplify', [status(thm)], ['6'])).
% 0.85/1.04  thf('8', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.04         (~ (v1_relat_1 @ X1)
% 0.85/1.04          | ((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.85/1.04          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ X2))
% 0.85/1.04          | ((sk_D @ X1 @ (k1_tarski @ X0) @ 
% 0.85/1.04              (sk_C_1 @ X2 @ (k11_relat_1 @ X1 @ X0))) = (X0)))),
% 0.85/1.04      inference('sup-', [status(thm)], ['5', '7'])).
% 0.85/1.04  thf('9', plain,
% 0.85/1.04      (![X5 : $i, X6 : $i]:
% 0.85/1.04         (((X5) = (k1_xboole_0))
% 0.85/1.04          | (r2_hidden @ (sk_C_1 @ X6 @ X5) @ X5)
% 0.85/1.04          | ((X5) = (k1_tarski @ X6)))),
% 0.85/1.04      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.85/1.04  thf('10', plain,
% 0.85/1.04      (![X7 : $i, X8 : $i]:
% 0.85/1.04         (((k11_relat_1 @ X7 @ X8) = (k9_relat_1 @ X7 @ (k1_tarski @ X8)))
% 0.85/1.04          | ~ (v1_relat_1 @ X7))),
% 0.85/1.04      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.85/1.04  thf('11', plain,
% 0.85/1.04      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.85/1.04         (~ (r2_hidden @ X11 @ (k9_relat_1 @ X12 @ X10))
% 0.85/1.04          | (r2_hidden @ (k4_tarski @ (sk_D @ X12 @ X10 @ X11) @ X11) @ X12)
% 0.85/1.04          | ~ (v1_relat_1 @ X12))),
% 0.85/1.04      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.85/1.04  thf('12', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.04         (~ (r2_hidden @ X2 @ (k11_relat_1 @ X1 @ X0))
% 0.85/1.04          | ~ (v1_relat_1 @ X1)
% 0.85/1.04          | ~ (v1_relat_1 @ X1)
% 0.85/1.04          | (r2_hidden @ 
% 0.85/1.04             (k4_tarski @ (sk_D @ X1 @ (k1_tarski @ X0) @ X2) @ X2) @ X1))),
% 0.85/1.04      inference('sup-', [status(thm)], ['10', '11'])).
% 0.85/1.04  thf('13', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.04         ((r2_hidden @ 
% 0.85/1.04           (k4_tarski @ (sk_D @ X1 @ (k1_tarski @ X0) @ X2) @ X2) @ X1)
% 0.85/1.04          | ~ (v1_relat_1 @ X1)
% 0.85/1.04          | ~ (r2_hidden @ X2 @ (k11_relat_1 @ X1 @ X0)))),
% 0.85/1.04      inference('simplify', [status(thm)], ['12'])).
% 0.85/1.04  thf('14', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.04         (((k11_relat_1 @ X1 @ X0) = (k1_tarski @ X2))
% 0.85/1.04          | ((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.85/1.04          | ~ (v1_relat_1 @ X1)
% 0.85/1.04          | (r2_hidden @ 
% 0.85/1.04             (k4_tarski @ 
% 0.85/1.04              (sk_D @ X1 @ (k1_tarski @ X0) @ 
% 0.85/1.04               (sk_C_1 @ X2 @ (k11_relat_1 @ X1 @ X0))) @ 
% 0.85/1.04              (sk_C_1 @ X2 @ (k11_relat_1 @ X1 @ X0))) @ 
% 0.85/1.04             X1))),
% 0.85/1.04      inference('sup-', [status(thm)], ['9', '13'])).
% 0.85/1.04  thf('15', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.04         ((r2_hidden @ 
% 0.85/1.04           (k4_tarski @ X0 @ (sk_C_1 @ X2 @ (k11_relat_1 @ X1 @ X0))) @ X1)
% 0.85/1.04          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ X2))
% 0.85/1.04          | ((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.85/1.04          | ~ (v1_relat_1 @ X1)
% 0.85/1.04          | ~ (v1_relat_1 @ X1)
% 0.85/1.04          | ((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.85/1.04          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ X2)))),
% 0.85/1.04      inference('sup+', [status(thm)], ['8', '14'])).
% 0.85/1.04  thf('16', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.04         (~ (v1_relat_1 @ X1)
% 0.85/1.04          | ((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.85/1.04          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ X2))
% 0.85/1.04          | (r2_hidden @ 
% 0.85/1.04             (k4_tarski @ X0 @ (sk_C_1 @ X2 @ (k11_relat_1 @ X1 @ X0))) @ X1))),
% 0.85/1.04      inference('simplify', [status(thm)], ['15'])).
% 0.85/1.04  thf(t8_funct_1, axiom,
% 0.85/1.04    (![A:$i,B:$i,C:$i]:
% 0.85/1.04     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.85/1.04       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.85/1.04         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.85/1.04           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.85/1.04  thf('17', plain,
% 0.85/1.04      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.85/1.04         (~ (r2_hidden @ (k4_tarski @ X26 @ X28) @ X27)
% 0.85/1.04          | ((X28) = (k1_funct_1 @ X27 @ X26))
% 0.85/1.04          | ~ (v1_funct_1 @ X27)
% 0.85/1.04          | ~ (v1_relat_1 @ X27))),
% 0.85/1.04      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.85/1.04  thf('18', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.04         (((k11_relat_1 @ X0 @ X1) = (k1_tarski @ X2))
% 0.85/1.04          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.85/1.04          | ~ (v1_relat_1 @ X0)
% 0.85/1.04          | ~ (v1_relat_1 @ X0)
% 0.85/1.04          | ~ (v1_funct_1 @ X0)
% 0.85/1.04          | ((sk_C_1 @ X2 @ (k11_relat_1 @ X0 @ X1)) = (k1_funct_1 @ X0 @ X1)))),
% 0.85/1.04      inference('sup-', [status(thm)], ['16', '17'])).
% 0.85/1.04  thf('19', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.04         (((sk_C_1 @ X2 @ (k11_relat_1 @ X0 @ X1)) = (k1_funct_1 @ X0 @ X1))
% 0.85/1.04          | ~ (v1_funct_1 @ X0)
% 0.85/1.04          | ~ (v1_relat_1 @ X0)
% 0.85/1.04          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.85/1.04          | ((k11_relat_1 @ X0 @ X1) = (k1_tarski @ X2)))),
% 0.85/1.04      inference('simplify', [status(thm)], ['18'])).
% 0.85/1.04  thf('20', plain,
% 0.85/1.04      (![X5 : $i, X6 : $i]:
% 0.85/1.04         (((X5) = (k1_xboole_0))
% 0.85/1.04          | ((sk_C_1 @ X6 @ X5) != (X6))
% 0.85/1.04          | ((X5) = (k1_tarski @ X6)))),
% 0.85/1.04      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.85/1.04  thf('21', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.04         (((k1_funct_1 @ X1 @ X0) != (X2))
% 0.85/1.04          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ X2))
% 0.85/1.04          | ((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.85/1.04          | ~ (v1_relat_1 @ X1)
% 0.85/1.04          | ~ (v1_funct_1 @ X1)
% 0.85/1.04          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ X2))
% 0.85/1.04          | ((k11_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.85/1.04      inference('sup-', [status(thm)], ['19', '20'])).
% 0.85/1.04  thf('22', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]:
% 0.85/1.04         (~ (v1_funct_1 @ X1)
% 0.85/1.04          | ~ (v1_relat_1 @ X1)
% 0.85/1.04          | ((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.85/1.04          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ (k1_funct_1 @ X1 @ X0))))),
% 0.85/1.04      inference('simplify', [status(thm)], ['21'])).
% 0.85/1.04  thf(t117_funct_1, conjecture,
% 0.85/1.04    (![A:$i,B:$i]:
% 0.85/1.04     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.85/1.04       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.85/1.04         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.85/1.04  thf(zf_stmt_0, negated_conjecture,
% 0.85/1.04    (~( ![A:$i,B:$i]:
% 0.85/1.04        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.85/1.04          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.85/1.04            ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 0.85/1.04    inference('cnf.neg', [status(esa)], [t117_funct_1])).
% 0.85/1.04  thf('23', plain,
% 0.85/1.04      (((k11_relat_1 @ sk_B @ sk_A) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('24', plain,
% 0.85/1.04      ((((k11_relat_1 @ sk_B @ sk_A) != (k11_relat_1 @ sk_B @ sk_A))
% 0.85/1.04        | ((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.85/1.04        | ~ (v1_relat_1 @ sk_B)
% 0.85/1.04        | ~ (v1_funct_1 @ sk_B))),
% 0.85/1.04      inference('sup-', [status(thm)], ['22', '23'])).
% 0.85/1.04  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('27', plain,
% 0.85/1.04      ((((k11_relat_1 @ sk_B @ sk_A) != (k11_relat_1 @ sk_B @ sk_A))
% 0.85/1.04        | ((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.85/1.04      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.85/1.04  thf('28', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.85/1.04      inference('simplify', [status(thm)], ['27'])).
% 0.85/1.04  thf('29', plain,
% 0.85/1.04      (![X0 : $i, X4 : $i]:
% 0.85/1.04         (((X4) = (k1_tarski @ X0))
% 0.85/1.04          | ((sk_C @ X4 @ X0) = (X0))
% 0.85/1.04          | (r2_hidden @ (sk_C @ X4 @ X0) @ X4))),
% 0.85/1.04      inference('cnf', [status(esa)], [d1_tarski])).
% 0.85/1.04  thf('30', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.04         ((r2_hidden @ (sk_D @ X1 @ (k1_tarski @ X0) @ X2) @ (k1_tarski @ X0))
% 0.85/1.04          | ~ (v1_relat_1 @ X1)
% 0.85/1.04          | ~ (r2_hidden @ X2 @ (k11_relat_1 @ X1 @ X0)))),
% 0.85/1.04      inference('simplify', [status(thm)], ['3'])).
% 0.85/1.04  thf('31', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.04         (((sk_C @ (k11_relat_1 @ X1 @ X0) @ X2) = (X2))
% 0.85/1.04          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ X2))
% 0.85/1.04          | ~ (v1_relat_1 @ X1)
% 0.85/1.04          | (r2_hidden @ 
% 0.85/1.04             (sk_D @ X1 @ (k1_tarski @ X0) @ 
% 0.85/1.04              (sk_C @ (k11_relat_1 @ X1 @ X0) @ X2)) @ 
% 0.85/1.04             (k1_tarski @ X0)))),
% 0.85/1.04      inference('sup-', [status(thm)], ['29', '30'])).
% 0.85/1.04  thf('32', plain,
% 0.85/1.04      (![X0 : $i, X3 : $i]:
% 0.85/1.04         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.85/1.04      inference('simplify', [status(thm)], ['6'])).
% 0.85/1.04  thf('33', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.04         (~ (v1_relat_1 @ X2)
% 0.85/1.04          | ((k11_relat_1 @ X2 @ X0) = (k1_tarski @ X1))
% 0.85/1.04          | ((sk_C @ (k11_relat_1 @ X2 @ X0) @ X1) = (X1))
% 0.85/1.04          | ((sk_D @ X2 @ (k1_tarski @ X0) @ 
% 0.85/1.04              (sk_C @ (k11_relat_1 @ X2 @ X0) @ X1)) = (X0)))),
% 0.85/1.04      inference('sup-', [status(thm)], ['31', '32'])).
% 0.85/1.04  thf('34', plain,
% 0.85/1.04      (![X0 : $i, X4 : $i]:
% 0.85/1.04         (((X4) = (k1_tarski @ X0))
% 0.85/1.04          | ((sk_C @ X4 @ X0) = (X0))
% 0.85/1.04          | (r2_hidden @ (sk_C @ X4 @ X0) @ X4))),
% 0.85/1.04      inference('cnf', [status(esa)], [d1_tarski])).
% 0.85/1.04  thf('35', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.04         ((r2_hidden @ 
% 0.85/1.04           (k4_tarski @ (sk_D @ X1 @ (k1_tarski @ X0) @ X2) @ X2) @ X1)
% 0.85/1.04          | ~ (v1_relat_1 @ X1)
% 0.85/1.04          | ~ (r2_hidden @ X2 @ (k11_relat_1 @ X1 @ X0)))),
% 0.85/1.04      inference('simplify', [status(thm)], ['12'])).
% 0.85/1.04  thf('36', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.04         (((sk_C @ (k11_relat_1 @ X1 @ X0) @ X2) = (X2))
% 0.85/1.04          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ X2))
% 0.85/1.04          | ~ (v1_relat_1 @ X1)
% 0.85/1.04          | (r2_hidden @ 
% 0.85/1.04             (k4_tarski @ 
% 0.85/1.04              (sk_D @ X1 @ (k1_tarski @ X0) @ 
% 0.85/1.04               (sk_C @ (k11_relat_1 @ X1 @ X0) @ X2)) @ 
% 0.85/1.04              (sk_C @ (k11_relat_1 @ X1 @ X0) @ X2)) @ 
% 0.85/1.04             X1))),
% 0.85/1.04      inference('sup-', [status(thm)], ['34', '35'])).
% 0.85/1.04  thf('37', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.04         ((r2_hidden @ 
% 0.85/1.04           (k4_tarski @ X0 @ (sk_C @ (k11_relat_1 @ X1 @ X0) @ X2)) @ X1)
% 0.85/1.04          | ((sk_C @ (k11_relat_1 @ X1 @ X0) @ X2) = (X2))
% 0.85/1.04          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ X2))
% 0.85/1.04          | ~ (v1_relat_1 @ X1)
% 0.85/1.04          | ~ (v1_relat_1 @ X1)
% 0.85/1.04          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ X2))
% 0.85/1.04          | ((sk_C @ (k11_relat_1 @ X1 @ X0) @ X2) = (X2)))),
% 0.85/1.04      inference('sup+', [status(thm)], ['33', '36'])).
% 0.85/1.04  thf('38', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.04         (~ (v1_relat_1 @ X1)
% 0.85/1.04          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ X2))
% 0.85/1.04          | ((sk_C @ (k11_relat_1 @ X1 @ X0) @ X2) = (X2))
% 0.85/1.04          | (r2_hidden @ 
% 0.85/1.04             (k4_tarski @ X0 @ (sk_C @ (k11_relat_1 @ X1 @ X0) @ X2)) @ X1))),
% 0.85/1.04      inference('simplify', [status(thm)], ['37'])).
% 0.85/1.04  thf('39', plain,
% 0.85/1.04      (![X0 : $i]:
% 0.85/1.04         ((r2_hidden @ (k4_tarski @ sk_A @ (sk_C @ k1_xboole_0 @ X0)) @ sk_B)
% 0.85/1.04          | ((sk_C @ (k11_relat_1 @ sk_B @ sk_A) @ X0) = (X0))
% 0.85/1.04          | ((k11_relat_1 @ sk_B @ sk_A) = (k1_tarski @ X0))
% 0.85/1.04          | ~ (v1_relat_1 @ sk_B))),
% 0.85/1.04      inference('sup+', [status(thm)], ['28', '38'])).
% 0.85/1.04  thf('40', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.85/1.04      inference('simplify', [status(thm)], ['27'])).
% 0.85/1.04  thf('41', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.85/1.04      inference('simplify', [status(thm)], ['27'])).
% 0.85/1.04  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('43', plain,
% 0.85/1.04      (![X0 : $i]:
% 0.85/1.04         ((r2_hidden @ (k4_tarski @ sk_A @ (sk_C @ k1_xboole_0 @ X0)) @ sk_B)
% 0.85/1.04          | ((sk_C @ k1_xboole_0 @ X0) = (X0))
% 0.85/1.04          | ((k1_xboole_0) = (k1_tarski @ X0)))),
% 0.85/1.04      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.85/1.04  thf('44', plain,
% 0.85/1.04      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.85/1.04         (~ (r2_hidden @ (k4_tarski @ X26 @ X28) @ X27)
% 0.85/1.04          | ((X28) = (k1_funct_1 @ X27 @ X26))
% 0.85/1.04          | ~ (v1_funct_1 @ X27)
% 0.85/1.04          | ~ (v1_relat_1 @ X27))),
% 0.85/1.04      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.85/1.04  thf('45', plain,
% 0.85/1.04      (![X0 : $i]:
% 0.85/1.04         (((k1_xboole_0) = (k1_tarski @ X0))
% 0.85/1.04          | ((sk_C @ k1_xboole_0 @ X0) = (X0))
% 0.85/1.04          | ~ (v1_relat_1 @ sk_B)
% 0.85/1.04          | ~ (v1_funct_1 @ sk_B)
% 0.85/1.04          | ((sk_C @ k1_xboole_0 @ X0) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.85/1.04      inference('sup-', [status(thm)], ['43', '44'])).
% 0.85/1.04  thf('46', plain, ((v1_relat_1 @ sk_B)),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('47', plain, ((v1_funct_1 @ sk_B)),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('48', plain,
% 0.85/1.04      (![X0 : $i]:
% 0.85/1.04         (((k1_xboole_0) = (k1_tarski @ X0))
% 0.85/1.04          | ((sk_C @ k1_xboole_0 @ X0) = (X0))
% 0.85/1.04          | ((sk_C @ k1_xboole_0 @ X0) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.85/1.04      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.85/1.04  thf('49', plain,
% 0.85/1.04      (![X0 : $i]:
% 0.85/1.04         (((k1_funct_1 @ sk_B @ sk_A) != (X0))
% 0.85/1.04          | ((sk_C @ k1_xboole_0 @ X0) = (X0))
% 0.85/1.04          | ((k1_xboole_0) = (k1_tarski @ X0)))),
% 0.85/1.04      inference('eq_fact', [status(thm)], ['48'])).
% 0.85/1.04  thf('50', plain,
% 0.85/1.04      ((((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.85/1.04        | ((sk_C @ k1_xboole_0 @ (k1_funct_1 @ sk_B @ sk_A))
% 0.85/1.04            = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.85/1.04      inference('simplify', [status(thm)], ['49'])).
% 0.85/1.04  thf('51', plain,
% 0.85/1.04      (((k11_relat_1 @ sk_B @ sk_A) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('52', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.85/1.04      inference('simplify', [status(thm)], ['27'])).
% 0.85/1.04  thf('53', plain,
% 0.85/1.04      (((k1_xboole_0) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.85/1.04      inference('demod', [status(thm)], ['51', '52'])).
% 0.85/1.04  thf('54', plain,
% 0.85/1.04      (((sk_C @ k1_xboole_0 @ (k1_funct_1 @ sk_B @ sk_A))
% 0.85/1.04         = (k1_funct_1 @ sk_B @ sk_A))),
% 0.85/1.04      inference('simplify_reflect-', [status(thm)], ['50', '53'])).
% 0.85/1.04  thf('55', plain,
% 0.85/1.04      (![X0 : $i, X4 : $i]:
% 0.85/1.04         (((X4) = (k1_tarski @ X0))
% 0.85/1.04          | ((sk_C @ X4 @ X0) != (X0))
% 0.85/1.04          | ~ (r2_hidden @ (sk_C @ X4 @ X0) @ X4))),
% 0.85/1.04      inference('cnf', [status(esa)], [d1_tarski])).
% 0.85/1.04  thf('56', plain,
% 0.85/1.04      ((~ (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ k1_xboole_0)
% 0.85/1.04        | ((sk_C @ k1_xboole_0 @ (k1_funct_1 @ sk_B @ sk_A))
% 0.85/1.04            != (k1_funct_1 @ sk_B @ sk_A))
% 0.85/1.04        | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.85/1.04      inference('sup-', [status(thm)], ['54', '55'])).
% 0.85/1.04  thf('57', plain,
% 0.85/1.04      (![X7 : $i, X8 : $i]:
% 0.85/1.04         (((k11_relat_1 @ X7 @ X8) = (k9_relat_1 @ X7 @ (k1_tarski @ X8)))
% 0.85/1.04          | ~ (v1_relat_1 @ X7))),
% 0.85/1.04      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.85/1.04  thf('58', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.04         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.85/1.04      inference('cnf', [status(esa)], [d1_tarski])).
% 0.85/1.04  thf('59', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.85/1.04      inference('simplify', [status(thm)], ['58'])).
% 0.85/1.04  thf('60', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('61', plain,
% 0.85/1.04      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.85/1.04         (~ (r2_hidden @ X26 @ (k1_relat_1 @ X27))
% 0.85/1.04          | ((X28) != (k1_funct_1 @ X27 @ X26))
% 0.85/1.04          | (r2_hidden @ (k4_tarski @ X26 @ X28) @ X27)
% 0.85/1.04          | ~ (v1_funct_1 @ X27)
% 0.85/1.04          | ~ (v1_relat_1 @ X27))),
% 0.85/1.04      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.85/1.04  thf('62', plain,
% 0.85/1.04      (![X26 : $i, X27 : $i]:
% 0.85/1.04         (~ (v1_relat_1 @ X27)
% 0.85/1.04          | ~ (v1_funct_1 @ X27)
% 0.85/1.04          | (r2_hidden @ (k4_tarski @ X26 @ (k1_funct_1 @ X27 @ X26)) @ X27)
% 0.85/1.04          | ~ (r2_hidden @ X26 @ (k1_relat_1 @ X27)))),
% 0.85/1.04      inference('simplify', [status(thm)], ['61'])).
% 0.85/1.04  thf('63', plain,
% 0.85/1.04      (((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 0.85/1.04        | ~ (v1_funct_1 @ sk_B)
% 0.85/1.04        | ~ (v1_relat_1 @ sk_B))),
% 0.85/1.04      inference('sup-', [status(thm)], ['60', '62'])).
% 0.85/1.04  thf('64', plain, ((v1_funct_1 @ sk_B)),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('65', plain, ((v1_relat_1 @ sk_B)),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('66', plain,
% 0.85/1.04      ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)),
% 0.85/1.04      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.85/1.04  thf('67', plain,
% 0.85/1.04      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.85/1.04         (~ (r2_hidden @ X9 @ X10)
% 0.85/1.04          | ~ (r2_hidden @ (k4_tarski @ X9 @ X11) @ X12)
% 0.85/1.04          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ X12))
% 0.85/1.04          | (r2_hidden @ X11 @ (k9_relat_1 @ X12 @ X10))
% 0.85/1.04          | ~ (v1_relat_1 @ X12))),
% 0.85/1.04      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.85/1.04  thf('68', plain,
% 0.85/1.04      (![X0 : $i]:
% 0.85/1.04         (~ (v1_relat_1 @ sk_B)
% 0.85/1.04          | (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ X0))
% 0.85/1.04          | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))
% 0.85/1.04          | ~ (r2_hidden @ sk_A @ X0))),
% 0.85/1.04      inference('sup-', [status(thm)], ['66', '67'])).
% 0.85/1.04  thf('69', plain, ((v1_relat_1 @ sk_B)),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('70', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('71', plain,
% 0.85/1.04      (![X0 : $i]:
% 0.85/1.04         ((r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ X0))
% 0.85/1.04          | ~ (r2_hidden @ sk_A @ X0))),
% 0.85/1.04      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.85/1.04  thf('72', plain,
% 0.85/1.04      ((r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.85/1.04        (k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.85/1.04      inference('sup-', [status(thm)], ['59', '71'])).
% 0.85/1.04  thf('73', plain,
% 0.85/1.04      (((r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k11_relat_1 @ sk_B @ sk_A))
% 0.85/1.04        | ~ (v1_relat_1 @ sk_B))),
% 0.85/1.04      inference('sup+', [status(thm)], ['57', '72'])).
% 0.85/1.04  thf('74', plain, ((v1_relat_1 @ sk_B)),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('75', plain,
% 0.85/1.04      ((r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k11_relat_1 @ sk_B @ sk_A))),
% 0.85/1.04      inference('demod', [status(thm)], ['73', '74'])).
% 0.85/1.04  thf('76', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.85/1.04      inference('simplify', [status(thm)], ['27'])).
% 0.85/1.04  thf('77', plain, ((r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ k1_xboole_0)),
% 0.85/1.04      inference('demod', [status(thm)], ['75', '76'])).
% 0.85/1.04  thf('78', plain,
% 0.85/1.04      (((sk_C @ k1_xboole_0 @ (k1_funct_1 @ sk_B @ sk_A))
% 0.85/1.04         = (k1_funct_1 @ sk_B @ sk_A))),
% 0.85/1.04      inference('simplify_reflect-', [status(thm)], ['50', '53'])).
% 0.85/1.04  thf('79', plain,
% 0.85/1.04      ((((k1_funct_1 @ sk_B @ sk_A) != (k1_funct_1 @ sk_B @ sk_A))
% 0.85/1.04        | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.85/1.04      inference('demod', [status(thm)], ['56', '77', '78'])).
% 0.85/1.04  thf('80', plain,
% 0.85/1.04      (((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.85/1.04      inference('simplify', [status(thm)], ['79'])).
% 0.85/1.04  thf('81', plain,
% 0.85/1.04      (((k1_xboole_0) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.85/1.04      inference('demod', [status(thm)], ['51', '52'])).
% 0.85/1.04  thf('82', plain, ($false),
% 0.85/1.04      inference('simplify_reflect-', [status(thm)], ['80', '81'])).
% 0.85/1.04  
% 0.85/1.04  % SZS output end Refutation
% 0.85/1.04  
% 0.85/1.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
