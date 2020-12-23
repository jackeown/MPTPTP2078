%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Umr0qSeVWm

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:44 EST 2020

% Result     : Theorem 3.44s
% Output     : Refutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 102 expanded)
%              Number of leaves         :   21 (  41 expanded)
%              Depth                    :   16
%              Number of atoms          :  626 (1028 expanded)
%              Number of equality atoms :   60 ( 116 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ( X10
       != ( k2_relat_1 @ X8 ) )
      | ( X11
        = ( k1_funct_1 @ X8 @ ( sk_D_1 @ X11 @ X8 ) ) )
      | ~ ( r2_hidden @ X11 @ X10 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('3',plain,(
    ! [X8: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k2_relat_1 @ X8 ) )
      | ( X11
        = ( k1_funct_1 @ X8 @ ( sk_D_1 @ X11 @ X8 ) ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(s3_funct_1__e2_24__funct_1,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ! [D: $i] :
          ( ( r2_hidden @ D @ A )
         => ( ( k1_funct_1 @ C @ D )
            = B ) )
      & ( ( k1_relat_1 @ C )
        = A )
      & ( v1_funct_1 @ C )
      & ( v1_relat_1 @ C ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X14 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ( X10
       != ( k2_relat_1 @ X8 ) )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 ) @ ( k1_relat_1 @ X8 ) )
      | ~ ( r2_hidden @ X11 @ X10 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('8',plain,(
    ! [X8: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k2_relat_1 @ X8 ) )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 ) @ ( k1_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X14 @ X15 ) @ X16 )
        = X14 )
      | ~ ( r2_hidden @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X2 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) @ ( sk_D_1 @ ( sk_C @ X3 @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) ) @ ( sk_C_2 @ X2 @ X0 ) ) )
        = X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) @ X3 )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','11'])).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) @ ( sk_D_1 @ ( sk_C @ X3 @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) ) @ ( sk_C_2 @ X2 @ X0 ) ) )
        = X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) @ X3 ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X1 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['4','15'])).

thf('17',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 )
      | ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) ) @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ ( sk_B @ X0 ) @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','23'])).

thf(t18_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( ( A = k1_xboole_0 )
            & ( B != k1_xboole_0 ) )
        & ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ~ ( ( B
                  = ( k1_relat_1 @ C ) )
                & ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ~ ( ( A = k1_xboole_0 )
              & ( B != k1_xboole_0 ) )
          & ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ~ ( ( B
                    = ( k1_relat_1 @ C ) )
                  & ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_funct_1])).

thf('25',plain,(
    ! [X17: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_B @ sk_A ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ ( sk_B @ sk_A ) @ X0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_B @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('28',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('29',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X14 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 != X0 ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['32'])).

thf('35',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X14 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('36',plain,(
    ! [X6: $i] :
      ( ( ( k1_relat_1 @ X6 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X6 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X17: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('43',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('44',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('45',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('46',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X14 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('47',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['42','43','44','45','46'])).

thf('48',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','47'])).

thf('49',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['32'])).

thf('51',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['49','50'])).

thf('52',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['33','51'])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['31','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Umr0qSeVWm
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:57:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.44/3.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.44/3.61  % Solved by: fo/fo7.sh
% 3.44/3.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.44/3.61  % done 2883 iterations in 3.155s
% 3.44/3.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.44/3.61  % SZS output start Refutation
% 3.44/3.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.44/3.61  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 3.44/3.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.44/3.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.44/3.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.44/3.61  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 3.44/3.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.44/3.61  thf(sk_B_type, type, sk_B: $i > $i).
% 3.44/3.61  thf(sk_A_type, type, sk_A: $i).
% 3.44/3.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.44/3.61  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 3.44/3.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.44/3.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.44/3.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.44/3.61  thf(t7_xboole_0, axiom,
% 3.44/3.61    (![A:$i]:
% 3.44/3.61     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 3.44/3.61          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 3.44/3.61  thf('0', plain,
% 3.44/3.61      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 3.44/3.61      inference('cnf', [status(esa)], [t7_xboole_0])).
% 3.44/3.61  thf(d3_tarski, axiom,
% 3.44/3.61    (![A:$i,B:$i]:
% 3.44/3.61     ( ( r1_tarski @ A @ B ) <=>
% 3.44/3.61       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.44/3.61  thf('1', plain,
% 3.44/3.61      (![X1 : $i, X3 : $i]:
% 3.44/3.61         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.44/3.61      inference('cnf', [status(esa)], [d3_tarski])).
% 3.44/3.61  thf(d5_funct_1, axiom,
% 3.44/3.61    (![A:$i]:
% 3.44/3.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.44/3.61       ( ![B:$i]:
% 3.44/3.61         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 3.44/3.61           ( ![C:$i]:
% 3.44/3.61             ( ( r2_hidden @ C @ B ) <=>
% 3.44/3.61               ( ?[D:$i]:
% 3.44/3.61                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 3.44/3.61                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 3.44/3.61  thf('2', plain,
% 3.44/3.61      (![X8 : $i, X10 : $i, X11 : $i]:
% 3.44/3.61         (((X10) != (k2_relat_1 @ X8))
% 3.44/3.61          | ((X11) = (k1_funct_1 @ X8 @ (sk_D_1 @ X11 @ X8)))
% 3.44/3.61          | ~ (r2_hidden @ X11 @ X10)
% 3.44/3.61          | ~ (v1_funct_1 @ X8)
% 3.44/3.61          | ~ (v1_relat_1 @ X8))),
% 3.44/3.61      inference('cnf', [status(esa)], [d5_funct_1])).
% 3.44/3.61  thf('3', plain,
% 3.44/3.61      (![X8 : $i, X11 : $i]:
% 3.44/3.61         (~ (v1_relat_1 @ X8)
% 3.44/3.61          | ~ (v1_funct_1 @ X8)
% 3.44/3.61          | ~ (r2_hidden @ X11 @ (k2_relat_1 @ X8))
% 3.44/3.61          | ((X11) = (k1_funct_1 @ X8 @ (sk_D_1 @ X11 @ X8))))),
% 3.44/3.61      inference('simplify', [status(thm)], ['2'])).
% 3.44/3.61  thf('4', plain,
% 3.44/3.61      (![X0 : $i, X1 : $i]:
% 3.44/3.61         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 3.44/3.61          | ((sk_C @ X1 @ (k2_relat_1 @ X0))
% 3.44/3.61              = (k1_funct_1 @ X0 @ 
% 3.44/3.61                 (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)))
% 3.44/3.61          | ~ (v1_funct_1 @ X0)
% 3.44/3.61          | ~ (v1_relat_1 @ X0))),
% 3.44/3.61      inference('sup-', [status(thm)], ['1', '3'])).
% 3.44/3.61  thf(s3_funct_1__e2_24__funct_1, axiom,
% 3.44/3.61    (![A:$i,B:$i]:
% 3.44/3.61     ( ?[C:$i]:
% 3.44/3.61       ( ( ![D:$i]:
% 3.44/3.61           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 3.44/3.61         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 3.44/3.61         ( v1_relat_1 @ C ) ) ))).
% 3.44/3.61  thf('5', plain,
% 3.44/3.61      (![X14 : $i, X15 : $i]: ((k1_relat_1 @ (sk_C_2 @ X14 @ X15)) = (X15))),
% 3.44/3.61      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 3.44/3.61  thf('6', plain,
% 3.44/3.61      (![X1 : $i, X3 : $i]:
% 3.44/3.61         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.44/3.61      inference('cnf', [status(esa)], [d3_tarski])).
% 3.44/3.61  thf('7', plain,
% 3.44/3.61      (![X8 : $i, X10 : $i, X11 : $i]:
% 3.44/3.61         (((X10) != (k2_relat_1 @ X8))
% 3.44/3.61          | (r2_hidden @ (sk_D_1 @ X11 @ X8) @ (k1_relat_1 @ X8))
% 3.44/3.61          | ~ (r2_hidden @ X11 @ X10)
% 3.44/3.61          | ~ (v1_funct_1 @ X8)
% 3.44/3.61          | ~ (v1_relat_1 @ X8))),
% 3.44/3.61      inference('cnf', [status(esa)], [d5_funct_1])).
% 3.44/3.61  thf('8', plain,
% 3.44/3.61      (![X8 : $i, X11 : $i]:
% 3.44/3.61         (~ (v1_relat_1 @ X8)
% 3.44/3.61          | ~ (v1_funct_1 @ X8)
% 3.44/3.61          | ~ (r2_hidden @ X11 @ (k2_relat_1 @ X8))
% 3.44/3.61          | (r2_hidden @ (sk_D_1 @ X11 @ X8) @ (k1_relat_1 @ X8)))),
% 3.44/3.61      inference('simplify', [status(thm)], ['7'])).
% 3.44/3.61  thf('9', plain,
% 3.44/3.61      (![X0 : $i, X1 : $i]:
% 3.44/3.61         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 3.44/3.61          | (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 3.44/3.61             (k1_relat_1 @ X0))
% 3.44/3.61          | ~ (v1_funct_1 @ X0)
% 3.44/3.61          | ~ (v1_relat_1 @ X0))),
% 3.44/3.61      inference('sup-', [status(thm)], ['6', '8'])).
% 3.44/3.61  thf('10', plain,
% 3.44/3.61      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.44/3.61         (((k1_funct_1 @ (sk_C_2 @ X14 @ X15) @ X16) = (X14))
% 3.44/3.61          | ~ (r2_hidden @ X16 @ X15))),
% 3.44/3.61      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 3.44/3.61  thf('11', plain,
% 3.44/3.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.44/3.61         (~ (v1_relat_1 @ X0)
% 3.44/3.61          | ~ (v1_funct_1 @ X0)
% 3.44/3.61          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 3.44/3.61          | ((k1_funct_1 @ (sk_C_2 @ X2 @ (k1_relat_1 @ X0)) @ 
% 3.44/3.61              (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)) = (X2)))),
% 3.44/3.61      inference('sup-', [status(thm)], ['9', '10'])).
% 3.44/3.61  thf('12', plain,
% 3.44/3.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.44/3.61         (((k1_funct_1 @ (sk_C_2 @ X1 @ X0) @ 
% 3.44/3.61            (sk_D_1 @ (sk_C @ X3 @ (k2_relat_1 @ (sk_C_2 @ X2 @ X0))) @ 
% 3.44/3.61             (sk_C_2 @ X2 @ X0)))
% 3.44/3.61            = (X1))
% 3.44/3.61          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X2 @ X0)) @ X3)
% 3.44/3.61          | ~ (v1_funct_1 @ (sk_C_2 @ X2 @ X0))
% 3.44/3.61          | ~ (v1_relat_1 @ (sk_C_2 @ X2 @ X0)))),
% 3.44/3.61      inference('sup+', [status(thm)], ['5', '11'])).
% 3.44/3.61  thf('13', plain,
% 3.44/3.61      (![X14 : $i, X15 : $i]: (v1_funct_1 @ (sk_C_2 @ X14 @ X15))),
% 3.44/3.61      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 3.44/3.61  thf('14', plain,
% 3.44/3.61      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (sk_C_2 @ X14 @ X15))),
% 3.44/3.61      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 3.44/3.61  thf('15', plain,
% 3.44/3.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.44/3.61         (((k1_funct_1 @ (sk_C_2 @ X1 @ X0) @ 
% 3.44/3.61            (sk_D_1 @ (sk_C @ X3 @ (k2_relat_1 @ (sk_C_2 @ X2 @ X0))) @ 
% 3.44/3.61             (sk_C_2 @ X2 @ X0)))
% 3.44/3.61            = (X1))
% 3.44/3.61          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X2 @ X0)) @ X3))),
% 3.44/3.61      inference('demod', [status(thm)], ['12', '13', '14'])).
% 3.44/3.61  thf('16', plain,
% 3.44/3.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.44/3.61         (((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1))
% 3.44/3.61          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 3.44/3.61          | ~ (v1_funct_1 @ (sk_C_2 @ X1 @ X0))
% 3.44/3.61          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2)
% 3.44/3.61          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2))),
% 3.44/3.61      inference('sup+', [status(thm)], ['4', '15'])).
% 3.44/3.61  thf('17', plain,
% 3.44/3.61      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (sk_C_2 @ X14 @ X15))),
% 3.44/3.61      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 3.44/3.61  thf('18', plain,
% 3.44/3.61      (![X14 : $i, X15 : $i]: (v1_funct_1 @ (sk_C_2 @ X14 @ X15))),
% 3.44/3.61      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 3.44/3.61  thf('19', plain,
% 3.44/3.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.44/3.61         (((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1))
% 3.44/3.61          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2)
% 3.44/3.61          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2))),
% 3.44/3.61      inference('demod', [status(thm)], ['16', '17', '18'])).
% 3.44/3.61  thf('20', plain,
% 3.44/3.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.44/3.61         ((r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2)
% 3.44/3.61          | ((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1)))),
% 3.44/3.61      inference('simplify', [status(thm)], ['19'])).
% 3.44/3.61  thf('21', plain,
% 3.44/3.61      (![X1 : $i, X3 : $i]:
% 3.44/3.61         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 3.44/3.61      inference('cnf', [status(esa)], [d3_tarski])).
% 3.44/3.61  thf('22', plain,
% 3.44/3.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.44/3.61         (~ (r2_hidden @ X0 @ X1)
% 3.44/3.61          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X2)) @ X1)
% 3.44/3.61          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X2)) @ X1))),
% 3.44/3.61      inference('sup-', [status(thm)], ['20', '21'])).
% 3.44/3.61  thf('23', plain,
% 3.44/3.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.44/3.61         ((r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X2)) @ X1)
% 3.44/3.61          | ~ (r2_hidden @ X0 @ X1))),
% 3.44/3.61      inference('simplify', [status(thm)], ['22'])).
% 3.44/3.61  thf('24', plain,
% 3.44/3.61      (![X0 : $i, X1 : $i]:
% 3.44/3.61         (((X0) = (k1_xboole_0))
% 3.44/3.61          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ (sk_B @ X0) @ X1)) @ X0))),
% 3.44/3.61      inference('sup-', [status(thm)], ['0', '23'])).
% 3.44/3.61  thf(t18_funct_1, conjecture,
% 3.44/3.61    (![A:$i,B:$i]:
% 3.44/3.61     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 3.44/3.61          ( ![C:$i]:
% 3.44/3.61            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 3.44/3.61              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 3.44/3.61                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 3.44/3.61  thf(zf_stmt_0, negated_conjecture,
% 3.44/3.61    (~( ![A:$i,B:$i]:
% 3.44/3.61        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 3.44/3.61             ( ![C:$i]:
% 3.44/3.61               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 3.44/3.61                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 3.44/3.61                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 3.44/3.61    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 3.44/3.61  thf('25', plain,
% 3.44/3.61      (![X17 : $i]:
% 3.44/3.61         (~ (r1_tarski @ (k2_relat_1 @ X17) @ sk_A)
% 3.44/3.61          | ((sk_B_1) != (k1_relat_1 @ X17))
% 3.44/3.61          | ~ (v1_funct_1 @ X17)
% 3.44/3.61          | ~ (v1_relat_1 @ X17))),
% 3.44/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.61  thf('26', plain,
% 3.44/3.61      (![X0 : $i]:
% 3.44/3.61         (((sk_A) = (k1_xboole_0))
% 3.44/3.61          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_B @ sk_A) @ X0))
% 3.44/3.61          | ~ (v1_funct_1 @ (sk_C_2 @ (sk_B @ sk_A) @ X0))
% 3.44/3.61          | ((sk_B_1) != (k1_relat_1 @ (sk_C_2 @ (sk_B @ sk_A) @ X0))))),
% 3.44/3.61      inference('sup-', [status(thm)], ['24', '25'])).
% 3.44/3.61  thf('27', plain,
% 3.44/3.61      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (sk_C_2 @ X14 @ X15))),
% 3.44/3.61      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 3.44/3.61  thf('28', plain,
% 3.44/3.61      (![X14 : $i, X15 : $i]: (v1_funct_1 @ (sk_C_2 @ X14 @ X15))),
% 3.44/3.61      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 3.44/3.61  thf('29', plain,
% 3.44/3.61      (![X14 : $i, X15 : $i]: ((k1_relat_1 @ (sk_C_2 @ X14 @ X15)) = (X15))),
% 3.44/3.61      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 3.44/3.61  thf('30', plain,
% 3.44/3.61      (![X0 : $i]: (((sk_A) = (k1_xboole_0)) | ((sk_B_1) != (X0)))),
% 3.44/3.61      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 3.44/3.61  thf('31', plain, (((sk_A) = (k1_xboole_0))),
% 3.44/3.61      inference('simplify', [status(thm)], ['30'])).
% 3.44/3.61  thf('32', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 3.44/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.61  thf('33', plain,
% 3.44/3.61      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 3.44/3.61      inference('split', [status(esa)], ['32'])).
% 3.44/3.61  thf('34', plain,
% 3.44/3.61      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 3.44/3.61      inference('split', [status(esa)], ['32'])).
% 3.44/3.61  thf('35', plain,
% 3.44/3.61      (![X14 : $i, X15 : $i]: ((k1_relat_1 @ (sk_C_2 @ X14 @ X15)) = (X15))),
% 3.44/3.61      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 3.44/3.61  thf(t65_relat_1, axiom,
% 3.44/3.61    (![A:$i]:
% 3.44/3.61     ( ( v1_relat_1 @ A ) =>
% 3.44/3.61       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 3.44/3.61         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 3.44/3.61  thf('36', plain,
% 3.44/3.61      (![X6 : $i]:
% 3.44/3.61         (((k1_relat_1 @ X6) != (k1_xboole_0))
% 3.44/3.61          | ((k2_relat_1 @ X6) = (k1_xboole_0))
% 3.44/3.61          | ~ (v1_relat_1 @ X6))),
% 3.44/3.61      inference('cnf', [status(esa)], [t65_relat_1])).
% 3.44/3.61  thf('37', plain,
% 3.44/3.61      (![X0 : $i, X1 : $i]:
% 3.44/3.61         (((X0) != (k1_xboole_0))
% 3.44/3.61          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 3.44/3.61          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_xboole_0)))),
% 3.44/3.61      inference('sup-', [status(thm)], ['35', '36'])).
% 3.44/3.61  thf('38', plain,
% 3.44/3.61      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (sk_C_2 @ X14 @ X15))),
% 3.44/3.61      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 3.44/3.61  thf('39', plain,
% 3.44/3.61      (![X0 : $i, X1 : $i]:
% 3.44/3.61         (((X0) != (k1_xboole_0))
% 3.44/3.61          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_xboole_0)))),
% 3.44/3.61      inference('demod', [status(thm)], ['37', '38'])).
% 3.44/3.61  thf('40', plain,
% 3.44/3.61      (![X1 : $i]: ((k2_relat_1 @ (sk_C_2 @ X1 @ k1_xboole_0)) = (k1_xboole_0))),
% 3.44/3.61      inference('simplify', [status(thm)], ['39'])).
% 3.44/3.61  thf('41', plain,
% 3.44/3.61      (![X17 : $i]:
% 3.44/3.61         (~ (r1_tarski @ (k2_relat_1 @ X17) @ sk_A)
% 3.44/3.61          | ((sk_B_1) != (k1_relat_1 @ X17))
% 3.44/3.61          | ~ (v1_funct_1 @ X17)
% 3.44/3.61          | ~ (v1_relat_1 @ X17))),
% 3.44/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.61  thf('42', plain,
% 3.44/3.61      (![X0 : $i]:
% 3.44/3.61         (~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 3.44/3.61          | ~ (v1_relat_1 @ (sk_C_2 @ X0 @ k1_xboole_0))
% 3.44/3.61          | ~ (v1_funct_1 @ (sk_C_2 @ X0 @ k1_xboole_0))
% 3.44/3.61          | ((sk_B_1) != (k1_relat_1 @ (sk_C_2 @ X0 @ k1_xboole_0))))),
% 3.44/3.61      inference('sup-', [status(thm)], ['40', '41'])).
% 3.44/3.61  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 3.44/3.61  thf('43', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 3.44/3.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.44/3.61  thf('44', plain,
% 3.44/3.61      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (sk_C_2 @ X14 @ X15))),
% 3.44/3.61      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 3.44/3.61  thf('45', plain,
% 3.44/3.61      (![X14 : $i, X15 : $i]: (v1_funct_1 @ (sk_C_2 @ X14 @ X15))),
% 3.44/3.61      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 3.44/3.61  thf('46', plain,
% 3.44/3.61      (![X14 : $i, X15 : $i]: ((k1_relat_1 @ (sk_C_2 @ X14 @ X15)) = (X15))),
% 3.44/3.61      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 3.44/3.61  thf('47', plain, (((sk_B_1) != (k1_xboole_0))),
% 3.44/3.61      inference('demod', [status(thm)], ['42', '43', '44', '45', '46'])).
% 3.44/3.61  thf('48', plain,
% 3.44/3.61      ((((sk_B_1) != (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 3.44/3.61      inference('sup-', [status(thm)], ['34', '47'])).
% 3.44/3.61  thf('49', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 3.44/3.61      inference('simplify', [status(thm)], ['48'])).
% 3.44/3.61  thf('50', plain,
% 3.44/3.61      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_1) = (k1_xboole_0)))),
% 3.44/3.61      inference('split', [status(esa)], ['32'])).
% 3.44/3.61  thf('51', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 3.44/3.61      inference('sat_resolution*', [status(thm)], ['49', '50'])).
% 3.44/3.61  thf('52', plain, (((sk_A) != (k1_xboole_0))),
% 3.44/3.61      inference('simpl_trail', [status(thm)], ['33', '51'])).
% 3.44/3.61  thf('53', plain, ($false),
% 3.44/3.61      inference('simplify_reflect-', [status(thm)], ['31', '52'])).
% 3.44/3.61  
% 3.44/3.61  % SZS output end Refutation
% 3.44/3.61  
% 3.44/3.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
