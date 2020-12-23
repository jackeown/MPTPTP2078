%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QJ2Yq2XBUS

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 463 expanded)
%              Number of leaves         :   20 ( 144 expanded)
%              Depth                    :   22
%              Number of atoms          :  923 (9841 expanded)
%              Number of equality atoms :   82 (1094 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t60_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k1_relat_1 @ A )
                = ( k2_relat_1 @ B ) )
              & ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i,D: $i] :
                  ( ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                    & ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) )
                 => ( ( ( k1_funct_1 @ A @ C )
                      = D )
                  <=> ( ( k1_funct_1 @ B @ D )
                      = C ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ( ( ( v2_funct_1 @ A )
                & ( ( k1_relat_1 @ A )
                  = ( k2_relat_1 @ B ) )
                & ( ( k2_relat_1 @ A )
                  = ( k1_relat_1 @ B ) )
                & ! [C: $i,D: $i] :
                    ( ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                      & ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) )
                   => ( ( ( k1_funct_1 @ A @ C )
                        = D )
                    <=> ( ( k1_funct_1 @ B @ D )
                        = C ) ) ) )
             => ( B
                = ( k2_funct_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t60_funct_1])).

thf('1',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ X1 )
        = ( k4_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_funct_1 @ sk_A )
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('8',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_A )
      = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) )
           => ( A = B ) ) ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X8 = X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X8 ) @ ( k1_relat_1 @ X8 ) )
      | ( ( k1_relat_1 @ X8 )
       != ( k1_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
       != ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ( X1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X1 )
       != ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_A )
       != ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
      | ( sk_B = X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_A )
       != ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_A ) )
      | ( sk_B = X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf('28',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) )
    | ( sk_B
      = ( k4_relat_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ ( k4_relat_1 @ sk_A ) @ sk_B ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','27'])).

thf('29',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('30',plain,(
    ! [X2: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('31',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('36',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ sk_A ) )
    | ( sk_B
      = ( k4_relat_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ ( k4_relat_1 @ sk_A ) @ sk_B ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','34','35'])).

thf('37',plain,
    ( ( r2_hidden @ ( sk_C @ ( k4_relat_1 @ sk_A ) @ sk_B ) @ ( k2_relat_1 @ sk_A ) )
    | ( sk_B
      = ( k4_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('40',plain,(
    sk_B
 != ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    r2_hidden @ ( sk_C @ ( k4_relat_1 @ sk_A ) @ sk_B ) @ ( k2_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['37','40'])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('43',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_relat_1 @ X4 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X4 @ X3 ) @ ( k2_relat_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C @ ( k4_relat_1 @ sk_A ) @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf('49',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ) )).

thf('50',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X5 ) )
      | ( X6
        = ( k1_funct_1 @ ( k2_funct_1 @ X5 ) @ ( k1_funct_1 @ X5 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t56_funct_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( X0
        = ( k1_funct_1 @ ( k2_funct_1 @ sk_A ) @ ( k1_funct_1 @ sk_A @ X0 ) ) )
      | ~ ( v2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('55',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( X0
        = ( k1_funct_1 @ ( k4_relat_1 @ sk_A ) @ ( k1_funct_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['51','52','53','54','55'])).

thf('57',plain,
    ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k4_relat_1 @ sk_A ) @ sk_B ) )
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_A ) @ ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B @ ( sk_C @ ( k4_relat_1 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['48','56'])).

thf('58',plain,(
    r2_hidden @ ( sk_C @ ( k4_relat_1 @ sk_A ) @ sk_B ) @ ( k2_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['37','40'])).

thf('59',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ sk_A ) )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ sk_B ) )
      | ( ( k1_funct_1 @ sk_A @ X9 )
        = X10 )
      | ( ( k1_funct_1 @ sk_B @ X10 )
       != X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X10: $i] :
      ( ( ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B @ X10 ) )
        = X10 )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ X10 ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X10: $i] :
      ( ( ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B @ X10 ) )
        = X10 )
      | ~ ( r2_hidden @ X10 @ ( k2_relat_1 @ sk_A ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ X10 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('65',plain,(
    ! [X10: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k2_relat_1 @ sk_A ) )
      | ( ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B @ X10 ) )
        = X10 ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k1_funct_1 @ sk_A @ ( k1_funct_1 @ sk_B @ ( sk_C @ ( k4_relat_1 @ sk_A ) @ sk_B ) ) )
    = ( sk_C @ ( k4_relat_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['58','65'])).

thf('67',plain,
    ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k4_relat_1 @ sk_A ) @ sk_B ) )
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_A ) @ ( sk_C @ ( k4_relat_1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','66'])).

thf('68',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X8 = X7 )
      | ( ( k1_funct_1 @ X8 @ ( sk_C @ X7 @ X8 ) )
       != ( k1_funct_1 @ X7 @ ( sk_C @ X7 @ X8 ) ) )
      | ( ( k1_relat_1 @ X8 )
       != ( k1_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('69',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k4_relat_1 @ sk_A ) @ sk_B ) )
     != ( k1_funct_1 @ sk_B @ ( sk_C @ ( k4_relat_1 @ sk_A ) @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_relat_1 @ sk_B )
     != ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) ) )
    | ( sk_B
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('74',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('75',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k4_relat_1 @ sk_A ) @ sk_B ) )
     != ( k1_funct_1 @ sk_B @ ( sk_C @ ( k4_relat_1 @ sk_A ) @ sk_B ) ) )
    | ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) ) )
    | ( sk_B
      = ( k4_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70','71','72','73','74'])).

thf('76',plain,
    ( ( sk_B
      = ( k4_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    sk_B
 != ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('78',plain,(
    ( k2_relat_1 @ sk_A )
 != ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','78'])).

thf('80',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('81',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('82',plain,(
    ( k2_relat_1 @ sk_A )
 != ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,(
    $false ),
    inference(simplify,[status(thm)],['82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QJ2Yq2XBUS
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:47:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 107 iterations in 0.063s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.21/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.52  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.52  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.52  thf(t37_relat_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) =>
% 0.21/0.52       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.21/0.52         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k1_relat_1 @ X0) = (k2_relat_1 @ (k4_relat_1 @ X0)))
% 0.21/0.52          | ~ (v1_relat_1 @ X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.21/0.52  thf(t60_funct_1, conjecture,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.52           ( ( ( v2_funct_1 @ A ) & 
% 0.21/0.52               ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ B ) ) & 
% 0.21/0.52               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.21/0.52               ( ![C:$i,D:$i]:
% 0.21/0.52                 ( ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.52                     ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) ) =>
% 0.21/0.52                   ( ( ( k1_funct_1 @ A @ C ) = ( D ) ) <=>
% 0.21/0.52                     ( ( k1_funct_1 @ B @ D ) = ( C ) ) ) ) ) ) =>
% 0.21/0.52             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.52              ( ( ( v2_funct_1 @ A ) & 
% 0.21/0.52                  ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ B ) ) & 
% 0.21/0.52                  ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.21/0.52                  ( ![C:$i,D:$i]:
% 0.21/0.52                    ( ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.52                        ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) ) =>
% 0.21/0.52                      ( ( ( k1_funct_1 @ A @ C ) = ( D ) ) <=>
% 0.21/0.52                        ( ( k1_funct_1 @ B @ D ) = ( C ) ) ) ) ) ) =>
% 0.21/0.52                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t60_funct_1])).
% 0.21/0.52  thf('1', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(d9_funct_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.52       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X1 : $i]:
% 0.21/0.52         (~ (v2_funct_1 @ X1)
% 0.21/0.52          | ((k2_funct_1 @ X1) = (k4_relat_1 @ X1))
% 0.21/0.52          | ~ (v1_funct_1 @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      ((~ (v1_funct_1 @ sk_A)
% 0.21/0.52        | ((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))
% 0.21/0.52        | ~ (v2_funct_1 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.52  thf('4', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('5', plain, ((v2_funct_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('6', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.21/0.52  thf(dt_k2_funct_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.52       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.21/0.52         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X2 : $i]:
% 0.21/0.52         ((v1_relat_1 @ (k2_funct_1 @ X2))
% 0.21/0.52          | ~ (v1_funct_1 @ X2)
% 0.21/0.52          | ~ (v1_relat_1 @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (((v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.21/0.52        | ~ (v1_relat_1 @ sk_A)
% 0.21/0.52        | ~ (v1_funct_1 @ sk_A))),
% 0.21/0.52      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.52  thf('9', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('10', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('11', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k2_relat_1 @ X0) = (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.21/0.52          | ~ (v1_relat_1 @ X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k1_relat_1 @ X0) = (k2_relat_1 @ (k4_relat_1 @ X0)))
% 0.21/0.52          | ~ (v1_relat_1 @ X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k2_relat_1 @ X0) = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.52        | ((k2_relat_1 @ sk_A)
% 0.21/0.52            = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_A)))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['11', '14'])).
% 0.21/0.52  thf('16', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (((k2_relat_1 @ sk_A) = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.52  thf('18', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k1_relat_1 @ X0) = (k2_relat_1 @ (k4_relat_1 @ X0)))
% 0.21/0.52          | ~ (v1_relat_1 @ X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.21/0.52  thf(t9_funct_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.52           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.21/0.52               ( ![C:$i]:
% 0.21/0.52                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 0.21/0.52                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 0.21/0.52             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X7)
% 0.21/0.52          | ~ (v1_funct_1 @ X7)
% 0.21/0.52          | ((X8) = (X7))
% 0.21/0.52          | (r2_hidden @ (sk_C @ X7 @ X8) @ (k1_relat_1 @ X8))
% 0.21/0.52          | ((k1_relat_1 @ X8) != (k1_relat_1 @ X7))
% 0.21/0.52          | ~ (v1_funct_1 @ X8)
% 0.21/0.52          | ~ (v1_relat_1 @ X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [t9_funct_1])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k1_relat_1 @ X1) != (k2_relat_1 @ (k4_relat_1 @ X0)))
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X1)
% 0.21/0.52          | ~ (v1_funct_1 @ X1)
% 0.21/0.52          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k1_relat_1 @ X1))
% 0.21/0.52          | ((X1) = (X0))
% 0.21/0.52          | ~ (v1_funct_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (v1_funct_1 @ X0)
% 0.21/0.52          | ((X1) = (X0))
% 0.21/0.52          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k1_relat_1 @ X1))
% 0.21/0.52          | ~ (v1_funct_1 @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | ((k1_relat_1 @ X1) != (k2_relat_1 @ (k4_relat_1 @ X0))))),
% 0.21/0.52      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k2_relat_1 @ sk_A) != (k2_relat_1 @ (k4_relat_1 @ X0)))
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ sk_B)
% 0.21/0.52          | ~ (v1_funct_1 @ sk_B)
% 0.21/0.52          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.21/0.52          | ((sk_B) = (X0))
% 0.21/0.52          | ~ (v1_funct_1 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['18', '22'])).
% 0.21/0.52  thf('24', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('25', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('26', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k2_relat_1 @ sk_A) != (k2_relat_1 @ (k4_relat_1 @ X0)))
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_A))
% 0.21/0.52          | ((sk_B) = (X0))
% 0.21/0.52          | ~ (v1_funct_1 @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      ((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))
% 0.21/0.52        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_A))
% 0.21/0.52        | ((sk_B) = (k4_relat_1 @ sk_A))
% 0.21/0.52        | (r2_hidden @ (sk_C @ (k4_relat_1 @ sk_A) @ sk_B) @ 
% 0.21/0.52           (k2_relat_1 @ sk_A))
% 0.21/0.52        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['17', '27'])).
% 0.21/0.52  thf('29', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      (![X2 : $i]:
% 0.21/0.52         ((v1_funct_1 @ (k2_funct_1 @ X2))
% 0.21/0.52          | ~ (v1_funct_1 @ X2)
% 0.21/0.52          | ~ (v1_relat_1 @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (((v1_funct_1 @ (k4_relat_1 @ sk_A))
% 0.21/0.52        | ~ (v1_relat_1 @ sk_A)
% 0.21/0.52        | ~ (v1_funct_1 @ sk_A))),
% 0.21/0.52      inference('sup+', [status(thm)], ['29', '30'])).
% 0.21/0.52  thf('32', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('33', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('34', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.21/0.52  thf('35', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      ((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))
% 0.21/0.52        | ((sk_B) = (k4_relat_1 @ sk_A))
% 0.21/0.52        | (r2_hidden @ (sk_C @ (k4_relat_1 @ sk_A) @ sk_B) @ 
% 0.21/0.52           (k2_relat_1 @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['28', '34', '35'])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      (((r2_hidden @ (sk_C @ (k4_relat_1 @ sk_A) @ sk_B) @ (k2_relat_1 @ sk_A))
% 0.21/0.52        | ((sk_B) = (k4_relat_1 @ sk_A)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.52  thf('38', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('39', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.21/0.52  thf('40', plain, (((sk_B) != (k4_relat_1 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      ((r2_hidden @ (sk_C @ (k4_relat_1 @ sk_A) @ sk_B) @ (k2_relat_1 @ sk_A))),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['37', '40'])).
% 0.21/0.52  thf('42', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t12_funct_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.52       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.52         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X3 @ (k1_relat_1 @ X4))
% 0.21/0.52          | (r2_hidden @ (k1_funct_1 @ X4 @ X3) @ (k2_relat_1 @ X4))
% 0.21/0.52          | ~ (v1_funct_1 @ X4)
% 0.21/0.52          | ~ (v1_relat_1 @ X4))),
% 0.21/0.52      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_A))
% 0.21/0.52          | ~ (v1_relat_1 @ sk_B)
% 0.21/0.52          | ~ (v1_funct_1 @ sk_B)
% 0.21/0.52          | (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.52  thf('45', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('46', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_A))
% 0.21/0.52          | (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_B)))),
% 0.21/0.52      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      ((r2_hidden @ 
% 0.21/0.52        (k1_funct_1 @ sk_B @ (sk_C @ (k4_relat_1 @ sk_A) @ sk_B)) @ 
% 0.21/0.52        (k2_relat_1 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['41', '47'])).
% 0.21/0.52  thf('49', plain, (((k1_relat_1 @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t56_funct_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.52       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 0.21/0.52         ( ( ( A ) =
% 0.21/0.52             ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 0.21/0.52           ( ( A ) =
% 0.21/0.52             ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ))).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i]:
% 0.21/0.52         (~ (v2_funct_1 @ X5)
% 0.21/0.52          | ~ (r2_hidden @ X6 @ (k1_relat_1 @ X5))
% 0.21/0.52          | ((X6) = (k1_funct_1 @ (k2_funct_1 @ X5) @ (k1_funct_1 @ X5 @ X6)))
% 0.21/0.52          | ~ (v1_funct_1 @ X5)
% 0.21/0.52          | ~ (v1_relat_1 @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [t56_funct_1])).
% 0.21/0.52  thf('51', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.21/0.52          | ~ (v1_relat_1 @ sk_A)
% 0.21/0.52          | ~ (v1_funct_1 @ sk_A)
% 0.21/0.52          | ((X0)
% 0.21/0.52              = (k1_funct_1 @ (k2_funct_1 @ sk_A) @ (k1_funct_1 @ sk_A @ X0)))
% 0.21/0.52          | ~ (v2_funct_1 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.52  thf('52', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('53', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('54', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.21/0.52  thf('55', plain, ((v2_funct_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('56', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.21/0.52          | ((X0)
% 0.21/0.52              = (k1_funct_1 @ (k4_relat_1 @ sk_A) @ (k1_funct_1 @ sk_A @ X0))))),
% 0.21/0.52      inference('demod', [status(thm)], ['51', '52', '53', '54', '55'])).
% 0.21/0.52  thf('57', plain,
% 0.21/0.52      (((k1_funct_1 @ sk_B @ (sk_C @ (k4_relat_1 @ sk_A) @ sk_B))
% 0.21/0.52         = (k1_funct_1 @ (k4_relat_1 @ sk_A) @ 
% 0.21/0.52            (k1_funct_1 @ sk_A @ 
% 0.21/0.52             (k1_funct_1 @ sk_B @ (sk_C @ (k4_relat_1 @ sk_A) @ sk_B)))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['48', '56'])).
% 0.21/0.52  thf('58', plain,
% 0.21/0.52      ((r2_hidden @ (sk_C @ (k4_relat_1 @ sk_A) @ sk_B) @ (k2_relat_1 @ sk_A))),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['37', '40'])).
% 0.21/0.52  thf('59', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X9 @ (k1_relat_1 @ sk_A))
% 0.21/0.52          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ sk_B))
% 0.21/0.52          | ((k1_funct_1 @ sk_A @ X9) = (X10))
% 0.21/0.52          | ((k1_funct_1 @ sk_B @ X10) != (X9)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('60', plain,
% 0.21/0.52      (![X10 : $i]:
% 0.21/0.52         (((k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B @ X10)) = (X10))
% 0.21/0.52          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ sk_B))
% 0.21/0.52          | ~ (r2_hidden @ (k1_funct_1 @ sk_B @ X10) @ (k1_relat_1 @ sk_A)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['59'])).
% 0.21/0.52  thf('61', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('62', plain, (((k1_relat_1 @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('63', plain,
% 0.21/0.52      (![X10 : $i]:
% 0.21/0.52         (((k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B @ X10)) = (X10))
% 0.21/0.52          | ~ (r2_hidden @ X10 @ (k2_relat_1 @ sk_A))
% 0.21/0.52          | ~ (r2_hidden @ (k1_funct_1 @ sk_B @ X10) @ (k2_relat_1 @ sk_B)))),
% 0.21/0.52      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.21/0.52  thf('64', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_A))
% 0.21/0.52          | (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_B)))),
% 0.21/0.52      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.21/0.52  thf('65', plain,
% 0.21/0.52      (![X10 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X10 @ (k2_relat_1 @ sk_A))
% 0.21/0.52          | ((k1_funct_1 @ sk_A @ (k1_funct_1 @ sk_B @ X10)) = (X10)))),
% 0.21/0.52      inference('clc', [status(thm)], ['63', '64'])).
% 0.21/0.52  thf('66', plain,
% 0.21/0.52      (((k1_funct_1 @ sk_A @ 
% 0.21/0.52         (k1_funct_1 @ sk_B @ (sk_C @ (k4_relat_1 @ sk_A) @ sk_B)))
% 0.21/0.52         = (sk_C @ (k4_relat_1 @ sk_A) @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['58', '65'])).
% 0.21/0.52  thf('67', plain,
% 0.21/0.52      (((k1_funct_1 @ sk_B @ (sk_C @ (k4_relat_1 @ sk_A) @ sk_B))
% 0.21/0.52         = (k1_funct_1 @ (k4_relat_1 @ sk_A) @ 
% 0.21/0.52            (sk_C @ (k4_relat_1 @ sk_A) @ sk_B)))),
% 0.21/0.52      inference('demod', [status(thm)], ['57', '66'])).
% 0.21/0.52  thf('68', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X7)
% 0.21/0.52          | ~ (v1_funct_1 @ X7)
% 0.21/0.52          | ((X8) = (X7))
% 0.21/0.52          | ((k1_funct_1 @ X8 @ (sk_C @ X7 @ X8))
% 0.21/0.52              != (k1_funct_1 @ X7 @ (sk_C @ X7 @ X8)))
% 0.21/0.52          | ((k1_relat_1 @ X8) != (k1_relat_1 @ X7))
% 0.21/0.52          | ~ (v1_funct_1 @ X8)
% 0.21/0.52          | ~ (v1_relat_1 @ X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [t9_funct_1])).
% 0.21/0.52  thf('69', plain,
% 0.21/0.52      ((((k1_funct_1 @ sk_B @ (sk_C @ (k4_relat_1 @ sk_A) @ sk_B))
% 0.21/0.52          != (k1_funct_1 @ sk_B @ (sk_C @ (k4_relat_1 @ sk_A) @ sk_B)))
% 0.21/0.52        | ~ (v1_relat_1 @ sk_B)
% 0.21/0.52        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.52        | ((k1_relat_1 @ sk_B) != (k1_relat_1 @ (k4_relat_1 @ sk_A)))
% 0.21/0.52        | ((sk_B) = (k4_relat_1 @ sk_A))
% 0.21/0.52        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_A))
% 0.21/0.52        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.52  thf('70', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('71', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('72', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('73', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.21/0.52  thf('74', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.52  thf('75', plain,
% 0.21/0.52      ((((k1_funct_1 @ sk_B @ (sk_C @ (k4_relat_1 @ sk_A) @ sk_B))
% 0.21/0.52          != (k1_funct_1 @ sk_B @ (sk_C @ (k4_relat_1 @ sk_A) @ sk_B)))
% 0.21/0.52        | ((k2_relat_1 @ sk_A) != (k1_relat_1 @ (k4_relat_1 @ sk_A)))
% 0.21/0.52        | ((sk_B) = (k4_relat_1 @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['69', '70', '71', '72', '73', '74'])).
% 0.21/0.52  thf('76', plain,
% 0.21/0.52      ((((sk_B) = (k4_relat_1 @ sk_A))
% 0.21/0.52        | ((k2_relat_1 @ sk_A) != (k1_relat_1 @ (k4_relat_1 @ sk_A))))),
% 0.21/0.52      inference('simplify', [status(thm)], ['75'])).
% 0.21/0.52  thf('77', plain, (((sk_B) != (k4_relat_1 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.52  thf('78', plain,
% 0.21/0.52      (((k2_relat_1 @ sk_A) != (k1_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['76', '77'])).
% 0.21/0.52  thf('79', plain,
% 0.21/0.52      ((((k2_relat_1 @ sk_A)
% 0.21/0.52          != (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_A))))
% 0.21/0.52        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['0', '78'])).
% 0.21/0.52  thf('80', plain,
% 0.21/0.52      (((k2_relat_1 @ sk_A) = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.52  thf('81', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.52  thf('82', plain, (((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.21/0.52  thf('83', plain, ($false), inference('simplify', [status(thm)], ['82'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
