%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.39cNEZrdHe

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:41 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 469 expanded)
%              Number of leaves         :   18 ( 141 expanded)
%              Depth                    :   18
%              Number of atoms          :  890 (9816 expanded)
%              Number of equality atoms :   67 (1309 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t156_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ! [D: $i] :
              ( ( ( v1_relat_1 @ D )
                & ( v1_funct_1 @ D ) )
             => ( ( ( A
                    = ( k2_relat_1 @ B ) )
                  & ( ( k1_relat_1 @ C )
                    = A )
                  & ( ( k1_relat_1 @ D )
                    = A )
                  & ( ( k5_relat_1 @ B @ C )
                    = ( k5_relat_1 @ B @ D ) ) )
               => ( C = D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ! [D: $i] :
                ( ( ( v1_relat_1 @ D )
                  & ( v1_funct_1 @ D ) )
               => ( ( ( A
                      = ( k2_relat_1 @ B ) )
                    & ( ( k1_relat_1 @ C )
                      = A )
                    & ( ( k1_relat_1 @ D )
                      = A )
                    & ( ( k5_relat_1 @ B @ C )
                      = ( k5_relat_1 @ B @ D ) ) )
                 => ( C = D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t156_funct_1])).

thf('0',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k1_relat_1 @ sk_D_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( X14 = X13 )
      | ( r2_hidden @ ( sk_C_1 @ X13 @ X14 ) @ ( k1_relat_1 @ X14 ) )
      | ( ( k1_relat_1 @ X14 )
       != ( k1_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D_2 )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) )
      | ( sk_D_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( k1_relat_1 @ sk_D_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_D_2 ) @ sk_A )
      | ( sk_D_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('8',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( sk_D_2 = sk_C_2 )
    | ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( sk_A != sk_A )
    | ( sk_D_2 = sk_C_2 )
    | ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_A )
    | ( sk_D_2 = sk_C_2 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    sk_C_2 != sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('16',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( X3
       != ( k2_relat_1 @ X1 ) )
      | ( X4
        = ( k1_funct_1 @ X1 @ ( sk_D_1 @ X4 @ X1 ) ) )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('17',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X1 ) )
      | ( X4
        = ( k1_funct_1 @ X1 @ ( sk_D_1 @ X4 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0
        = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0
        = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ X0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( sk_C_1 @ sk_C_2 @ sk_D_2 )
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t21_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
          <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
              & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X7 @ X8 ) @ ( k1_relat_1 @ X9 ) )
      | ( r2_hidden @ X8 @ ( k1_relat_1 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ X1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ sk_C_2 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ X1 @ X0 ) @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ sk_C_2 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ~ ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_B ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('34',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( X3
       != ( k2_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ X4 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('36',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ X4 @ X1 ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_B ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['29','30','31','32','41'])).

thf('43',plain,
    ( ( k5_relat_1 @ sk_B @ sk_C_2 )
    = ( k5_relat_1 @ sk_B @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t22_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A )
              = ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) )).

thf('44',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X10 @ X11 ) @ X12 )
        = ( k1_funct_1 @ X11 @ ( k1_funct_1 @ X10 @ X12 ) ) )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ ( k5_relat_1 @ X10 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_C_2 ) ) )
      | ~ ( v1_relat_1 @ sk_D_2 )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_D_2 ) @ X0 )
        = ( k1_funct_1 @ sk_D_2 @ ( k1_funct_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k5_relat_1 @ sk_B @ sk_C_2 )
    = ( k5_relat_1 @ sk_B @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_C_2 ) ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C_2 ) @ X0 )
        = ( k1_funct_1 @ sk_D_2 @ ( k1_funct_1 @ sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['45','46','47','48','49','50'])).

thf('52',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C_2 ) @ ( sk_D_1 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_B ) )
    = ( k1_funct_1 @ sk_D_2 @ ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['42','51'])).

thf('53',plain,
    ( ( sk_C_1 @ sk_C_2 @ sk_D_2 )
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('54',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C_2 ) @ ( sk_D_1 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_B ) )
    = ( k1_funct_1 @ sk_D_2 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_B ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['29','30','31','32','41'])).

thf('56',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X10 @ X11 ) @ X12 )
        = ( k1_funct_1 @ X11 @ ( k1_funct_1 @ X10 @ X12 ) ) )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ ( k5_relat_1 @ X10 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('57',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C_2 ) @ ( sk_D_1 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_B ) )
      = ( k1_funct_1 @ sk_C_2 @ ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( sk_C_1 @ sk_C_2 @ sk_D_2 )
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('61',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C_2 ) @ ( sk_D_1 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_B ) )
    = ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['57','58','59','60','61','62'])).

thf('64',plain,
    ( ( k1_funct_1 @ sk_D_2 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) )
    = ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['54','63'])).

thf('65',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( X14 = X13 )
      | ( ( k1_funct_1 @ X14 @ ( sk_C_1 @ X13 @ X14 ) )
       != ( k1_funct_1 @ X13 @ ( sk_C_1 @ X13 @ X14 ) ) )
      | ( ( k1_relat_1 @ X14 )
       != ( k1_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('66',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) ) )
    | ~ ( v1_relat_1 @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ( ( k1_relat_1 @ sk_D_2 )
     != ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_D_2 = sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k1_relat_1 @ sk_D_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) ) )
    | ( sk_A != sk_A )
    | ( sk_D_2 = sk_C_2 ) ),
    inference(demod,[status(thm)],['66','67','68','69','70','71','72'])).

thf('74',plain,(
    sk_D_2 = sk_C_2 ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    sk_C_2 != sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['74','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.39cNEZrdHe
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:20:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.59/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.76  % Solved by: fo/fo7.sh
% 0.59/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.76  % done 162 iterations in 0.316s
% 0.59/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.76  % SZS output start Refutation
% 0.59/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.59/0.76  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.59/0.76  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.59/0.76  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.59/0.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.59/0.76  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.59/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.76  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.59/0.76  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.59/0.76  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.59/0.76  thf(t156_funct_1, conjecture,
% 0.59/0.76    (![A:$i,B:$i]:
% 0.59/0.76     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.59/0.76       ( ![C:$i]:
% 0.59/0.76         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.59/0.76           ( ![D:$i]:
% 0.59/0.76             ( ( ( v1_relat_1 @ D ) & ( v1_funct_1 @ D ) ) =>
% 0.59/0.76               ( ( ( ( A ) = ( k2_relat_1 @ B ) ) & 
% 0.59/0.76                   ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.59/0.76                   ( ( k1_relat_1 @ D ) = ( A ) ) & 
% 0.59/0.76                   ( ( k5_relat_1 @ B @ C ) = ( k5_relat_1 @ B @ D ) ) ) =>
% 0.59/0.76                 ( ( C ) = ( D ) ) ) ) ) ) ) ))).
% 0.59/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.76    (~( ![A:$i,B:$i]:
% 0.59/0.76        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.59/0.76          ( ![C:$i]:
% 0.59/0.76            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.59/0.76              ( ![D:$i]:
% 0.59/0.76                ( ( ( v1_relat_1 @ D ) & ( v1_funct_1 @ D ) ) =>
% 0.59/0.76                  ( ( ( ( A ) = ( k2_relat_1 @ B ) ) & 
% 0.59/0.76                      ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.59/0.76                      ( ( k1_relat_1 @ D ) = ( A ) ) & 
% 0.59/0.76                      ( ( k5_relat_1 @ B @ C ) = ( k5_relat_1 @ B @ D ) ) ) =>
% 0.59/0.76                    ( ( C ) = ( D ) ) ) ) ) ) ) ) )),
% 0.59/0.76    inference('cnf.neg', [status(esa)], [t156_funct_1])).
% 0.59/0.76  thf('0', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('1', plain, (((k1_relat_1 @ sk_D_2) = (sk_A))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf(t9_funct_1, axiom,
% 0.59/0.76    (![A:$i]:
% 0.59/0.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.59/0.76       ( ![B:$i]:
% 0.59/0.76         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.59/0.76           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.59/0.76               ( ![C:$i]:
% 0.59/0.76                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 0.59/0.76                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 0.59/0.76             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.59/0.76  thf('2', plain,
% 0.59/0.76      (![X13 : $i, X14 : $i]:
% 0.59/0.76         (~ (v1_relat_1 @ X13)
% 0.59/0.76          | ~ (v1_funct_1 @ X13)
% 0.59/0.76          | ((X14) = (X13))
% 0.59/0.76          | (r2_hidden @ (sk_C_1 @ X13 @ X14) @ (k1_relat_1 @ X14))
% 0.59/0.76          | ((k1_relat_1 @ X14) != (k1_relat_1 @ X13))
% 0.59/0.76          | ~ (v1_funct_1 @ X14)
% 0.59/0.76          | ~ (v1_relat_1 @ X14))),
% 0.59/0.76      inference('cnf', [status(esa)], [t9_funct_1])).
% 0.59/0.76  thf('3', plain,
% 0.59/0.76      (![X0 : $i]:
% 0.59/0.76         (((sk_A) != (k1_relat_1 @ X0))
% 0.59/0.76          | ~ (v1_relat_1 @ sk_D_2)
% 0.59/0.76          | ~ (v1_funct_1 @ sk_D_2)
% 0.59/0.76          | (r2_hidden @ (sk_C_1 @ X0 @ sk_D_2) @ (k1_relat_1 @ sk_D_2))
% 0.59/0.76          | ((sk_D_2) = (X0))
% 0.59/0.76          | ~ (v1_funct_1 @ X0)
% 0.59/0.76          | ~ (v1_relat_1 @ X0))),
% 0.59/0.76      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.76  thf('4', plain, ((v1_relat_1 @ sk_D_2)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('5', plain, ((v1_funct_1 @ sk_D_2)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('6', plain, (((k1_relat_1 @ sk_D_2) = (sk_A))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('7', plain,
% 0.59/0.76      (![X0 : $i]:
% 0.59/0.76         (((sk_A) != (k1_relat_1 @ X0))
% 0.59/0.76          | (r2_hidden @ (sk_C_1 @ X0 @ sk_D_2) @ sk_A)
% 0.59/0.76          | ((sk_D_2) = (X0))
% 0.59/0.76          | ~ (v1_funct_1 @ X0)
% 0.59/0.76          | ~ (v1_relat_1 @ X0))),
% 0.59/0.76      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.59/0.76  thf('8', plain,
% 0.59/0.76      ((((sk_A) != (sk_A))
% 0.59/0.76        | ~ (v1_relat_1 @ sk_C_2)
% 0.59/0.76        | ~ (v1_funct_1 @ sk_C_2)
% 0.59/0.76        | ((sk_D_2) = (sk_C_2))
% 0.59/0.76        | (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_A))),
% 0.59/0.76      inference('sup-', [status(thm)], ['0', '7'])).
% 0.59/0.76  thf('9', plain, ((v1_relat_1 @ sk_C_2)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('10', plain, ((v1_funct_1 @ sk_C_2)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('11', plain,
% 0.59/0.76      ((((sk_A) != (sk_A))
% 0.59/0.76        | ((sk_D_2) = (sk_C_2))
% 0.59/0.76        | (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_A))),
% 0.59/0.76      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.59/0.76  thf('12', plain,
% 0.59/0.76      (((r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_A) | ((sk_D_2) = (sk_C_2)))),
% 0.59/0.76      inference('simplify', [status(thm)], ['11'])).
% 0.59/0.76  thf('13', plain, (((sk_C_2) != (sk_D_2))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('14', plain, ((r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_A)),
% 0.59/0.76      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.59/0.76  thf('15', plain, (((sk_A) = (k2_relat_1 @ sk_B))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf(d5_funct_1, axiom,
% 0.59/0.76    (![A:$i]:
% 0.59/0.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.59/0.76       ( ![B:$i]:
% 0.59/0.76         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.59/0.76           ( ![C:$i]:
% 0.59/0.76             ( ( r2_hidden @ C @ B ) <=>
% 0.59/0.76               ( ?[D:$i]:
% 0.59/0.76                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.59/0.76                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.59/0.76  thf('16', plain,
% 0.59/0.76      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.59/0.76         (((X3) != (k2_relat_1 @ X1))
% 0.59/0.76          | ((X4) = (k1_funct_1 @ X1 @ (sk_D_1 @ X4 @ X1)))
% 0.59/0.76          | ~ (r2_hidden @ X4 @ X3)
% 0.59/0.76          | ~ (v1_funct_1 @ X1)
% 0.59/0.76          | ~ (v1_relat_1 @ X1))),
% 0.59/0.76      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.59/0.76  thf('17', plain,
% 0.59/0.76      (![X1 : $i, X4 : $i]:
% 0.59/0.76         (~ (v1_relat_1 @ X1)
% 0.59/0.76          | ~ (v1_funct_1 @ X1)
% 0.59/0.76          | ~ (r2_hidden @ X4 @ (k2_relat_1 @ X1))
% 0.59/0.76          | ((X4) = (k1_funct_1 @ X1 @ (sk_D_1 @ X4 @ X1))))),
% 0.59/0.76      inference('simplify', [status(thm)], ['16'])).
% 0.59/0.76  thf('18', plain,
% 0.59/0.76      (![X0 : $i]:
% 0.59/0.76         (~ (r2_hidden @ X0 @ sk_A)
% 0.59/0.76          | ((X0) = (k1_funct_1 @ sk_B @ (sk_D_1 @ X0 @ sk_B)))
% 0.59/0.76          | ~ (v1_funct_1 @ sk_B)
% 0.59/0.76          | ~ (v1_relat_1 @ sk_B))),
% 0.59/0.76      inference('sup-', [status(thm)], ['15', '17'])).
% 0.59/0.76  thf('19', plain, ((v1_funct_1 @ sk_B)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('21', plain,
% 0.59/0.76      (![X0 : $i]:
% 0.59/0.76         (~ (r2_hidden @ X0 @ sk_A)
% 0.59/0.76          | ((X0) = (k1_funct_1 @ sk_B @ (sk_D_1 @ X0 @ sk_B))))),
% 0.59/0.76      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.59/0.76  thf('22', plain,
% 0.59/0.76      (((sk_C_1 @ sk_C_2 @ sk_D_2)
% 0.59/0.76         = (k1_funct_1 @ sk_B @ (sk_D_1 @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_B)))),
% 0.59/0.76      inference('sup-', [status(thm)], ['14', '21'])).
% 0.59/0.76  thf('23', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf(t21_funct_1, axiom,
% 0.59/0.76    (![A:$i,B:$i]:
% 0.59/0.76     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.59/0.76       ( ![C:$i]:
% 0.59/0.76         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.59/0.76           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) <=>
% 0.59/0.76             ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.59/0.76               ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.59/0.76  thf('24', plain,
% 0.59/0.76      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.59/0.76         (~ (v1_relat_1 @ X7)
% 0.59/0.76          | ~ (v1_funct_1 @ X7)
% 0.59/0.76          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ X7))
% 0.59/0.76          | ~ (r2_hidden @ (k1_funct_1 @ X7 @ X8) @ (k1_relat_1 @ X9))
% 0.59/0.76          | (r2_hidden @ X8 @ (k1_relat_1 @ (k5_relat_1 @ X7 @ X9)))
% 0.59/0.76          | ~ (v1_funct_1 @ X9)
% 0.59/0.76          | ~ (v1_relat_1 @ X9))),
% 0.59/0.76      inference('cnf', [status(esa)], [t21_funct_1])).
% 0.59/0.76  thf('25', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         (~ (r2_hidden @ (k1_funct_1 @ X1 @ X0) @ sk_A)
% 0.59/0.76          | ~ (v1_relat_1 @ sk_C_2)
% 0.59/0.76          | ~ (v1_funct_1 @ sk_C_2)
% 0.59/0.76          | (r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ sk_C_2)))
% 0.59/0.76          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ X1))
% 0.59/0.76          | ~ (v1_funct_1 @ X1)
% 0.59/0.76          | ~ (v1_relat_1 @ X1))),
% 0.59/0.76      inference('sup-', [status(thm)], ['23', '24'])).
% 0.59/0.76  thf('26', plain, ((v1_relat_1 @ sk_C_2)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('27', plain, ((v1_funct_1 @ sk_C_2)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('28', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         (~ (r2_hidden @ (k1_funct_1 @ X1 @ X0) @ sk_A)
% 0.59/0.76          | (r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ sk_C_2)))
% 0.59/0.76          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ X1))
% 0.59/0.76          | ~ (v1_funct_1 @ X1)
% 0.59/0.76          | ~ (v1_relat_1 @ X1))),
% 0.59/0.76      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.59/0.76  thf('29', plain,
% 0.59/0.76      ((~ (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_A)
% 0.59/0.76        | ~ (v1_relat_1 @ sk_B)
% 0.59/0.76        | ~ (v1_funct_1 @ sk_B)
% 0.59/0.76        | ~ (r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_B) @ 
% 0.59/0.76             (k1_relat_1 @ sk_B))
% 0.59/0.76        | (r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_B) @ 
% 0.59/0.76           (k1_relat_1 @ (k5_relat_1 @ sk_B @ sk_C_2))))),
% 0.59/0.76      inference('sup-', [status(thm)], ['22', '28'])).
% 0.59/0.76  thf('30', plain, ((r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_A)),
% 0.59/0.76      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.59/0.76  thf('31', plain, ((v1_relat_1 @ sk_B)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('32', plain, ((v1_funct_1 @ sk_B)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('33', plain, ((r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_A)),
% 0.59/0.76      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.59/0.76  thf('34', plain, (((sk_A) = (k2_relat_1 @ sk_B))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('35', plain,
% 0.59/0.76      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.59/0.76         (((X3) != (k2_relat_1 @ X1))
% 0.59/0.76          | (r2_hidden @ (sk_D_1 @ X4 @ X1) @ (k1_relat_1 @ X1))
% 0.59/0.76          | ~ (r2_hidden @ X4 @ X3)
% 0.59/0.76          | ~ (v1_funct_1 @ X1)
% 0.59/0.76          | ~ (v1_relat_1 @ X1))),
% 0.59/0.76      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.59/0.76  thf('36', plain,
% 0.59/0.76      (![X1 : $i, X4 : $i]:
% 0.59/0.76         (~ (v1_relat_1 @ X1)
% 0.59/0.76          | ~ (v1_funct_1 @ X1)
% 0.59/0.76          | ~ (r2_hidden @ X4 @ (k2_relat_1 @ X1))
% 0.59/0.76          | (r2_hidden @ (sk_D_1 @ X4 @ X1) @ (k1_relat_1 @ X1)))),
% 0.59/0.76      inference('simplify', [status(thm)], ['35'])).
% 0.59/0.76  thf('37', plain,
% 0.59/0.76      (![X0 : $i]:
% 0.59/0.76         (~ (r2_hidden @ X0 @ sk_A)
% 0.59/0.76          | (r2_hidden @ (sk_D_1 @ X0 @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.59/0.76          | ~ (v1_funct_1 @ sk_B)
% 0.59/0.76          | ~ (v1_relat_1 @ sk_B))),
% 0.59/0.76      inference('sup-', [status(thm)], ['34', '36'])).
% 0.59/0.76  thf('38', plain, ((v1_funct_1 @ sk_B)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('40', plain,
% 0.59/0.76      (![X0 : $i]:
% 0.59/0.76         (~ (r2_hidden @ X0 @ sk_A)
% 0.59/0.76          | (r2_hidden @ (sk_D_1 @ X0 @ sk_B) @ (k1_relat_1 @ sk_B)))),
% 0.59/0.76      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.59/0.76  thf('41', plain,
% 0.59/0.76      ((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_B) @ 
% 0.59/0.76        (k1_relat_1 @ sk_B))),
% 0.59/0.76      inference('sup-', [status(thm)], ['33', '40'])).
% 0.59/0.76  thf('42', plain,
% 0.59/0.76      ((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_B) @ 
% 0.59/0.76        (k1_relat_1 @ (k5_relat_1 @ sk_B @ sk_C_2)))),
% 0.59/0.76      inference('demod', [status(thm)], ['29', '30', '31', '32', '41'])).
% 0.59/0.76  thf('43', plain,
% 0.59/0.76      (((k5_relat_1 @ sk_B @ sk_C_2) = (k5_relat_1 @ sk_B @ sk_D_2))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf(t22_funct_1, axiom,
% 0.59/0.76    (![A:$i,B:$i]:
% 0.59/0.76     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.59/0.76       ( ![C:$i]:
% 0.59/0.76         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.59/0.76           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.59/0.76             ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A ) =
% 0.59/0.76               ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) ))).
% 0.59/0.76  thf('44', plain,
% 0.59/0.76      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.59/0.76         (~ (v1_relat_1 @ X10)
% 0.59/0.76          | ~ (v1_funct_1 @ X10)
% 0.59/0.76          | ((k1_funct_1 @ (k5_relat_1 @ X10 @ X11) @ X12)
% 0.59/0.76              = (k1_funct_1 @ X11 @ (k1_funct_1 @ X10 @ X12)))
% 0.59/0.76          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ (k5_relat_1 @ X10 @ X11)))
% 0.59/0.76          | ~ (v1_funct_1 @ X11)
% 0.59/0.76          | ~ (v1_relat_1 @ X11))),
% 0.59/0.76      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.59/0.76  thf('45', plain,
% 0.59/0.76      (![X0 : $i]:
% 0.59/0.76         (~ (r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_B @ sk_C_2)))
% 0.59/0.76          | ~ (v1_relat_1 @ sk_D_2)
% 0.59/0.76          | ~ (v1_funct_1 @ sk_D_2)
% 0.59/0.76          | ((k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_D_2) @ X0)
% 0.59/0.76              = (k1_funct_1 @ sk_D_2 @ (k1_funct_1 @ sk_B @ X0)))
% 0.59/0.76          | ~ (v1_funct_1 @ sk_B)
% 0.59/0.76          | ~ (v1_relat_1 @ sk_B))),
% 0.59/0.76      inference('sup-', [status(thm)], ['43', '44'])).
% 0.59/0.76  thf('46', plain, ((v1_relat_1 @ sk_D_2)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('47', plain, ((v1_funct_1 @ sk_D_2)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('48', plain,
% 0.59/0.76      (((k5_relat_1 @ sk_B @ sk_C_2) = (k5_relat_1 @ sk_B @ sk_D_2))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('49', plain, ((v1_funct_1 @ sk_B)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('50', plain, ((v1_relat_1 @ sk_B)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('51', plain,
% 0.59/0.76      (![X0 : $i]:
% 0.59/0.76         (~ (r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_B @ sk_C_2)))
% 0.59/0.76          | ((k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C_2) @ X0)
% 0.59/0.76              = (k1_funct_1 @ sk_D_2 @ (k1_funct_1 @ sk_B @ X0))))),
% 0.59/0.76      inference('demod', [status(thm)], ['45', '46', '47', '48', '49', '50'])).
% 0.59/0.76  thf('52', plain,
% 0.59/0.76      (((k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C_2) @ 
% 0.59/0.76         (sk_D_1 @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_B))
% 0.59/0.76         = (k1_funct_1 @ sk_D_2 @ 
% 0.59/0.76            (k1_funct_1 @ sk_B @ (sk_D_1 @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_B))))),
% 0.59/0.76      inference('sup-', [status(thm)], ['42', '51'])).
% 0.59/0.76  thf('53', plain,
% 0.59/0.76      (((sk_C_1 @ sk_C_2 @ sk_D_2)
% 0.59/0.76         = (k1_funct_1 @ sk_B @ (sk_D_1 @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_B)))),
% 0.59/0.76      inference('sup-', [status(thm)], ['14', '21'])).
% 0.59/0.76  thf('54', plain,
% 0.59/0.76      (((k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C_2) @ 
% 0.59/0.76         (sk_D_1 @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_B))
% 0.59/0.76         = (k1_funct_1 @ sk_D_2 @ (sk_C_1 @ sk_C_2 @ sk_D_2)))),
% 0.59/0.76      inference('demod', [status(thm)], ['52', '53'])).
% 0.59/0.76  thf('55', plain,
% 0.59/0.76      ((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_B) @ 
% 0.59/0.76        (k1_relat_1 @ (k5_relat_1 @ sk_B @ sk_C_2)))),
% 0.59/0.76      inference('demod', [status(thm)], ['29', '30', '31', '32', '41'])).
% 0.59/0.76  thf('56', plain,
% 0.59/0.76      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.59/0.76         (~ (v1_relat_1 @ X10)
% 0.59/0.76          | ~ (v1_funct_1 @ X10)
% 0.59/0.76          | ((k1_funct_1 @ (k5_relat_1 @ X10 @ X11) @ X12)
% 0.59/0.76              = (k1_funct_1 @ X11 @ (k1_funct_1 @ X10 @ X12)))
% 0.59/0.76          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ (k5_relat_1 @ X10 @ X11)))
% 0.59/0.76          | ~ (v1_funct_1 @ X11)
% 0.59/0.76          | ~ (v1_relat_1 @ X11))),
% 0.59/0.76      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.59/0.76  thf('57', plain,
% 0.59/0.76      ((~ (v1_relat_1 @ sk_C_2)
% 0.59/0.76        | ~ (v1_funct_1 @ sk_C_2)
% 0.59/0.76        | ((k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C_2) @ 
% 0.59/0.76            (sk_D_1 @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_B))
% 0.59/0.76            = (k1_funct_1 @ sk_C_2 @ 
% 0.59/0.76               (k1_funct_1 @ sk_B @ 
% 0.59/0.76                (sk_D_1 @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_B))))
% 0.59/0.76        | ~ (v1_funct_1 @ sk_B)
% 0.59/0.76        | ~ (v1_relat_1 @ sk_B))),
% 0.59/0.76      inference('sup-', [status(thm)], ['55', '56'])).
% 0.59/0.76  thf('58', plain, ((v1_relat_1 @ sk_C_2)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('59', plain, ((v1_funct_1 @ sk_C_2)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('60', plain,
% 0.59/0.76      (((sk_C_1 @ sk_C_2 @ sk_D_2)
% 0.59/0.76         = (k1_funct_1 @ sk_B @ (sk_D_1 @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_B)))),
% 0.59/0.76      inference('sup-', [status(thm)], ['14', '21'])).
% 0.59/0.76  thf('61', plain, ((v1_funct_1 @ sk_B)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('62', plain, ((v1_relat_1 @ sk_B)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('63', plain,
% 0.59/0.76      (((k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C_2) @ 
% 0.59/0.76         (sk_D_1 @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_B))
% 0.59/0.76         = (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_D_2)))),
% 0.59/0.76      inference('demod', [status(thm)], ['57', '58', '59', '60', '61', '62'])).
% 0.59/0.76  thf('64', plain,
% 0.59/0.76      (((k1_funct_1 @ sk_D_2 @ (sk_C_1 @ sk_C_2 @ sk_D_2))
% 0.59/0.76         = (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_D_2)))),
% 0.59/0.76      inference('sup+', [status(thm)], ['54', '63'])).
% 0.59/0.76  thf('65', plain,
% 0.59/0.76      (![X13 : $i, X14 : $i]:
% 0.59/0.76         (~ (v1_relat_1 @ X13)
% 0.59/0.76          | ~ (v1_funct_1 @ X13)
% 0.59/0.76          | ((X14) = (X13))
% 0.59/0.76          | ((k1_funct_1 @ X14 @ (sk_C_1 @ X13 @ X14))
% 0.59/0.76              != (k1_funct_1 @ X13 @ (sk_C_1 @ X13 @ X14)))
% 0.59/0.76          | ((k1_relat_1 @ X14) != (k1_relat_1 @ X13))
% 0.59/0.76          | ~ (v1_funct_1 @ X14)
% 0.59/0.76          | ~ (v1_relat_1 @ X14))),
% 0.59/0.76      inference('cnf', [status(esa)], [t9_funct_1])).
% 0.59/0.76  thf('66', plain,
% 0.59/0.76      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_D_2))
% 0.59/0.76          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_D_2)))
% 0.59/0.76        | ~ (v1_relat_1 @ sk_D_2)
% 0.59/0.76        | ~ (v1_funct_1 @ sk_D_2)
% 0.59/0.76        | ((k1_relat_1 @ sk_D_2) != (k1_relat_1 @ sk_C_2))
% 0.59/0.76        | ((sk_D_2) = (sk_C_2))
% 0.59/0.76        | ~ (v1_funct_1 @ sk_C_2)
% 0.59/0.76        | ~ (v1_relat_1 @ sk_C_2))),
% 0.59/0.76      inference('sup-', [status(thm)], ['64', '65'])).
% 0.59/0.76  thf('67', plain, ((v1_relat_1 @ sk_D_2)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('68', plain, ((v1_funct_1 @ sk_D_2)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('69', plain, (((k1_relat_1 @ sk_D_2) = (sk_A))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('70', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('71', plain, ((v1_funct_1 @ sk_C_2)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('72', plain, ((v1_relat_1 @ sk_C_2)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('73', plain,
% 0.59/0.76      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_D_2))
% 0.59/0.76          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_D_2)))
% 0.59/0.76        | ((sk_A) != (sk_A))
% 0.59/0.76        | ((sk_D_2) = (sk_C_2)))),
% 0.59/0.76      inference('demod', [status(thm)],
% 0.59/0.76                ['66', '67', '68', '69', '70', '71', '72'])).
% 0.59/0.76  thf('74', plain, (((sk_D_2) = (sk_C_2))),
% 0.59/0.76      inference('simplify', [status(thm)], ['73'])).
% 0.59/0.76  thf('75', plain, (((sk_C_2) != (sk_D_2))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('76', plain, ($false),
% 0.59/0.76      inference('simplify_reflect-', [status(thm)], ['74', '75'])).
% 0.59/0.76  
% 0.59/0.76  % SZS output end Refutation
% 0.59/0.76  
% 0.62/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
