%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iVQOFLXcZb

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:42 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 267 expanded)
%              Number of leaves         :   17 (  84 expanded)
%              Depth                    :   19
%              Number of atoms          :  670 (5430 expanded)
%              Number of equality atoms :   62 ( 727 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

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
    ( ( k1_relat_1 @ sk_D_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k1_relat_1 @ sk_C_2 )
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
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( X11 = X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X11 ) @ ( k1_relat_1 @ X11 ) )
      | ( ( k1_relat_1 @ X11 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('8',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ( sk_C_2 = sk_D_2 )
    | ( r2_hidden @ ( sk_C_1 @ sk_D_2 @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_2 = sk_D_2 )
    | ( r2_hidden @ ( sk_C_1 @ sk_D_2 @ sk_C_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D_2 @ sk_C_2 ) @ sk_A )
    | ( sk_C_2 = sk_D_2 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    sk_C_2 != sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r2_hidden @ ( sk_C_1 @ sk_D_2 @ sk_C_2 ) @ sk_A ),
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
      | ( r2_hidden @ ( sk_D_1 @ X4 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('17',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ X4 @ X1 ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
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
      | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_D_2 @ sk_C_2 ) @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf(t23_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A )
              = ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k1_funct_1 @ X7 @ ( k1_funct_1 @ X8 @ X9 ) ) )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ ( sk_D_1 @ ( sk_C_1 @ sk_D_2 @ sk_C_2 ) @ sk_B ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( sk_C_1 @ sk_D_2 @ sk_C_2 ) @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r2_hidden @ ( sk_C_1 @ sk_D_2 @ sk_C_2 ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('28',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( X3
       != ( k2_relat_1 @ X1 ) )
      | ( X4
        = ( k1_funct_1 @ X1 @ ( sk_D_1 @ X4 @ X1 ) ) )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('30',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X1 ) )
      | ( X4
        = ( k1_funct_1 @ X1 @ ( sk_D_1 @ X4 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0
        = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0
        = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ X0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( sk_C_1 @ sk_D_2 @ sk_C_2 )
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( sk_C_1 @ sk_D_2 @ sk_C_2 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ ( sk_D_1 @ ( sk_C_1 @ sk_D_2 @ sk_C_2 ) @ sk_B ) )
        = ( k1_funct_1 @ X0 @ ( sk_C_1 @ sk_D_2 @ sk_C_2 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25','26','35'])).

thf('37',plain,
    ( ( k5_relat_1 @ sk_B @ sk_C_2 )
    = ( k5_relat_1 @ sk_B @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ ( sk_D_1 @ ( sk_C_1 @ sk_D_2 @ sk_C_2 ) @ sk_B ) )
        = ( k1_funct_1 @ X0 @ ( sk_C_1 @ sk_D_2 @ sk_C_2 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25','26','35'])).

thf('39',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C_2 ) @ ( sk_D_1 @ ( sk_C_1 @ sk_D_2 @ sk_C_2 ) @ sk_B ) )
      = ( k1_funct_1 @ sk_D_2 @ ( sk_C_1 @ sk_D_2 @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C_2 ) @ ( sk_D_1 @ ( sk_C_1 @ sk_D_2 @ sk_C_2 ) @ sk_B ) )
    = ( k1_funct_1 @ sk_D_2 @ ( sk_C_1 @ sk_D_2 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D_2 @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D_2 @ ( sk_C_1 @ sk_D_2 @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['36','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D_2 @ sk_C_2 ) )
    = ( k1_funct_1 @ sk_D_2 @ ( sk_C_1 @ sk_D_2 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( X11 = X10 )
      | ( ( k1_funct_1 @ X11 @ ( sk_C_1 @ X10 @ X11 ) )
       != ( k1_funct_1 @ X10 @ ( sk_C_1 @ X10 @ X11 ) ) )
      | ( ( k1_relat_1 @ X11 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('48',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D_2 @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D_2 @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D_2 ) )
    | ( sk_C_2 = sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k1_relat_1 @ sk_D_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D_2 @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D_2 @ sk_C_2 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_2 = sk_D_2 ) ),
    inference(demod,[status(thm)],['48','49','50','51','52','53','54'])).

thf('56',plain,(
    sk_C_2 = sk_D_2 ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    sk_C_2 != sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['56','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iVQOFLXcZb
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:02:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.71/0.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.71/0.89  % Solved by: fo/fo7.sh
% 0.71/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.71/0.89  % done 292 iterations in 0.454s
% 0.71/0.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.71/0.89  % SZS output start Refutation
% 0.71/0.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.71/0.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.71/0.89  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.71/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.71/0.89  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.71/0.89  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.71/0.89  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.71/0.89  thf(sk_B_type, type, sk_B: $i).
% 0.71/0.89  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.71/0.89  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.71/0.89  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.71/0.89  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.71/0.89  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.71/0.89  thf(t156_funct_1, conjecture,
% 0.71/0.89    (![A:$i,B:$i]:
% 0.71/0.89     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.71/0.89       ( ![C:$i]:
% 0.71/0.89         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.71/0.89           ( ![D:$i]:
% 0.71/0.89             ( ( ( v1_relat_1 @ D ) & ( v1_funct_1 @ D ) ) =>
% 0.71/0.89               ( ( ( ( A ) = ( k2_relat_1 @ B ) ) & 
% 0.71/0.89                   ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.71/0.89                   ( ( k1_relat_1 @ D ) = ( A ) ) & 
% 0.71/0.89                   ( ( k5_relat_1 @ B @ C ) = ( k5_relat_1 @ B @ D ) ) ) =>
% 0.71/0.89                 ( ( C ) = ( D ) ) ) ) ) ) ) ))).
% 0.71/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.71/0.89    (~( ![A:$i,B:$i]:
% 0.71/0.89        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.71/0.89          ( ![C:$i]:
% 0.71/0.89            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.71/0.89              ( ![D:$i]:
% 0.71/0.89                ( ( ( v1_relat_1 @ D ) & ( v1_funct_1 @ D ) ) =>
% 0.71/0.89                  ( ( ( ( A ) = ( k2_relat_1 @ B ) ) & 
% 0.71/0.89                      ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.71/0.89                      ( ( k1_relat_1 @ D ) = ( A ) ) & 
% 0.71/0.89                      ( ( k5_relat_1 @ B @ C ) = ( k5_relat_1 @ B @ D ) ) ) =>
% 0.71/0.89                    ( ( C ) = ( D ) ) ) ) ) ) ) ) )),
% 0.71/0.89    inference('cnf.neg', [status(esa)], [t156_funct_1])).
% 0.71/0.89  thf('0', plain, (((k1_relat_1 @ sk_D_2) = (sk_A))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('1', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf(t9_funct_1, axiom,
% 0.71/0.89    (![A:$i]:
% 0.71/0.89     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.71/0.89       ( ![B:$i]:
% 0.71/0.89         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.71/0.89           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.71/0.89               ( ![C:$i]:
% 0.71/0.89                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 0.71/0.89                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 0.71/0.89             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.71/0.89  thf('2', plain,
% 0.71/0.89      (![X10 : $i, X11 : $i]:
% 0.71/0.89         (~ (v1_relat_1 @ X10)
% 0.71/0.89          | ~ (v1_funct_1 @ X10)
% 0.71/0.89          | ((X11) = (X10))
% 0.71/0.89          | (r2_hidden @ (sk_C_1 @ X10 @ X11) @ (k1_relat_1 @ X11))
% 0.71/0.89          | ((k1_relat_1 @ X11) != (k1_relat_1 @ X10))
% 0.71/0.89          | ~ (v1_funct_1 @ X11)
% 0.71/0.89          | ~ (v1_relat_1 @ X11))),
% 0.71/0.89      inference('cnf', [status(esa)], [t9_funct_1])).
% 0.71/0.89  thf('3', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         (((sk_A) != (k1_relat_1 @ X0))
% 0.71/0.89          | ~ (v1_relat_1 @ sk_C_2)
% 0.71/0.89          | ~ (v1_funct_1 @ sk_C_2)
% 0.71/0.89          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 0.71/0.89          | ((sk_C_2) = (X0))
% 0.71/0.89          | ~ (v1_funct_1 @ X0)
% 0.71/0.89          | ~ (v1_relat_1 @ X0))),
% 0.71/0.89      inference('sup-', [status(thm)], ['1', '2'])).
% 0.71/0.89  thf('4', plain, ((v1_relat_1 @ sk_C_2)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('5', plain, ((v1_funct_1 @ sk_C_2)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('6', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('7', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         (((sk_A) != (k1_relat_1 @ X0))
% 0.71/0.89          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A)
% 0.71/0.89          | ((sk_C_2) = (X0))
% 0.71/0.89          | ~ (v1_funct_1 @ X0)
% 0.71/0.89          | ~ (v1_relat_1 @ X0))),
% 0.71/0.89      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.71/0.89  thf('8', plain,
% 0.71/0.89      ((((sk_A) != (sk_A))
% 0.71/0.89        | ~ (v1_relat_1 @ sk_D_2)
% 0.71/0.89        | ~ (v1_funct_1 @ sk_D_2)
% 0.71/0.89        | ((sk_C_2) = (sk_D_2))
% 0.71/0.89        | (r2_hidden @ (sk_C_1 @ sk_D_2 @ sk_C_2) @ sk_A))),
% 0.71/0.90      inference('sup-', [status(thm)], ['0', '7'])).
% 0.71/0.90  thf('9', plain, ((v1_relat_1 @ sk_D_2)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('10', plain, ((v1_funct_1 @ sk_D_2)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('11', plain,
% 0.71/0.90      ((((sk_A) != (sk_A))
% 0.71/0.90        | ((sk_C_2) = (sk_D_2))
% 0.71/0.90        | (r2_hidden @ (sk_C_1 @ sk_D_2 @ sk_C_2) @ sk_A))),
% 0.71/0.90      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.71/0.90  thf('12', plain,
% 0.71/0.90      (((r2_hidden @ (sk_C_1 @ sk_D_2 @ sk_C_2) @ sk_A) | ((sk_C_2) = (sk_D_2)))),
% 0.71/0.90      inference('simplify', [status(thm)], ['11'])).
% 0.71/0.90  thf('13', plain, (((sk_C_2) != (sk_D_2))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('14', plain, ((r2_hidden @ (sk_C_1 @ sk_D_2 @ sk_C_2) @ sk_A)),
% 0.71/0.90      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.71/0.90  thf('15', plain, (((sk_A) = (k2_relat_1 @ sk_B))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf(d5_funct_1, axiom,
% 0.71/0.90    (![A:$i]:
% 0.71/0.90     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.71/0.90       ( ![B:$i]:
% 0.71/0.90         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.71/0.90           ( ![C:$i]:
% 0.71/0.90             ( ( r2_hidden @ C @ B ) <=>
% 0.71/0.90               ( ?[D:$i]:
% 0.71/0.90                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.71/0.90                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.71/0.90  thf('16', plain,
% 0.71/0.90      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.71/0.90         (((X3) != (k2_relat_1 @ X1))
% 0.71/0.90          | (r2_hidden @ (sk_D_1 @ X4 @ X1) @ (k1_relat_1 @ X1))
% 0.71/0.90          | ~ (r2_hidden @ X4 @ X3)
% 0.71/0.90          | ~ (v1_funct_1 @ X1)
% 0.71/0.90          | ~ (v1_relat_1 @ X1))),
% 0.71/0.90      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.71/0.90  thf('17', plain,
% 0.71/0.90      (![X1 : $i, X4 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ X1)
% 0.71/0.90          | ~ (v1_funct_1 @ X1)
% 0.71/0.90          | ~ (r2_hidden @ X4 @ (k2_relat_1 @ X1))
% 0.71/0.90          | (r2_hidden @ (sk_D_1 @ X4 @ X1) @ (k1_relat_1 @ X1)))),
% 0.71/0.90      inference('simplify', [status(thm)], ['16'])).
% 0.71/0.90  thf('18', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         (~ (r2_hidden @ X0 @ sk_A)
% 0.71/0.90          | (r2_hidden @ (sk_D_1 @ X0 @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.71/0.90          | ~ (v1_funct_1 @ sk_B)
% 0.71/0.90          | ~ (v1_relat_1 @ sk_B))),
% 0.71/0.90      inference('sup-', [status(thm)], ['15', '17'])).
% 0.71/0.90  thf('19', plain, ((v1_funct_1 @ sk_B)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('21', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         (~ (r2_hidden @ X0 @ sk_A)
% 0.71/0.90          | (r2_hidden @ (sk_D_1 @ X0 @ sk_B) @ (k1_relat_1 @ sk_B)))),
% 0.71/0.90      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.71/0.90  thf('22', plain,
% 0.71/0.90      ((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_D_2 @ sk_C_2) @ sk_B) @ 
% 0.71/0.90        (k1_relat_1 @ sk_B))),
% 0.71/0.90      inference('sup-', [status(thm)], ['14', '21'])).
% 0.71/0.90  thf(t23_funct_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.71/0.90       ( ![C:$i]:
% 0.71/0.90         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.71/0.90           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.71/0.90             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.71/0.90               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.71/0.90  thf('23', plain,
% 0.71/0.90      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ X7)
% 0.71/0.90          | ~ (v1_funct_1 @ X7)
% 0.71/0.90          | ((k1_funct_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 0.71/0.90              = (k1_funct_1 @ X7 @ (k1_funct_1 @ X8 @ X9)))
% 0.71/0.90          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ X8))
% 0.71/0.90          | ~ (v1_funct_1 @ X8)
% 0.71/0.90          | ~ (v1_relat_1 @ X8))),
% 0.71/0.90      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.71/0.90  thf('24', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ sk_B)
% 0.71/0.90          | ~ (v1_funct_1 @ sk_B)
% 0.71/0.90          | ((k1_funct_1 @ (k5_relat_1 @ sk_B @ X0) @ 
% 0.71/0.90              (sk_D_1 @ (sk_C_1 @ sk_D_2 @ sk_C_2) @ sk_B))
% 0.71/0.90              = (k1_funct_1 @ X0 @ 
% 0.71/0.90                 (k1_funct_1 @ sk_B @ 
% 0.71/0.90                  (sk_D_1 @ (sk_C_1 @ sk_D_2 @ sk_C_2) @ sk_B))))
% 0.71/0.90          | ~ (v1_funct_1 @ X0)
% 0.71/0.90          | ~ (v1_relat_1 @ X0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['22', '23'])).
% 0.71/0.90  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('27', plain, ((r2_hidden @ (sk_C_1 @ sk_D_2 @ sk_C_2) @ sk_A)),
% 0.71/0.90      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.71/0.90  thf('28', plain, (((sk_A) = (k2_relat_1 @ sk_B))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('29', plain,
% 0.71/0.90      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.71/0.90         (((X3) != (k2_relat_1 @ X1))
% 0.71/0.90          | ((X4) = (k1_funct_1 @ X1 @ (sk_D_1 @ X4 @ X1)))
% 0.71/0.90          | ~ (r2_hidden @ X4 @ X3)
% 0.71/0.90          | ~ (v1_funct_1 @ X1)
% 0.71/0.90          | ~ (v1_relat_1 @ X1))),
% 0.71/0.90      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.71/0.90  thf('30', plain,
% 0.71/0.90      (![X1 : $i, X4 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ X1)
% 0.71/0.90          | ~ (v1_funct_1 @ X1)
% 0.71/0.90          | ~ (r2_hidden @ X4 @ (k2_relat_1 @ X1))
% 0.71/0.90          | ((X4) = (k1_funct_1 @ X1 @ (sk_D_1 @ X4 @ X1))))),
% 0.71/0.90      inference('simplify', [status(thm)], ['29'])).
% 0.71/0.90  thf('31', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         (~ (r2_hidden @ X0 @ sk_A)
% 0.71/0.90          | ((X0) = (k1_funct_1 @ sk_B @ (sk_D_1 @ X0 @ sk_B)))
% 0.71/0.90          | ~ (v1_funct_1 @ sk_B)
% 0.71/0.90          | ~ (v1_relat_1 @ sk_B))),
% 0.71/0.90      inference('sup-', [status(thm)], ['28', '30'])).
% 0.71/0.90  thf('32', plain, ((v1_funct_1 @ sk_B)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('34', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         (~ (r2_hidden @ X0 @ sk_A)
% 0.71/0.90          | ((X0) = (k1_funct_1 @ sk_B @ (sk_D_1 @ X0 @ sk_B))))),
% 0.71/0.90      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.71/0.90  thf('35', plain,
% 0.71/0.90      (((sk_C_1 @ sk_D_2 @ sk_C_2)
% 0.71/0.90         = (k1_funct_1 @ sk_B @ (sk_D_1 @ (sk_C_1 @ sk_D_2 @ sk_C_2) @ sk_B)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['27', '34'])).
% 0.71/0.90  thf('36', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         (((k1_funct_1 @ (k5_relat_1 @ sk_B @ X0) @ 
% 0.71/0.90            (sk_D_1 @ (sk_C_1 @ sk_D_2 @ sk_C_2) @ sk_B))
% 0.71/0.90            = (k1_funct_1 @ X0 @ (sk_C_1 @ sk_D_2 @ sk_C_2)))
% 0.71/0.90          | ~ (v1_funct_1 @ X0)
% 0.71/0.90          | ~ (v1_relat_1 @ X0))),
% 0.71/0.90      inference('demod', [status(thm)], ['24', '25', '26', '35'])).
% 0.71/0.90  thf('37', plain,
% 0.71/0.90      (((k5_relat_1 @ sk_B @ sk_C_2) = (k5_relat_1 @ sk_B @ sk_D_2))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('38', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         (((k1_funct_1 @ (k5_relat_1 @ sk_B @ X0) @ 
% 0.71/0.90            (sk_D_1 @ (sk_C_1 @ sk_D_2 @ sk_C_2) @ sk_B))
% 0.71/0.90            = (k1_funct_1 @ X0 @ (sk_C_1 @ sk_D_2 @ sk_C_2)))
% 0.71/0.90          | ~ (v1_funct_1 @ X0)
% 0.71/0.90          | ~ (v1_relat_1 @ X0))),
% 0.71/0.90      inference('demod', [status(thm)], ['24', '25', '26', '35'])).
% 0.71/0.90  thf('39', plain,
% 0.71/0.90      ((((k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C_2) @ 
% 0.71/0.90          (sk_D_1 @ (sk_C_1 @ sk_D_2 @ sk_C_2) @ sk_B))
% 0.71/0.90          = (k1_funct_1 @ sk_D_2 @ (sk_C_1 @ sk_D_2 @ sk_C_2)))
% 0.71/0.90        | ~ (v1_relat_1 @ sk_D_2)
% 0.71/0.90        | ~ (v1_funct_1 @ sk_D_2))),
% 0.71/0.90      inference('sup+', [status(thm)], ['37', '38'])).
% 0.71/0.90  thf('40', plain, ((v1_relat_1 @ sk_D_2)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('41', plain, ((v1_funct_1 @ sk_D_2)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('42', plain,
% 0.71/0.90      (((k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C_2) @ 
% 0.71/0.90         (sk_D_1 @ (sk_C_1 @ sk_D_2 @ sk_C_2) @ sk_B))
% 0.71/0.90         = (k1_funct_1 @ sk_D_2 @ (sk_C_1 @ sk_D_2 @ sk_C_2)))),
% 0.71/0.90      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.71/0.90  thf('43', plain,
% 0.71/0.90      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D_2 @ sk_C_2))
% 0.71/0.90          = (k1_funct_1 @ sk_D_2 @ (sk_C_1 @ sk_D_2 @ sk_C_2)))
% 0.71/0.90        | ~ (v1_relat_1 @ sk_C_2)
% 0.71/0.90        | ~ (v1_funct_1 @ sk_C_2))),
% 0.71/0.90      inference('sup+', [status(thm)], ['36', '42'])).
% 0.71/0.90  thf('44', plain, ((v1_relat_1 @ sk_C_2)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('45', plain, ((v1_funct_1 @ sk_C_2)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('46', plain,
% 0.71/0.90      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D_2 @ sk_C_2))
% 0.71/0.90         = (k1_funct_1 @ sk_D_2 @ (sk_C_1 @ sk_D_2 @ sk_C_2)))),
% 0.71/0.90      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.71/0.90  thf('47', plain,
% 0.71/0.90      (![X10 : $i, X11 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ X10)
% 0.71/0.90          | ~ (v1_funct_1 @ X10)
% 0.71/0.90          | ((X11) = (X10))
% 0.71/0.90          | ((k1_funct_1 @ X11 @ (sk_C_1 @ X10 @ X11))
% 0.71/0.90              != (k1_funct_1 @ X10 @ (sk_C_1 @ X10 @ X11)))
% 0.71/0.90          | ((k1_relat_1 @ X11) != (k1_relat_1 @ X10))
% 0.71/0.90          | ~ (v1_funct_1 @ X11)
% 0.71/0.90          | ~ (v1_relat_1 @ X11))),
% 0.71/0.90      inference('cnf', [status(esa)], [t9_funct_1])).
% 0.71/0.90  thf('48', plain,
% 0.71/0.90      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D_2 @ sk_C_2))
% 0.71/0.90          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D_2 @ sk_C_2)))
% 0.71/0.90        | ~ (v1_relat_1 @ sk_C_2)
% 0.71/0.90        | ~ (v1_funct_1 @ sk_C_2)
% 0.71/0.90        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D_2))
% 0.71/0.90        | ((sk_C_2) = (sk_D_2))
% 0.71/0.90        | ~ (v1_funct_1 @ sk_D_2)
% 0.71/0.90        | ~ (v1_relat_1 @ sk_D_2))),
% 0.71/0.90      inference('sup-', [status(thm)], ['46', '47'])).
% 0.71/0.90  thf('49', plain, ((v1_relat_1 @ sk_C_2)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('50', plain, ((v1_funct_1 @ sk_C_2)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('51', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('52', plain, (((k1_relat_1 @ sk_D_2) = (sk_A))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('53', plain, ((v1_funct_1 @ sk_D_2)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('54', plain, ((v1_relat_1 @ sk_D_2)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('55', plain,
% 0.71/0.90      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D_2 @ sk_C_2))
% 0.71/0.90          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D_2 @ sk_C_2)))
% 0.71/0.90        | ((sk_A) != (sk_A))
% 0.71/0.90        | ((sk_C_2) = (sk_D_2)))),
% 0.71/0.90      inference('demod', [status(thm)],
% 0.71/0.90                ['48', '49', '50', '51', '52', '53', '54'])).
% 0.71/0.90  thf('56', plain, (((sk_C_2) = (sk_D_2))),
% 0.71/0.90      inference('simplify', [status(thm)], ['55'])).
% 0.71/0.90  thf('57', plain, (((sk_C_2) != (sk_D_2))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('58', plain, ($false),
% 0.71/0.90      inference('simplify_reflect-', [status(thm)], ['56', '57'])).
% 0.71/0.90  
% 0.71/0.90  % SZS output end Refutation
% 0.71/0.90  
% 0.71/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
