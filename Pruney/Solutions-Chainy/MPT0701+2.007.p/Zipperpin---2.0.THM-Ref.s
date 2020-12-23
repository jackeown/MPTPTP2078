%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WvEcvriK6U

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 280 expanded)
%              Number of leaves         :   19 (  89 expanded)
%              Depth                    :   21
%              Number of atoms          :  672 (5542 expanded)
%              Number of equality atoms :   58 ( 723 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X4 @ X2 ) @ X4 ) @ X2 )
      | ( X3
       != ( k2_relat_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('17',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X4 @ X2 ) @ X4 ) @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X0 @ sk_B ) @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_B ) @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) ) @ sk_B ),
    inference('sup-',[status(thm)],['14','18'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ X11 )
      | ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['21','22','23'])).

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

thf('25',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k1_funct_1 @ X7 @ ( k1_funct_1 @ X8 @ X9 ) ) )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ ( sk_D_1 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_B ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_B ) @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) ) @ sk_B ),
    inference('sup-',[status(thm)],['14','18'])).

thf('30',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ X11 )
      | ( X12
        = ( k1_funct_1 @ X11 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( sk_C_1 @ sk_C_2 @ sk_D_2 )
      = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( sk_C_1 @ sk_C_2 @ sk_D_2 )
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ ( sk_D_1 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_B ) )
        = ( k1_funct_1 @ X0 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27','28','34'])).

thf('36',plain,
    ( ( k5_relat_1 @ sk_B @ sk_C_2 )
    = ( k5_relat_1 @ sk_B @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ ( sk_D_1 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_B ) )
        = ( k1_funct_1 @ X0 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27','28','34'])).

thf('38',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C_2 ) @ ( sk_D_1 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_B ) )
      = ( k1_funct_1 @ sk_D_2 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) ) )
    | ~ ( v1_relat_1 @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C_2 ) @ ( sk_D_1 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) @ sk_B ) )
    = ( k1_funct_1 @ sk_D_2 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) )
      = ( k1_funct_1 @ sk_D_2 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['35','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) )
    = ( k1_funct_1 @ sk_D_2 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
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

thf('47',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) ) )
    | ~ ( v1_relat_1 @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ( ( k1_relat_1 @ sk_D_2 )
     != ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_D_2 = sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k1_relat_1 @ sk_D_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_D_2 ) ) )
    | ( sk_A != sk_A )
    | ( sk_D_2 = sk_C_2 ) ),
    inference(demod,[status(thm)],['47','48','49','50','51','52','53'])).

thf('55',plain,(
    sk_D_2 = sk_C_2 ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    sk_C_2 != sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['55','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WvEcvriK6U
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:59:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 100 iterations in 0.110s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.57  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.57  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.21/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.57  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.21/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.57  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.57  thf(t156_funct_1, conjecture,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.57       ( ![C:$i]:
% 0.21/0.57         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.57           ( ![D:$i]:
% 0.21/0.57             ( ( ( v1_relat_1 @ D ) & ( v1_funct_1 @ D ) ) =>
% 0.21/0.57               ( ( ( ( A ) = ( k2_relat_1 @ B ) ) & 
% 0.21/0.57                   ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.21/0.57                   ( ( k1_relat_1 @ D ) = ( A ) ) & 
% 0.21/0.57                   ( ( k5_relat_1 @ B @ C ) = ( k5_relat_1 @ B @ D ) ) ) =>
% 0.21/0.57                 ( ( C ) = ( D ) ) ) ) ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i,B:$i]:
% 0.21/0.57        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.57          ( ![C:$i]:
% 0.21/0.57            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.57              ( ![D:$i]:
% 0.21/0.57                ( ( ( v1_relat_1 @ D ) & ( v1_funct_1 @ D ) ) =>
% 0.21/0.57                  ( ( ( ( A ) = ( k2_relat_1 @ B ) ) & 
% 0.21/0.57                      ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.21/0.57                      ( ( k1_relat_1 @ D ) = ( A ) ) & 
% 0.21/0.57                      ( ( k5_relat_1 @ B @ C ) = ( k5_relat_1 @ B @ D ) ) ) =>
% 0.21/0.57                    ( ( C ) = ( D ) ) ) ) ) ) ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t156_funct_1])).
% 0.21/0.57  thf('0', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('1', plain, (((k1_relat_1 @ sk_D_2) = (sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t9_funct_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.57           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.21/0.57               ( ![C:$i]:
% 0.21/0.57                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 0.21/0.57                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 0.21/0.57             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      (![X13 : $i, X14 : $i]:
% 0.21/0.57         (~ (v1_relat_1 @ X13)
% 0.21/0.57          | ~ (v1_funct_1 @ X13)
% 0.21/0.57          | ((X14) = (X13))
% 0.21/0.57          | (r2_hidden @ (sk_C_1 @ X13 @ X14) @ (k1_relat_1 @ X14))
% 0.21/0.57          | ((k1_relat_1 @ X14) != (k1_relat_1 @ X13))
% 0.21/0.57          | ~ (v1_funct_1 @ X14)
% 0.21/0.57          | ~ (v1_relat_1 @ X14))),
% 0.21/0.57      inference('cnf', [status(esa)], [t9_funct_1])).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((sk_A) != (k1_relat_1 @ X0))
% 0.21/0.57          | ~ (v1_relat_1 @ sk_D_2)
% 0.21/0.57          | ~ (v1_funct_1 @ sk_D_2)
% 0.21/0.57          | (r2_hidden @ (sk_C_1 @ X0 @ sk_D_2) @ (k1_relat_1 @ sk_D_2))
% 0.21/0.57          | ((sk_D_2) = (X0))
% 0.21/0.57          | ~ (v1_funct_1 @ X0)
% 0.21/0.57          | ~ (v1_relat_1 @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.57  thf('4', plain, ((v1_relat_1 @ sk_D_2)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('5', plain, ((v1_funct_1 @ sk_D_2)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('6', plain, (((k1_relat_1 @ sk_D_2) = (sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('7', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((sk_A) != (k1_relat_1 @ X0))
% 0.21/0.57          | (r2_hidden @ (sk_C_1 @ X0 @ sk_D_2) @ sk_A)
% 0.21/0.57          | ((sk_D_2) = (X0))
% 0.21/0.57          | ~ (v1_funct_1 @ X0)
% 0.21/0.57          | ~ (v1_relat_1 @ X0))),
% 0.21/0.57      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.21/0.57  thf('8', plain,
% 0.21/0.57      ((((sk_A) != (sk_A))
% 0.21/0.57        | ~ (v1_relat_1 @ sk_C_2)
% 0.21/0.57        | ~ (v1_funct_1 @ sk_C_2)
% 0.21/0.57        | ((sk_D_2) = (sk_C_2))
% 0.21/0.57        | (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['0', '7'])).
% 0.21/0.57  thf('9', plain, ((v1_relat_1 @ sk_C_2)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('10', plain, ((v1_funct_1 @ sk_C_2)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('11', plain,
% 0.21/0.57      ((((sk_A) != (sk_A))
% 0.21/0.57        | ((sk_D_2) = (sk_C_2))
% 0.21/0.57        | (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.57  thf('12', plain,
% 0.21/0.57      (((r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_A) | ((sk_D_2) = (sk_C_2)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.57  thf('13', plain, (((sk_C_2) != (sk_D_2))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('14', plain, ((r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_A)),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.21/0.57  thf('15', plain, (((sk_A) = (k2_relat_1 @ sk_B))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(d5_relat_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.21/0.57       ( ![C:$i]:
% 0.21/0.57         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.57           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.21/0.57  thf('16', plain,
% 0.21/0.57      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.57          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X4 @ X2) @ X4) @ X2)
% 0.21/0.57          | ((X3) != (k2_relat_1 @ X2)))),
% 0.21/0.57      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.21/0.57  thf('17', plain,
% 0.21/0.57      (![X2 : $i, X4 : $i]:
% 0.21/0.57         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X4 @ X2) @ X4) @ X2)
% 0.21/0.57          | ~ (r2_hidden @ X4 @ (k2_relat_1 @ X2)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.57  thf('18', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.57          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X0 @ sk_B) @ X0) @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['15', '17'])).
% 0.21/0.57  thf('19', plain,
% 0.21/0.57      ((r2_hidden @ 
% 0.21/0.57        (k4_tarski @ (sk_D_1 @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_B) @ 
% 0.21/0.57         (sk_C_1 @ sk_C_2 @ sk_D_2)) @ 
% 0.21/0.57        sk_B)),
% 0.21/0.57      inference('sup-', [status(thm)], ['14', '18'])).
% 0.21/0.57  thf(t8_funct_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.57       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.21/0.57         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.21/0.57           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.21/0.57  thf('20', plain,
% 0.21/0.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.57         (~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ X11)
% 0.21/0.57          | (r2_hidden @ X10 @ (k1_relat_1 @ X11))
% 0.21/0.57          | ~ (v1_funct_1 @ X11)
% 0.21/0.57          | ~ (v1_relat_1 @ X11))),
% 0.21/0.57      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.21/0.57  thf('21', plain,
% 0.21/0.57      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.57        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.57        | (r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_B) @ 
% 0.21/0.57           (k1_relat_1 @ sk_B)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.57  thf('22', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('23', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('24', plain,
% 0.21/0.57      ((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_B) @ 
% 0.21/0.57        (k1_relat_1 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.21/0.57  thf(t23_funct_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.57       ( ![C:$i]:
% 0.21/0.57         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.57           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.57             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.21/0.57               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.21/0.57  thf('25', plain,
% 0.21/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.57         (~ (v1_relat_1 @ X7)
% 0.21/0.57          | ~ (v1_funct_1 @ X7)
% 0.21/0.57          | ((k1_funct_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 0.21/0.57              = (k1_funct_1 @ X7 @ (k1_funct_1 @ X8 @ X9)))
% 0.21/0.57          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ X8))
% 0.21/0.57          | ~ (v1_funct_1 @ X8)
% 0.21/0.57          | ~ (v1_relat_1 @ X8))),
% 0.21/0.57      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.21/0.57  thf('26', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (v1_relat_1 @ sk_B)
% 0.21/0.57          | ~ (v1_funct_1 @ sk_B)
% 0.21/0.57          | ((k1_funct_1 @ (k5_relat_1 @ sk_B @ X0) @ 
% 0.21/0.57              (sk_D_1 @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_B))
% 0.21/0.57              = (k1_funct_1 @ X0 @ 
% 0.21/0.57                 (k1_funct_1 @ sk_B @ 
% 0.21/0.57                  (sk_D_1 @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_B))))
% 0.21/0.57          | ~ (v1_funct_1 @ X0)
% 0.21/0.57          | ~ (v1_relat_1 @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.57  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('28', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('29', plain,
% 0.21/0.57      ((r2_hidden @ 
% 0.21/0.57        (k4_tarski @ (sk_D_1 @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_B) @ 
% 0.21/0.57         (sk_C_1 @ sk_C_2 @ sk_D_2)) @ 
% 0.21/0.57        sk_B)),
% 0.21/0.57      inference('sup-', [status(thm)], ['14', '18'])).
% 0.21/0.57  thf('30', plain,
% 0.21/0.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.57         (~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ X11)
% 0.21/0.57          | ((X12) = (k1_funct_1 @ X11 @ X10))
% 0.21/0.57          | ~ (v1_funct_1 @ X11)
% 0.21/0.57          | ~ (v1_relat_1 @ X11))),
% 0.21/0.57      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.21/0.57  thf('31', plain,
% 0.21/0.57      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.57        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.57        | ((sk_C_1 @ sk_C_2 @ sk_D_2)
% 0.21/0.57            = (k1_funct_1 @ sk_B @ (sk_D_1 @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_B))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.57  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('33', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('34', plain,
% 0.21/0.57      (((sk_C_1 @ sk_C_2 @ sk_D_2)
% 0.21/0.57         = (k1_funct_1 @ sk_B @ (sk_D_1 @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_B)))),
% 0.21/0.57      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.21/0.57  thf('35', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((k1_funct_1 @ (k5_relat_1 @ sk_B @ X0) @ 
% 0.21/0.57            (sk_D_1 @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_B))
% 0.21/0.57            = (k1_funct_1 @ X0 @ (sk_C_1 @ sk_C_2 @ sk_D_2)))
% 0.21/0.57          | ~ (v1_funct_1 @ X0)
% 0.21/0.57          | ~ (v1_relat_1 @ X0))),
% 0.21/0.57      inference('demod', [status(thm)], ['26', '27', '28', '34'])).
% 0.21/0.57  thf('36', plain,
% 0.21/0.57      (((k5_relat_1 @ sk_B @ sk_C_2) = (k5_relat_1 @ sk_B @ sk_D_2))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('37', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((k1_funct_1 @ (k5_relat_1 @ sk_B @ X0) @ 
% 0.21/0.57            (sk_D_1 @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_B))
% 0.21/0.57            = (k1_funct_1 @ X0 @ (sk_C_1 @ sk_C_2 @ sk_D_2)))
% 0.21/0.57          | ~ (v1_funct_1 @ X0)
% 0.21/0.57          | ~ (v1_relat_1 @ X0))),
% 0.21/0.57      inference('demod', [status(thm)], ['26', '27', '28', '34'])).
% 0.21/0.57  thf('38', plain,
% 0.21/0.57      ((((k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C_2) @ 
% 0.21/0.57          (sk_D_1 @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_B))
% 0.21/0.57          = (k1_funct_1 @ sk_D_2 @ (sk_C_1 @ sk_C_2 @ sk_D_2)))
% 0.21/0.57        | ~ (v1_relat_1 @ sk_D_2)
% 0.21/0.57        | ~ (v1_funct_1 @ sk_D_2))),
% 0.21/0.57      inference('sup+', [status(thm)], ['36', '37'])).
% 0.21/0.57  thf('39', plain, ((v1_relat_1 @ sk_D_2)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('40', plain, ((v1_funct_1 @ sk_D_2)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('41', plain,
% 0.21/0.57      (((k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C_2) @ 
% 0.21/0.57         (sk_D_1 @ (sk_C_1 @ sk_C_2 @ sk_D_2) @ sk_B))
% 0.21/0.57         = (k1_funct_1 @ sk_D_2 @ (sk_C_1 @ sk_C_2 @ sk_D_2)))),
% 0.21/0.57      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.21/0.57  thf('42', plain,
% 0.21/0.57      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_D_2))
% 0.21/0.57          = (k1_funct_1 @ sk_D_2 @ (sk_C_1 @ sk_C_2 @ sk_D_2)))
% 0.21/0.57        | ~ (v1_relat_1 @ sk_C_2)
% 0.21/0.57        | ~ (v1_funct_1 @ sk_C_2))),
% 0.21/0.57      inference('sup+', [status(thm)], ['35', '41'])).
% 0.21/0.57  thf('43', plain, ((v1_relat_1 @ sk_C_2)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('44', plain, ((v1_funct_1 @ sk_C_2)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('45', plain,
% 0.21/0.57      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_D_2))
% 0.21/0.57         = (k1_funct_1 @ sk_D_2 @ (sk_C_1 @ sk_C_2 @ sk_D_2)))),
% 0.21/0.57      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.21/0.57  thf('46', plain,
% 0.21/0.57      (![X13 : $i, X14 : $i]:
% 0.21/0.57         (~ (v1_relat_1 @ X13)
% 0.21/0.57          | ~ (v1_funct_1 @ X13)
% 0.21/0.57          | ((X14) = (X13))
% 0.21/0.57          | ((k1_funct_1 @ X14 @ (sk_C_1 @ X13 @ X14))
% 0.21/0.57              != (k1_funct_1 @ X13 @ (sk_C_1 @ X13 @ X14)))
% 0.21/0.57          | ((k1_relat_1 @ X14) != (k1_relat_1 @ X13))
% 0.21/0.57          | ~ (v1_funct_1 @ X14)
% 0.21/0.57          | ~ (v1_relat_1 @ X14))),
% 0.21/0.57      inference('cnf', [status(esa)], [t9_funct_1])).
% 0.21/0.57  thf('47', plain,
% 0.21/0.57      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_D_2))
% 0.21/0.57          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_D_2)))
% 0.21/0.57        | ~ (v1_relat_1 @ sk_D_2)
% 0.21/0.57        | ~ (v1_funct_1 @ sk_D_2)
% 0.21/0.57        | ((k1_relat_1 @ sk_D_2) != (k1_relat_1 @ sk_C_2))
% 0.21/0.57        | ((sk_D_2) = (sk_C_2))
% 0.21/0.57        | ~ (v1_funct_1 @ sk_C_2)
% 0.21/0.57        | ~ (v1_relat_1 @ sk_C_2))),
% 0.21/0.57      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.57  thf('48', plain, ((v1_relat_1 @ sk_D_2)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('49', plain, ((v1_funct_1 @ sk_D_2)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('50', plain, (((k1_relat_1 @ sk_D_2) = (sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('51', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('52', plain, ((v1_funct_1 @ sk_C_2)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('53', plain, ((v1_relat_1 @ sk_C_2)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('54', plain,
% 0.21/0.57      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_D_2))
% 0.21/0.57          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_D_2)))
% 0.21/0.57        | ((sk_A) != (sk_A))
% 0.21/0.57        | ((sk_D_2) = (sk_C_2)))),
% 0.21/0.57      inference('demod', [status(thm)],
% 0.21/0.57                ['47', '48', '49', '50', '51', '52', '53'])).
% 0.21/0.57  thf('55', plain, (((sk_D_2) = (sk_C_2))),
% 0.21/0.57      inference('simplify', [status(thm)], ['54'])).
% 0.21/0.57  thf('56', plain, (((sk_C_2) != (sk_D_2))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('57', plain, ($false),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['55', '56'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.42/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
