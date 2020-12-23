%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HNuR3JxYWC

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:20 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 888 expanded)
%              Number of leaves         :   20 ( 261 expanded)
%              Depth                    :   31
%              Number of atoms          : 1578 (14287 expanded)
%              Number of equality atoms :   84 ( 981 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_funct_1 @ X8 )
        = ( k4_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_funct_1 @ X8 )
        = ( k4_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('5',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t57_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( v2_funct_1 @ B )
            & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) )
         => ( ( A
              = ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) )
            & ( A
              = ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t57_funct_1])).

thf('8',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
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

thf('9',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ( X4
       != ( k2_relat_1 @ X2 ) )
      | ( r2_hidden @ ( sk_D_1 @ X5 @ X2 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ X5 @ X4 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('10',plain,(
    ! [X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( r2_hidden @ X5 @ ( k2_relat_1 @ X2 ) )
      | ( r2_hidden @ ( sk_D_1 @ X5 @ X2 ) @ ( k1_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_funct_1 @ X8 )
        = ( k4_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('16',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12','13'])).

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

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X13 ) )
      | ( X14
        = ( k1_funct_1 @ ( k2_funct_1 @ X13 ) @ ( k1_funct_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t56_funct_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ( X4
       != ( k2_relat_1 @ X2 ) )
      | ( X5
        = ( k1_funct_1 @ X2 @ ( sk_D_1 @ X5 @ X2 ) ) )
      | ~ ( r2_hidden @ X5 @ X4 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('23',plain,(
    ! [X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( r2_hidden @ X5 @ ( k2_relat_1 @ X2 ) )
      | ( X5
        = ( k1_funct_1 @ X2 @ ( sk_D_1 @ X5 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( sk_A
      = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20','27','28'])).

thf('30',plain,
    ( ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('35',plain,(
    r2_hidden @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['14','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('39',plain,(
    ! [X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( r2_hidden @ X5 @ ( k2_relat_1 @ X2 ) )
      | ( r2_hidden @ ( sk_D_1 @ X5 @ X2 ) @ ( k1_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ ( k4_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ ( k4_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ ( k4_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ ( k4_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ ( k4_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46','47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('51',plain,(
    r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46','47','48'])).

thf('52',plain,
    ( ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( r2_hidden @ X5 @ ( k2_relat_1 @ X2 ) )
      | ( X5
        = ( k1_funct_1 @ X2 @ ( sk_D_1 @ X5 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('56',plain,
    ( ( ( sk_D_1 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) )
      = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( sk_D_1 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ) @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( sk_D_1 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) )
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( sk_D_1 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_funct_1 @ X8 )
        = ( k4_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('61',plain,(
    r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('62',plain,(
    ! [X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( r2_hidden @ X5 @ ( k2_relat_1 @ X2 ) )
      | ( r2_hidden @ ( sk_D_1 @ X5 @ X2 ) @ ( k1_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('63',plain,
    ( ( r2_hidden @ ( sk_D_1 @ ( sk_D_1 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ) @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_D_1 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ) @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X13 ) )
      | ( X14
        = ( k1_funct_1 @ ( k2_funct_1 @ X13 ) @ ( k1_funct_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t56_funct_1])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( sk_D_1 @ ( sk_D_1 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ) @ sk_B )
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( sk_D_1 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ) @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( sk_D_1 @ ( sk_D_1 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ) @ sk_B )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( sk_D_1 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['68','69','70','71'])).

thf('73',plain,
    ( ( sk_D_1 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) )
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( sk_D_1 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('74',plain,
    ( ( sk_D_1 @ ( sk_D_1 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ) @ sk_B )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( sk_D_1 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( sk_D_1 @ ( sk_D_1 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ) @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( sk_D_1 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['60','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('78',plain,(
    r2_hidden @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['14','34'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('80',plain,(
    ! [X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( r2_hidden @ X5 @ ( k2_relat_1 @ X2 ) )
      | ( X5
        = ( k1_funct_1 @ X2 @ ( sk_D_1 @ X5 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X1
        = ( k1_funct_1 @ ( k4_relat_1 @ X0 ) @ ( sk_D_1 @ X1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ( ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( sk_D_1 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ( ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( sk_D_1 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( sk_D_1 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['77','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( sk_D_1 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['85','86','87','88'])).

thf('90',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( sk_D_1 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['76','89'])).

thf('91',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A )
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( sk_D_1 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['90','91','92','93'])).

thf('95',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( sk_D_1 @ ( sk_D_1 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ) @ sk_B )
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['75','94','95','96','97'])).

thf('99',plain,
    ( ( sk_D_1 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) )
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','98'])).

thf('100',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('101',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('102',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( sk_D_1 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['99','102'])).

thf('104',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','103'])).

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

thf('105',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X11 @ X10 ) @ X12 )
        = ( k1_funct_1 @ X10 @ ( k1_funct_1 @ X11 @ X12 ) ) )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','106'])).

thf('108',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['107','108','109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113','114','115'])).

thf('117',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_funct_1 @ X8 )
        = ( k4_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('118',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(split,[status(esa)],['118'])).

thf('120',plain,
    ( ( ( sk_A
       != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','119'])).

thf('121',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['120','121','122','123'])).

thf('125',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20','27','28'])).

thf('126',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['118'])).

thf('127',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('129',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
    | ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['118'])).

thf('132',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['130','131'])).

thf('133',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['124','132'])).

thf('134',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['116','133'])).

thf('135',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('136',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['134','135','136','137'])).

thf('139',plain,(
    $false ),
    inference(simplify,[status(thm)],['138'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HNuR3JxYWC
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:45:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.43/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.43/0.63  % Solved by: fo/fo7.sh
% 0.43/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.63  % done 118 iterations in 0.167s
% 0.43/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.43/0.63  % SZS output start Refutation
% 0.43/0.63  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.43/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.43/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.43/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.43/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.63  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.43/0.63  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.43/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.43/0.63  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.43/0.63  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.43/0.63  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.43/0.63  thf(d9_funct_1, axiom,
% 0.43/0.63    (![A:$i]:
% 0.43/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.43/0.63       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.43/0.63  thf('0', plain,
% 0.43/0.63      (![X8 : $i]:
% 0.43/0.63         (~ (v2_funct_1 @ X8)
% 0.43/0.63          | ((k2_funct_1 @ X8) = (k4_relat_1 @ X8))
% 0.43/0.63          | ~ (v1_funct_1 @ X8)
% 0.43/0.63          | ~ (v1_relat_1 @ X8))),
% 0.43/0.63      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.43/0.63  thf(dt_k2_funct_1, axiom,
% 0.43/0.63    (![A:$i]:
% 0.43/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.43/0.63       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.43/0.63         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.43/0.63  thf('1', plain,
% 0.43/0.63      (![X9 : $i]:
% 0.43/0.63         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 0.43/0.63          | ~ (v1_funct_1 @ X9)
% 0.43/0.63          | ~ (v1_relat_1 @ X9))),
% 0.43/0.63      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.43/0.63  thf('2', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         ((v1_funct_1 @ (k4_relat_1 @ X0))
% 0.43/0.63          | ~ (v1_relat_1 @ X0)
% 0.43/0.63          | ~ (v1_funct_1 @ X0)
% 0.43/0.63          | ~ (v2_funct_1 @ X0)
% 0.43/0.63          | ~ (v1_relat_1 @ X0)
% 0.43/0.63          | ~ (v1_funct_1 @ X0))),
% 0.43/0.63      inference('sup+', [status(thm)], ['0', '1'])).
% 0.43/0.63  thf('3', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (v2_funct_1 @ X0)
% 0.43/0.63          | ~ (v1_funct_1 @ X0)
% 0.43/0.63          | ~ (v1_relat_1 @ X0)
% 0.43/0.63          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.43/0.63      inference('simplify', [status(thm)], ['2'])).
% 0.43/0.63  thf('4', plain,
% 0.43/0.63      (![X8 : $i]:
% 0.43/0.63         (~ (v2_funct_1 @ X8)
% 0.43/0.63          | ((k2_funct_1 @ X8) = (k4_relat_1 @ X8))
% 0.43/0.63          | ~ (v1_funct_1 @ X8)
% 0.43/0.63          | ~ (v1_relat_1 @ X8))),
% 0.43/0.63      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.43/0.63  thf('5', plain,
% 0.43/0.63      (![X9 : $i]:
% 0.43/0.63         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 0.43/0.63          | ~ (v1_funct_1 @ X9)
% 0.43/0.63          | ~ (v1_relat_1 @ X9))),
% 0.43/0.63      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.43/0.63  thf('6', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         ((v1_relat_1 @ (k4_relat_1 @ X0))
% 0.43/0.63          | ~ (v1_relat_1 @ X0)
% 0.43/0.63          | ~ (v1_funct_1 @ X0)
% 0.43/0.63          | ~ (v2_funct_1 @ X0)
% 0.43/0.63          | ~ (v1_relat_1 @ X0)
% 0.43/0.63          | ~ (v1_funct_1 @ X0))),
% 0.43/0.63      inference('sup+', [status(thm)], ['4', '5'])).
% 0.43/0.63  thf('7', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (v2_funct_1 @ X0)
% 0.43/0.63          | ~ (v1_funct_1 @ X0)
% 0.43/0.63          | ~ (v1_relat_1 @ X0)
% 0.43/0.63          | (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.43/0.63      inference('simplify', [status(thm)], ['6'])).
% 0.43/0.63  thf(t57_funct_1, conjecture,
% 0.43/0.63    (![A:$i,B:$i]:
% 0.43/0.63     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.43/0.63       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.43/0.63         ( ( ( A ) =
% 0.43/0.63             ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.43/0.63           ( ( A ) =
% 0.43/0.63             ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ))).
% 0.43/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.63    (~( ![A:$i,B:$i]:
% 0.43/0.63        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.43/0.63          ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.43/0.63            ( ( ( A ) =
% 0.43/0.63                ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.43/0.63              ( ( A ) =
% 0.43/0.63                ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )),
% 0.43/0.63    inference('cnf.neg', [status(esa)], [t57_funct_1])).
% 0.43/0.63  thf('8', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf(d5_funct_1, axiom,
% 0.43/0.63    (![A:$i]:
% 0.43/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.43/0.63       ( ![B:$i]:
% 0.43/0.63         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.43/0.63           ( ![C:$i]:
% 0.43/0.63             ( ( r2_hidden @ C @ B ) <=>
% 0.43/0.63               ( ?[D:$i]:
% 0.43/0.63                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.43/0.63                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.43/0.63  thf('9', plain,
% 0.43/0.63      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.43/0.63         (((X4) != (k2_relat_1 @ X2))
% 0.43/0.63          | (r2_hidden @ (sk_D_1 @ X5 @ X2) @ (k1_relat_1 @ X2))
% 0.43/0.63          | ~ (r2_hidden @ X5 @ X4)
% 0.43/0.63          | ~ (v1_funct_1 @ X2)
% 0.43/0.63          | ~ (v1_relat_1 @ X2))),
% 0.43/0.63      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.43/0.63  thf('10', plain,
% 0.43/0.63      (![X2 : $i, X5 : $i]:
% 0.43/0.63         (~ (v1_relat_1 @ X2)
% 0.43/0.63          | ~ (v1_funct_1 @ X2)
% 0.43/0.63          | ~ (r2_hidden @ X5 @ (k2_relat_1 @ X2))
% 0.43/0.63          | (r2_hidden @ (sk_D_1 @ X5 @ X2) @ (k1_relat_1 @ X2)))),
% 0.43/0.63      inference('simplify', [status(thm)], ['9'])).
% 0.43/0.63  thf('11', plain,
% 0.43/0.63      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.43/0.63        | ~ (v1_funct_1 @ sk_B)
% 0.43/0.63        | ~ (v1_relat_1 @ sk_B))),
% 0.43/0.63      inference('sup-', [status(thm)], ['8', '10'])).
% 0.43/0.63  thf('12', plain, ((v1_funct_1 @ sk_B)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('13', plain, ((v1_relat_1 @ sk_B)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('14', plain,
% 0.43/0.63      ((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))),
% 0.43/0.63      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.43/0.63  thf('15', plain,
% 0.43/0.63      (![X8 : $i]:
% 0.43/0.63         (~ (v2_funct_1 @ X8)
% 0.43/0.63          | ((k2_funct_1 @ X8) = (k4_relat_1 @ X8))
% 0.43/0.63          | ~ (v1_funct_1 @ X8)
% 0.43/0.63          | ~ (v1_relat_1 @ X8))),
% 0.43/0.63      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.43/0.63  thf('16', plain,
% 0.43/0.63      ((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))),
% 0.43/0.63      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.43/0.63  thf(t56_funct_1, axiom,
% 0.43/0.63    (![A:$i,B:$i]:
% 0.43/0.63     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.43/0.63       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 0.43/0.63         ( ( ( A ) =
% 0.43/0.63             ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 0.43/0.63           ( ( A ) =
% 0.43/0.63             ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ))).
% 0.43/0.63  thf('17', plain,
% 0.43/0.63      (![X13 : $i, X14 : $i]:
% 0.43/0.63         (~ (v2_funct_1 @ X13)
% 0.43/0.63          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X13))
% 0.43/0.63          | ((X14)
% 0.43/0.63              = (k1_funct_1 @ (k2_funct_1 @ X13) @ (k1_funct_1 @ X13 @ X14)))
% 0.43/0.63          | ~ (v1_funct_1 @ X13)
% 0.43/0.63          | ~ (v1_relat_1 @ X13))),
% 0.43/0.63      inference('cnf', [status(esa)], [t56_funct_1])).
% 0.43/0.63  thf('18', plain,
% 0.43/0.63      ((~ (v1_relat_1 @ sk_B)
% 0.43/0.63        | ~ (v1_funct_1 @ sk_B)
% 0.43/0.63        | ((sk_D_1 @ sk_A @ sk_B)
% 0.43/0.63            = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 0.43/0.63               (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B))))
% 0.43/0.63        | ~ (v2_funct_1 @ sk_B))),
% 0.43/0.63      inference('sup-', [status(thm)], ['16', '17'])).
% 0.43/0.63  thf('19', plain, ((v1_relat_1 @ sk_B)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('20', plain, ((v1_funct_1 @ sk_B)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('21', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('22', plain,
% 0.43/0.63      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.43/0.63         (((X4) != (k2_relat_1 @ X2))
% 0.43/0.63          | ((X5) = (k1_funct_1 @ X2 @ (sk_D_1 @ X5 @ X2)))
% 0.43/0.63          | ~ (r2_hidden @ X5 @ X4)
% 0.43/0.63          | ~ (v1_funct_1 @ X2)
% 0.43/0.63          | ~ (v1_relat_1 @ X2))),
% 0.43/0.63      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.43/0.63  thf('23', plain,
% 0.43/0.63      (![X2 : $i, X5 : $i]:
% 0.43/0.63         (~ (v1_relat_1 @ X2)
% 0.43/0.63          | ~ (v1_funct_1 @ X2)
% 0.43/0.63          | ~ (r2_hidden @ X5 @ (k2_relat_1 @ X2))
% 0.43/0.63          | ((X5) = (k1_funct_1 @ X2 @ (sk_D_1 @ X5 @ X2))))),
% 0.43/0.63      inference('simplify', [status(thm)], ['22'])).
% 0.43/0.63  thf('24', plain,
% 0.43/0.63      ((((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))
% 0.43/0.63        | ~ (v1_funct_1 @ sk_B)
% 0.43/0.63        | ~ (v1_relat_1 @ sk_B))),
% 0.43/0.63      inference('sup-', [status(thm)], ['21', '23'])).
% 0.43/0.63  thf('25', plain, ((v1_funct_1 @ sk_B)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('27', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 0.43/0.63      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.43/0.63  thf('28', plain, ((v2_funct_1 @ sk_B)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('29', plain,
% 0.43/0.63      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 0.43/0.63      inference('demod', [status(thm)], ['18', '19', '20', '27', '28'])).
% 0.43/0.63  thf('30', plain,
% 0.43/0.63      ((((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))
% 0.43/0.63        | ~ (v1_relat_1 @ sk_B)
% 0.43/0.63        | ~ (v1_funct_1 @ sk_B)
% 0.43/0.63        | ~ (v2_funct_1 @ sk_B))),
% 0.43/0.63      inference('sup+', [status(thm)], ['15', '29'])).
% 0.43/0.63  thf('31', plain, ((v1_relat_1 @ sk_B)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('32', plain, ((v1_funct_1 @ sk_B)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('33', plain, ((v2_funct_1 @ sk_B)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('34', plain,
% 0.43/0.63      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))),
% 0.43/0.63      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 0.43/0.63  thf('35', plain,
% 0.43/0.63      ((r2_hidden @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.43/0.63        (k1_relat_1 @ sk_B))),
% 0.43/0.63      inference('demod', [status(thm)], ['14', '34'])).
% 0.43/0.63  thf('36', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (v2_funct_1 @ X0)
% 0.43/0.63          | ~ (v1_funct_1 @ X0)
% 0.43/0.63          | ~ (v1_relat_1 @ X0)
% 0.43/0.63          | (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.43/0.63      inference('simplify', [status(thm)], ['6'])).
% 0.43/0.63  thf('37', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (v2_funct_1 @ X0)
% 0.43/0.63          | ~ (v1_funct_1 @ X0)
% 0.43/0.63          | ~ (v1_relat_1 @ X0)
% 0.43/0.63          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.43/0.63      inference('simplify', [status(thm)], ['2'])).
% 0.43/0.63  thf(t37_relat_1, axiom,
% 0.43/0.63    (![A:$i]:
% 0.43/0.63     ( ( v1_relat_1 @ A ) =>
% 0.43/0.63       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.43/0.63         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.43/0.63  thf('38', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (((k1_relat_1 @ X0) = (k2_relat_1 @ (k4_relat_1 @ X0)))
% 0.43/0.63          | ~ (v1_relat_1 @ X0))),
% 0.43/0.63      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.43/0.63  thf('39', plain,
% 0.43/0.63      (![X2 : $i, X5 : $i]:
% 0.43/0.63         (~ (v1_relat_1 @ X2)
% 0.43/0.63          | ~ (v1_funct_1 @ X2)
% 0.43/0.63          | ~ (r2_hidden @ X5 @ (k2_relat_1 @ X2))
% 0.43/0.63          | (r2_hidden @ (sk_D_1 @ X5 @ X2) @ (k1_relat_1 @ X2)))),
% 0.43/0.63      inference('simplify', [status(thm)], ['9'])).
% 0.43/0.63  thf('40', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i]:
% 0.43/0.63         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.43/0.63          | ~ (v1_relat_1 @ X0)
% 0.43/0.63          | (r2_hidden @ (sk_D_1 @ X1 @ (k4_relat_1 @ X0)) @ 
% 0.43/0.63             (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.43/0.63          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 0.43/0.63          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['38', '39'])).
% 0.43/0.63  thf('41', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i]:
% 0.43/0.63         (~ (v1_relat_1 @ X0)
% 0.43/0.63          | ~ (v1_funct_1 @ X0)
% 0.43/0.63          | ~ (v2_funct_1 @ X0)
% 0.43/0.63          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.43/0.63          | (r2_hidden @ (sk_D_1 @ X1 @ (k4_relat_1 @ X0)) @ 
% 0.43/0.63             (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.43/0.63          | ~ (v1_relat_1 @ X0)
% 0.43/0.63          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['37', '40'])).
% 0.43/0.63  thf('42', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i]:
% 0.43/0.63         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.43/0.63          | (r2_hidden @ (sk_D_1 @ X1 @ (k4_relat_1 @ X0)) @ 
% 0.43/0.63             (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.43/0.63          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.43/0.63          | ~ (v2_funct_1 @ X0)
% 0.43/0.63          | ~ (v1_funct_1 @ X0)
% 0.43/0.63          | ~ (v1_relat_1 @ X0))),
% 0.43/0.63      inference('simplify', [status(thm)], ['41'])).
% 0.43/0.63  thf('43', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i]:
% 0.43/0.63         (~ (v1_relat_1 @ X0)
% 0.43/0.63          | ~ (v1_funct_1 @ X0)
% 0.43/0.63          | ~ (v2_funct_1 @ X0)
% 0.43/0.63          | ~ (v1_relat_1 @ X0)
% 0.43/0.63          | ~ (v1_funct_1 @ X0)
% 0.43/0.63          | ~ (v2_funct_1 @ X0)
% 0.43/0.63          | (r2_hidden @ (sk_D_1 @ X1 @ (k4_relat_1 @ X0)) @ 
% 0.43/0.63             (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.43/0.63          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['36', '42'])).
% 0.43/0.63  thf('44', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i]:
% 0.43/0.63         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.43/0.63          | (r2_hidden @ (sk_D_1 @ X1 @ (k4_relat_1 @ X0)) @ 
% 0.43/0.63             (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.43/0.63          | ~ (v2_funct_1 @ X0)
% 0.43/0.63          | ~ (v1_funct_1 @ X0)
% 0.43/0.63          | ~ (v1_relat_1 @ X0))),
% 0.43/0.63      inference('simplify', [status(thm)], ['43'])).
% 0.43/0.63  thf('45', plain,
% 0.43/0.63      ((~ (v1_relat_1 @ sk_B)
% 0.43/0.63        | ~ (v1_funct_1 @ sk_B)
% 0.43/0.63        | ~ (v2_funct_1 @ sk_B)
% 0.43/0.63        | (r2_hidden @ 
% 0.43/0.63           (sk_D_1 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.43/0.63            (k4_relat_1 @ sk_B)) @ 
% 0.43/0.63           (k1_relat_1 @ (k4_relat_1 @ sk_B))))),
% 0.43/0.63      inference('sup-', [status(thm)], ['35', '44'])).
% 0.43/0.63  thf('46', plain, ((v1_relat_1 @ sk_B)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('47', plain, ((v1_funct_1 @ sk_B)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('48', plain, ((v2_funct_1 @ sk_B)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('49', plain,
% 0.43/0.63      ((r2_hidden @ 
% 0.43/0.63        (sk_D_1 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.43/0.63         (k4_relat_1 @ sk_B)) @ 
% 0.43/0.63        (k1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 0.43/0.63      inference('demod', [status(thm)], ['45', '46', '47', '48'])).
% 0.43/0.63  thf('50', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (((k2_relat_1 @ X0) = (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.43/0.63          | ~ (v1_relat_1 @ X0))),
% 0.43/0.63      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.43/0.63  thf('51', plain,
% 0.43/0.63      ((r2_hidden @ 
% 0.43/0.63        (sk_D_1 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.43/0.63         (k4_relat_1 @ sk_B)) @ 
% 0.43/0.63        (k1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 0.43/0.63      inference('demod', [status(thm)], ['45', '46', '47', '48'])).
% 0.43/0.63  thf('52', plain,
% 0.43/0.63      (((r2_hidden @ 
% 0.43/0.63         (sk_D_1 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.43/0.63          (k4_relat_1 @ sk_B)) @ 
% 0.43/0.63         (k2_relat_1 @ sk_B))
% 0.43/0.63        | ~ (v1_relat_1 @ sk_B))),
% 0.43/0.63      inference('sup+', [status(thm)], ['50', '51'])).
% 0.43/0.63  thf('53', plain, ((v1_relat_1 @ sk_B)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('54', plain,
% 0.43/0.63      ((r2_hidden @ 
% 0.43/0.63        (sk_D_1 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.43/0.63         (k4_relat_1 @ sk_B)) @ 
% 0.43/0.63        (k2_relat_1 @ sk_B))),
% 0.43/0.63      inference('demod', [status(thm)], ['52', '53'])).
% 0.43/0.63  thf('55', plain,
% 0.43/0.63      (![X2 : $i, X5 : $i]:
% 0.43/0.63         (~ (v1_relat_1 @ X2)
% 0.43/0.63          | ~ (v1_funct_1 @ X2)
% 0.43/0.63          | ~ (r2_hidden @ X5 @ (k2_relat_1 @ X2))
% 0.43/0.63          | ((X5) = (k1_funct_1 @ X2 @ (sk_D_1 @ X5 @ X2))))),
% 0.48/0.63      inference('simplify', [status(thm)], ['22'])).
% 0.48/0.63  thf('56', plain,
% 0.48/0.63      ((((sk_D_1 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.48/0.63          (k4_relat_1 @ sk_B))
% 0.48/0.63          = (k1_funct_1 @ sk_B @ 
% 0.48/0.63             (sk_D_1 @ 
% 0.48/0.63              (sk_D_1 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.48/0.63               (k4_relat_1 @ sk_B)) @ 
% 0.48/0.63              sk_B)))
% 0.48/0.63        | ~ (v1_funct_1 @ sk_B)
% 0.48/0.63        | ~ (v1_relat_1 @ sk_B))),
% 0.48/0.63      inference('sup-', [status(thm)], ['54', '55'])).
% 0.48/0.63  thf('57', plain, ((v1_funct_1 @ sk_B)),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('58', plain, ((v1_relat_1 @ sk_B)),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('59', plain,
% 0.48/0.63      (((sk_D_1 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.48/0.63         (k4_relat_1 @ sk_B))
% 0.48/0.63         = (k1_funct_1 @ sk_B @ 
% 0.48/0.63            (sk_D_1 @ 
% 0.48/0.63             (sk_D_1 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.48/0.63              (k4_relat_1 @ sk_B)) @ 
% 0.48/0.63             sk_B)))),
% 0.48/0.63      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.48/0.63  thf('60', plain,
% 0.48/0.63      (![X8 : $i]:
% 0.48/0.63         (~ (v2_funct_1 @ X8)
% 0.48/0.63          | ((k2_funct_1 @ X8) = (k4_relat_1 @ X8))
% 0.48/0.63          | ~ (v1_funct_1 @ X8)
% 0.48/0.63          | ~ (v1_relat_1 @ X8))),
% 0.48/0.63      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.48/0.63  thf('61', plain,
% 0.48/0.63      ((r2_hidden @ 
% 0.48/0.63        (sk_D_1 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.48/0.63         (k4_relat_1 @ sk_B)) @ 
% 0.48/0.63        (k2_relat_1 @ sk_B))),
% 0.48/0.63      inference('demod', [status(thm)], ['52', '53'])).
% 0.48/0.63  thf('62', plain,
% 0.48/0.63      (![X2 : $i, X5 : $i]:
% 0.48/0.63         (~ (v1_relat_1 @ X2)
% 0.48/0.63          | ~ (v1_funct_1 @ X2)
% 0.48/0.63          | ~ (r2_hidden @ X5 @ (k2_relat_1 @ X2))
% 0.48/0.63          | (r2_hidden @ (sk_D_1 @ X5 @ X2) @ (k1_relat_1 @ X2)))),
% 0.48/0.63      inference('simplify', [status(thm)], ['9'])).
% 0.48/0.63  thf('63', plain,
% 0.48/0.63      (((r2_hidden @ 
% 0.48/0.63         (sk_D_1 @ 
% 0.48/0.63          (sk_D_1 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.48/0.63           (k4_relat_1 @ sk_B)) @ 
% 0.48/0.63          sk_B) @ 
% 0.48/0.63         (k1_relat_1 @ sk_B))
% 0.48/0.63        | ~ (v1_funct_1 @ sk_B)
% 0.48/0.63        | ~ (v1_relat_1 @ sk_B))),
% 0.48/0.63      inference('sup-', [status(thm)], ['61', '62'])).
% 0.48/0.63  thf('64', plain, ((v1_funct_1 @ sk_B)),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('65', plain, ((v1_relat_1 @ sk_B)),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('66', plain,
% 0.48/0.63      ((r2_hidden @ 
% 0.48/0.63        (sk_D_1 @ 
% 0.48/0.63         (sk_D_1 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.48/0.63          (k4_relat_1 @ sk_B)) @ 
% 0.48/0.63         sk_B) @ 
% 0.48/0.63        (k1_relat_1 @ sk_B))),
% 0.48/0.63      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.48/0.63  thf('67', plain,
% 0.48/0.63      (![X13 : $i, X14 : $i]:
% 0.48/0.63         (~ (v2_funct_1 @ X13)
% 0.48/0.63          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X13))
% 0.48/0.63          | ((X14)
% 0.48/0.63              = (k1_funct_1 @ (k2_funct_1 @ X13) @ (k1_funct_1 @ X13 @ X14)))
% 0.48/0.63          | ~ (v1_funct_1 @ X13)
% 0.48/0.63          | ~ (v1_relat_1 @ X13))),
% 0.48/0.63      inference('cnf', [status(esa)], [t56_funct_1])).
% 0.48/0.63  thf('68', plain,
% 0.48/0.63      ((~ (v1_relat_1 @ sk_B)
% 0.48/0.63        | ~ (v1_funct_1 @ sk_B)
% 0.48/0.63        | ((sk_D_1 @ 
% 0.48/0.63            (sk_D_1 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.48/0.63             (k4_relat_1 @ sk_B)) @ 
% 0.48/0.63            sk_B)
% 0.48/0.63            = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 0.48/0.63               (k1_funct_1 @ sk_B @ 
% 0.48/0.63                (sk_D_1 @ 
% 0.48/0.63                 (sk_D_1 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.48/0.63                  (k4_relat_1 @ sk_B)) @ 
% 0.48/0.63                 sk_B))))
% 0.48/0.63        | ~ (v2_funct_1 @ sk_B))),
% 0.48/0.63      inference('sup-', [status(thm)], ['66', '67'])).
% 0.48/0.63  thf('69', plain, ((v1_relat_1 @ sk_B)),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('70', plain, ((v1_funct_1 @ sk_B)),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('71', plain, ((v2_funct_1 @ sk_B)),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('72', plain,
% 0.48/0.63      (((sk_D_1 @ 
% 0.48/0.63         (sk_D_1 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.48/0.63          (k4_relat_1 @ sk_B)) @ 
% 0.48/0.63         sk_B)
% 0.48/0.63         = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 0.48/0.63            (k1_funct_1 @ sk_B @ 
% 0.48/0.63             (sk_D_1 @ 
% 0.48/0.63              (sk_D_1 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.48/0.63               (k4_relat_1 @ sk_B)) @ 
% 0.48/0.63              sk_B))))),
% 0.48/0.63      inference('demod', [status(thm)], ['68', '69', '70', '71'])).
% 0.48/0.63  thf('73', plain,
% 0.48/0.63      (((sk_D_1 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.48/0.63         (k4_relat_1 @ sk_B))
% 0.48/0.63         = (k1_funct_1 @ sk_B @ 
% 0.48/0.63            (sk_D_1 @ 
% 0.48/0.63             (sk_D_1 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.48/0.63              (k4_relat_1 @ sk_B)) @ 
% 0.48/0.63             sk_B)))),
% 0.48/0.63      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.48/0.63  thf('74', plain,
% 0.48/0.63      (((sk_D_1 @ 
% 0.48/0.63         (sk_D_1 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.48/0.63          (k4_relat_1 @ sk_B)) @ 
% 0.48/0.63         sk_B)
% 0.48/0.63         = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 0.48/0.63            (sk_D_1 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.48/0.63             (k4_relat_1 @ sk_B))))),
% 0.48/0.63      inference('demod', [status(thm)], ['72', '73'])).
% 0.48/0.63  thf('75', plain,
% 0.48/0.63      ((((sk_D_1 @ 
% 0.48/0.63          (sk_D_1 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.48/0.63           (k4_relat_1 @ sk_B)) @ 
% 0.48/0.63          sk_B)
% 0.48/0.63          = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ 
% 0.48/0.63             (sk_D_1 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.48/0.63              (k4_relat_1 @ sk_B))))
% 0.48/0.63        | ~ (v1_relat_1 @ sk_B)
% 0.48/0.63        | ~ (v1_funct_1 @ sk_B)
% 0.48/0.63        | ~ (v2_funct_1 @ sk_B))),
% 0.48/0.63      inference('sup+', [status(thm)], ['60', '74'])).
% 0.48/0.63  thf('76', plain,
% 0.48/0.63      (![X0 : $i]:
% 0.48/0.63         (~ (v2_funct_1 @ X0)
% 0.48/0.63          | ~ (v1_funct_1 @ X0)
% 0.48/0.63          | ~ (v1_relat_1 @ X0)
% 0.48/0.63          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.48/0.63      inference('simplify', [status(thm)], ['2'])).
% 0.48/0.63  thf('77', plain,
% 0.48/0.63      (![X0 : $i]:
% 0.48/0.63         (~ (v2_funct_1 @ X0)
% 0.48/0.63          | ~ (v1_funct_1 @ X0)
% 0.48/0.63          | ~ (v1_relat_1 @ X0)
% 0.48/0.63          | (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.48/0.63      inference('simplify', [status(thm)], ['6'])).
% 0.48/0.63  thf('78', plain,
% 0.48/0.63      ((r2_hidden @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.48/0.63        (k1_relat_1 @ sk_B))),
% 0.48/0.63      inference('demod', [status(thm)], ['14', '34'])).
% 0.48/0.63  thf('79', plain,
% 0.48/0.63      (![X0 : $i]:
% 0.48/0.63         (((k1_relat_1 @ X0) = (k2_relat_1 @ (k4_relat_1 @ X0)))
% 0.48/0.63          | ~ (v1_relat_1 @ X0))),
% 0.48/0.63      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.48/0.63  thf('80', plain,
% 0.48/0.63      (![X2 : $i, X5 : $i]:
% 0.48/0.63         (~ (v1_relat_1 @ X2)
% 0.48/0.63          | ~ (v1_funct_1 @ X2)
% 0.48/0.63          | ~ (r2_hidden @ X5 @ (k2_relat_1 @ X2))
% 0.48/0.63          | ((X5) = (k1_funct_1 @ X2 @ (sk_D_1 @ X5 @ X2))))),
% 0.48/0.63      inference('simplify', [status(thm)], ['22'])).
% 0.48/0.63  thf('81', plain,
% 0.48/0.63      (![X0 : $i, X1 : $i]:
% 0.48/0.63         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.48/0.63          | ~ (v1_relat_1 @ X0)
% 0.48/0.63          | ((X1)
% 0.48/0.63              = (k1_funct_1 @ (k4_relat_1 @ X0) @ 
% 0.48/0.63                 (sk_D_1 @ X1 @ (k4_relat_1 @ X0))))
% 0.48/0.63          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 0.48/0.63          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.48/0.63      inference('sup-', [status(thm)], ['79', '80'])).
% 0.48/0.63  thf('82', plain,
% 0.48/0.63      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.48/0.63        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.48/0.63        | ((k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)
% 0.48/0.63            = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ 
% 0.48/0.63               (sk_D_1 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.48/0.63                (k4_relat_1 @ sk_B))))
% 0.48/0.63        | ~ (v1_relat_1 @ sk_B))),
% 0.48/0.63      inference('sup-', [status(thm)], ['78', '81'])).
% 0.48/0.63  thf('83', plain, ((v1_relat_1 @ sk_B)),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('84', plain,
% 0.48/0.63      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.48/0.63        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.48/0.63        | ((k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)
% 0.48/0.63            = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ 
% 0.48/0.63               (sk_D_1 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.48/0.63                (k4_relat_1 @ sk_B)))))),
% 0.48/0.63      inference('demod', [status(thm)], ['82', '83'])).
% 0.48/0.63  thf('85', plain,
% 0.48/0.63      ((~ (v1_relat_1 @ sk_B)
% 0.48/0.63        | ~ (v1_funct_1 @ sk_B)
% 0.48/0.63        | ~ (v2_funct_1 @ sk_B)
% 0.48/0.63        | ((k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)
% 0.48/0.63            = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ 
% 0.48/0.63               (sk_D_1 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.48/0.63                (k4_relat_1 @ sk_B))))
% 0.48/0.63        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.48/0.63      inference('sup-', [status(thm)], ['77', '84'])).
% 0.48/0.63  thf('86', plain, ((v1_relat_1 @ sk_B)),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('87', plain, ((v1_funct_1 @ sk_B)),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('88', plain, ((v2_funct_1 @ sk_B)),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('89', plain,
% 0.48/0.63      ((((k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)
% 0.48/0.63          = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ 
% 0.48/0.63             (sk_D_1 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.48/0.63              (k4_relat_1 @ sk_B))))
% 0.48/0.63        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.48/0.63      inference('demod', [status(thm)], ['85', '86', '87', '88'])).
% 0.48/0.63  thf('90', plain,
% 0.48/0.63      ((~ (v1_relat_1 @ sk_B)
% 0.48/0.63        | ~ (v1_funct_1 @ sk_B)
% 0.48/0.63        | ~ (v2_funct_1 @ sk_B)
% 0.48/0.63        | ((k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)
% 0.48/0.63            = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ 
% 0.48/0.63               (sk_D_1 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.48/0.63                (k4_relat_1 @ sk_B)))))),
% 0.48/0.63      inference('sup-', [status(thm)], ['76', '89'])).
% 0.48/0.63  thf('91', plain, ((v1_relat_1 @ sk_B)),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('92', plain, ((v1_funct_1 @ sk_B)),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('93', plain, ((v2_funct_1 @ sk_B)),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('94', plain,
% 0.48/0.63      (((k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)
% 0.48/0.63         = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ 
% 0.48/0.63            (sk_D_1 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.48/0.63             (k4_relat_1 @ sk_B))))),
% 0.48/0.63      inference('demod', [status(thm)], ['90', '91', '92', '93'])).
% 0.48/0.63  thf('95', plain, ((v1_relat_1 @ sk_B)),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('96', plain, ((v1_funct_1 @ sk_B)),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('97', plain, ((v2_funct_1 @ sk_B)),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('98', plain,
% 0.48/0.63      (((sk_D_1 @ 
% 0.48/0.63         (sk_D_1 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.48/0.63          (k4_relat_1 @ sk_B)) @ 
% 0.48/0.63         sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))),
% 0.48/0.63      inference('demod', [status(thm)], ['75', '94', '95', '96', '97'])).
% 0.48/0.63  thf('99', plain,
% 0.48/0.63      (((sk_D_1 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.48/0.63         (k4_relat_1 @ sk_B))
% 0.48/0.63         = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))),
% 0.48/0.63      inference('demod', [status(thm)], ['59', '98'])).
% 0.48/0.63  thf('100', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 0.48/0.63      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.48/0.63  thf('101', plain,
% 0.48/0.63      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))),
% 0.48/0.63      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 0.48/0.63  thf('102', plain,
% 0.48/0.63      (((sk_A)
% 0.48/0.63         = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))),
% 0.48/0.63      inference('demod', [status(thm)], ['100', '101'])).
% 0.48/0.63  thf('103', plain,
% 0.48/0.63      (((sk_D_1 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.48/0.63         (k4_relat_1 @ sk_B)) = (sk_A))),
% 0.48/0.63      inference('demod', [status(thm)], ['99', '102'])).
% 0.48/0.63  thf('104', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 0.48/0.63      inference('demod', [status(thm)], ['49', '103'])).
% 0.48/0.63  thf(t23_funct_1, axiom,
% 0.48/0.63    (![A:$i,B:$i]:
% 0.48/0.63     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.48/0.63       ( ![C:$i]:
% 0.48/0.63         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.48/0.63           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.48/0.63             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.48/0.63               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.48/0.63  thf('105', plain,
% 0.48/0.63      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.48/0.63         (~ (v1_relat_1 @ X10)
% 0.48/0.63          | ~ (v1_funct_1 @ X10)
% 0.48/0.63          | ((k1_funct_1 @ (k5_relat_1 @ X11 @ X10) @ X12)
% 0.48/0.63              = (k1_funct_1 @ X10 @ (k1_funct_1 @ X11 @ X12)))
% 0.48/0.63          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X11))
% 0.48/0.63          | ~ (v1_funct_1 @ X11)
% 0.48/0.63          | ~ (v1_relat_1 @ X11))),
% 0.48/0.63      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.48/0.63  thf('106', plain,
% 0.48/0.63      (![X0 : $i]:
% 0.48/0.63         (~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.48/0.63          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.48/0.63          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.48/0.63              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.48/0.63          | ~ (v1_funct_1 @ X0)
% 0.48/0.63          | ~ (v1_relat_1 @ X0))),
% 0.48/0.63      inference('sup-', [status(thm)], ['104', '105'])).
% 0.48/0.63  thf('107', plain,
% 0.48/0.63      (![X0 : $i]:
% 0.48/0.63         (~ (v1_relat_1 @ sk_B)
% 0.48/0.63          | ~ (v1_funct_1 @ sk_B)
% 0.48/0.63          | ~ (v2_funct_1 @ sk_B)
% 0.48/0.63          | ~ (v1_relat_1 @ X0)
% 0.48/0.63          | ~ (v1_funct_1 @ X0)
% 0.48/0.63          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.48/0.63              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.48/0.63          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.48/0.63      inference('sup-', [status(thm)], ['7', '106'])).
% 0.48/0.63  thf('108', plain, ((v1_relat_1 @ sk_B)),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('109', plain, ((v1_funct_1 @ sk_B)),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('110', plain, ((v2_funct_1 @ sk_B)),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('111', plain,
% 0.48/0.63      (![X0 : $i]:
% 0.48/0.63         (~ (v1_relat_1 @ X0)
% 0.48/0.63          | ~ (v1_funct_1 @ X0)
% 0.48/0.63          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.48/0.63              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.48/0.63          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.48/0.63      inference('demod', [status(thm)], ['107', '108', '109', '110'])).
% 0.48/0.63  thf('112', plain,
% 0.48/0.63      (![X0 : $i]:
% 0.48/0.63         (~ (v1_relat_1 @ sk_B)
% 0.48/0.63          | ~ (v1_funct_1 @ sk_B)
% 0.48/0.63          | ~ (v2_funct_1 @ sk_B)
% 0.48/0.63          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.48/0.63              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.48/0.63          | ~ (v1_funct_1 @ X0)
% 0.48/0.63          | ~ (v1_relat_1 @ X0))),
% 0.48/0.63      inference('sup-', [status(thm)], ['3', '111'])).
% 0.48/0.63  thf('113', plain, ((v1_relat_1 @ sk_B)),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('114', plain, ((v1_funct_1 @ sk_B)),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('115', plain, ((v2_funct_1 @ sk_B)),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('116', plain,
% 0.48/0.63      (![X0 : $i]:
% 0.48/0.63         (((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.48/0.63            = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.48/0.63          | ~ (v1_funct_1 @ X0)
% 0.48/0.63          | ~ (v1_relat_1 @ X0))),
% 0.48/0.63      inference('demod', [status(thm)], ['112', '113', '114', '115'])).
% 0.48/0.63  thf('117', plain,
% 0.48/0.63      (![X8 : $i]:
% 0.48/0.63         (~ (v2_funct_1 @ X8)
% 0.48/0.63          | ((k2_funct_1 @ X8) = (k4_relat_1 @ X8))
% 0.48/0.63          | ~ (v1_funct_1 @ X8)
% 0.48/0.63          | ~ (v1_relat_1 @ X8))),
% 0.48/0.63      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.48/0.63  thf('118', plain,
% 0.48/0.63      ((((sk_A)
% 0.48/0.63          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 0.48/0.63        | ((sk_A)
% 0.48/0.63            != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('119', plain,
% 0.48/0.63      ((((sk_A)
% 0.48/0.63          != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))
% 0.48/0.63         <= (~
% 0.48/0.63             (((sk_A)
% 0.48/0.63                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.48/0.63                   sk_A))))),
% 0.48/0.63      inference('split', [status(esa)], ['118'])).
% 0.48/0.63  thf('120', plain,
% 0.48/0.63      (((((sk_A)
% 0.48/0.63           != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A))
% 0.48/0.63         | ~ (v1_relat_1 @ sk_B)
% 0.48/0.63         | ~ (v1_funct_1 @ sk_B)
% 0.48/0.63         | ~ (v2_funct_1 @ sk_B)))
% 0.48/0.63         <= (~
% 0.48/0.63             (((sk_A)
% 0.48/0.63                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.48/0.63                   sk_A))))),
% 0.48/0.63      inference('sup-', [status(thm)], ['117', '119'])).
% 0.48/0.63  thf('121', plain, ((v1_relat_1 @ sk_B)),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('122', plain, ((v1_funct_1 @ sk_B)),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('123', plain, ((v2_funct_1 @ sk_B)),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('124', plain,
% 0.48/0.63      ((((sk_A)
% 0.48/0.63          != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A)))
% 0.48/0.63         <= (~
% 0.48/0.63             (((sk_A)
% 0.48/0.63                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.48/0.63                   sk_A))))),
% 0.48/0.63      inference('demod', [status(thm)], ['120', '121', '122', '123'])).
% 0.48/0.63  thf('125', plain,
% 0.48/0.63      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 0.48/0.63      inference('demod', [status(thm)], ['18', '19', '20', '27', '28'])).
% 0.48/0.63  thf('126', plain,
% 0.48/0.63      ((((sk_A)
% 0.48/0.63          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))
% 0.48/0.63         <= (~
% 0.48/0.63             (((sk_A)
% 0.48/0.63                = (k1_funct_1 @ sk_B @ 
% 0.48/0.63                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.48/0.63      inference('split', [status(esa)], ['118'])).
% 0.48/0.63  thf('127', plain,
% 0.48/0.63      ((((sk_A) != (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B))))
% 0.48/0.63         <= (~
% 0.48/0.63             (((sk_A)
% 0.48/0.63                = (k1_funct_1 @ sk_B @ 
% 0.48/0.63                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.48/0.63      inference('sup-', [status(thm)], ['125', '126'])).
% 0.48/0.63  thf('128', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 0.48/0.63      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.48/0.63  thf('129', plain,
% 0.48/0.63      ((((sk_A) != (sk_A)))
% 0.48/0.63         <= (~
% 0.48/0.63             (((sk_A)
% 0.48/0.63                = (k1_funct_1 @ sk_B @ 
% 0.48/0.63                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.48/0.63      inference('demod', [status(thm)], ['127', '128'])).
% 0.48/0.63  thf('130', plain,
% 0.48/0.63      ((((sk_A)
% 0.48/0.63          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.48/0.63      inference('simplify', [status(thm)], ['129'])).
% 0.48/0.63  thf('131', plain,
% 0.48/0.63      (~
% 0.48/0.63       (((sk_A)
% 0.48/0.63          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A))) | 
% 0.48/0.63       ~
% 0.48/0.63       (((sk_A)
% 0.48/0.63          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.48/0.63      inference('split', [status(esa)], ['118'])).
% 0.48/0.63  thf('132', plain,
% 0.48/0.63      (~
% 0.48/0.63       (((sk_A)
% 0.48/0.63          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.48/0.63      inference('sat_resolution*', [status(thm)], ['130', '131'])).
% 0.48/0.63  thf('133', plain,
% 0.48/0.63      (((sk_A)
% 0.48/0.63         != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A))),
% 0.48/0.63      inference('simpl_trail', [status(thm)], ['124', '132'])).
% 0.48/0.63  thf('134', plain,
% 0.48/0.63      ((((sk_A)
% 0.48/0.63          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.48/0.63        | ~ (v1_relat_1 @ sk_B)
% 0.48/0.63        | ~ (v1_funct_1 @ sk_B))),
% 0.48/0.63      inference('sup-', [status(thm)], ['116', '133'])).
% 0.48/0.63  thf('135', plain,
% 0.48/0.63      (((sk_A)
% 0.48/0.63         = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))),
% 0.48/0.63      inference('demod', [status(thm)], ['100', '101'])).
% 0.48/0.63  thf('136', plain, ((v1_relat_1 @ sk_B)),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('137', plain, ((v1_funct_1 @ sk_B)),
% 0.48/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.63  thf('138', plain, (((sk_A) != (sk_A))),
% 0.48/0.63      inference('demod', [status(thm)], ['134', '135', '136', '137'])).
% 0.48/0.63  thf('139', plain, ($false), inference('simplify', [status(thm)], ['138'])).
% 0.48/0.63  
% 0.48/0.63  % SZS output end Refutation
% 0.48/0.63  
% 0.49/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
