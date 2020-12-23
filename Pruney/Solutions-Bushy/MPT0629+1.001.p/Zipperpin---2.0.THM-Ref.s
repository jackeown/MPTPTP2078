%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0629+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xKXUgMtYRX

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:13 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 158 expanded)
%              Number of leaves         :   17 (  55 expanded)
%              Depth                    :   13
%              Number of atoms          :  642 (2003 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t25_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k2_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
           => ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ( ( r2_hidden @ A @ ( k2_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
             => ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_funct_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(fc2_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('3',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ),
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

thf('4',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( X3
       != ( k2_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ X4 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('5',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ X4 @ X1 ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8','9','10','11'])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( r2_hidden @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

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

thf('17',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ ( k5_relat_1 @ X11 @ X13 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X11 @ X12 ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['18','19','20','21','22'])).

thf('24',plain,(
    ! [X1: $i,X3: $i,X5: $i,X6: $i] :
      ( ( X3
       != ( k2_relat_1 @ X1 ) )
      | ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X1 ) )
      | ( X5
       != ( k1_funct_1 @ X1 @ X6 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('25',plain,(
    ! [X1: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ X6 ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_C_1 @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_C_1 @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

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

thf('31',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X14 @ X15 ) @ X16 )
        = ( k1_funct_1 @ X15 @ ( k1_funct_1 @ X14 @ X16 ) ) )
      | ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ ( k5_relat_1 @ X14 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) )
      = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_C_1 @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('36',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('37',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( X3
       != ( k2_relat_1 @ X1 ) )
      | ( X4
        = ( k1_funct_1 @ X1 @ ( sk_D_1 @ X4 @ X1 ) ) )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('39',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X1 ) )
      | ( X4
        = ( k1_funct_1 @ X1 @ ( sk_D_1 @ X4 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( sk_A
      = ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) )
    | ( sk_A
      = ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['36','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) )
    | ( sk_A
      = ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['41','42','43','44','45'])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_A
      = ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['35','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( sk_A
    = ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_C_1 @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['32','33','34','50','51','52'])).

thf('54',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['0','54'])).


%------------------------------------------------------------------------------
