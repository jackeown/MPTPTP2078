%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jByJbzdZcs

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 187 expanded)
%              Number of leaves         :   18 (  61 expanded)
%              Depth                    :   14
%              Number of atoms          :  697 (2997 expanded)
%              Number of equality atoms :   49 ( 225 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('1',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

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

thf('2',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_relat_1 @ X11 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

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

thf('4',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X9 @ X8 ) @ X10 )
        = ( k1_funct_1 @ X8 @ ( k1_funct_1 @ X9 @ X10 ) ) )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X2 ) @ X1 )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( X3
       != ( k2_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ X4 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('9',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ X4 @ X1 ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['10','11','12'])).

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

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X12 ) )
      | ( X13
        = ( k1_funct_1 @ ( k2_funct_1 @ X12 ) @ ( k1_funct_1 @ X12 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t56_funct_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( X3
       != ( k2_relat_1 @ X1 ) )
      | ( X4
        = ( k1_funct_1 @ X1 @ ( sk_D_1 @ X4 @ X1 ) ) )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('20',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X1 ) )
      | ( X4
        = ( k1_funct_1 @ X1 @ ( sk_D_1 @ X4 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( sk_A
      = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17','24','25'])).

thf('27',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','26','27','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['0','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17','24','25'])).

thf('42',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['39'])).

thf('43',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('45',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
    | ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['39'])).

thf('48',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['46','47'])).

thf('49',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['40','48'])).

thf('50',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['38','49'])).

thf('51',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('52',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,(
    $false ),
    inference(simplify,[status(thm)],['54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jByJbzdZcs
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:31:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 117 iterations in 0.108s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.56  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.20/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.56  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.56  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.56  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.56  thf(dt_k2_funct_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.56       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.20/0.56         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.20/0.56  thf('0', plain,
% 0.20/0.56      (![X7 : $i]:
% 0.20/0.56         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 0.20/0.56          | ~ (v1_funct_1 @ X7)
% 0.20/0.56          | ~ (v1_relat_1 @ X7))),
% 0.20/0.56      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.56  thf('1', plain,
% 0.20/0.56      (![X7 : $i]:
% 0.20/0.56         ((v1_funct_1 @ (k2_funct_1 @ X7))
% 0.20/0.56          | ~ (v1_funct_1 @ X7)
% 0.20/0.56          | ~ (v1_relat_1 @ X7))),
% 0.20/0.56      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.56  thf(t57_funct_1, conjecture,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.56       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.20/0.56         ( ( ( A ) =
% 0.20/0.56             ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.20/0.56           ( ( A ) =
% 0.20/0.56             ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i,B:$i]:
% 0.20/0.56        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.56          ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.20/0.56            ( ( ( A ) =
% 0.20/0.56                ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.20/0.56              ( ( A ) =
% 0.20/0.56                ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t57_funct_1])).
% 0.20/0.56  thf('2', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(t55_funct_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.56       ( ( v2_funct_1 @ A ) =>
% 0.20/0.56         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.20/0.56           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.20/0.56  thf('3', plain,
% 0.20/0.56      (![X11 : $i]:
% 0.20/0.56         (~ (v2_funct_1 @ X11)
% 0.20/0.56          | ((k2_relat_1 @ X11) = (k1_relat_1 @ (k2_funct_1 @ X11)))
% 0.20/0.56          | ~ (v1_funct_1 @ X11)
% 0.20/0.56          | ~ (v1_relat_1 @ X11))),
% 0.20/0.56      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.20/0.56  thf(t23_funct_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.56       ( ![C:$i]:
% 0.20/0.56         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.56           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.56             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.20/0.56               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.20/0.56  thf('4', plain,
% 0.20/0.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.56         (~ (v1_relat_1 @ X8)
% 0.20/0.56          | ~ (v1_funct_1 @ X8)
% 0.20/0.56          | ((k1_funct_1 @ (k5_relat_1 @ X9 @ X8) @ X10)
% 0.20/0.56              = (k1_funct_1 @ X8 @ (k1_funct_1 @ X9 @ X10)))
% 0.20/0.56          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X9))
% 0.20/0.56          | ~ (v1_funct_1 @ X9)
% 0.20/0.56          | ~ (v1_relat_1 @ X9))),
% 0.20/0.56      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.20/0.56  thf('5', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.20/0.56          | ~ (v1_relat_1 @ X0)
% 0.20/0.56          | ~ (v1_funct_1 @ X0)
% 0.20/0.56          | ~ (v2_funct_1 @ X0)
% 0.20/0.56          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.56          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.56          | ((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X2) @ X1)
% 0.20/0.56              = (k1_funct_1 @ X2 @ (k1_funct_1 @ (k2_funct_1 @ X0) @ X1)))
% 0.20/0.56          | ~ (v1_funct_1 @ X2)
% 0.20/0.56          | ~ (v1_relat_1 @ X2))),
% 0.38/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.56  thf('6', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X0)
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ sk_A)
% 0.38/0.56              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 0.38/0.56          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.38/0.56          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.38/0.56          | ~ (v2_funct_1 @ sk_B)
% 0.38/0.56          | ~ (v1_funct_1 @ sk_B)
% 0.38/0.56          | ~ (v1_relat_1 @ sk_B))),
% 0.38/0.56      inference('sup-', [status(thm)], ['2', '5'])).
% 0.38/0.56  thf('7', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(d5_funct_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.38/0.56           ( ![C:$i]:
% 0.38/0.56             ( ( r2_hidden @ C @ B ) <=>
% 0.38/0.56               ( ?[D:$i]:
% 0.38/0.56                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.38/0.56                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.38/0.56  thf('8', plain,
% 0.38/0.56      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.38/0.56         (((X3) != (k2_relat_1 @ X1))
% 0.38/0.56          | (r2_hidden @ (sk_D_1 @ X4 @ X1) @ (k1_relat_1 @ X1))
% 0.38/0.56          | ~ (r2_hidden @ X4 @ X3)
% 0.38/0.56          | ~ (v1_funct_1 @ X1)
% 0.38/0.56          | ~ (v1_relat_1 @ X1))),
% 0.38/0.56      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.38/0.56  thf('9', plain,
% 0.38/0.56      (![X1 : $i, X4 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X1)
% 0.38/0.56          | ~ (v1_funct_1 @ X1)
% 0.38/0.56          | ~ (r2_hidden @ X4 @ (k2_relat_1 @ X1))
% 0.38/0.56          | (r2_hidden @ (sk_D_1 @ X4 @ X1) @ (k1_relat_1 @ X1)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['8'])).
% 0.38/0.56  thf('10', plain,
% 0.38/0.56      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.38/0.56        | ~ (v1_funct_1 @ sk_B)
% 0.38/0.56        | ~ (v1_relat_1 @ sk_B))),
% 0.38/0.56      inference('sup-', [status(thm)], ['7', '9'])).
% 0.38/0.56  thf('11', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('13', plain,
% 0.38/0.56      ((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))),
% 0.38/0.56      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.38/0.56  thf(t56_funct_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.56       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 0.38/0.56         ( ( ( A ) =
% 0.38/0.56             ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 0.38/0.56           ( ( A ) =
% 0.38/0.56             ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ))).
% 0.38/0.56  thf('14', plain,
% 0.38/0.56      (![X12 : $i, X13 : $i]:
% 0.38/0.56         (~ (v2_funct_1 @ X12)
% 0.38/0.56          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X12))
% 0.38/0.56          | ((X13)
% 0.38/0.56              = (k1_funct_1 @ (k2_funct_1 @ X12) @ (k1_funct_1 @ X12 @ X13)))
% 0.38/0.56          | ~ (v1_funct_1 @ X12)
% 0.38/0.56          | ~ (v1_relat_1 @ X12))),
% 0.38/0.56      inference('cnf', [status(esa)], [t56_funct_1])).
% 0.38/0.56  thf('15', plain,
% 0.38/0.56      ((~ (v1_relat_1 @ sk_B)
% 0.38/0.56        | ~ (v1_funct_1 @ sk_B)
% 0.38/0.56        | ((sk_D_1 @ sk_A @ sk_B)
% 0.38/0.56            = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 0.38/0.56               (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B))))
% 0.38/0.56        | ~ (v2_funct_1 @ sk_B))),
% 0.38/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.38/0.56  thf('16', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('17', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('18', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('19', plain,
% 0.38/0.56      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.38/0.56         (((X3) != (k2_relat_1 @ X1))
% 0.38/0.56          | ((X4) = (k1_funct_1 @ X1 @ (sk_D_1 @ X4 @ X1)))
% 0.38/0.56          | ~ (r2_hidden @ X4 @ X3)
% 0.38/0.56          | ~ (v1_funct_1 @ X1)
% 0.38/0.56          | ~ (v1_relat_1 @ X1))),
% 0.38/0.56      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.38/0.56  thf('20', plain,
% 0.38/0.56      (![X1 : $i, X4 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X1)
% 0.38/0.56          | ~ (v1_funct_1 @ X1)
% 0.38/0.56          | ~ (r2_hidden @ X4 @ (k2_relat_1 @ X1))
% 0.38/0.56          | ((X4) = (k1_funct_1 @ X1 @ (sk_D_1 @ X4 @ X1))))),
% 0.38/0.56      inference('simplify', [status(thm)], ['19'])).
% 0.38/0.56  thf('21', plain,
% 0.38/0.56      ((((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))
% 0.38/0.56        | ~ (v1_funct_1 @ sk_B)
% 0.38/0.56        | ~ (v1_relat_1 @ sk_B))),
% 0.38/0.56      inference('sup-', [status(thm)], ['18', '20'])).
% 0.38/0.56  thf('22', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('24', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 0.38/0.56      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.38/0.56  thf('25', plain, ((v2_funct_1 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('26', plain,
% 0.38/0.56      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['15', '16', '17', '24', '25'])).
% 0.38/0.56  thf('27', plain, ((v2_funct_1 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('28', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('30', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X0)
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ sk_A)
% 0.38/0.56              = (k1_funct_1 @ X0 @ (sk_D_1 @ sk_A @ sk_B)))
% 0.38/0.56          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.38/0.56          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.38/0.56      inference('demod', [status(thm)], ['6', '26', '27', '28', '29'])).
% 0.38/0.56  thf('31', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ sk_B)
% 0.38/0.56          | ~ (v1_funct_1 @ sk_B)
% 0.38/0.56          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.38/0.56          | ((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ sk_A)
% 0.38/0.56              = (k1_funct_1 @ X0 @ (sk_D_1 @ sk_A @ sk_B)))
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_relat_1 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['1', '30'])).
% 0.38/0.56  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('33', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('34', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.38/0.56          | ((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ sk_A)
% 0.38/0.56              = (k1_funct_1 @ X0 @ (sk_D_1 @ sk_A @ sk_B)))
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_relat_1 @ X0))),
% 0.38/0.56      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.38/0.56  thf('35', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ sk_B)
% 0.38/0.56          | ~ (v1_funct_1 @ sk_B)
% 0.38/0.56          | ~ (v1_relat_1 @ X0)
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ sk_A)
% 0.38/0.56              = (k1_funct_1 @ X0 @ (sk_D_1 @ sk_A @ sk_B))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['0', '34'])).
% 0.38/0.56  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('37', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('38', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X0)
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ sk_A)
% 0.38/0.56              = (k1_funct_1 @ X0 @ (sk_D_1 @ sk_A @ sk_B))))),
% 0.38/0.56      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.38/0.56  thf('39', plain,
% 0.38/0.56      ((((sk_A)
% 0.38/0.56          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 0.38/0.56        | ((sk_A)
% 0.38/0.56            != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('40', plain,
% 0.38/0.56      ((((sk_A)
% 0.38/0.56          != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))
% 0.38/0.56         <= (~
% 0.38/0.56             (((sk_A)
% 0.38/0.56                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.38/0.56                   sk_A))))),
% 0.38/0.56      inference('split', [status(esa)], ['39'])).
% 0.38/0.56  thf('41', plain,
% 0.38/0.56      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['15', '16', '17', '24', '25'])).
% 0.38/0.56  thf('42', plain,
% 0.38/0.56      ((((sk_A)
% 0.38/0.56          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))
% 0.38/0.56         <= (~
% 0.38/0.56             (((sk_A)
% 0.38/0.56                = (k1_funct_1 @ sk_B @ 
% 0.38/0.56                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.38/0.56      inference('split', [status(esa)], ['39'])).
% 0.38/0.56  thf('43', plain,
% 0.38/0.56      ((((sk_A) != (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B))))
% 0.38/0.56         <= (~
% 0.38/0.56             (((sk_A)
% 0.38/0.56                = (k1_funct_1 @ sk_B @ 
% 0.38/0.56                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['41', '42'])).
% 0.38/0.56  thf('44', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 0.38/0.56      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.38/0.56  thf('45', plain,
% 0.38/0.56      ((((sk_A) != (sk_A)))
% 0.38/0.56         <= (~
% 0.38/0.56             (((sk_A)
% 0.38/0.56                = (k1_funct_1 @ sk_B @ 
% 0.38/0.56                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.38/0.56      inference('demod', [status(thm)], ['43', '44'])).
% 0.38/0.56  thf('46', plain,
% 0.38/0.56      ((((sk_A)
% 0.38/0.56          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.38/0.56      inference('simplify', [status(thm)], ['45'])).
% 0.38/0.56  thf('47', plain,
% 0.38/0.56      (~
% 0.38/0.56       (((sk_A)
% 0.38/0.56          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A))) | 
% 0.38/0.56       ~
% 0.38/0.56       (((sk_A)
% 0.38/0.56          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.38/0.56      inference('split', [status(esa)], ['39'])).
% 0.38/0.56  thf('48', plain,
% 0.38/0.56      (~
% 0.38/0.56       (((sk_A)
% 0.38/0.56          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.38/0.56      inference('sat_resolution*', [status(thm)], ['46', '47'])).
% 0.38/0.56  thf('49', plain,
% 0.38/0.56      (((sk_A)
% 0.38/0.56         != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A))),
% 0.38/0.56      inference('simpl_trail', [status(thm)], ['40', '48'])).
% 0.38/0.56  thf('50', plain,
% 0.38/0.56      ((((sk_A) != (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))
% 0.38/0.56        | ~ (v1_funct_1 @ sk_B)
% 0.38/0.56        | ~ (v1_relat_1 @ sk_B))),
% 0.38/0.56      inference('sup-', [status(thm)], ['38', '49'])).
% 0.38/0.56  thf('51', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 0.38/0.56      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.38/0.56  thf('52', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('53', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('54', plain, (((sk_A) != (sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.38/0.56  thf('55', plain, ($false), inference('simplify', [status(thm)], ['54'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.38/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
