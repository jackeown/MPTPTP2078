%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0643+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.p27tLOnLZx

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:15 EST 2020

% Result     : Theorem 4.09s
% Output     : Refutation 4.09s
% Verified   : 
% Statistics : Number of formulae       :  237 (1203 expanded)
%              Number of leaves         :   29 ( 346 expanded)
%              Depth                    :   30
%              Number of atoms          : 2650 (23464 expanded)
%              Number of equality atoms :  195 (2628 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(t50_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( ( ( k1_relat_1 @ B )
                = A )
              & ( ( k1_relat_1 @ C )
                = A )
              & ( r1_tarski @ ( k2_relat_1 @ C ) @ A )
              & ( v2_funct_1 @ B )
              & ( ( k5_relat_1 @ C @ B )
                = B ) )
           => ( C
              = ( k6_relat_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ( ( ( ( k1_relat_1 @ B )
                  = A )
                & ( ( k1_relat_1 @ C )
                  = A )
                & ( r1_tarski @ ( k2_relat_1 @ C ) @ A )
                & ( v2_funct_1 @ B )
                & ( ( k5_relat_1 @ C @ B )
                  = B ) )
             => ( C
                = ( k6_relat_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_funct_1])).

thf('0',plain,
    ( ( k5_relat_1 @ sk_C_3 @ sk_B_1 )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ( ( ( k1_relat_1 @ B )
            = A )
          & ! [C: $i] :
              ( ( r2_hidden @ C @ A )
             => ( ( k1_funct_1 @ B @ C )
                = C ) ) ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k1_relat_1 @ X16 )
       != X15 )
      | ( r2_hidden @ ( sk_C_2 @ X16 @ X15 ) @ X15 )
      | ( X16
        = ( k6_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('2',plain,(
    ! [X16: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( X16
        = ( k6_relat_1 @ ( k1_relat_1 @ X16 ) ) )
      | ( r2_hidden @ ( sk_C_2 @ X16 @ ( k1_relat_1 @ X16 ) ) @ ( k1_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

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

thf('3',plain,(
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

thf('4',plain,(
    ! [X1: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ X6 ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_2 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_2 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( X3
       != ( k2_relat_1 @ X1 ) )
      | ( X4
        = ( k1_funct_1 @ X1 @ ( sk_D_1 @ X4 @ X1 ) ) )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('8',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X1 ) )
      | ( X4
        = ( k1_funct_1 @ X1 @ ( sk_D_1 @ X4 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ ( sk_C_2 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( k1_funct_1 @ X0 @ ( sk_C_2 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ X0 @ ( sk_C_2 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( k1_funct_1 @ X0 @ ( sk_C_2 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_2 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('12',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( X3
       != ( k2_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ X4 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('13',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ X4 @ X1 ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ X0 @ ( sk_C_2 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ X0 @ ( sk_C_2 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

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

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X11 @ X10 ) @ X12 )
        = ( k1_funct_1 @ X10 @ ( k1_funct_1 @ X11 @ X12 ) ) )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_D_1 @ ( k1_funct_1 @ X0 @ ( sk_C_2 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ X0 ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( k1_funct_1 @ X0 @ ( sk_C_2 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_D_1 @ ( k1_funct_1 @ X0 @ ( sk_C_2 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ X0 ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( k1_funct_1 @ X0 @ ( sk_C_2 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_D_1 @ ( k1_funct_1 @ X0 @ ( sk_C_2 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ X0 ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_C_2 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_D_1 @ ( k1_funct_1 @ X0 @ ( sk_C_2 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ X0 ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_C_2 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ ( k1_relat_1 @ sk_C_3 ) ) ) @ sk_C_3 ) )
      = ( k1_funct_1 @ sk_B_1 @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ ( k1_relat_1 @ sk_C_3 ) ) ) ) )
    | ( sk_C_3
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C_3 ) ) )
    | ~ ( v1_funct_1 @ sk_C_3 )
    | ~ ( v1_relat_1 @ sk_C_3 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['0','20'])).

thf('22',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_C_3 ) )
      = ( k1_funct_1 @ sk_B_1 @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) ) )
    | ( sk_C_3
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25','26','27','28'])).

thf('30',plain,(
    sk_C_3
 != ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_C_3 ) )
    = ( k1_funct_1 @ sk_B_1 @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_2 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('34',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ ( k2_relat_1 @ sk_C_3 ) )
    | ( sk_C_3
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C_3 ) ) )
    | ~ ( v1_funct_1 @ sk_C_3 )
    | ~ ( v1_relat_1 @ sk_C_3 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ ( k2_relat_1 @ sk_C_3 ) )
    | ( sk_C_3
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,(
    sk_C_3
 != ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ ( k2_relat_1 @ sk_C_3 ) ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X1 ) )
      | ( X4
        = ( k1_funct_1 @ X1 @ ( sk_D_1 @ X4 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('42',plain,
    ( ( ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) )
      = ( k1_funct_1 @ sk_C_3 @ ( sk_D_1 @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_C_3 ) ) )
    | ~ ( v1_funct_1 @ sk_C_3 )
    | ~ ( v1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) )
    = ( k1_funct_1 @ sk_C_3 @ ( sk_D_1 @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ! [X16: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( X16
        = ( k6_relat_1 @ ( k1_relat_1 @ X16 ) ) )
      | ( r2_hidden @ ( sk_C_2 @ X16 @ ( k1_relat_1 @ X16 ) ) @ ( k1_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(d8_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
      <=> ! [B: $i,C: $i] :
            ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
              & ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
              & ( ( k1_funct_1 @ A @ B )
                = ( k1_funct_1 @ A @ C ) ) )
           => ( B = C ) ) ) ) )).

thf('47',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X7 ) )
      | ( ( k1_funct_1 @ X7 @ X8 )
       != ( k1_funct_1 @ X7 @ X9 ) )
      | ( X8 = X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_C_2 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X1 )
      | ( ( k1_funct_1 @ X0 @ ( sk_C_2 @ X0 @ ( k1_relat_1 @ X0 ) ) )
       != ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ ( sk_C_2 @ X0 @ ( k1_relat_1 @ X0 ) ) )
       != ( k1_funct_1 @ X0 @ X1 ) )
      | ( ( sk_C_2 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ ( k1_relat_1 @ sk_C_3 ) ) )
     != ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) )
    | ( sk_C_3
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C_3 ) ) )
    | ~ ( v1_funct_1 @ sk_C_3 )
    | ~ ( v1_relat_1 @ sk_C_3 )
    | ( ( sk_C_2 @ sk_C_3 @ ( k1_relat_1 @ sk_C_3 ) )
      = ( sk_D_1 @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_C_3 ) )
    | ~ ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_C_3 ) @ ( k1_relat_1 @ sk_C_3 ) )
    | ~ ( v2_funct_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['45','49'])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ ( k2_relat_1 @ sk_C_3 ) ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

thf('58',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ X4 @ X1 ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('59',plain,
    ( ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_C_3 ) @ ( k1_relat_1 @ sk_C_3 ) )
    | ~ ( v1_funct_1 @ sk_C_3 )
    | ~ ( v1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_C_3 ) @ sk_A ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,
    ( ( ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) )
     != ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) )
    | ( sk_C_3
      = ( k6_relat_1 @ sk_A ) )
    | ( ( sk_C_2 @ sk_C_3 @ sk_A )
      = ( sk_D_1 @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_C_3 ) )
    | ~ ( v2_funct_1 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['50','51','52','53','54','55','56','63'])).

thf('65',plain,
    ( ~ ( v2_funct_1 @ sk_C_3 )
    | ( ( sk_C_2 @ sk_C_3 @ sk_A )
      = ( sk_D_1 @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_C_3 ) )
    | ( sk_C_3
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    sk_C_3
 != ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ~ ( v2_funct_1 @ sk_C_3 )
    | ( ( sk_C_2 @ sk_C_3 @ sk_A )
      = ( sk_D_1 @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_C_3 ) ) ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X16: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( X16
        = ( k6_relat_1 @ ( k1_relat_1 @ X16 ) ) )
      | ( r2_hidden @ ( sk_C_2 @ X16 @ ( k1_relat_1 @ X16 ) ) @ ( k1_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('70',plain,
    ( ( r2_hidden @ ( sk_C_2 @ sk_C_3 @ sk_A ) @ ( k1_relat_1 @ sk_C_3 ) )
    | ( sk_C_3
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C_3 ) ) )
    | ~ ( v1_funct_1 @ sk_C_3 )
    | ~ ( v1_relat_1 @ sk_C_3 ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( r2_hidden @ ( sk_C_2 @ sk_C_3 @ sk_A ) @ sk_A )
    | ( sk_C_3
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71','72','73','74'])).

thf('76',plain,(
    sk_C_3
 != ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    r2_hidden @ ( sk_C_2 @ sk_C_3 @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X1: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ X6 ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B_1 @ X0 ) @ ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B_1 @ X0 ) @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['77','83'])).

thf('85',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X1 ) )
      | ( X4
        = ( k1_funct_1 @ X1 @ ( sk_D_1 @ X4 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('86',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) )
      = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X7 ) )
      | ( ( k1_funct_1 @ X7 @ X8 )
       != ( k1_funct_1 @ X7 @ X9 ) )
      | ( X8 = X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['92','93','94','95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_B_1 )
        = X0 )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','97'])).

thf('99',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['77','83'])).

thf('100',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ X4 @ X1 ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('101',plain,
    ( ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['101','102','103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_B_1 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['98','105'])).

thf('107',plain,
    ( ( ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_B_1 )
      = ( sk_C_2 @ sk_C_3 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_C_2 @ sk_C_3 @ sk_A ) @ sk_A ) ),
    inference(eq_res,[status(thm)],['106'])).

thf('108',plain,(
    r2_hidden @ ( sk_C_2 @ sk_C_3 @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['75','76'])).

thf('109',plain,
    ( ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_B_1 )
    = ( sk_C_2 @ sk_C_3 @ sk_A ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X7: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X7 ) @ ( k1_relat_1 @ X7 ) )
      | ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('112',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_C_3 ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C_3 )
    | ~ ( v1_funct_1 @ sk_C_3 )
    | ( v2_funct_1 @ sk_C_3 ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_C_3 ) @ sk_A )
    | ( v2_funct_1 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,
    ( ( k5_relat_1 @ sk_C_3 @ sk_B_1 )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X7: $i] :
      ( ( r2_hidden @ ( sk_B @ X7 ) @ ( k1_relat_1 @ X7 ) )
      | ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('118',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X11 @ X10 ) @ X12 )
        = ( k1_funct_1 @ X10 @ ( k1_funct_1 @ X11 @ X12 ) ) )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_B @ X0 ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_B @ X0 ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X7: $i] :
      ( ( ( k1_funct_1 @ X7 @ ( sk_B @ X7 ) )
        = ( k1_funct_1 @ X7 @ ( sk_C_1 @ X7 ) ) )
      | ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('122',plain,(
    ! [X7: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X7 ) @ ( k1_relat_1 @ X7 ) )
      | ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('123',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X11 @ X10 ) @ X12 )
        = ( k1_funct_1 @ X10 @ ( k1_funct_1 @ X11 @ X12 ) ) )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_C_1 @ X0 ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_C_1 @ X0 ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X0 ) ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_C_1 @ X0 ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['121','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_C_1 @ X0 ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_C_1 @ X0 ) )
        = ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['120','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_C_1 @ X0 ) )
        = ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_1 @ sk_C_3 ) )
      = ( k1_funct_1 @ ( k5_relat_1 @ sk_C_3 @ sk_B_1 ) @ ( sk_B @ sk_C_3 ) ) )
    | ~ ( v1_relat_1 @ sk_C_3 )
    | ~ ( v1_funct_1 @ sk_C_3 )
    | ( v2_funct_1 @ sk_C_3 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['116','129'])).

thf('131',plain,
    ( ( k5_relat_1 @ sk_C_3 @ sk_B_1 )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_1 @ sk_C_3 ) )
      = ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_C_3 ) ) )
    | ( v2_funct_1 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['130','131','132','133','134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['92','93','94','95','96'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_C_3 ) )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ( v2_funct_1 @ sk_C_3 )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( sk_C_1 @ sk_C_3 )
        = X0 )
      | ~ ( r2_hidden @ ( sk_C_1 @ sk_C_3 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ sk_C_3 )
      | ( ( sk_C_1 @ sk_C_3 )
        = X0 )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( v2_funct_1 @ sk_C_3 )
      | ( ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_C_3 ) )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['115','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_C_3 ) )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( sk_C_1 @ sk_C_3 )
        = X0 )
      | ( v2_funct_1 @ sk_C_3 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,
    ( ( v2_funct_1 @ sk_C_3 )
    | ( ( sk_C_1 @ sk_C_3 )
      = ( sk_B @ sk_C_3 ) )
    | ~ ( r2_hidden @ ( sk_B @ sk_C_3 ) @ sk_A ) ),
    inference(eq_res,[status(thm)],['140'])).

thf('142',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X7: $i] :
      ( ( r2_hidden @ ( sk_B @ X7 ) @ ( k1_relat_1 @ X7 ) )
      | ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('144',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_3 ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C_3 )
    | ~ ( v1_funct_1 @ sk_C_3 )
    | ( v2_funct_1 @ sk_C_3 ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_3 ) @ sk_A )
    | ( v2_funct_1 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['144','145','146'])).

thf('148',plain,
    ( ( ( sk_C_1 @ sk_C_3 )
      = ( sk_B @ sk_C_3 ) )
    | ( v2_funct_1 @ sk_C_3 ) ),
    inference(clc,[status(thm)],['141','147'])).

thf('149',plain,
    ( ~ ( v2_funct_1 @ sk_C_3 )
    | ( ( sk_C_2 @ sk_C_3 @ sk_A )
      = ( sk_D_1 @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_C_3 ) ) ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('150',plain,
    ( ( ( sk_C_1 @ sk_C_3 )
      = ( sk_B @ sk_C_3 ) )
    | ( ( sk_C_2 @ sk_C_3 @ sk_A )
      = ( sk_D_1 @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,
    ( ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_C_3 ) )
    = ( k1_funct_1 @ sk_B_1 @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('152',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) )
      = ( k1_funct_1 @ sk_B_1 @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) ) )
    | ( ( sk_C_1 @ sk_C_3 )
      = ( sk_B @ sk_C_3 ) ) ),
    inference('sup+',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_B_1 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['98','105'])).

thf('154',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) )
     != ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) )
    | ( ( sk_C_1 @ sk_C_3 )
      = ( sk_B @ sk_C_3 ) )
    | ( ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_B_1 )
      = ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) )
    | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_2 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('156',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_3 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('157',plain,(
    ! [X18: $i,X20: $i] :
      ( ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('158',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_3 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('159',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( m1_subset_1 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,
    ( ( sk_C_3
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C_3 ) ) )
    | ~ ( v1_funct_1 @ sk_C_3 )
    | ~ ( v1_relat_1 @ sk_C_3 )
    | ( m1_subset_1 @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ ( k1_relat_1 @ sk_C_3 ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['155','160'])).

thf('162',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( sk_C_3
      = ( k6_relat_1 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['161','162','163','164','165'])).

thf('167',plain,(
    sk_C_3
 != ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['166','167'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('169',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('170',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    r2_hidden @ ( sk_C_2 @ sk_C_3 @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['75','76'])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('172',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('173',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_A ),
    inference(clc,[status(thm)],['170','173'])).

thf('175',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) )
     != ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) )
    | ( ( sk_C_1 @ sk_C_3 )
      = ( sk_B @ sk_C_3 ) )
    | ( ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_B_1 )
      = ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['154','174'])).

thf('176',plain,
    ( ( ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_B_1 )
      = ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) )
    | ( ( sk_C_1 @ sk_C_3 )
      = ( sk_B @ sk_C_3 ) ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,
    ( ( ( sk_C_2 @ sk_C_3 @ sk_A )
      = ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) )
    | ( ( sk_C_1 @ sk_C_3 )
      = ( sk_B @ sk_C_3 ) ) ),
    inference('sup+',[status(thm)],['109','176'])).

thf('178',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k1_relat_1 @ X16 )
       != X15 )
      | ( ( k1_funct_1 @ X16 @ ( sk_C_2 @ X16 @ X15 ) )
       != ( sk_C_2 @ X16 @ X15 ) )
      | ( X16
        = ( k6_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('180',plain,(
    ! [X16: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( X16
        = ( k6_relat_1 @ ( k1_relat_1 @ X16 ) ) )
      | ( ( k1_funct_1 @ X16 @ ( sk_C_2 @ X16 @ ( k1_relat_1 @ X16 ) ) )
       != ( sk_C_2 @ X16 @ ( k1_relat_1 @ X16 ) ) ) ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,
    ( ( ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) )
     != ( sk_C_2 @ sk_C_3 @ ( k1_relat_1 @ sk_C_3 ) ) )
    | ( sk_C_3
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C_3 ) ) )
    | ~ ( v1_funct_1 @ sk_C_3 )
    | ~ ( v1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['178','180'])).

thf('182',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) )
     != ( sk_C_2 @ sk_C_3 @ sk_A ) )
    | ( sk_C_3
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['181','182','183','184','185'])).

thf('187',plain,(
    sk_C_3
 != ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) )
 != ( sk_C_2 @ sk_C_3 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['186','187'])).

thf('189',plain,
    ( ( sk_C_1 @ sk_C_3 )
    = ( sk_B @ sk_C_3 ) ),
    inference('simplify_reflect-',[status(thm)],['177','188'])).

thf('190',plain,(
    ! [X7: $i] :
      ( ( ( sk_B @ X7 )
       != ( sk_C_1 @ X7 ) )
      | ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('191',plain,
    ( ( ( sk_B @ sk_C_3 )
     != ( sk_B @ sk_C_3 ) )
    | ~ ( v1_relat_1 @ sk_C_3 )
    | ~ ( v1_funct_1 @ sk_C_3 )
    | ( v2_funct_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( ( sk_B @ sk_C_3 )
     != ( sk_B @ sk_C_3 ) )
    | ( v2_funct_1 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['191','192','193'])).

thf('195',plain,(
    v2_funct_1 @ sk_C_3 ),
    inference(simplify,[status(thm)],['194'])).

thf('196',plain,
    ( ( sk_C_2 @ sk_C_3 @ sk_A )
    = ( sk_D_1 @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_C_3 ) ),
    inference(demod,[status(thm)],['67','195'])).

thf('197',plain,
    ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) )
    = ( k1_funct_1 @ sk_B_1 @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_B_1 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['98','105'])).

thf('199',plain,
    ( ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_B_1 )
    = ( sk_C_2 @ sk_C_3 @ sk_A ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( sk_C_2 @ sk_C_3 @ sk_A )
        = X0 ) ) ),
    inference(demod,[status(thm)],['198','199'])).

thf('201',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) )
     != ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) )
    | ( ( sk_C_2 @ sk_C_3 @ sk_A )
      = ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) )
    | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['197','200'])).

thf('202',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) @ sk_A ),
    inference(clc,[status(thm)],['170','173'])).

thf('203',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) )
     != ( k1_funct_1 @ sk_B_1 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) )
    | ( ( sk_C_2 @ sk_C_3 @ sk_A )
      = ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,
    ( ( sk_C_2 @ sk_C_3 @ sk_A )
    = ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,(
    ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_C_3 @ sk_A ) )
 != ( sk_C_2 @ sk_C_3 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['186','187'])).

thf('206',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['204','205'])).


%------------------------------------------------------------------------------
