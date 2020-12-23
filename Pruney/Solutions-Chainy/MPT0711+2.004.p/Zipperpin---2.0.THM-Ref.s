%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.N4Umzmd7ll

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:11 EST 2020

% Result     : Theorem 6.18s
% Output     : Refutation 6.18s
% Verified   : 
% Statistics : Number of formulae       :  196 (1664 expanded)
%              Number of leaves         :   23 ( 569 expanded)
%              Depth                    :   34
%              Number of atoms          : 2059 (19734 expanded)
%              Number of equality atoms :  139 (1720 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t166_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ! [C: $i] :
              ( ( ( ( k1_relat_1 @ A )
                  = ( k1_relat_1 @ B ) )
                & ! [D: $i] :
                    ( ( r2_hidden @ D @ C )
                   => ( ( k1_funct_1 @ A @ D )
                      = ( k1_funct_1 @ B @ D ) ) ) )
             => ( ( k7_relat_1 @ A @ C )
                = ( k7_relat_1 @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ! [C: $i] :
                ( ( ( ( k1_relat_1 @ A )
                    = ( k1_relat_1 @ B ) )
                  & ! [D: $i] :
                      ( ( r2_hidden @ D @ C )
                     => ( ( k1_funct_1 @ A @ D )
                        = ( k1_funct_1 @ B @ D ) ) ) )
               => ( ( k7_relat_1 @ A @ C )
                  = ( k7_relat_1 @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t166_funct_1])).

thf('0',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t89_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf('2',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_A ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) @ ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf(t165_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ! [C: $i] :
              ( ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) )
                & ( r1_tarski @ C @ ( k1_relat_1 @ B ) ) )
             => ( ( ( k7_relat_1 @ A @ C )
                  = ( k7_relat_1 @ B @ C ) )
              <=> ! [D: $i] :
                    ( ( r2_hidden @ D @ C )
                   => ( ( k1_funct_1 @ A @ D )
                      = ( k1_funct_1 @ B @ D ) ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( r2_hidden @ ( sk_D @ X20 @ X19 @ X21 ) @ X20 )
      | ( ( k7_relat_1 @ X21 @ X20 )
        = ( k7_relat_1 @ X19 @ X20 ) )
      | ~ ( r1_tarski @ X20 @ ( k1_relat_1 @ X19 ) )
      | ~ ( r1_tarski @ X20 @ ( k1_relat_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t165_funct_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ( ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) )
        = ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) )
      | ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ sk_A @ X1 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ( ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) )
        = ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) )
      | ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ sk_A @ X1 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf(s3_funct_1__e9_44_1__funct_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ B @ C )
            = k1_xboole_0 ) )
      & ( ( k1_relat_1 @ B )
        = A )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('23',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( sk_B @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( sk_B @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( sk_B @ ( k1_relat_1 @ sk_A ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( sk_B @ ( k1_relat_1 @ sk_A ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['21','28'])).

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('31',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('32',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( sk_B @ X0 ) @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( sk_B @ X0 ) @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ ( sk_B @ X1 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ ( sk_B @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('38',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( sk_B @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( sk_B @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','41','42'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','41','42'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','41','42'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','41','42'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k1_relat_1 @ X1 ) )
      | ( ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
        = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ sk_A @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','43','44','45','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k1_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ sk_A @ sk_B_1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
      | ( ( k7_relat_1 @ sk_B_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
        = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('52',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( sk_B @ X0 ) @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( sk_B @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( sk_B @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ ( sk_B @ X0 ) @ X1 ) ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ ( sk_B @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( sk_B @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ ( sk_B @ X1 ) ) @ X0 ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ ( sk_B @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_B @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( sk_B @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('60',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k1_relat_1 @ ( k7_relat_1 @ ( sk_B @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf(t189_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) )
            = ( k7_relat_1 @ A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) )).

thf('62',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k7_relat_1 @ X7 @ ( k1_relat_1 @ X6 ) )
        = ( k7_relat_1 @ X7 @ ( k1_relat_1 @ ( k7_relat_1 @ X6 @ ( k1_relat_1 @ X7 ) ) ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ ( sk_B @ X1 ) ) )
        = ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('65',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X0 @ X1 )
        = ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_B_1 @ X0 )
        = ( k7_relat_1 @ sk_B_1 @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_A ) ) ) )
      | ~ ( v1_relat_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['52','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B_1 @ X0 )
      = ( k7_relat_1 @ sk_B_1 @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B_1 @ X0 )
      = ( k7_relat_1 @ sk_B_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ sk_A @ sk_B_1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
      | ( ( k7_relat_1 @ sk_B_1 @ X0 )
        = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['49','50','70','71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','41','42'])).

thf('75',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('76',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k7_relat_1 @ X7 @ ( k1_relat_1 @ X6 ) )
        = ( k7_relat_1 @ X7 @ ( k1_relat_1 @ ( k7_relat_1 @ X6 @ ( k1_relat_1 @ X7 ) ) ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf('77',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X0 @ X1 )
        = ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('81',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( sk_B @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k1_relat_1 @ ( k7_relat_1 @ ( sk_B @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = X1 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['82','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf('93',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['91','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = X1 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('106',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k7_relat_1 @ X7 @ ( k1_relat_1 @ X6 ) )
        = ( k7_relat_1 @ X7 @ ( k1_relat_1 @ ( k7_relat_1 @ X6 @ ( k1_relat_1 @ X7 ) ) ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( sk_B @ X0 ) @ ( k1_relat_1 @ X1 ) )
        = ( k7_relat_1 @ ( sk_B @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( sk_B @ X0 ) @ ( k1_relat_1 @ X1 ) )
        = ( k7_relat_1 @ ( sk_B @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k7_relat_1 @ X7 @ ( k1_relat_1 @ X6 ) )
        = ( k7_relat_1 @ X7 @ ( k1_relat_1 @ ( k7_relat_1 @ X6 @ ( k1_relat_1 @ X7 ) ) ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k1_relat_1 @ ( k7_relat_1 @ ( sk_B @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ ( sk_B @ X1 ) ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ ( sk_B @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( sk_B @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k1_relat_1 @ ( k7_relat_1 @ ( sk_B @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('115',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) )
        = ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113','114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ ( sk_B @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ ( sk_B @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['109','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k1_relat_1 @ ( k7_relat_1 @ ( sk_B @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('120',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('122',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) )
        = ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['117','118','119','120','121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['104','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k7_relat_1 @ X7 @ ( k1_relat_1 @ X6 ) )
        = ( k7_relat_1 @ X7 @ ( k1_relat_1 @ ( k7_relat_1 @ X6 @ ( k1_relat_1 @ X7 ) ) ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( sk_B @ X0 ) ) )
        = ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['75','130'])).

thf('132',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('133',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_A @ X0 )
        = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['74','134'])).

thf('136',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_A @ X0 )
      = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ sk_A @ sk_B_1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
      | ( ( k7_relat_1 @ sk_B_1 @ X0 )
        = ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['73','137'])).

thf('139',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('140',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('141',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X9 ) ) )
      | ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['139','143'])).

thf('145',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('146',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_B_1 @ X0 )
        = ( k7_relat_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['138','146'])).

thf('148',plain,(
    ! [X23: $i] :
      ( ( ( k1_funct_1 @ sk_A @ X23 )
        = ( k1_funct_1 @ sk_B_1 @ X23 ) )
      | ~ ( r2_hidden @ X23 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( ( k7_relat_1 @ sk_B_1 @ sk_C )
      = ( k7_relat_1 @ sk_A @ sk_C ) )
    | ( ( k1_funct_1 @ sk_A @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C ) @ sk_A @ sk_B_1 ) )
      = ( k1_funct_1 @ sk_B_1 @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C ) @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('152',plain,
    ( ( ( k7_relat_1 @ sk_B_1 @ sk_C )
      = ( k7_relat_1 @ sk_A @ sk_C ) )
    | ( ( k1_funct_1 @ sk_A @ ( sk_D @ ( k3_xboole_0 @ sk_C @ ( k1_relat_1 @ sk_A ) ) @ sk_A @ sk_B_1 ) )
      = ( k1_funct_1 @ sk_B_1 @ ( sk_D @ ( k3_xboole_0 @ sk_C @ ( k1_relat_1 @ sk_A ) ) @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,(
    ( k7_relat_1 @ sk_A @ sk_C )
 != ( k7_relat_1 @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_D @ ( k3_xboole_0 @ sk_C @ ( k1_relat_1 @ sk_A ) ) @ sk_A @ sk_B_1 ) )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D @ ( k3_xboole_0 @ sk_C @ ( k1_relat_1 @ sk_A ) ) @ sk_A @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( ( k1_funct_1 @ X21 @ ( sk_D @ X20 @ X19 @ X21 ) )
       != ( k1_funct_1 @ X19 @ ( sk_D @ X20 @ X19 @ X21 ) ) )
      | ( ( k7_relat_1 @ X21 @ X20 )
        = ( k7_relat_1 @ X19 @ X20 ) )
      | ~ ( r1_tarski @ X20 @ ( k1_relat_1 @ X19 ) )
      | ~ ( r1_tarski @ X20 @ ( k1_relat_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t165_funct_1])).

thf('156',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_D @ ( k3_xboole_0 @ sk_C @ ( k1_relat_1 @ sk_A ) ) @ sk_A @ sk_B_1 ) )
     != ( k1_funct_1 @ sk_A @ ( sk_D @ ( k3_xboole_0 @ sk_C @ ( k1_relat_1 @ sk_A ) ) @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_C @ ( k1_relat_1 @ sk_A ) ) @ ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_C @ ( k1_relat_1 @ sk_A ) ) @ ( k1_relat_1 @ sk_A ) )
    | ( ( k7_relat_1 @ sk_B_1 @ ( k3_xboole_0 @ sk_C @ ( k1_relat_1 @ sk_A ) ) )
      = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ ( k1_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B_1 @ X0 )
      = ( k7_relat_1 @ sk_B_1 @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_A @ X0 )
      = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_A @ X0 )
      = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['163','164'])).

thf('166',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_D @ ( k3_xboole_0 @ sk_C @ ( k1_relat_1 @ sk_A ) ) @ sk_A @ sk_B_1 ) )
     != ( k1_funct_1 @ sk_A @ ( sk_D @ ( k3_xboole_0 @ sk_C @ ( k1_relat_1 @ sk_A ) ) @ sk_A @ sk_B_1 ) ) )
    | ( ( k7_relat_1 @ sk_B_1 @ sk_C )
      = ( k7_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['156','157','158','159','160','161','162','165','166','167'])).

thf('169',plain,
    ( ( k7_relat_1 @ sk_B_1 @ sk_C )
    = ( k7_relat_1 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,(
    ( k7_relat_1 @ sk_A @ sk_C )
 != ( k7_relat_1 @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['169','170'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.N4Umzmd7ll
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:26:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.18/6.41  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.18/6.41  % Solved by: fo/fo7.sh
% 6.18/6.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.18/6.41  % done 5479 iterations in 5.948s
% 6.18/6.41  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.18/6.41  % SZS output start Refutation
% 6.18/6.41  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.18/6.41  thf(sk_C_type, type, sk_C: $i).
% 6.18/6.41  thf(sk_B_type, type, sk_B: $i > $i).
% 6.18/6.41  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 6.18/6.41  thf(sk_A_type, type, sk_A: $i).
% 6.18/6.41  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.18/6.41  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 6.18/6.41  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 6.18/6.41  thf(sk_B_1_type, type, sk_B_1: $i).
% 6.18/6.41  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.18/6.41  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.18/6.41  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.18/6.41  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.18/6.41  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.18/6.41  thf(t166_funct_1, conjecture,
% 6.18/6.41    (![A:$i]:
% 6.18/6.41     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.18/6.41       ( ![B:$i]:
% 6.18/6.41         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.18/6.41           ( ![C:$i]:
% 6.18/6.41             ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 6.18/6.41                 ( ![D:$i]:
% 6.18/6.41                   ( ( r2_hidden @ D @ C ) =>
% 6.18/6.41                     ( ( k1_funct_1 @ A @ D ) = ( k1_funct_1 @ B @ D ) ) ) ) ) =>
% 6.18/6.41               ( ( k7_relat_1 @ A @ C ) = ( k7_relat_1 @ B @ C ) ) ) ) ) ) ))).
% 6.18/6.41  thf(zf_stmt_0, negated_conjecture,
% 6.18/6.41    (~( ![A:$i]:
% 6.18/6.41        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.18/6.41          ( ![B:$i]:
% 6.18/6.41            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.18/6.41              ( ![C:$i]:
% 6.18/6.41                ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 6.18/6.41                    ( ![D:$i]:
% 6.18/6.41                      ( ( r2_hidden @ D @ C ) =>
% 6.18/6.41                        ( ( k1_funct_1 @ A @ D ) = ( k1_funct_1 @ B @ D ) ) ) ) ) =>
% 6.18/6.41                  ( ( k7_relat_1 @ A @ C ) = ( k7_relat_1 @ B @ C ) ) ) ) ) ) ) )),
% 6.18/6.41    inference('cnf.neg', [status(esa)], [t166_funct_1])).
% 6.18/6.41  thf('0', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B_1))),
% 6.18/6.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.41  thf(t89_relat_1, axiom,
% 6.18/6.41    (![A:$i,B:$i]:
% 6.18/6.41     ( ( v1_relat_1 @ B ) =>
% 6.18/6.41       ( r1_tarski @
% 6.18/6.41         ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ))).
% 6.18/6.41  thf('1', plain,
% 6.18/6.41      (![X11 : $i, X12 : $i]:
% 6.18/6.41         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X11 @ X12)) @ 
% 6.18/6.41           (k1_relat_1 @ X11))
% 6.18/6.41          | ~ (v1_relat_1 @ X11))),
% 6.18/6.41      inference('cnf', [status(esa)], [t89_relat_1])).
% 6.18/6.41  thf('2', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B_1))),
% 6.18/6.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.41  thf(t91_relat_1, axiom,
% 6.18/6.41    (![A:$i,B:$i]:
% 6.18/6.41     ( ( v1_relat_1 @ B ) =>
% 6.18/6.41       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 6.18/6.41         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 6.18/6.41  thf('3', plain,
% 6.18/6.41      (![X15 : $i, X16 : $i]:
% 6.18/6.41         (~ (r1_tarski @ X15 @ (k1_relat_1 @ X16))
% 6.18/6.41          | ((k1_relat_1 @ (k7_relat_1 @ X16 @ X15)) = (X15))
% 6.18/6.41          | ~ (v1_relat_1 @ X16))),
% 6.18/6.41      inference('cnf', [status(esa)], [t91_relat_1])).
% 6.18/6.41  thf('4', plain,
% 6.18/6.41      (![X0 : $i]:
% 6.18/6.41         (~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_A))
% 6.18/6.41          | ~ (v1_relat_1 @ sk_B_1)
% 6.18/6.41          | ((k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0)) = (X0)))),
% 6.18/6.41      inference('sup-', [status(thm)], ['2', '3'])).
% 6.18/6.41  thf('5', plain, ((v1_relat_1 @ sk_B_1)),
% 6.18/6.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.41  thf('6', plain,
% 6.18/6.41      (![X0 : $i]:
% 6.18/6.41         (~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_A))
% 6.18/6.41          | ((k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0)) = (X0)))),
% 6.18/6.41      inference('demod', [status(thm)], ['4', '5'])).
% 6.18/6.41  thf('7', plain,
% 6.18/6.41      (![X0 : $i]:
% 6.18/6.41         (~ (v1_relat_1 @ sk_A)
% 6.18/6.41          | ((k1_relat_1 @ 
% 6.18/6.41              (k7_relat_1 @ sk_B_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))
% 6.18/6.41              = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))),
% 6.18/6.41      inference('sup-', [status(thm)], ['1', '6'])).
% 6.18/6.41  thf('8', plain, ((v1_relat_1 @ sk_A)),
% 6.18/6.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.41  thf('9', plain,
% 6.18/6.41      (![X0 : $i]:
% 6.18/6.41         ((k1_relat_1 @ 
% 6.18/6.41           (k7_relat_1 @ sk_B_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))
% 6.18/6.41           = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))),
% 6.18/6.41      inference('demod', [status(thm)], ['7', '8'])).
% 6.18/6.41  thf('10', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B_1))),
% 6.18/6.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.41  thf('11', plain,
% 6.18/6.41      (![X11 : $i, X12 : $i]:
% 6.18/6.41         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X11 @ X12)) @ 
% 6.18/6.41           (k1_relat_1 @ X11))
% 6.18/6.41          | ~ (v1_relat_1 @ X11))),
% 6.18/6.41      inference('cnf', [status(esa)], [t89_relat_1])).
% 6.18/6.41  thf('12', plain,
% 6.18/6.41      (![X0 : $i]:
% 6.18/6.41         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0)) @ 
% 6.18/6.41           (k1_relat_1 @ sk_A))
% 6.18/6.41          | ~ (v1_relat_1 @ sk_B_1))),
% 6.18/6.41      inference('sup+', [status(thm)], ['10', '11'])).
% 6.18/6.41  thf('13', plain, ((v1_relat_1 @ sk_B_1)),
% 6.18/6.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.41  thf('14', plain,
% 6.18/6.41      (![X0 : $i]:
% 6.18/6.41         (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0)) @ 
% 6.18/6.41          (k1_relat_1 @ sk_A))),
% 6.18/6.41      inference('demod', [status(thm)], ['12', '13'])).
% 6.18/6.41  thf('15', plain,
% 6.18/6.41      (![X0 : $i]:
% 6.18/6.41         (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ 
% 6.18/6.41          (k1_relat_1 @ sk_A))),
% 6.18/6.41      inference('sup+', [status(thm)], ['9', '14'])).
% 6.18/6.41  thf(t165_funct_1, axiom,
% 6.18/6.41    (![A:$i]:
% 6.18/6.41     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.18/6.41       ( ![B:$i]:
% 6.18/6.41         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.18/6.41           ( ![C:$i]:
% 6.18/6.41             ( ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 6.18/6.41                 ( r1_tarski @ C @ ( k1_relat_1 @ B ) ) ) =>
% 6.18/6.41               ( ( ( k7_relat_1 @ A @ C ) = ( k7_relat_1 @ B @ C ) ) <=>
% 6.18/6.41                 ( ![D:$i]:
% 6.18/6.41                   ( ( r2_hidden @ D @ C ) =>
% 6.18/6.41                     ( ( k1_funct_1 @ A @ D ) = ( k1_funct_1 @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 6.18/6.41  thf('16', plain,
% 6.18/6.41      (![X19 : $i, X20 : $i, X21 : $i]:
% 6.18/6.41         (~ (v1_relat_1 @ X19)
% 6.18/6.41          | ~ (v1_funct_1 @ X19)
% 6.18/6.41          | (r2_hidden @ (sk_D @ X20 @ X19 @ X21) @ X20)
% 6.18/6.41          | ((k7_relat_1 @ X21 @ X20) = (k7_relat_1 @ X19 @ X20))
% 6.18/6.41          | ~ (r1_tarski @ X20 @ (k1_relat_1 @ X19))
% 6.18/6.41          | ~ (r1_tarski @ X20 @ (k1_relat_1 @ X21))
% 6.18/6.41          | ~ (v1_funct_1 @ X21)
% 6.18/6.41          | ~ (v1_relat_1 @ X21))),
% 6.18/6.41      inference('cnf', [status(esa)], [t165_funct_1])).
% 6.18/6.41  thf('17', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (~ (v1_relat_1 @ X1)
% 6.18/6.41          | ~ (v1_funct_1 @ X1)
% 6.18/6.41          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ 
% 6.18/6.41               (k1_relat_1 @ X1))
% 6.18/6.41          | ((k7_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))
% 6.18/6.41              = (k7_relat_1 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))
% 6.18/6.41          | (r2_hidden @ 
% 6.18/6.41             (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ sk_A @ X1) @ 
% 6.18/6.41             (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))
% 6.18/6.41          | ~ (v1_funct_1 @ sk_A)
% 6.18/6.41          | ~ (v1_relat_1 @ sk_A))),
% 6.18/6.41      inference('sup-', [status(thm)], ['15', '16'])).
% 6.18/6.41  thf('18', plain, ((v1_funct_1 @ sk_A)),
% 6.18/6.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.41  thf('19', plain, ((v1_relat_1 @ sk_A)),
% 6.18/6.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.41  thf('20', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (~ (v1_relat_1 @ X1)
% 6.18/6.41          | ~ (v1_funct_1 @ X1)
% 6.18/6.41          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ 
% 6.18/6.41               (k1_relat_1 @ X1))
% 6.18/6.41          | ((k7_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))
% 6.18/6.41              = (k7_relat_1 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))
% 6.18/6.41          | (r2_hidden @ 
% 6.18/6.41             (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ sk_A @ X1) @ 
% 6.18/6.41             (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))),
% 6.18/6.41      inference('demod', [status(thm)], ['17', '18', '19'])).
% 6.18/6.41  thf(t90_relat_1, axiom,
% 6.18/6.41    (![A:$i,B:$i]:
% 6.18/6.41     ( ( v1_relat_1 @ B ) =>
% 6.18/6.41       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 6.18/6.41         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 6.18/6.41  thf('21', plain,
% 6.18/6.41      (![X13 : $i, X14 : $i]:
% 6.18/6.41         (((k1_relat_1 @ (k7_relat_1 @ X13 @ X14))
% 6.18/6.41            = (k3_xboole_0 @ (k1_relat_1 @ X13) @ X14))
% 6.18/6.41          | ~ (v1_relat_1 @ X13))),
% 6.18/6.41      inference('cnf', [status(esa)], [t90_relat_1])).
% 6.18/6.41  thf('22', plain,
% 6.18/6.41      (![X0 : $i]:
% 6.18/6.41         (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ 
% 6.18/6.41          (k1_relat_1 @ sk_A))),
% 6.18/6.41      inference('sup+', [status(thm)], ['9', '14'])).
% 6.18/6.41  thf(s3_funct_1__e9_44_1__funct_1, axiom,
% 6.18/6.41    (![A:$i]:
% 6.18/6.41     ( ?[B:$i]:
% 6.18/6.41       ( ( ![C:$i]:
% 6.18/6.41           ( ( r2_hidden @ C @ A ) =>
% 6.18/6.41             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 6.18/6.41         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 6.18/6.41         ( v1_relat_1 @ B ) ) ))).
% 6.18/6.41  thf('23', plain, (![X17 : $i]: ((k1_relat_1 @ (sk_B @ X17)) = (X17))),
% 6.18/6.41      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 6.18/6.41  thf('24', plain,
% 6.18/6.41      (![X15 : $i, X16 : $i]:
% 6.18/6.41         (~ (r1_tarski @ X15 @ (k1_relat_1 @ X16))
% 6.18/6.41          | ((k1_relat_1 @ (k7_relat_1 @ X16 @ X15)) = (X15))
% 6.18/6.41          | ~ (v1_relat_1 @ X16))),
% 6.18/6.41      inference('cnf', [status(esa)], [t91_relat_1])).
% 6.18/6.41  thf('25', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (~ (r1_tarski @ X1 @ X0)
% 6.18/6.41          | ~ (v1_relat_1 @ (sk_B @ X0))
% 6.18/6.41          | ((k1_relat_1 @ (k7_relat_1 @ (sk_B @ X0) @ X1)) = (X1)))),
% 6.18/6.41      inference('sup-', [status(thm)], ['23', '24'])).
% 6.18/6.41  thf('26', plain, (![X17 : $i]: (v1_relat_1 @ (sk_B @ X17))),
% 6.18/6.41      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 6.18/6.41  thf('27', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (~ (r1_tarski @ X1 @ X0)
% 6.18/6.41          | ((k1_relat_1 @ (k7_relat_1 @ (sk_B @ X0) @ X1)) = (X1)))),
% 6.18/6.41      inference('demod', [status(thm)], ['25', '26'])).
% 6.18/6.41  thf('28', plain,
% 6.18/6.41      (![X0 : $i]:
% 6.18/6.41         ((k1_relat_1 @ 
% 6.18/6.41           (k7_relat_1 @ (sk_B @ (k1_relat_1 @ sk_A)) @ 
% 6.18/6.41            (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))
% 6.18/6.41           = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))),
% 6.18/6.41      inference('sup-', [status(thm)], ['22', '27'])).
% 6.18/6.41  thf('29', plain,
% 6.18/6.41      (![X0 : $i]:
% 6.18/6.41         (((k1_relat_1 @ 
% 6.18/6.41            (k7_relat_1 @ (sk_B @ (k1_relat_1 @ sk_A)) @ 
% 6.18/6.41             (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))
% 6.18/6.41            = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))
% 6.18/6.41          | ~ (v1_relat_1 @ sk_A))),
% 6.18/6.41      inference('sup+', [status(thm)], ['21', '28'])).
% 6.18/6.41  thf('30', plain,
% 6.18/6.41      (![X13 : $i, X14 : $i]:
% 6.18/6.41         (((k1_relat_1 @ (k7_relat_1 @ X13 @ X14))
% 6.18/6.41            = (k3_xboole_0 @ (k1_relat_1 @ X13) @ X14))
% 6.18/6.41          | ~ (v1_relat_1 @ X13))),
% 6.18/6.41      inference('cnf', [status(esa)], [t90_relat_1])).
% 6.18/6.41  thf('31', plain, (![X17 : $i]: ((k1_relat_1 @ (sk_B @ X17)) = (X17))),
% 6.18/6.41      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 6.18/6.41  thf('32', plain,
% 6.18/6.41      (![X11 : $i, X12 : $i]:
% 6.18/6.41         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X11 @ X12)) @ 
% 6.18/6.41           (k1_relat_1 @ X11))
% 6.18/6.41          | ~ (v1_relat_1 @ X11))),
% 6.18/6.41      inference('cnf', [status(esa)], [t89_relat_1])).
% 6.18/6.41  thf('33', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ (sk_B @ X0) @ X1)) @ X0)
% 6.18/6.41          | ~ (v1_relat_1 @ (sk_B @ X0)))),
% 6.18/6.41      inference('sup+', [status(thm)], ['31', '32'])).
% 6.18/6.41  thf('34', plain, (![X17 : $i]: (v1_relat_1 @ (sk_B @ X17))),
% 6.18/6.41      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 6.18/6.41  thf('35', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ (sk_B @ X0) @ X1)) @ X0)),
% 6.18/6.41      inference('demod', [status(thm)], ['33', '34'])).
% 6.18/6.41  thf('36', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         ((r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ (sk_B @ X1)) @ X0) @ X1)
% 6.18/6.41          | ~ (v1_relat_1 @ (sk_B @ X1)))),
% 6.18/6.41      inference('sup+', [status(thm)], ['30', '35'])).
% 6.18/6.41  thf('37', plain, (![X17 : $i]: ((k1_relat_1 @ (sk_B @ X17)) = (X17))),
% 6.18/6.41      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 6.18/6.41  thf('38', plain, (![X17 : $i]: (v1_relat_1 @ (sk_B @ X17))),
% 6.18/6.41      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 6.18/6.41  thf('39', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 6.18/6.41      inference('demod', [status(thm)], ['36', '37', '38'])).
% 6.18/6.41  thf('40', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (~ (r1_tarski @ X1 @ X0)
% 6.18/6.41          | ((k1_relat_1 @ (k7_relat_1 @ (sk_B @ X0) @ X1)) = (X1)))),
% 6.18/6.41      inference('demod', [status(thm)], ['25', '26'])).
% 6.18/6.41  thf('41', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         ((k1_relat_1 @ (k7_relat_1 @ (sk_B @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 6.18/6.41           = (k3_xboole_0 @ X0 @ X1))),
% 6.18/6.41      inference('sup-', [status(thm)], ['39', '40'])).
% 6.18/6.41  thf('42', plain, ((v1_relat_1 @ sk_A)),
% 6.18/6.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.41  thf('43', plain,
% 6.18/6.41      (![X0 : $i]:
% 6.18/6.41         ((k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)
% 6.18/6.41           = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))),
% 6.18/6.41      inference('demod', [status(thm)], ['29', '41', '42'])).
% 6.18/6.41  thf('44', plain,
% 6.18/6.41      (![X0 : $i]:
% 6.18/6.41         ((k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)
% 6.18/6.41           = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))),
% 6.18/6.41      inference('demod', [status(thm)], ['29', '41', '42'])).
% 6.18/6.41  thf('45', plain,
% 6.18/6.41      (![X0 : $i]:
% 6.18/6.41         ((k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)
% 6.18/6.41           = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))),
% 6.18/6.41      inference('demod', [status(thm)], ['29', '41', '42'])).
% 6.18/6.41  thf('46', plain,
% 6.18/6.41      (![X0 : $i]:
% 6.18/6.41         ((k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)
% 6.18/6.41           = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))),
% 6.18/6.41      inference('demod', [status(thm)], ['29', '41', '42'])).
% 6.18/6.41  thf('47', plain,
% 6.18/6.41      (![X0 : $i]:
% 6.18/6.41         ((k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)
% 6.18/6.41           = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))),
% 6.18/6.41      inference('demod', [status(thm)], ['29', '41', '42'])).
% 6.18/6.41  thf('48', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (~ (v1_relat_1 @ X1)
% 6.18/6.41          | ~ (v1_funct_1 @ X1)
% 6.18/6.41          | ~ (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 6.18/6.41               (k1_relat_1 @ X1))
% 6.18/6.41          | ((k7_relat_1 @ X1 @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 6.18/6.41              = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))
% 6.18/6.41          | (r2_hidden @ 
% 6.18/6.41             (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ sk_A @ X1) @ 
% 6.18/6.41             (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))),
% 6.18/6.41      inference('demod', [status(thm)], ['20', '43', '44', '45', '46', '47'])).
% 6.18/6.41  thf('49', plain,
% 6.18/6.41      (![X0 : $i]:
% 6.18/6.41         (~ (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 6.18/6.41             (k1_relat_1 @ sk_A))
% 6.18/6.41          | (r2_hidden @ 
% 6.18/6.41             (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ sk_A @ sk_B_1) @ 
% 6.18/6.41             (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 6.18/6.41          | ((k7_relat_1 @ sk_B_1 @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 6.18/6.41              = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))
% 6.18/6.41          | ~ (v1_funct_1 @ sk_B_1)
% 6.18/6.41          | ~ (v1_relat_1 @ sk_B_1))),
% 6.18/6.41      inference('sup-', [status(thm)], ['0', '48'])).
% 6.18/6.41  thf('50', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 6.18/6.41      inference('demod', [status(thm)], ['36', '37', '38'])).
% 6.18/6.41  thf(commutativity_k3_xboole_0, axiom,
% 6.18/6.41    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 6.18/6.41  thf('51', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.18/6.41      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.18/6.41  thf('52', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B_1))),
% 6.18/6.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.41  thf('53', plain,
% 6.18/6.41      (![X13 : $i, X14 : $i]:
% 6.18/6.41         (((k1_relat_1 @ (k7_relat_1 @ X13 @ X14))
% 6.18/6.41            = (k3_xboole_0 @ (k1_relat_1 @ X13) @ X14))
% 6.18/6.41          | ~ (v1_relat_1 @ X13))),
% 6.18/6.41      inference('cnf', [status(esa)], [t90_relat_1])).
% 6.18/6.41  thf('54', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ (sk_B @ X0) @ X1)) @ X0)),
% 6.18/6.41      inference('demod', [status(thm)], ['33', '34'])).
% 6.18/6.41  thf('55', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (~ (r1_tarski @ X1 @ X0)
% 6.18/6.41          | ((k1_relat_1 @ (k7_relat_1 @ (sk_B @ X0) @ X1)) = (X1)))),
% 6.18/6.41      inference('demod', [status(thm)], ['25', '26'])).
% 6.18/6.41  thf('56', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         ((k1_relat_1 @ 
% 6.18/6.41           (k7_relat_1 @ (sk_B @ X0) @ 
% 6.18/6.41            (k1_relat_1 @ (k7_relat_1 @ (sk_B @ X0) @ X1))))
% 6.18/6.41           = (k1_relat_1 @ (k7_relat_1 @ (sk_B @ X0) @ X1)))),
% 6.18/6.41      inference('sup-', [status(thm)], ['54', '55'])).
% 6.18/6.41  thf('57', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (((k1_relat_1 @ 
% 6.18/6.41            (k7_relat_1 @ (sk_B @ X1) @ 
% 6.18/6.41             (k3_xboole_0 @ (k1_relat_1 @ (sk_B @ X1)) @ X0)))
% 6.18/6.41            = (k1_relat_1 @ (k7_relat_1 @ (sk_B @ X1) @ X0)))
% 6.18/6.41          | ~ (v1_relat_1 @ (sk_B @ X1)))),
% 6.18/6.41      inference('sup+', [status(thm)], ['53', '56'])).
% 6.18/6.41  thf('58', plain, (![X17 : $i]: ((k1_relat_1 @ (sk_B @ X17)) = (X17))),
% 6.18/6.41      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 6.18/6.41  thf('59', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         ((k1_relat_1 @ (k7_relat_1 @ (sk_B @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 6.18/6.41           = (k3_xboole_0 @ X0 @ X1))),
% 6.18/6.41      inference('sup-', [status(thm)], ['39', '40'])).
% 6.18/6.41  thf('60', plain, (![X17 : $i]: (v1_relat_1 @ (sk_B @ X17))),
% 6.18/6.41      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 6.18/6.41  thf('61', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         ((k3_xboole_0 @ X1 @ X0)
% 6.18/6.41           = (k1_relat_1 @ (k7_relat_1 @ (sk_B @ X1) @ X0)))),
% 6.18/6.41      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 6.18/6.41  thf(t189_relat_1, axiom,
% 6.18/6.41    (![A:$i]:
% 6.18/6.41     ( ( v1_relat_1 @ A ) =>
% 6.18/6.41       ( ![B:$i]:
% 6.18/6.41         ( ( v1_relat_1 @ B ) =>
% 6.18/6.41           ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) ) =
% 6.18/6.41             ( k7_relat_1 @
% 6.18/6.41               A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ))).
% 6.18/6.41  thf('62', plain,
% 6.18/6.41      (![X6 : $i, X7 : $i]:
% 6.18/6.41         (~ (v1_relat_1 @ X6)
% 6.18/6.41          | ((k7_relat_1 @ X7 @ (k1_relat_1 @ X6))
% 6.18/6.41              = (k7_relat_1 @ X7 @ 
% 6.18/6.41                 (k1_relat_1 @ (k7_relat_1 @ X6 @ (k1_relat_1 @ X7)))))
% 6.18/6.41          | ~ (v1_relat_1 @ X7))),
% 6.18/6.41      inference('cnf', [status(esa)], [t189_relat_1])).
% 6.18/6.41  thf('63', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (((k7_relat_1 @ X0 @ (k1_relat_1 @ (sk_B @ X1)))
% 6.18/6.41            = (k7_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0))))
% 6.18/6.41          | ~ (v1_relat_1 @ X0)
% 6.18/6.41          | ~ (v1_relat_1 @ (sk_B @ X1)))),
% 6.18/6.41      inference('sup+', [status(thm)], ['61', '62'])).
% 6.18/6.41  thf('64', plain, (![X17 : $i]: ((k1_relat_1 @ (sk_B @ X17)) = (X17))),
% 6.18/6.41      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 6.18/6.41  thf('65', plain, (![X17 : $i]: (v1_relat_1 @ (sk_B @ X17))),
% 6.18/6.41      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 6.18/6.41  thf('66', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (((k7_relat_1 @ X0 @ X1)
% 6.18/6.41            = (k7_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0))))
% 6.18/6.41          | ~ (v1_relat_1 @ X0))),
% 6.18/6.41      inference('demod', [status(thm)], ['63', '64', '65'])).
% 6.18/6.41  thf('67', plain,
% 6.18/6.41      (![X0 : $i]:
% 6.18/6.41         (((k7_relat_1 @ sk_B_1 @ X0)
% 6.18/6.41            = (k7_relat_1 @ sk_B_1 @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_A))))
% 6.18/6.41          | ~ (v1_relat_1 @ sk_B_1))),
% 6.18/6.41      inference('sup+', [status(thm)], ['52', '66'])).
% 6.18/6.41  thf('68', plain, ((v1_relat_1 @ sk_B_1)),
% 6.18/6.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.41  thf('69', plain,
% 6.18/6.41      (![X0 : $i]:
% 6.18/6.41         ((k7_relat_1 @ sk_B_1 @ X0)
% 6.18/6.41           = (k7_relat_1 @ sk_B_1 @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_A))))),
% 6.18/6.41      inference('demod', [status(thm)], ['67', '68'])).
% 6.18/6.41  thf('70', plain,
% 6.18/6.41      (![X0 : $i]:
% 6.18/6.41         ((k7_relat_1 @ sk_B_1 @ X0)
% 6.18/6.41           = (k7_relat_1 @ sk_B_1 @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))),
% 6.18/6.41      inference('sup+', [status(thm)], ['51', '69'])).
% 6.18/6.41  thf('71', plain, ((v1_funct_1 @ sk_B_1)),
% 6.18/6.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.41  thf('72', plain, ((v1_relat_1 @ sk_B_1)),
% 6.18/6.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.41  thf('73', plain,
% 6.18/6.41      (![X0 : $i]:
% 6.18/6.41         ((r2_hidden @ 
% 6.18/6.41           (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ sk_A @ sk_B_1) @ 
% 6.18/6.41           (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 6.18/6.41          | ((k7_relat_1 @ sk_B_1 @ X0)
% 6.18/6.41              = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))))),
% 6.18/6.41      inference('demod', [status(thm)], ['49', '50', '70', '71', '72'])).
% 6.18/6.41  thf('74', plain,
% 6.18/6.41      (![X0 : $i]:
% 6.18/6.41         ((k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)
% 6.18/6.41           = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))),
% 6.18/6.41      inference('demod', [status(thm)], ['29', '41', '42'])).
% 6.18/6.41  thf('75', plain, (![X17 : $i]: ((k1_relat_1 @ (sk_B @ X17)) = (X17))),
% 6.18/6.41      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 6.18/6.41  thf('76', plain,
% 6.18/6.41      (![X6 : $i, X7 : $i]:
% 6.18/6.41         (~ (v1_relat_1 @ X6)
% 6.18/6.41          | ((k7_relat_1 @ X7 @ (k1_relat_1 @ X6))
% 6.18/6.41              = (k7_relat_1 @ X7 @ 
% 6.18/6.41                 (k1_relat_1 @ (k7_relat_1 @ X6 @ (k1_relat_1 @ X7)))))
% 6.18/6.41          | ~ (v1_relat_1 @ X7))),
% 6.18/6.41      inference('cnf', [status(esa)], [t189_relat_1])).
% 6.18/6.41  thf('77', plain,
% 6.18/6.41      (![X13 : $i, X14 : $i]:
% 6.18/6.41         (((k1_relat_1 @ (k7_relat_1 @ X13 @ X14))
% 6.18/6.41            = (k3_xboole_0 @ (k1_relat_1 @ X13) @ X14))
% 6.18/6.41          | ~ (v1_relat_1 @ X13))),
% 6.18/6.41      inference('cnf', [status(esa)], [t90_relat_1])).
% 6.18/6.41  thf('78', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (((k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 6.18/6.41            = (k3_xboole_0 @ (k1_relat_1 @ X1) @ 
% 6.18/6.41               (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)))))
% 6.18/6.41          | ~ (v1_relat_1 @ X1)
% 6.18/6.41          | ~ (v1_relat_1 @ X0)
% 6.18/6.41          | ~ (v1_relat_1 @ X1))),
% 6.18/6.41      inference('sup+', [status(thm)], ['76', '77'])).
% 6.18/6.41  thf('79', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (~ (v1_relat_1 @ X0)
% 6.18/6.41          | ~ (v1_relat_1 @ X1)
% 6.18/6.41          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 6.18/6.41              = (k3_xboole_0 @ (k1_relat_1 @ X1) @ 
% 6.18/6.41                 (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1))))))),
% 6.18/6.41      inference('simplify', [status(thm)], ['78'])).
% 6.18/6.41  thf('80', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (((k7_relat_1 @ X0 @ X1)
% 6.18/6.41            = (k7_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0))))
% 6.18/6.41          | ~ (v1_relat_1 @ X0))),
% 6.18/6.41      inference('demod', [status(thm)], ['63', '64', '65'])).
% 6.18/6.41  thf('81', plain,
% 6.18/6.41      (![X13 : $i, X14 : $i]:
% 6.18/6.41         (((k1_relat_1 @ (k7_relat_1 @ X13 @ X14))
% 6.18/6.41            = (k3_xboole_0 @ (k1_relat_1 @ X13) @ X14))
% 6.18/6.41          | ~ (v1_relat_1 @ X13))),
% 6.18/6.41      inference('cnf', [status(esa)], [t90_relat_1])).
% 6.18/6.41  thf('82', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 6.18/6.41            = (k3_xboole_0 @ (k1_relat_1 @ X1) @ 
% 6.18/6.41               (k3_xboole_0 @ X0 @ (k1_relat_1 @ X1))))
% 6.18/6.41          | ~ (v1_relat_1 @ X1)
% 6.18/6.41          | ~ (v1_relat_1 @ X1))),
% 6.18/6.41      inference('sup+', [status(thm)], ['80', '81'])).
% 6.18/6.41  thf('83', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.18/6.41      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.18/6.41  thf('84', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 6.18/6.41      inference('demod', [status(thm)], ['36', '37', '38'])).
% 6.18/6.41  thf('85', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 6.18/6.41      inference('sup+', [status(thm)], ['83', '84'])).
% 6.18/6.41  thf('86', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (~ (r1_tarski @ X1 @ X0)
% 6.18/6.41          | ((k1_relat_1 @ (k7_relat_1 @ (sk_B @ X0) @ X1)) = (X1)))),
% 6.18/6.41      inference('demod', [status(thm)], ['25', '26'])).
% 6.18/6.41  thf('87', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         ((k3_xboole_0 @ X1 @ X0)
% 6.18/6.41           = (k1_relat_1 @ (k7_relat_1 @ (sk_B @ X1) @ X0)))),
% 6.18/6.41      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 6.18/6.41  thf('88', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (~ (r1_tarski @ X1 @ X0) | ((k3_xboole_0 @ X0 @ X1) = (X1)))),
% 6.18/6.41      inference('demod', [status(thm)], ['86', '87'])).
% 6.18/6.41  thf('89', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 6.18/6.41           = (k3_xboole_0 @ X1 @ X0))),
% 6.18/6.41      inference('sup-', [status(thm)], ['85', '88'])).
% 6.18/6.41  thf('90', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 6.18/6.41            = (k3_xboole_0 @ X0 @ (k1_relat_1 @ X1)))
% 6.18/6.41          | ~ (v1_relat_1 @ X1)
% 6.18/6.41          | ~ (v1_relat_1 @ X1))),
% 6.18/6.41      inference('demod', [status(thm)], ['82', '89'])).
% 6.18/6.41  thf('91', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (~ (v1_relat_1 @ X1)
% 6.18/6.41          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 6.18/6.41              = (k3_xboole_0 @ X0 @ (k1_relat_1 @ X1))))),
% 6.18/6.41      inference('simplify', [status(thm)], ['90'])).
% 6.18/6.41  thf('92', plain,
% 6.18/6.41      (![X11 : $i, X12 : $i]:
% 6.18/6.41         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X11 @ X12)) @ 
% 6.18/6.41           (k1_relat_1 @ X11))
% 6.18/6.41          | ~ (v1_relat_1 @ X11))),
% 6.18/6.41      inference('cnf', [status(esa)], [t89_relat_1])).
% 6.18/6.41  thf('93', plain,
% 6.18/6.41      (![X15 : $i, X16 : $i]:
% 6.18/6.41         (~ (r1_tarski @ X15 @ (k1_relat_1 @ X16))
% 6.18/6.41          | ((k1_relat_1 @ (k7_relat_1 @ X16 @ X15)) = (X15))
% 6.18/6.41          | ~ (v1_relat_1 @ X16))),
% 6.18/6.41      inference('cnf', [status(esa)], [t91_relat_1])).
% 6.18/6.41  thf('94', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (~ (v1_relat_1 @ X0)
% 6.18/6.41          | ~ (v1_relat_1 @ X0)
% 6.18/6.41          | ((k1_relat_1 @ 
% 6.18/6.41              (k7_relat_1 @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1))))
% 6.18/6.41              = (k1_relat_1 @ (k7_relat_1 @ X0 @ X1))))),
% 6.18/6.41      inference('sup-', [status(thm)], ['92', '93'])).
% 6.18/6.41  thf('95', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (((k1_relat_1 @ 
% 6.18/6.41            (k7_relat_1 @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1))))
% 6.18/6.41            = (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)))
% 6.18/6.41          | ~ (v1_relat_1 @ X0))),
% 6.18/6.41      inference('simplify', [status(thm)], ['94'])).
% 6.18/6.41  thf('96', plain,
% 6.18/6.41      (![X13 : $i, X14 : $i]:
% 6.18/6.41         (((k1_relat_1 @ (k7_relat_1 @ X13 @ X14))
% 6.18/6.41            = (k3_xboole_0 @ (k1_relat_1 @ X13) @ X14))
% 6.18/6.41          | ~ (v1_relat_1 @ X13))),
% 6.18/6.41      inference('cnf', [status(esa)], [t90_relat_1])).
% 6.18/6.41  thf('97', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 6.18/6.41            = (k3_xboole_0 @ (k1_relat_1 @ X1) @ 
% 6.18/6.41               (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 6.18/6.41          | ~ (v1_relat_1 @ X1)
% 6.18/6.41          | ~ (v1_relat_1 @ X1))),
% 6.18/6.41      inference('sup+', [status(thm)], ['95', '96'])).
% 6.18/6.41  thf('98', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (~ (v1_relat_1 @ X1)
% 6.18/6.41          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 6.18/6.41              = (k3_xboole_0 @ (k1_relat_1 @ X1) @ 
% 6.18/6.41                 (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))))),
% 6.18/6.41      inference('simplify', [status(thm)], ['97'])).
% 6.18/6.41  thf('99', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 6.18/6.41      inference('sup+', [status(thm)], ['83', '84'])).
% 6.18/6.41  thf('100', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 6.18/6.41           (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 6.18/6.41          | ~ (v1_relat_1 @ X1))),
% 6.18/6.41      inference('sup+', [status(thm)], ['98', '99'])).
% 6.18/6.41  thf('101', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 6.18/6.41           (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 6.18/6.41          | ~ (v1_relat_1 @ X0)
% 6.18/6.41          | ~ (v1_relat_1 @ X0))),
% 6.18/6.41      inference('sup+', [status(thm)], ['91', '100'])).
% 6.18/6.41  thf('102', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (~ (v1_relat_1 @ X0)
% 6.18/6.41          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 6.18/6.41             (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0))))),
% 6.18/6.41      inference('simplify', [status(thm)], ['101'])).
% 6.18/6.41  thf('103', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (~ (r1_tarski @ X1 @ X0) | ((k3_xboole_0 @ X0 @ X1) = (X1)))),
% 6.18/6.41      inference('demod', [status(thm)], ['86', '87'])).
% 6.18/6.41  thf('104', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (~ (v1_relat_1 @ X0)
% 6.18/6.41          | ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)) @ 
% 6.18/6.41              (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)))
% 6.18/6.41              = (k1_relat_1 @ (k7_relat_1 @ X0 @ X1))))),
% 6.18/6.41      inference('sup-', [status(thm)], ['102', '103'])).
% 6.18/6.41  thf('105', plain, (![X17 : $i]: ((k1_relat_1 @ (sk_B @ X17)) = (X17))),
% 6.18/6.41      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 6.18/6.41  thf('106', plain,
% 6.18/6.41      (![X6 : $i, X7 : $i]:
% 6.18/6.41         (~ (v1_relat_1 @ X6)
% 6.18/6.41          | ((k7_relat_1 @ X7 @ (k1_relat_1 @ X6))
% 6.18/6.41              = (k7_relat_1 @ X7 @ 
% 6.18/6.41                 (k1_relat_1 @ (k7_relat_1 @ X6 @ (k1_relat_1 @ X7)))))
% 6.18/6.41          | ~ (v1_relat_1 @ X7))),
% 6.18/6.41      inference('cnf', [status(esa)], [t189_relat_1])).
% 6.18/6.41  thf('107', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (((k7_relat_1 @ (sk_B @ X0) @ (k1_relat_1 @ X1))
% 6.18/6.41            = (k7_relat_1 @ (sk_B @ X0) @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 6.18/6.41          | ~ (v1_relat_1 @ (sk_B @ X0))
% 6.18/6.41          | ~ (v1_relat_1 @ X1))),
% 6.18/6.41      inference('sup+', [status(thm)], ['105', '106'])).
% 6.18/6.41  thf('108', plain, (![X17 : $i]: (v1_relat_1 @ (sk_B @ X17))),
% 6.18/6.41      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 6.18/6.41  thf('109', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (((k7_relat_1 @ (sk_B @ X0) @ (k1_relat_1 @ X1))
% 6.18/6.41            = (k7_relat_1 @ (sk_B @ X0) @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 6.18/6.41          | ~ (v1_relat_1 @ X1))),
% 6.18/6.41      inference('demod', [status(thm)], ['107', '108'])).
% 6.18/6.41  thf('110', plain,
% 6.18/6.41      (![X6 : $i, X7 : $i]:
% 6.18/6.41         (~ (v1_relat_1 @ X6)
% 6.18/6.41          | ((k7_relat_1 @ X7 @ (k1_relat_1 @ X6))
% 6.18/6.41              = (k7_relat_1 @ X7 @ 
% 6.18/6.41                 (k1_relat_1 @ (k7_relat_1 @ X6 @ (k1_relat_1 @ X7)))))
% 6.18/6.41          | ~ (v1_relat_1 @ X7))),
% 6.18/6.41      inference('cnf', [status(esa)], [t189_relat_1])).
% 6.18/6.41  thf('111', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         ((k3_xboole_0 @ X1 @ X0)
% 6.18/6.41           = (k1_relat_1 @ (k7_relat_1 @ (sk_B @ X1) @ X0)))),
% 6.18/6.41      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 6.18/6.41  thf('112', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (((k3_xboole_0 @ X1 @ 
% 6.18/6.41            (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ (sk_B @ X1)))))
% 6.18/6.41            = (k1_relat_1 @ (k7_relat_1 @ (sk_B @ X1) @ (k1_relat_1 @ X0))))
% 6.18/6.41          | ~ (v1_relat_1 @ (sk_B @ X1))
% 6.18/6.41          | ~ (v1_relat_1 @ X0))),
% 6.18/6.41      inference('sup+', [status(thm)], ['110', '111'])).
% 6.18/6.41  thf('113', plain, (![X17 : $i]: ((k1_relat_1 @ (sk_B @ X17)) = (X17))),
% 6.18/6.41      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 6.18/6.41  thf('114', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         ((k3_xboole_0 @ X1 @ X0)
% 6.18/6.41           = (k1_relat_1 @ (k7_relat_1 @ (sk_B @ X1) @ X0)))),
% 6.18/6.41      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 6.18/6.41  thf('115', plain, (![X17 : $i]: (v1_relat_1 @ (sk_B @ X17))),
% 6.18/6.41      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 6.18/6.41  thf('116', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (((k3_xboole_0 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)))
% 6.18/6.41            = (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 6.18/6.41          | ~ (v1_relat_1 @ X0))),
% 6.18/6.41      inference('demod', [status(thm)], ['112', '113', '114', '115'])).
% 6.18/6.41  thf('117', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (((k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 6.18/6.41            (k1_relat_1 @ (k7_relat_1 @ (sk_B @ X1) @ (k1_relat_1 @ X0))))
% 6.18/6.41            = (k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 6.18/6.41               (k1_relat_1 @ (sk_B @ X1))))
% 6.18/6.41          | ~ (v1_relat_1 @ X0)
% 6.18/6.41          | ~ (v1_relat_1 @ (sk_B @ X1)))),
% 6.18/6.41      inference('sup+', [status(thm)], ['109', '116'])).
% 6.18/6.41  thf('118', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         ((k3_xboole_0 @ X1 @ X0)
% 6.18/6.41           = (k1_relat_1 @ (k7_relat_1 @ (sk_B @ X1) @ X0)))),
% 6.18/6.41      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 6.18/6.41  thf('119', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.18/6.41      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.18/6.41  thf('120', plain, (![X17 : $i]: ((k1_relat_1 @ (sk_B @ X17)) = (X17))),
% 6.18/6.41      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 6.18/6.41  thf('121', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.18/6.41      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.18/6.41  thf('122', plain, (![X17 : $i]: (v1_relat_1 @ (sk_B @ X17))),
% 6.18/6.41      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 6.18/6.41  thf('123', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (((k3_xboole_0 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)) @ 
% 6.18/6.41            (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)))
% 6.18/6.41            = (k3_xboole_0 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1))))
% 6.18/6.41          | ~ (v1_relat_1 @ X0))),
% 6.18/6.41      inference('demod', [status(thm)],
% 6.18/6.41                ['117', '118', '119', '120', '121', '122'])).
% 6.18/6.41  thf('124', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 6.18/6.41            = (k3_xboole_0 @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 6.18/6.41          | ~ (v1_relat_1 @ X1)
% 6.18/6.41          | ~ (v1_relat_1 @ X1))),
% 6.18/6.41      inference('sup+', [status(thm)], ['104', '123'])).
% 6.18/6.41  thf('125', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (~ (v1_relat_1 @ X1)
% 6.18/6.41          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 6.18/6.41              = (k3_xboole_0 @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))))),
% 6.18/6.41      inference('simplify', [status(thm)], ['124'])).
% 6.18/6.41  thf('126', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (((k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)))
% 6.18/6.41            = (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0))))
% 6.18/6.41          | ~ (v1_relat_1 @ X1)
% 6.18/6.41          | ~ (v1_relat_1 @ X0)
% 6.18/6.41          | ~ (v1_relat_1 @ X0))),
% 6.18/6.41      inference('sup+', [status(thm)], ['79', '125'])).
% 6.18/6.41  thf('127', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (~ (v1_relat_1 @ X0)
% 6.18/6.41          | ~ (v1_relat_1 @ X1)
% 6.18/6.41          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)))
% 6.18/6.41              = (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))))),
% 6.18/6.41      inference('simplify', [status(thm)], ['126'])).
% 6.18/6.41  thf('128', plain,
% 6.18/6.41      (![X6 : $i, X7 : $i]:
% 6.18/6.41         (~ (v1_relat_1 @ X6)
% 6.18/6.41          | ((k7_relat_1 @ X7 @ (k1_relat_1 @ X6))
% 6.18/6.41              = (k7_relat_1 @ X7 @ 
% 6.18/6.41                 (k1_relat_1 @ (k7_relat_1 @ X6 @ (k1_relat_1 @ X7)))))
% 6.18/6.41          | ~ (v1_relat_1 @ X7))),
% 6.18/6.41      inference('cnf', [status(esa)], [t189_relat_1])).
% 6.18/6.41  thf('129', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (((k7_relat_1 @ X1 @ (k1_relat_1 @ X0))
% 6.18/6.41            = (k7_relat_1 @ X1 @ 
% 6.18/6.41               (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))))
% 6.18/6.41          | ~ (v1_relat_1 @ X0)
% 6.18/6.41          | ~ (v1_relat_1 @ X1)
% 6.18/6.41          | ~ (v1_relat_1 @ X1)
% 6.18/6.41          | ~ (v1_relat_1 @ X0))),
% 6.18/6.41      inference('sup+', [status(thm)], ['127', '128'])).
% 6.18/6.41  thf('130', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (~ (v1_relat_1 @ X1)
% 6.18/6.41          | ~ (v1_relat_1 @ X0)
% 6.18/6.41          | ((k7_relat_1 @ X1 @ (k1_relat_1 @ X0))
% 6.18/6.41              = (k7_relat_1 @ X1 @ 
% 6.18/6.41                 (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0))))))),
% 6.18/6.41      inference('simplify', [status(thm)], ['129'])).
% 6.18/6.41  thf('131', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (((k7_relat_1 @ X1 @ (k1_relat_1 @ (sk_B @ X0)))
% 6.18/6.41            = (k7_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 6.18/6.41          | ~ (v1_relat_1 @ (sk_B @ X0))
% 6.18/6.41          | ~ (v1_relat_1 @ X1))),
% 6.18/6.41      inference('sup+', [status(thm)], ['75', '130'])).
% 6.18/6.41  thf('132', plain, (![X17 : $i]: ((k1_relat_1 @ (sk_B @ X17)) = (X17))),
% 6.18/6.41      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 6.18/6.41  thf('133', plain, (![X17 : $i]: (v1_relat_1 @ (sk_B @ X17))),
% 6.18/6.41      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 6.18/6.41  thf('134', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]:
% 6.18/6.41         (((k7_relat_1 @ X1 @ X0)
% 6.18/6.41            = (k7_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 6.18/6.41          | ~ (v1_relat_1 @ X1))),
% 6.18/6.41      inference('demod', [status(thm)], ['131', '132', '133'])).
% 6.18/6.41  thf('135', plain,
% 6.18/6.41      (![X0 : $i]:
% 6.18/6.41         (((k7_relat_1 @ sk_A @ X0)
% 6.18/6.41            = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))
% 6.18/6.41          | ~ (v1_relat_1 @ sk_A))),
% 6.18/6.41      inference('sup+', [status(thm)], ['74', '134'])).
% 6.18/6.41  thf('136', plain, ((v1_relat_1 @ sk_A)),
% 6.18/6.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.41  thf('137', plain,
% 6.18/6.41      (![X0 : $i]:
% 6.18/6.41         ((k7_relat_1 @ sk_A @ X0)
% 6.18/6.41           = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))),
% 6.18/6.41      inference('demod', [status(thm)], ['135', '136'])).
% 6.18/6.41  thf('138', plain,
% 6.18/6.41      (![X0 : $i]:
% 6.18/6.41         ((r2_hidden @ 
% 6.18/6.41           (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ sk_A @ sk_B_1) @ 
% 6.18/6.41           (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 6.18/6.41          | ((k7_relat_1 @ sk_B_1 @ X0) = (k7_relat_1 @ sk_A @ X0)))),
% 6.18/6.41      inference('demod', [status(thm)], ['73', '137'])).
% 6.18/6.41  thf('139', plain, (![X17 : $i]: ((k1_relat_1 @ (sk_B @ X17)) = (X17))),
% 6.18/6.41      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 6.18/6.41  thf('140', plain,
% 6.18/6.41      (![X13 : $i, X14 : $i]:
% 6.18/6.41         (((k1_relat_1 @ (k7_relat_1 @ X13 @ X14))
% 6.18/6.41            = (k3_xboole_0 @ (k1_relat_1 @ X13) @ X14))
% 6.18/6.41          | ~ (v1_relat_1 @ X13))),
% 6.18/6.41      inference('cnf', [status(esa)], [t90_relat_1])).
% 6.18/6.41  thf(t86_relat_1, axiom,
% 6.18/6.41    (![A:$i,B:$i,C:$i]:
% 6.18/6.41     ( ( v1_relat_1 @ C ) =>
% 6.18/6.41       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 6.18/6.41         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 6.18/6.41  thf('141', plain,
% 6.18/6.41      (![X8 : $i, X9 : $i, X10 : $i]:
% 6.18/6.41         (~ (r2_hidden @ X8 @ (k1_relat_1 @ (k7_relat_1 @ X10 @ X9)))
% 6.18/6.41          | (r2_hidden @ X8 @ X9)
% 6.18/6.41          | ~ (v1_relat_1 @ X10))),
% 6.18/6.41      inference('cnf', [status(esa)], [t86_relat_1])).
% 6.18/6.41  thf('142', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.18/6.41         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 6.18/6.41          | ~ (v1_relat_1 @ X1)
% 6.18/6.41          | ~ (v1_relat_1 @ X1)
% 6.18/6.41          | (r2_hidden @ X2 @ X0))),
% 6.18/6.41      inference('sup-', [status(thm)], ['140', '141'])).
% 6.18/6.41  thf('143', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.18/6.41         ((r2_hidden @ X2 @ X0)
% 6.18/6.41          | ~ (v1_relat_1 @ X1)
% 6.18/6.41          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 6.18/6.41      inference('simplify', [status(thm)], ['142'])).
% 6.18/6.41  thf('144', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.18/6.41         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1))
% 6.18/6.41          | ~ (v1_relat_1 @ (sk_B @ X0))
% 6.18/6.41          | (r2_hidden @ X2 @ X1))),
% 6.18/6.41      inference('sup-', [status(thm)], ['139', '143'])).
% 6.18/6.41  thf('145', plain, (![X17 : $i]: (v1_relat_1 @ (sk_B @ X17))),
% 6.18/6.41      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 6.18/6.41  thf('146', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.18/6.41         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)) | (r2_hidden @ X2 @ X1))),
% 6.18/6.41      inference('demod', [status(thm)], ['144', '145'])).
% 6.18/6.41  thf('147', plain,
% 6.18/6.41      (![X0 : $i]:
% 6.18/6.41         (((k7_relat_1 @ sk_B_1 @ X0) = (k7_relat_1 @ sk_A @ X0))
% 6.18/6.41          | (r2_hidden @ 
% 6.18/6.41             (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ sk_A @ sk_B_1) @ 
% 6.18/6.41             X0))),
% 6.18/6.41      inference('sup-', [status(thm)], ['138', '146'])).
% 6.18/6.41  thf('148', plain,
% 6.18/6.41      (![X23 : $i]:
% 6.18/6.41         (((k1_funct_1 @ sk_A @ X23) = (k1_funct_1 @ sk_B_1 @ X23))
% 6.18/6.41          | ~ (r2_hidden @ X23 @ sk_C))),
% 6.18/6.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.41  thf('149', plain,
% 6.18/6.41      ((((k7_relat_1 @ sk_B_1 @ sk_C) = (k7_relat_1 @ sk_A @ sk_C))
% 6.18/6.41        | ((k1_funct_1 @ sk_A @ 
% 6.18/6.41            (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C) @ sk_A @ sk_B_1))
% 6.18/6.41            = (k1_funct_1 @ sk_B_1 @ 
% 6.18/6.41               (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C) @ sk_A @ 
% 6.18/6.41                sk_B_1))))),
% 6.18/6.41      inference('sup-', [status(thm)], ['147', '148'])).
% 6.18/6.41  thf('150', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.18/6.41      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.18/6.41  thf('151', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.18/6.41      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.18/6.41  thf('152', plain,
% 6.18/6.41      ((((k7_relat_1 @ sk_B_1 @ sk_C) = (k7_relat_1 @ sk_A @ sk_C))
% 6.18/6.41        | ((k1_funct_1 @ sk_A @ 
% 6.18/6.41            (sk_D @ (k3_xboole_0 @ sk_C @ (k1_relat_1 @ sk_A)) @ sk_A @ sk_B_1))
% 6.18/6.41            = (k1_funct_1 @ sk_B_1 @ 
% 6.18/6.41               (sk_D @ (k3_xboole_0 @ sk_C @ (k1_relat_1 @ sk_A)) @ sk_A @ 
% 6.18/6.41                sk_B_1))))),
% 6.18/6.41      inference('demod', [status(thm)], ['149', '150', '151'])).
% 6.18/6.41  thf('153', plain,
% 6.18/6.41      (((k7_relat_1 @ sk_A @ sk_C) != (k7_relat_1 @ sk_B_1 @ sk_C))),
% 6.18/6.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.41  thf('154', plain,
% 6.18/6.41      (((k1_funct_1 @ sk_A @ 
% 6.18/6.41         (sk_D @ (k3_xboole_0 @ sk_C @ (k1_relat_1 @ sk_A)) @ sk_A @ sk_B_1))
% 6.18/6.41         = (k1_funct_1 @ sk_B_1 @ 
% 6.18/6.41            (sk_D @ (k3_xboole_0 @ sk_C @ (k1_relat_1 @ sk_A)) @ sk_A @ sk_B_1)))),
% 6.18/6.41      inference('simplify_reflect-', [status(thm)], ['152', '153'])).
% 6.18/6.41  thf('155', plain,
% 6.18/6.41      (![X19 : $i, X20 : $i, X21 : $i]:
% 6.18/6.41         (~ (v1_relat_1 @ X19)
% 6.18/6.41          | ~ (v1_funct_1 @ X19)
% 6.18/6.41          | ((k1_funct_1 @ X21 @ (sk_D @ X20 @ X19 @ X21))
% 6.18/6.41              != (k1_funct_1 @ X19 @ (sk_D @ X20 @ X19 @ X21)))
% 6.18/6.41          | ((k7_relat_1 @ X21 @ X20) = (k7_relat_1 @ X19 @ X20))
% 6.18/6.41          | ~ (r1_tarski @ X20 @ (k1_relat_1 @ X19))
% 6.18/6.41          | ~ (r1_tarski @ X20 @ (k1_relat_1 @ X21))
% 6.18/6.41          | ~ (v1_funct_1 @ X21)
% 6.18/6.41          | ~ (v1_relat_1 @ X21))),
% 6.18/6.41      inference('cnf', [status(esa)], [t165_funct_1])).
% 6.18/6.41  thf('156', plain,
% 6.18/6.41      ((((k1_funct_1 @ sk_A @ 
% 6.18/6.41          (sk_D @ (k3_xboole_0 @ sk_C @ (k1_relat_1 @ sk_A)) @ sk_A @ sk_B_1))
% 6.18/6.41          != (k1_funct_1 @ sk_A @ 
% 6.18/6.41              (sk_D @ (k3_xboole_0 @ sk_C @ (k1_relat_1 @ sk_A)) @ sk_A @ 
% 6.18/6.41               sk_B_1)))
% 6.18/6.41        | ~ (v1_relat_1 @ sk_B_1)
% 6.18/6.41        | ~ (v1_funct_1 @ sk_B_1)
% 6.18/6.41        | ~ (r1_tarski @ (k3_xboole_0 @ sk_C @ (k1_relat_1 @ sk_A)) @ 
% 6.18/6.41             (k1_relat_1 @ sk_B_1))
% 6.18/6.41        | ~ (r1_tarski @ (k3_xboole_0 @ sk_C @ (k1_relat_1 @ sk_A)) @ 
% 6.18/6.41             (k1_relat_1 @ sk_A))
% 6.18/6.41        | ((k7_relat_1 @ sk_B_1 @ (k3_xboole_0 @ sk_C @ (k1_relat_1 @ sk_A)))
% 6.18/6.41            = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ sk_C @ (k1_relat_1 @ sk_A))))
% 6.18/6.41        | ~ (v1_funct_1 @ sk_A)
% 6.18/6.41        | ~ (v1_relat_1 @ sk_A))),
% 6.18/6.41      inference('sup-', [status(thm)], ['154', '155'])).
% 6.18/6.41  thf('157', plain, ((v1_relat_1 @ sk_B_1)),
% 6.18/6.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.41  thf('158', plain, ((v1_funct_1 @ sk_B_1)),
% 6.18/6.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.41  thf('159', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B_1))),
% 6.18/6.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.41  thf('160', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 6.18/6.41      inference('sup+', [status(thm)], ['83', '84'])).
% 6.18/6.41  thf('161', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 6.18/6.41      inference('sup+', [status(thm)], ['83', '84'])).
% 6.18/6.41  thf('162', plain,
% 6.18/6.41      (![X0 : $i]:
% 6.18/6.41         ((k7_relat_1 @ sk_B_1 @ X0)
% 6.18/6.41           = (k7_relat_1 @ sk_B_1 @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_A))))),
% 6.18/6.41      inference('demod', [status(thm)], ['67', '68'])).
% 6.18/6.41  thf('163', plain,
% 6.18/6.41      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.18/6.41      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.18/6.41  thf('164', plain,
% 6.18/6.41      (![X0 : $i]:
% 6.18/6.41         ((k7_relat_1 @ sk_A @ X0)
% 6.18/6.41           = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))),
% 6.18/6.41      inference('demod', [status(thm)], ['135', '136'])).
% 6.18/6.41  thf('165', plain,
% 6.18/6.41      (![X0 : $i]:
% 6.18/6.41         ((k7_relat_1 @ sk_A @ X0)
% 6.18/6.41           = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_A))))),
% 6.18/6.41      inference('sup+', [status(thm)], ['163', '164'])).
% 6.18/6.41  thf('166', plain, ((v1_funct_1 @ sk_A)),
% 6.18/6.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.41  thf('167', plain, ((v1_relat_1 @ sk_A)),
% 6.18/6.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.41  thf('168', plain,
% 6.18/6.41      ((((k1_funct_1 @ sk_A @ 
% 6.18/6.41          (sk_D @ (k3_xboole_0 @ sk_C @ (k1_relat_1 @ sk_A)) @ sk_A @ sk_B_1))
% 6.18/6.41          != (k1_funct_1 @ sk_A @ 
% 6.18/6.41              (sk_D @ (k3_xboole_0 @ sk_C @ (k1_relat_1 @ sk_A)) @ sk_A @ 
% 6.18/6.41               sk_B_1)))
% 6.18/6.41        | ((k7_relat_1 @ sk_B_1 @ sk_C) = (k7_relat_1 @ sk_A @ sk_C)))),
% 6.18/6.41      inference('demod', [status(thm)],
% 6.18/6.41                ['156', '157', '158', '159', '160', '161', '162', '165', 
% 6.18/6.41                 '166', '167'])).
% 6.18/6.41  thf('169', plain,
% 6.18/6.41      (((k7_relat_1 @ sk_B_1 @ sk_C) = (k7_relat_1 @ sk_A @ sk_C))),
% 6.18/6.41      inference('simplify', [status(thm)], ['168'])).
% 6.18/6.41  thf('170', plain,
% 6.18/6.41      (((k7_relat_1 @ sk_A @ sk_C) != (k7_relat_1 @ sk_B_1 @ sk_C))),
% 6.18/6.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.41  thf('171', plain, ($false),
% 6.18/6.41      inference('simplify_reflect-', [status(thm)], ['169', '170'])).
% 6.18/6.41  
% 6.18/6.41  % SZS output end Refutation
% 6.18/6.41  
% 6.18/6.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
