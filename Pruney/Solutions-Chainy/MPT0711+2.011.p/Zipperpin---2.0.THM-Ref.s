%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FQv6fFNfeO

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:12 EST 2020

% Result     : Theorem 2.68s
% Output     : Refutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 753 expanded)
%              Number of leaves         :   20 ( 240 expanded)
%              Depth                    :   21
%              Number of atoms          : 1289 (11547 expanded)
%              Number of equality atoms :   82 ( 953 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t89_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) @ ( k1_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

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

thf('6',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( r2_hidden @ ( sk_D @ X17 @ X16 @ X18 ) @ X17 )
      | ( ( k7_relat_1 @ X18 @ X17 )
        = ( k7_relat_1 @ X16 @ X17 ) )
      | ~ ( r1_tarski @ X17 @ ( k1_relat_1 @ X16 ) )
      | ~ ( r1_tarski @ X17 @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t165_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ( ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) )
        = ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) )
      | ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ sk_A @ X1 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ( ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) )
        = ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) )
      | ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ sk_A @ X1 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t189_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) )
            = ( k7_relat_1 @ A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X9 @ ( k1_relat_1 @ X10 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X9 ) )
        = X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

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

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_relat_1 @ ( sk_C @ X13 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('18',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ sk_A ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ sk_A ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ sk_A ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( sk_C @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ sk_A ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( sk_C @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( sk_C @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','25'])).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_relat_1 @ ( sk_C @ X13 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('28',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( sk_C @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ sk_A ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( sk_C @ X1 @ X0 ) ) )
        = ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( sk_C @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_relat_1 @ ( sk_C @ X13 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('37',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( sk_C @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_A @ X0 )
      = ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_A @ X0 )
      = ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ( ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) )
        = ( k7_relat_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ sk_A @ X1 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['10','30','31','32','41','42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ ( k1_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ sk_A @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) )
      | ( ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) )
        = ( k7_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','44'])).

thf('46',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) @ ( k1_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf('47',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X9 @ ( k1_relat_1 @ X10 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X9 ) )
        = X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_A ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ sk_A ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('58',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ sk_A ) ) ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ sk_A ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( sk_C @ X1 @ X0 ) ) )
        = ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( sk_C @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','62'])).

thf('64',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_relat_1 @ ( sk_C @ X13 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('65',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( sk_C @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B @ X0 )
      = ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B @ X0 )
      = ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ sk_A @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) )
      | ( ( k7_relat_1 @ sk_B @ X0 )
        = ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','56','68','69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ sk_A ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('73',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X4 @ X3 ) ) )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ ( sk_C @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( sk_C @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('76',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_relat_1 @ ( sk_C @ X13 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('77',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('79',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_B @ X0 )
        = ( k7_relat_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','79'])).

thf('81',plain,(
    ! [X20: $i] :
      ( ( ( k1_funct_1 @ sk_A @ X20 )
        = ( k1_funct_1 @ sk_B @ X20 ) )
      | ~ ( r2_hidden @ X20 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_C_1 )
      = ( k7_relat_1 @ sk_A @ sk_C_1 ) )
    | ( ( k1_funct_1 @ sk_A @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_A @ sk_B ) )
      = ( k1_funct_1 @ sk_B @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ( k7_relat_1 @ sk_A @ sk_C_1 )
 != ( k7_relat_1 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_A @ sk_B ) )
    = ( k1_funct_1 @ sk_B @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( ( k1_funct_1 @ X18 @ ( sk_D @ X17 @ X16 @ X18 ) )
       != ( k1_funct_1 @ X16 @ ( sk_D @ X17 @ X16 @ X18 ) ) )
      | ( ( k7_relat_1 @ X18 @ X17 )
        = ( k7_relat_1 @ X16 @ X17 ) )
      | ~ ( r1_tarski @ X17 @ ( k1_relat_1 @ X16 ) )
      | ~ ( r1_tarski @ X17 @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t165_funct_1])).

thf('86',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_A @ sk_B ) )
     != ( k1_funct_1 @ sk_A @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ sk_A ) )
    | ( ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) )
      = ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('91',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B @ X0 )
      = ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_A @ X0 )
      = ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('94',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_A @ sk_B ) )
     != ( k1_funct_1 @ sk_A @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_A @ sk_B ) ) )
    | ( ( k7_relat_1 @ sk_B @ sk_C_1 )
      = ( k7_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['86','87','88','89','90','91','92','93','94','95'])).

thf('97',plain,
    ( ( k7_relat_1 @ sk_B @ sk_C_1 )
    = ( k7_relat_1 @ sk_A @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ( k7_relat_1 @ sk_A @ sk_C_1 )
 != ( k7_relat_1 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['97','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FQv6fFNfeO
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:31:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.68/2.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.68/2.89  % Solved by: fo/fo7.sh
% 2.68/2.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.68/2.89  % done 2041 iterations in 2.439s
% 2.68/2.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.68/2.89  % SZS output start Refutation
% 2.68/2.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.68/2.89  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.68/2.89  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.68/2.89  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.68/2.89  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 2.68/2.89  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.68/2.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.68/2.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.68/2.89  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.68/2.89  thf(sk_B_type, type, sk_B: $i).
% 2.68/2.89  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.68/2.89  thf(sk_A_type, type, sk_A: $i).
% 2.68/2.89  thf(t166_funct_1, conjecture,
% 2.68/2.89    (![A:$i]:
% 2.68/2.89     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.68/2.89       ( ![B:$i]:
% 2.68/2.89         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.68/2.89           ( ![C:$i]:
% 2.68/2.89             ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 2.68/2.89                 ( ![D:$i]:
% 2.68/2.89                   ( ( r2_hidden @ D @ C ) =>
% 2.68/2.89                     ( ( k1_funct_1 @ A @ D ) = ( k1_funct_1 @ B @ D ) ) ) ) ) =>
% 2.68/2.89               ( ( k7_relat_1 @ A @ C ) = ( k7_relat_1 @ B @ C ) ) ) ) ) ) ))).
% 2.68/2.89  thf(zf_stmt_0, negated_conjecture,
% 2.68/2.89    (~( ![A:$i]:
% 2.68/2.89        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.68/2.89          ( ![B:$i]:
% 2.68/2.89            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.68/2.89              ( ![C:$i]:
% 2.68/2.89                ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 2.68/2.89                    ( ![D:$i]:
% 2.68/2.89                      ( ( r2_hidden @ D @ C ) =>
% 2.68/2.89                        ( ( k1_funct_1 @ A @ D ) = ( k1_funct_1 @ B @ D ) ) ) ) ) =>
% 2.68/2.89                  ( ( k7_relat_1 @ A @ C ) = ( k7_relat_1 @ B @ C ) ) ) ) ) ) ) )),
% 2.68/2.89    inference('cnf.neg', [status(esa)], [t166_funct_1])).
% 2.68/2.89  thf('0', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 2.68/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.89  thf('1', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 2.68/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.89  thf(t89_relat_1, axiom,
% 2.68/2.89    (![A:$i,B:$i]:
% 2.68/2.89     ( ( v1_relat_1 @ B ) =>
% 2.68/2.89       ( r1_tarski @
% 2.68/2.89         ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ))).
% 2.68/2.89  thf('2', plain,
% 2.68/2.89      (![X7 : $i, X8 : $i]:
% 2.68/2.89         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X7 @ X8)) @ 
% 2.68/2.89           (k1_relat_1 @ X7))
% 2.68/2.89          | ~ (v1_relat_1 @ X7))),
% 2.68/2.89      inference('cnf', [status(esa)], [t89_relat_1])).
% 2.68/2.89  thf('3', plain,
% 2.68/2.89      (![X0 : $i]:
% 2.68/2.89         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ 
% 2.68/2.89           (k1_relat_1 @ sk_A))
% 2.68/2.89          | ~ (v1_relat_1 @ sk_B))),
% 2.68/2.89      inference('sup+', [status(thm)], ['1', '2'])).
% 2.68/2.89  thf('4', plain, ((v1_relat_1 @ sk_B)),
% 2.68/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.89  thf('5', plain,
% 2.68/2.89      (![X0 : $i]:
% 2.68/2.89         (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ 
% 2.68/2.89          (k1_relat_1 @ sk_A))),
% 2.68/2.89      inference('demod', [status(thm)], ['3', '4'])).
% 2.68/2.89  thf(t165_funct_1, axiom,
% 2.68/2.89    (![A:$i]:
% 2.68/2.89     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.68/2.89       ( ![B:$i]:
% 2.68/2.89         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.68/2.89           ( ![C:$i]:
% 2.68/2.89             ( ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 2.68/2.89                 ( r1_tarski @ C @ ( k1_relat_1 @ B ) ) ) =>
% 2.68/2.89               ( ( ( k7_relat_1 @ A @ C ) = ( k7_relat_1 @ B @ C ) ) <=>
% 2.68/2.89                 ( ![D:$i]:
% 2.68/2.89                   ( ( r2_hidden @ D @ C ) =>
% 2.68/2.89                     ( ( k1_funct_1 @ A @ D ) = ( k1_funct_1 @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 2.68/2.89  thf('6', plain,
% 2.68/2.89      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.68/2.89         (~ (v1_relat_1 @ X16)
% 2.68/2.89          | ~ (v1_funct_1 @ X16)
% 2.68/2.89          | (r2_hidden @ (sk_D @ X17 @ X16 @ X18) @ X17)
% 2.68/2.89          | ((k7_relat_1 @ X18 @ X17) = (k7_relat_1 @ X16 @ X17))
% 2.68/2.89          | ~ (r1_tarski @ X17 @ (k1_relat_1 @ X16))
% 2.68/2.89          | ~ (r1_tarski @ X17 @ (k1_relat_1 @ X18))
% 2.68/2.89          | ~ (v1_funct_1 @ X18)
% 2.68/2.89          | ~ (v1_relat_1 @ X18))),
% 2.68/2.89      inference('cnf', [status(esa)], [t165_funct_1])).
% 2.68/2.89  thf('7', plain,
% 2.68/2.89      (![X0 : $i, X1 : $i]:
% 2.68/2.89         (~ (v1_relat_1 @ X1)
% 2.68/2.89          | ~ (v1_funct_1 @ X1)
% 2.68/2.89          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ 
% 2.68/2.89               (k1_relat_1 @ X1))
% 2.68/2.89          | ((k7_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))
% 2.68/2.89              = (k7_relat_1 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))))
% 2.68/2.89          | (r2_hidden @ 
% 2.68/2.89             (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ sk_A @ X1) @ 
% 2.68/2.89             (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))
% 2.68/2.89          | ~ (v1_funct_1 @ sk_A)
% 2.68/2.89          | ~ (v1_relat_1 @ sk_A))),
% 2.68/2.89      inference('sup-', [status(thm)], ['5', '6'])).
% 2.68/2.89  thf('8', plain, ((v1_funct_1 @ sk_A)),
% 2.68/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.89  thf('9', plain, ((v1_relat_1 @ sk_A)),
% 2.68/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.89  thf('10', plain,
% 2.68/2.89      (![X0 : $i, X1 : $i]:
% 2.68/2.89         (~ (v1_relat_1 @ X1)
% 2.68/2.89          | ~ (v1_funct_1 @ X1)
% 2.68/2.89          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ 
% 2.68/2.89               (k1_relat_1 @ X1))
% 2.68/2.89          | ((k7_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))
% 2.68/2.89              = (k7_relat_1 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))))
% 2.68/2.89          | (r2_hidden @ 
% 2.68/2.89             (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ sk_A @ X1) @ 
% 2.68/2.89             (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))))),
% 2.68/2.89      inference('demod', [status(thm)], ['7', '8', '9'])).
% 2.68/2.89  thf(t189_relat_1, axiom,
% 2.68/2.89    (![A:$i]:
% 2.68/2.89     ( ( v1_relat_1 @ A ) =>
% 2.68/2.89       ( ![B:$i]:
% 2.68/2.89         ( ( v1_relat_1 @ B ) =>
% 2.68/2.89           ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) ) =
% 2.68/2.89             ( k7_relat_1 @
% 2.68/2.89               A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ))).
% 2.68/2.89  thf('11', plain,
% 2.68/2.89      (![X0 : $i, X1 : $i]:
% 2.68/2.89         (~ (v1_relat_1 @ X0)
% 2.68/2.89          | ((k7_relat_1 @ X1 @ (k1_relat_1 @ X0))
% 2.68/2.89              = (k7_relat_1 @ X1 @ 
% 2.68/2.89                 (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)))))
% 2.68/2.89          | ~ (v1_relat_1 @ X1))),
% 2.68/2.89      inference('cnf', [status(esa)], [t189_relat_1])).
% 2.68/2.89  thf(t87_relat_1, axiom,
% 2.68/2.89    (![A:$i,B:$i]:
% 2.68/2.89     ( ( v1_relat_1 @ B ) =>
% 2.68/2.89       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 2.68/2.89  thf('12', plain,
% 2.68/2.89      (![X5 : $i, X6 : $i]:
% 2.68/2.89         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X5 @ X6)) @ X6)
% 2.68/2.89          | ~ (v1_relat_1 @ X5))),
% 2.68/2.89      inference('cnf', [status(esa)], [t87_relat_1])).
% 2.68/2.89  thf(t91_relat_1, axiom,
% 2.68/2.89    (![A:$i,B:$i]:
% 2.68/2.89     ( ( v1_relat_1 @ B ) =>
% 2.68/2.89       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 2.68/2.89         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 2.68/2.89  thf('13', plain,
% 2.68/2.89      (![X9 : $i, X10 : $i]:
% 2.68/2.89         (~ (r1_tarski @ X9 @ (k1_relat_1 @ X10))
% 2.68/2.89          | ((k1_relat_1 @ (k7_relat_1 @ X10 @ X9)) = (X9))
% 2.68/2.89          | ~ (v1_relat_1 @ X10))),
% 2.68/2.89      inference('cnf', [status(esa)], [t91_relat_1])).
% 2.68/2.89  thf('14', plain,
% 2.68/2.89      (![X0 : $i, X1 : $i]:
% 2.68/2.89         (~ (v1_relat_1 @ X1)
% 2.68/2.89          | ~ (v1_relat_1 @ X0)
% 2.68/2.89          | ((k1_relat_1 @ 
% 2.68/2.89              (k7_relat_1 @ X0 @ 
% 2.68/2.89               (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))))
% 2.68/2.89              = (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))))),
% 2.68/2.89      inference('sup-', [status(thm)], ['12', '13'])).
% 2.68/2.89  thf('15', plain,
% 2.68/2.89      (![X0 : $i, X1 : $i]:
% 2.68/2.89         (((k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 2.68/2.89            = (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1))))
% 2.68/2.89          | ~ (v1_relat_1 @ X1)
% 2.68/2.89          | ~ (v1_relat_1 @ X0)
% 2.68/2.89          | ~ (v1_relat_1 @ X1)
% 2.68/2.89          | ~ (v1_relat_1 @ X0))),
% 2.68/2.89      inference('sup+', [status(thm)], ['11', '14'])).
% 2.68/2.89  thf('16', plain,
% 2.68/2.89      (![X0 : $i, X1 : $i]:
% 2.68/2.89         (~ (v1_relat_1 @ X0)
% 2.68/2.89          | ~ (v1_relat_1 @ X1)
% 2.68/2.89          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 2.68/2.89              = (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)))))),
% 2.68/2.89      inference('simplify', [status(thm)], ['15'])).
% 2.68/2.89  thf(s3_funct_1__e2_24__funct_1, axiom,
% 2.68/2.89    (![A:$i,B:$i]:
% 2.68/2.89     ( ?[C:$i]:
% 2.68/2.89       ( ( ![D:$i]:
% 2.68/2.89           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 2.68/2.89         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 2.68/2.89         ( v1_relat_1 @ C ) ) ))).
% 2.68/2.89  thf('17', plain,
% 2.68/2.89      (![X13 : $i, X14 : $i]: ((k1_relat_1 @ (sk_C @ X13 @ X14)) = (X14))),
% 2.68/2.89      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.68/2.89  thf('18', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 2.68/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.89  thf('19', plain,
% 2.68/2.89      (![X0 : $i, X1 : $i]:
% 2.68/2.89         (~ (v1_relat_1 @ X0)
% 2.68/2.89          | ~ (v1_relat_1 @ X1)
% 2.68/2.89          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 2.68/2.89              = (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)))))),
% 2.68/2.89      inference('simplify', [status(thm)], ['15'])).
% 2.68/2.89  thf('20', plain,
% 2.68/2.89      (![X0 : $i]:
% 2.68/2.89         (((k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ sk_A)))
% 2.68/2.89            = (k1_relat_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ X0))))
% 2.68/2.89          | ~ (v1_relat_1 @ X0)
% 2.68/2.89          | ~ (v1_relat_1 @ sk_B))),
% 2.68/2.89      inference('sup+', [status(thm)], ['18', '19'])).
% 2.68/2.89  thf('21', plain, ((v1_relat_1 @ sk_B)),
% 2.68/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.89  thf('22', plain,
% 2.68/2.89      (![X0 : $i]:
% 2.68/2.89         (((k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ sk_A)))
% 2.68/2.89            = (k1_relat_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ X0))))
% 2.68/2.89          | ~ (v1_relat_1 @ X0))),
% 2.68/2.89      inference('demod', [status(thm)], ['20', '21'])).
% 2.68/2.89  thf('23', plain,
% 2.68/2.89      (![X0 : $i, X1 : $i]:
% 2.68/2.89         (((k1_relat_1 @ (k7_relat_1 @ (sk_C @ X1 @ X0) @ (k1_relat_1 @ sk_A)))
% 2.68/2.89            = (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))
% 2.68/2.89          | ~ (v1_relat_1 @ (sk_C @ X1 @ X0)))),
% 2.68/2.89      inference('sup+', [status(thm)], ['17', '22'])).
% 2.68/2.89  thf('24', plain, (![X13 : $i, X14 : $i]: (v1_relat_1 @ (sk_C @ X13 @ X14))),
% 2.68/2.89      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.68/2.89  thf('25', plain,
% 2.68/2.89      (![X0 : $i, X1 : $i]:
% 2.68/2.89         ((k1_relat_1 @ (k7_relat_1 @ (sk_C @ X1 @ X0) @ (k1_relat_1 @ sk_A)))
% 2.68/2.89           = (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))),
% 2.68/2.89      inference('demod', [status(thm)], ['23', '24'])).
% 2.68/2.89  thf('26', plain,
% 2.68/2.89      (![X0 : $i, X1 : $i]:
% 2.68/2.89         (((k1_relat_1 @ (k7_relat_1 @ sk_A @ (k1_relat_1 @ (sk_C @ X1 @ X0))))
% 2.68/2.89            = (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))
% 2.68/2.89          | ~ (v1_relat_1 @ sk_A)
% 2.68/2.89          | ~ (v1_relat_1 @ (sk_C @ X1 @ X0)))),
% 2.68/2.89      inference('sup+', [status(thm)], ['16', '25'])).
% 2.68/2.89  thf('27', plain,
% 2.68/2.89      (![X13 : $i, X14 : $i]: ((k1_relat_1 @ (sk_C @ X13 @ X14)) = (X14))),
% 2.68/2.89      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.68/2.89  thf('28', plain, ((v1_relat_1 @ sk_A)),
% 2.68/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.89  thf('29', plain, (![X13 : $i, X14 : $i]: (v1_relat_1 @ (sk_C @ X13 @ X14))),
% 2.68/2.89      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.68/2.89  thf('30', plain,
% 2.68/2.89      (![X0 : $i]:
% 2.68/2.89         ((k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))
% 2.68/2.89           = (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))),
% 2.68/2.89      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 2.68/2.89  thf('31', plain,
% 2.68/2.89      (![X0 : $i]:
% 2.68/2.89         ((k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))
% 2.68/2.89           = (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))),
% 2.68/2.89      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 2.68/2.89  thf('32', plain,
% 2.68/2.89      (![X0 : $i]:
% 2.68/2.89         ((k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))
% 2.68/2.89           = (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))),
% 2.68/2.89      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 2.68/2.89  thf('33', plain,
% 2.68/2.89      (![X0 : $i, X1 : $i]:
% 2.68/2.89         ((k1_relat_1 @ (k7_relat_1 @ (sk_C @ X1 @ X0) @ (k1_relat_1 @ sk_A)))
% 2.68/2.89           = (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))),
% 2.68/2.89      inference('demod', [status(thm)], ['23', '24'])).
% 2.68/2.89  thf('34', plain,
% 2.68/2.89      (![X0 : $i, X1 : $i]:
% 2.68/2.89         (~ (v1_relat_1 @ X0)
% 2.68/2.89          | ((k7_relat_1 @ X1 @ (k1_relat_1 @ X0))
% 2.68/2.89              = (k7_relat_1 @ X1 @ 
% 2.68/2.89                 (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)))))
% 2.68/2.89          | ~ (v1_relat_1 @ X1))),
% 2.68/2.89      inference('cnf', [status(esa)], [t189_relat_1])).
% 2.68/2.89  thf('35', plain,
% 2.68/2.89      (![X0 : $i, X1 : $i]:
% 2.68/2.89         (((k7_relat_1 @ sk_A @ (k1_relat_1 @ (sk_C @ X1 @ X0)))
% 2.68/2.89            = (k7_relat_1 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))))
% 2.68/2.89          | ~ (v1_relat_1 @ sk_A)
% 2.68/2.89          | ~ (v1_relat_1 @ (sk_C @ X1 @ X0)))),
% 2.68/2.89      inference('sup+', [status(thm)], ['33', '34'])).
% 2.68/2.89  thf('36', plain,
% 2.68/2.89      (![X13 : $i, X14 : $i]: ((k1_relat_1 @ (sk_C @ X13 @ X14)) = (X14))),
% 2.68/2.89      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.68/2.89  thf('37', plain, ((v1_relat_1 @ sk_A)),
% 2.68/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.89  thf('38', plain, (![X13 : $i, X14 : $i]: (v1_relat_1 @ (sk_C @ X13 @ X14))),
% 2.68/2.89      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.68/2.89  thf('39', plain,
% 2.68/2.89      (![X0 : $i]:
% 2.68/2.89         ((k7_relat_1 @ sk_A @ X0)
% 2.68/2.89           = (k7_relat_1 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))))),
% 2.68/2.89      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 2.68/2.89  thf('40', plain,
% 2.68/2.89      (![X0 : $i]:
% 2.68/2.89         ((k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))
% 2.68/2.89           = (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))),
% 2.68/2.89      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 2.68/2.89  thf('41', plain,
% 2.68/2.89      (![X0 : $i]:
% 2.68/2.89         ((k7_relat_1 @ sk_A @ X0)
% 2.68/2.89           = (k7_relat_1 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))),
% 2.68/2.89      inference('demod', [status(thm)], ['39', '40'])).
% 2.68/2.89  thf('42', plain,
% 2.68/2.89      (![X0 : $i]:
% 2.68/2.89         ((k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))
% 2.68/2.89           = (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))),
% 2.68/2.89      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 2.68/2.89  thf('43', plain,
% 2.68/2.89      (![X0 : $i]:
% 2.68/2.89         ((k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))
% 2.68/2.89           = (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))),
% 2.68/2.89      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 2.68/2.89  thf('44', plain,
% 2.68/2.89      (![X0 : $i, X1 : $i]:
% 2.68/2.89         (~ (v1_relat_1 @ X1)
% 2.68/2.89          | ~ (v1_funct_1 @ X1)
% 2.68/2.89          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ 
% 2.68/2.89               (k1_relat_1 @ X1))
% 2.68/2.89          | ((k7_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))
% 2.68/2.89              = (k7_relat_1 @ sk_A @ X0))
% 2.68/2.89          | (r2_hidden @ 
% 2.68/2.89             (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ sk_A @ X1) @ 
% 2.68/2.89             (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))),
% 2.68/2.89      inference('demod', [status(thm)],
% 2.68/2.89                ['10', '30', '31', '32', '41', '42', '43'])).
% 2.68/2.89  thf('45', plain,
% 2.68/2.89      (![X0 : $i]:
% 2.68/2.89         (~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ 
% 2.68/2.89             (k1_relat_1 @ sk_A))
% 2.68/2.89          | (r2_hidden @ 
% 2.68/2.89             (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ sk_A @ sk_B) @ 
% 2.68/2.89             (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))
% 2.68/2.89          | ((k7_relat_1 @ sk_B @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))
% 2.68/2.89              = (k7_relat_1 @ sk_A @ X0))
% 2.68/2.89          | ~ (v1_funct_1 @ sk_B)
% 2.68/2.89          | ~ (v1_relat_1 @ sk_B))),
% 2.68/2.89      inference('sup-', [status(thm)], ['0', '44'])).
% 2.68/2.89  thf('46', plain,
% 2.68/2.89      (![X7 : $i, X8 : $i]:
% 2.68/2.89         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X7 @ X8)) @ 
% 2.68/2.89           (k1_relat_1 @ X7))
% 2.68/2.89          | ~ (v1_relat_1 @ X7))),
% 2.68/2.89      inference('cnf', [status(esa)], [t89_relat_1])).
% 2.68/2.89  thf('47', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 2.68/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.89  thf('48', plain,
% 2.68/2.89      (![X9 : $i, X10 : $i]:
% 2.68/2.89         (~ (r1_tarski @ X9 @ (k1_relat_1 @ X10))
% 2.68/2.89          | ((k1_relat_1 @ (k7_relat_1 @ X10 @ X9)) = (X9))
% 2.68/2.89          | ~ (v1_relat_1 @ X10))),
% 2.68/2.89      inference('cnf', [status(esa)], [t91_relat_1])).
% 2.68/2.89  thf('49', plain,
% 2.68/2.89      (![X0 : $i]:
% 2.68/2.89         (~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_A))
% 2.68/2.89          | ~ (v1_relat_1 @ sk_B)
% 2.68/2.89          | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) = (X0)))),
% 2.68/2.89      inference('sup-', [status(thm)], ['47', '48'])).
% 2.68/2.89  thf('50', plain, ((v1_relat_1 @ sk_B)),
% 2.68/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.89  thf('51', plain,
% 2.68/2.89      (![X0 : $i]:
% 2.68/2.89         (~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_A))
% 2.68/2.89          | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) = (X0)))),
% 2.68/2.89      inference('demod', [status(thm)], ['49', '50'])).
% 2.68/2.89  thf('52', plain,
% 2.68/2.89      (![X0 : $i]:
% 2.68/2.89         (~ (v1_relat_1 @ sk_A)
% 2.68/2.89          | ((k1_relat_1 @ 
% 2.68/2.89              (k7_relat_1 @ sk_B @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))
% 2.68/2.89              = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))),
% 2.68/2.89      inference('sup-', [status(thm)], ['46', '51'])).
% 2.68/2.89  thf('53', plain, ((v1_relat_1 @ sk_A)),
% 2.68/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.89  thf('54', plain,
% 2.68/2.89      (![X0 : $i]:
% 2.68/2.89         ((k1_relat_1 @ 
% 2.68/2.89           (k7_relat_1 @ sk_B @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))
% 2.68/2.89           = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))),
% 2.68/2.89      inference('demod', [status(thm)], ['52', '53'])).
% 2.68/2.89  thf('55', plain,
% 2.68/2.89      (![X0 : $i]:
% 2.68/2.89         (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ 
% 2.68/2.89          (k1_relat_1 @ sk_A))),
% 2.68/2.89      inference('demod', [status(thm)], ['3', '4'])).
% 2.68/2.89  thf('56', plain,
% 2.68/2.89      (![X0 : $i]:
% 2.68/2.89         (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ 
% 2.68/2.89          (k1_relat_1 @ sk_A))),
% 2.68/2.89      inference('sup+', [status(thm)], ['54', '55'])).
% 2.68/2.89  thf('57', plain,
% 2.68/2.89      (![X0 : $i, X1 : $i]:
% 2.68/2.89         ((k1_relat_1 @ (k7_relat_1 @ (sk_C @ X1 @ X0) @ (k1_relat_1 @ sk_A)))
% 2.68/2.89           = (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))),
% 2.68/2.89      inference('demod', [status(thm)], ['23', '24'])).
% 2.68/2.89  thf('58', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 2.68/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.89  thf('59', plain,
% 2.68/2.89      (![X0 : $i, X1 : $i]:
% 2.68/2.89         (~ (v1_relat_1 @ X0)
% 2.68/2.89          | ((k7_relat_1 @ X1 @ (k1_relat_1 @ X0))
% 2.68/2.89              = (k7_relat_1 @ X1 @ 
% 2.68/2.89                 (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)))))
% 2.68/2.89          | ~ (v1_relat_1 @ X1))),
% 2.68/2.89      inference('cnf', [status(esa)], [t189_relat_1])).
% 2.68/2.89  thf('60', plain,
% 2.68/2.89      (![X0 : $i]:
% 2.68/2.89         (((k7_relat_1 @ sk_B @ (k1_relat_1 @ X0))
% 2.68/2.89            = (k7_relat_1 @ sk_B @ 
% 2.68/2.89               (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ sk_A)))))
% 2.68/2.89          | ~ (v1_relat_1 @ sk_B)
% 2.68/2.89          | ~ (v1_relat_1 @ X0))),
% 2.68/2.89      inference('sup+', [status(thm)], ['58', '59'])).
% 2.68/2.89  thf('61', plain, ((v1_relat_1 @ sk_B)),
% 2.68/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.89  thf('62', plain,
% 2.68/2.89      (![X0 : $i]:
% 2.68/2.89         (((k7_relat_1 @ sk_B @ (k1_relat_1 @ X0))
% 2.68/2.89            = (k7_relat_1 @ sk_B @ 
% 2.68/2.89               (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ sk_A)))))
% 2.68/2.89          | ~ (v1_relat_1 @ X0))),
% 2.68/2.89      inference('demod', [status(thm)], ['60', '61'])).
% 2.68/2.89  thf('63', plain,
% 2.68/2.89      (![X0 : $i, X1 : $i]:
% 2.68/2.89         (((k7_relat_1 @ sk_B @ (k1_relat_1 @ (sk_C @ X1 @ X0)))
% 2.68/2.89            = (k7_relat_1 @ sk_B @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))))
% 2.68/2.89          | ~ (v1_relat_1 @ (sk_C @ X1 @ X0)))),
% 2.68/2.89      inference('sup+', [status(thm)], ['57', '62'])).
% 2.68/2.89  thf('64', plain,
% 2.68/2.89      (![X13 : $i, X14 : $i]: ((k1_relat_1 @ (sk_C @ X13 @ X14)) = (X14))),
% 2.68/2.89      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.68/2.89  thf('65', plain, (![X13 : $i, X14 : $i]: (v1_relat_1 @ (sk_C @ X13 @ X14))),
% 2.68/2.89      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.68/2.89  thf('66', plain,
% 2.68/2.89      (![X0 : $i]:
% 2.68/2.89         ((k7_relat_1 @ sk_B @ X0)
% 2.68/2.89           = (k7_relat_1 @ sk_B @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))))),
% 2.68/2.89      inference('demod', [status(thm)], ['63', '64', '65'])).
% 2.68/2.89  thf('67', plain,
% 2.68/2.89      (![X0 : $i]:
% 2.68/2.89         ((k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))
% 2.68/2.89           = (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))),
% 2.68/2.89      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 2.68/2.89  thf('68', plain,
% 2.68/2.89      (![X0 : $i]:
% 2.68/2.89         ((k7_relat_1 @ sk_B @ X0)
% 2.68/2.89           = (k7_relat_1 @ sk_B @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))),
% 2.68/2.89      inference('demod', [status(thm)], ['66', '67'])).
% 2.68/2.89  thf('69', plain, ((v1_funct_1 @ sk_B)),
% 2.68/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.89  thf('70', plain, ((v1_relat_1 @ sk_B)),
% 2.68/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.89  thf('71', plain,
% 2.68/2.89      (![X0 : $i]:
% 2.68/2.89         ((r2_hidden @ 
% 2.68/2.89           (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ sk_A @ sk_B) @ 
% 2.68/2.89           (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))
% 2.68/2.89          | ((k7_relat_1 @ sk_B @ X0) = (k7_relat_1 @ sk_A @ X0)))),
% 2.68/2.89      inference('demod', [status(thm)], ['45', '56', '68', '69', '70'])).
% 2.68/2.89  thf('72', plain,
% 2.68/2.89      (![X0 : $i, X1 : $i]:
% 2.68/2.89         ((k1_relat_1 @ (k7_relat_1 @ (sk_C @ X1 @ X0) @ (k1_relat_1 @ sk_A)))
% 2.68/2.89           = (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))),
% 2.68/2.89      inference('demod', [status(thm)], ['23', '24'])).
% 2.68/2.89  thf(t86_relat_1, axiom,
% 2.68/2.89    (![A:$i,B:$i,C:$i]:
% 2.68/2.89     ( ( v1_relat_1 @ C ) =>
% 2.68/2.89       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 2.68/2.89         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 2.68/2.89  thf('73', plain,
% 2.68/2.89      (![X2 : $i, X3 : $i, X4 : $i]:
% 2.68/2.89         (~ (r2_hidden @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X4 @ X3)))
% 2.68/2.89          | (r2_hidden @ X2 @ (k1_relat_1 @ X4))
% 2.68/2.89          | ~ (v1_relat_1 @ X4))),
% 2.68/2.89      inference('cnf', [status(esa)], [t86_relat_1])).
% 2.68/2.89  thf('74', plain,
% 2.68/2.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.68/2.89         (~ (r2_hidden @ X2 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))
% 2.68/2.89          | ~ (v1_relat_1 @ (sk_C @ X1 @ X0))
% 2.68/2.89          | (r2_hidden @ X2 @ (k1_relat_1 @ (sk_C @ X1 @ X0))))),
% 2.68/2.89      inference('sup-', [status(thm)], ['72', '73'])).
% 2.68/2.89  thf('75', plain, (![X13 : $i, X14 : $i]: (v1_relat_1 @ (sk_C @ X13 @ X14))),
% 2.68/2.89      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.68/2.89  thf('76', plain,
% 2.68/2.89      (![X13 : $i, X14 : $i]: ((k1_relat_1 @ (sk_C @ X13 @ X14)) = (X14))),
% 2.68/2.89      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.68/2.89  thf('77', plain,
% 2.68/2.89      (![X0 : $i, X2 : $i]:
% 2.68/2.89         (~ (r2_hidden @ X2 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))
% 2.68/2.89          | (r2_hidden @ X2 @ X0))),
% 2.68/2.89      inference('demod', [status(thm)], ['74', '75', '76'])).
% 2.68/2.89  thf('78', plain,
% 2.68/2.89      (![X0 : $i]:
% 2.68/2.89         ((k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))
% 2.68/2.89           = (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))),
% 2.68/2.89      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 2.68/2.89  thf('79', plain,
% 2.68/2.89      (![X0 : $i, X2 : $i]:
% 2.68/2.89         (~ (r2_hidden @ X2 @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))
% 2.68/2.89          | (r2_hidden @ X2 @ X0))),
% 2.68/2.89      inference('demod', [status(thm)], ['77', '78'])).
% 2.68/2.89  thf('80', plain,
% 2.68/2.89      (![X0 : $i]:
% 2.68/2.89         (((k7_relat_1 @ sk_B @ X0) = (k7_relat_1 @ sk_A @ X0))
% 2.68/2.89          | (r2_hidden @ 
% 2.68/2.89             (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ sk_A @ sk_B) @ 
% 2.68/2.89             X0))),
% 2.68/2.89      inference('sup-', [status(thm)], ['71', '79'])).
% 2.68/2.89  thf('81', plain,
% 2.68/2.89      (![X20 : $i]:
% 2.68/2.89         (((k1_funct_1 @ sk_A @ X20) = (k1_funct_1 @ sk_B @ X20))
% 2.68/2.89          | ~ (r2_hidden @ X20 @ sk_C_1))),
% 2.68/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.89  thf('82', plain,
% 2.68/2.89      ((((k7_relat_1 @ sk_B @ sk_C_1) = (k7_relat_1 @ sk_A @ sk_C_1))
% 2.68/2.89        | ((k1_funct_1 @ sk_A @ 
% 2.68/2.89            (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)) @ sk_A @ sk_B))
% 2.68/2.89            = (k1_funct_1 @ sk_B @ 
% 2.68/2.89               (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)) @ sk_A @ 
% 2.68/2.89                sk_B))))),
% 2.68/2.89      inference('sup-', [status(thm)], ['80', '81'])).
% 2.68/2.89  thf('83', plain,
% 2.68/2.89      (((k7_relat_1 @ sk_A @ sk_C_1) != (k7_relat_1 @ sk_B @ sk_C_1))),
% 2.68/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.89  thf('84', plain,
% 2.68/2.89      (((k1_funct_1 @ sk_A @ 
% 2.68/2.89         (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)) @ sk_A @ sk_B))
% 2.68/2.89         = (k1_funct_1 @ sk_B @ 
% 2.68/2.89            (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)) @ sk_A @ sk_B)))),
% 2.68/2.89      inference('simplify_reflect-', [status(thm)], ['82', '83'])).
% 2.68/2.89  thf('85', plain,
% 2.68/2.89      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.68/2.89         (~ (v1_relat_1 @ X16)
% 2.68/2.89          | ~ (v1_funct_1 @ X16)
% 2.68/2.89          | ((k1_funct_1 @ X18 @ (sk_D @ X17 @ X16 @ X18))
% 2.68/2.89              != (k1_funct_1 @ X16 @ (sk_D @ X17 @ X16 @ X18)))
% 2.68/2.89          | ((k7_relat_1 @ X18 @ X17) = (k7_relat_1 @ X16 @ X17))
% 2.68/2.89          | ~ (r1_tarski @ X17 @ (k1_relat_1 @ X16))
% 2.68/2.89          | ~ (r1_tarski @ X17 @ (k1_relat_1 @ X18))
% 2.68/2.89          | ~ (v1_funct_1 @ X18)
% 2.68/2.89          | ~ (v1_relat_1 @ X18))),
% 2.68/2.89      inference('cnf', [status(esa)], [t165_funct_1])).
% 2.68/2.89  thf('86', plain,
% 2.68/2.89      ((((k1_funct_1 @ sk_A @ 
% 2.68/2.89          (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)) @ sk_A @ sk_B))
% 2.68/2.89          != (k1_funct_1 @ sk_A @ 
% 2.68/2.89              (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)) @ sk_A @ sk_B)))
% 2.68/2.89        | ~ (v1_relat_1 @ sk_B)
% 2.68/2.89        | ~ (v1_funct_1 @ sk_B)
% 2.68/2.89        | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)) @ 
% 2.68/2.89             (k1_relat_1 @ sk_B))
% 2.68/2.89        | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)) @ 
% 2.68/2.89             (k1_relat_1 @ sk_A))
% 2.68/2.89        | ((k7_relat_1 @ sk_B @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)))
% 2.68/2.89            = (k7_relat_1 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1))))
% 2.68/2.89        | ~ (v1_funct_1 @ sk_A)
% 2.68/2.89        | ~ (v1_relat_1 @ sk_A))),
% 2.68/2.89      inference('sup-', [status(thm)], ['84', '85'])).
% 2.68/2.89  thf('87', plain, ((v1_relat_1 @ sk_B)),
% 2.68/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.89  thf('88', plain, ((v1_funct_1 @ sk_B)),
% 2.68/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.89  thf('89', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 2.68/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.89  thf('90', plain,
% 2.68/2.89      (![X0 : $i]:
% 2.68/2.89         (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ 
% 2.68/2.89          (k1_relat_1 @ sk_A))),
% 2.68/2.89      inference('sup+', [status(thm)], ['54', '55'])).
% 2.68/2.89  thf('91', plain,
% 2.68/2.89      (![X0 : $i]:
% 2.68/2.89         (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ 
% 2.68/2.89          (k1_relat_1 @ sk_A))),
% 2.68/2.89      inference('sup+', [status(thm)], ['54', '55'])).
% 2.68/2.89  thf('92', plain,
% 2.68/2.89      (![X0 : $i]:
% 2.68/2.89         ((k7_relat_1 @ sk_B @ X0)
% 2.68/2.89           = (k7_relat_1 @ sk_B @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))),
% 2.68/2.89      inference('demod', [status(thm)], ['66', '67'])).
% 2.68/2.89  thf('93', plain,
% 2.68/2.89      (![X0 : $i]:
% 2.68/2.89         ((k7_relat_1 @ sk_A @ X0)
% 2.68/2.89           = (k7_relat_1 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))),
% 2.68/2.89      inference('demod', [status(thm)], ['39', '40'])).
% 2.68/2.89  thf('94', plain, ((v1_funct_1 @ sk_A)),
% 2.68/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.89  thf('95', plain, ((v1_relat_1 @ sk_A)),
% 2.68/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.89  thf('96', plain,
% 2.68/2.89      ((((k1_funct_1 @ sk_A @ 
% 2.68/2.89          (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)) @ sk_A @ sk_B))
% 2.68/2.89          != (k1_funct_1 @ sk_A @ 
% 2.68/2.89              (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)) @ sk_A @ sk_B)))
% 2.68/2.89        | ((k7_relat_1 @ sk_B @ sk_C_1) = (k7_relat_1 @ sk_A @ sk_C_1)))),
% 2.68/2.89      inference('demod', [status(thm)],
% 2.68/2.89                ['86', '87', '88', '89', '90', '91', '92', '93', '94', '95'])).
% 2.68/2.89  thf('97', plain,
% 2.68/2.89      (((k7_relat_1 @ sk_B @ sk_C_1) = (k7_relat_1 @ sk_A @ sk_C_1))),
% 2.68/2.89      inference('simplify', [status(thm)], ['96'])).
% 2.68/2.89  thf('98', plain,
% 2.68/2.89      (((k7_relat_1 @ sk_A @ sk_C_1) != (k7_relat_1 @ sk_B @ sk_C_1))),
% 2.68/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.68/2.89  thf('99', plain, ($false),
% 2.68/2.89      inference('simplify_reflect-', [status(thm)], ['97', '98'])).
% 2.68/2.89  
% 2.68/2.89  % SZS output end Refutation
% 2.68/2.89  
% 2.77/2.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
