%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0808+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xkJRwFV7O5

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 (  96 expanded)
%              Number of leaves         :   21 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :  545 (1762 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(r3_wellord1_type,type,(
    r3_wellord1: $i > $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(t61_wellord1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ( ( ( v2_wellord1 @ A )
                  & ( r3_wellord1 @ A @ B @ C ) )
               => ! [D: $i] :
                    ~ ( ( r2_hidden @ D @ ( k3_relat_1 @ A ) )
                      & ! [E: $i] :
                          ~ ( ( r2_hidden @ E @ ( k3_relat_1 @ B ) )
                            & ( r4_wellord1 @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ D ) ) @ ( k2_wellord1 @ B @ ( k1_wellord1 @ B @ E ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ! [C: $i] :
                ( ( ( v1_relat_1 @ C )
                  & ( v1_funct_1 @ C ) )
               => ( ( ( v2_wellord1 @ A )
                    & ( r3_wellord1 @ A @ B @ C ) )
                 => ! [D: $i] :
                      ~ ( ( r2_hidden @ D @ ( k3_relat_1 @ A ) )
                        & ! [E: $i] :
                            ~ ( ( r2_hidden @ E @ ( k3_relat_1 @ B ) )
                              & ( r4_wellord1 @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ D ) ) @ ( k2_wellord1 @ B @ ( k1_wellord1 @ B @ E ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_wellord1])).

thf('0',plain,(
    r3_wellord1 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_D @ ( k3_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t60_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ( ( r3_wellord1 @ A @ B @ C )
               => ! [D: $i] :
                    ~ ( ( r2_hidden @ D @ ( k3_relat_1 @ A ) )
                      & ! [E: $i] :
                          ~ ( ( r2_hidden @ E @ ( k3_relat_1 @ B ) )
                            & ( ( k9_relat_1 @ C @ ( k1_wellord1 @ A @ D ) )
                              = ( k1_wellord1 @ B @ E ) ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( r3_wellord1 @ X7 @ X6 @ X8 )
      | ( ( k9_relat_1 @ X8 @ ( k1_wellord1 @ X7 @ X9 ) )
        = ( k1_wellord1 @ X6 @ ( sk_E @ X9 @ X8 @ X6 @ X7 ) ) )
      | ~ ( r2_hidden @ X9 @ ( k3_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t60_wellord1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k1_wellord1 @ sk_A @ sk_D ) )
        = ( k1_wellord1 @ X1 @ ( sk_E @ sk_D @ X0 @ X1 @ sk_A ) ) )
      | ~ ( r3_wellord1 @ sk_A @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k1_wellord1 @ sk_A @ sk_D ) )
        = ( k1_wellord1 @ X1 @ ( sk_E @ sk_D @ X0 @ X1 @ sk_A ) ) )
      | ~ ( r3_wellord1 @ sk_A @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k9_relat_1 @ sk_C @ ( k1_wellord1 @ sk_A @ sk_D ) )
      = ( k1_wellord1 @ sk_B @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_wellord1 @ sk_A @ sk_D ) )
    = ( k1_wellord1 @ sk_B @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('11',plain,(
    ! [X10: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_relat_1 @ sk_B ) )
      | ~ ( r4_wellord1 @ ( k2_wellord1 @ sk_A @ ( k1_wellord1 @ sk_A @ sk_D ) ) @ ( k2_wellord1 @ sk_B @ ( k1_wellord1 @ sk_B @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( r4_wellord1 @ ( k2_wellord1 @ sk_A @ ( k1_wellord1 @ sk_A @ sk_D ) ) @ ( k2_wellord1 @ sk_B @ ( k9_relat_1 @ sk_C @ ( k1_wellord1 @ sk_A @ sk_D ) ) ) )
    | ~ ( r2_hidden @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r3_wellord1 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_wellord1 @ B @ A ) @ ( k3_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t13_wellord1])).

thf(t59_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ! [D: $i] :
              ( ( ( v1_relat_1 @ D )
                & ( v1_funct_1 @ D ) )
             => ( ( ( v2_wellord1 @ B )
                  & ( r1_tarski @ A @ ( k3_relat_1 @ B ) )
                  & ( r3_wellord1 @ B @ C @ D ) )
               => ( ( r3_wellord1 @ ( k2_wellord1 @ B @ A ) @ ( k2_wellord1 @ C @ ( k9_relat_1 @ D @ A ) ) @ ( k7_relat_1 @ D @ A ) )
                  & ( r4_wellord1 @ ( k2_wellord1 @ B @ A ) @ ( k2_wellord1 @ C @ ( k9_relat_1 @ D @ A ) ) ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v2_wellord1 @ X3 )
      | ~ ( r1_tarski @ X4 @ ( k3_relat_1 @ X3 ) )
      | ~ ( r3_wellord1 @ X3 @ X2 @ X5 )
      | ( r4_wellord1 @ ( k2_wellord1 @ X3 @ X4 ) @ ( k2_wellord1 @ X2 @ ( k9_relat_1 @ X5 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t59_wellord1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( r4_wellord1 @ ( k2_wellord1 @ X0 @ ( k1_wellord1 @ X0 @ X1 ) ) @ ( k2_wellord1 @ X3 @ ( k9_relat_1 @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) ) )
      | ~ ( r3_wellord1 @ X0 @ X3 @ X2 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( r3_wellord1 @ X0 @ X3 @ X2 )
      | ( r4_wellord1 @ ( k2_wellord1 @ X0 @ ( k1_wellord1 @ X0 @ X1 ) ) @ ( k2_wellord1 @ X3 @ ( k9_relat_1 @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r4_wellord1 @ ( k2_wellord1 @ sk_A @ ( k1_wellord1 @ sk_A @ X0 ) ) @ ( k2_wellord1 @ sk_B @ ( k9_relat_1 @ sk_C @ ( k1_wellord1 @ sk_A @ X0 ) ) ) )
      | ~ ( v2_wellord1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( r4_wellord1 @ ( k2_wellord1 @ sk_A @ ( k1_wellord1 @ sk_A @ X0 ) ) @ ( k2_wellord1 @ sk_B @ ( k9_relat_1 @ sk_C @ ( k1_wellord1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['18','19','20','21','22','23'])).

thf('25',plain,(
    r3_wellord1 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r2_hidden @ sk_D @ ( k3_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( r3_wellord1 @ X7 @ X6 @ X8 )
      | ( r2_hidden @ ( sk_E @ X9 @ X8 @ X6 @ X7 ) @ ( k3_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ X9 @ ( k3_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t60_wellord1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_E @ sk_D @ X0 @ X1 @ sk_A ) @ ( k3_relat_1 @ X1 ) )
      | ~ ( r3_wellord1 @ sk_A @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_E @ sk_D @ X0 @ X1 @ sk_A ) @ ( k3_relat_1 @ X1 ) )
      | ~ ( r3_wellord1 @ sk_A @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r2_hidden @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['12','24','35'])).


%------------------------------------------------------------------------------
