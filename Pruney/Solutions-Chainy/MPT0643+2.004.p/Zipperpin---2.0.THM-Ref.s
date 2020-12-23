%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.l9sViygzFi

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:14 EST 2020

% Result     : Theorem 0.87s
% Output     : Refutation 0.87s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 261 expanded)
%              Number of leaves         :   23 (  85 expanded)
%              Depth                    :   17
%              Number of atoms          : 1117 (4866 expanded)
%              Number of equality atoms :   78 ( 548 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_4_type,type,(
    sk_C_4: $i )).

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
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
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
    ! [X22: $i,X23: $i] :
      ( ( ( k1_relat_1 @ X23 )
       != X22 )
      | ( r2_hidden @ ( sk_C_3 @ X23 @ X22 ) @ X22 )
      | ( X23
        = ( k6_relat_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('2',plain,(
    ! [X23: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( X23
        = ( k6_relat_1 @ ( k1_relat_1 @ X23 ) ) )
      | ( r2_hidden @ ( sk_C_3 @ X23 @ ( k1_relat_1 @ X23 ) ) @ ( k1_relat_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,
    ( ( r2_hidden @ ( sk_C_3 @ sk_C_4 @ sk_A ) @ ( k1_relat_1 @ sk_C_4 ) )
    | ( sk_C_4
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C_4 ) ) )
    | ~ ( v1_funct_1 @ sk_C_4 )
    | ~ ( v1_relat_1 @ sk_C_4 ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf('4',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ ( sk_C_3 @ sk_C_4 @ sk_A ) @ sk_A )
    | ( sk_C_4
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5','6','7'])).

thf('9',plain,(
    sk_C_4
 != ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r2_hidden @ ( sk_C_3 @ sk_C_4 @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X26 ) )
      | ( X27
       != ( k1_funct_1 @ X26 @ X25 ) )
      | ( r2_hidden @ ( k4_tarski @ X25 @ X27 ) @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('13',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ( r2_hidden @ ( k4_tarski @ X25 @ ( k1_funct_1 @ X26 @ X25 ) ) @ X26 )
      | ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_B_1 @ X0 ) ) @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_B_1 @ X0 ) ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_3 @ sk_C_4 @ sk_A ) @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['10','17'])).

thf('19',plain,
    ( ( k5_relat_1 @ sk_C_4 @ sk_B_1 )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( C
                  = ( k5_relat_1 @ A @ B ) )
              <=> ! [D: $i,E: $i] :
                    ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
                  <=> ? [F: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B )
                        & ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( X6
       != ( k5_relat_1 @ X5 @ X4 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X10 @ X7 @ X4 @ X5 ) @ X10 ) @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X10 ) @ X6 )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('21',plain,(
    ! [X4: $i,X5: $i,X7: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X10 ) @ ( k5_relat_1 @ X5 @ X4 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X10 @ X7 @ X4 @ X5 ) @ X10 ) @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X0 @ X1 @ sk_B_1 @ sk_C_4 ) @ X0 ) @ sk_B_1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C_4 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_C_4 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k5_relat_1 @ sk_C_4 @ sk_B_1 )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_B_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X0 @ X1 @ sk_B_1 @ sk_C_4 ) @ X0 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['22','23','24','25','26'])).

thf('28',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ ( sk_C_3 @ sk_C_4 @ sk_A ) @ sk_B_1 @ sk_C_4 ) @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['18','27'])).

thf('29',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_3 @ sk_C_4 @ sk_A ) @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['10','17'])).

thf('30',plain,
    ( ( k5_relat_1 @ sk_C_4 @ sk_B_1 )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( X6
       != ( k5_relat_1 @ X5 @ X4 ) )
      | ( r2_hidden @ ( k4_tarski @ X7 @ ( sk_F_1 @ X10 @ X7 @ X4 @ X5 ) ) @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X10 ) @ X6 )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('32',plain,(
    ! [X4: $i,X5: $i,X7: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X10 ) @ ( k5_relat_1 @ X5 @ X4 ) )
      | ( r2_hidden @ ( k4_tarski @ X7 @ ( sk_F_1 @ X10 @ X7 @ X4 @ X5 ) ) @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_F_1 @ X0 @ X1 @ sk_B_1 @ sk_C_4 ) ) @ sk_C_4 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C_4 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_C_4 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k5_relat_1 @ sk_C_4 @ sk_B_1 )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_B_1 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_F_1 @ X0 @ X1 @ sk_B_1 @ sk_C_4 ) ) @ sk_C_4 ) ) ),
    inference(demod,[status(thm)],['33','34','35','36','37'])).

thf('39',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_3 @ sk_C_4 @ sk_A ) @ ( sk_F_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ ( sk_C_3 @ sk_C_4 @ sk_A ) @ sk_B_1 @ sk_C_4 ) ) @ sk_C_4 ),
    inference('sup-',[status(thm)],['29','38'])).

thf('40',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X25 @ X27 ) @ X26 )
      | ( X27
        = ( k1_funct_1 @ X26 @ X25 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ sk_C_4 )
    | ~ ( v1_funct_1 @ sk_C_4 )
    | ( ( sk_F_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ ( sk_C_3 @ sk_C_4 @ sk_A ) @ sk_B_1 @ sk_C_4 )
      = ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( sk_F_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ ( sk_C_3 @ sk_C_4 @ sk_A ) @ sk_B_1 @ sk_C_4 )
    = ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) ) @ sk_B_1 ),
    inference(demod,[status(thm)],['28','44'])).

thf('46',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X25 @ X27 ) @ X26 )
      | ( X27
        = ( k1_funct_1 @ X26 @ X25 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
      = ( k1_funct_1 @ sk_B_1 @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
    = ( k1_funct_1 @ sk_B_1 @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('52',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X19 ) )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X19 ) )
      | ( ( k1_funct_1 @ X19 @ X20 )
       != ( k1_funct_1 @ X19 @ X21 ) )
      | ( X20 = X21 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
        = X0 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','58'])).

thf('60',plain,(
    ! [X23: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( X23
        = ( k6_relat_1 @ ( k1_relat_1 @ X23 ) ) )
      | ( r2_hidden @ ( sk_C_3 @ X23 @ ( k1_relat_1 @ X23 ) ) @ ( k1_relat_1 @ X23 ) ) ) ),
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

thf('61',plain,(
    ! [X13: $i,X15: $i,X17: $i,X18: $i] :
      ( ( X15
       != ( k2_relat_1 @ X13 ) )
      | ( r2_hidden @ X17 @ X15 )
      | ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ X13 ) )
      | ( X17
       != ( k1_funct_1 @ X13 @ X18 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('62',plain,(
    ! [X13: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ X13 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X13 @ X18 ) @ ( k2_relat_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_3 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_3 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_4 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_4 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( sk_C_4
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C_4 ) ) )
    | ~ ( v1_funct_1 @ sk_C_4 )
    | ~ ( v1_relat_1 @ sk_C_4 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ ( k1_relat_1 @ sk_C_4 ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( sk_C_4
      = ( k6_relat_1 @ sk_A ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','70','71','72'])).

thf('74',plain,(
    sk_C_4
 != ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['59','75'])).

thf('77',plain,
    ( ( ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
      = ( sk_C_3 @ sk_C_4 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_C_3 @ sk_C_4 @ sk_A ) @ sk_A ) ),
    inference(eq_res,[status(thm)],['76'])).

thf('78',plain,(
    r2_hidden @ ( sk_C_3 @ sk_C_4 @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('79',plain,
    ( ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
    = ( sk_C_3 @ sk_C_4 @ sk_A ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k1_relat_1 @ X23 )
       != X22 )
      | ( ( k1_funct_1 @ X23 @ ( sk_C_3 @ X23 @ X22 ) )
       != ( sk_C_3 @ X23 @ X22 ) )
      | ( X23
        = ( k6_relat_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('82',plain,(
    ! [X23: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( X23
        = ( k6_relat_1 @ ( k1_relat_1 @ X23 ) ) )
      | ( ( k1_funct_1 @ X23 @ ( sk_C_3 @ X23 @ ( k1_relat_1 @ X23 ) ) )
       != ( sk_C_3 @ X23 @ ( k1_relat_1 @ X23 ) ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
     != ( sk_C_3 @ sk_C_4 @ ( k1_relat_1 @ sk_C_4 ) ) )
    | ( sk_C_4
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C_4 ) ) )
    | ~ ( v1_funct_1 @ sk_C_4 )
    | ~ ( v1_relat_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['80','82'])).

thf('84',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( k1_relat_1 @ sk_C_4 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
     != ( sk_C_3 @ sk_C_4 @ sk_A ) )
    | ( sk_C_4
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['83','84','85','86','87'])).

thf('89',plain,(
    sk_C_4
 != ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ( k1_funct_1 @ sk_C_4 @ ( sk_C_3 @ sk_C_4 @ sk_A ) )
 != ( sk_C_3 @ sk_C_4 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['88','89'])).

thf('91',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['79','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.l9sViygzFi
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:47:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.87/1.07  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.87/1.07  % Solved by: fo/fo7.sh
% 0.87/1.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.87/1.07  % done 905 iterations in 0.610s
% 0.87/1.07  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.87/1.07  % SZS output start Refutation
% 0.87/1.07  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i > $i).
% 0.87/1.07  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.87/1.07  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.87/1.07  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.87/1.07  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.87/1.07  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.87/1.07  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.87/1.07  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.87/1.07  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.87/1.07  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.87/1.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.87/1.07  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.87/1.07  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.87/1.07  thf(sk_A_type, type, sk_A: $i).
% 0.87/1.07  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.87/1.07  thf(sk_C_4_type, type, sk_C_4: $i).
% 0.87/1.07  thf(t50_funct_1, conjecture,
% 0.87/1.07    (![A:$i,B:$i]:
% 0.87/1.07     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.87/1.07       ( ![C:$i]:
% 0.87/1.07         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.87/1.07           ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.87/1.07               ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.87/1.07               ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) & ( v2_funct_1 @ B ) & 
% 0.87/1.07               ( ( k5_relat_1 @ C @ B ) = ( B ) ) ) =>
% 0.87/1.07             ( ( C ) = ( k6_relat_1 @ A ) ) ) ) ) ))).
% 0.87/1.07  thf(zf_stmt_0, negated_conjecture,
% 0.87/1.07    (~( ![A:$i,B:$i]:
% 0.87/1.07        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.87/1.07          ( ![C:$i]:
% 0.87/1.07            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.87/1.07              ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.87/1.07                  ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.87/1.07                  ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) & 
% 0.87/1.07                  ( v2_funct_1 @ B ) & ( ( k5_relat_1 @ C @ B ) = ( B ) ) ) =>
% 0.87/1.07                ( ( C ) = ( k6_relat_1 @ A ) ) ) ) ) ) )),
% 0.87/1.07    inference('cnf.neg', [status(esa)], [t50_funct_1])).
% 0.87/1.07  thf('0', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf(t34_funct_1, axiom,
% 0.87/1.07    (![A:$i,B:$i]:
% 0.87/1.07     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.87/1.07       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.87/1.07         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.87/1.07           ( ![C:$i]:
% 0.87/1.07             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.87/1.07  thf('1', plain,
% 0.87/1.07      (![X22 : $i, X23 : $i]:
% 0.87/1.07         (((k1_relat_1 @ X23) != (X22))
% 0.87/1.07          | (r2_hidden @ (sk_C_3 @ X23 @ X22) @ X22)
% 0.87/1.07          | ((X23) = (k6_relat_1 @ X22))
% 0.87/1.07          | ~ (v1_funct_1 @ X23)
% 0.87/1.07          | ~ (v1_relat_1 @ X23))),
% 0.87/1.07      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.87/1.07  thf('2', plain,
% 0.87/1.07      (![X23 : $i]:
% 0.87/1.07         (~ (v1_relat_1 @ X23)
% 0.87/1.07          | ~ (v1_funct_1 @ X23)
% 0.87/1.07          | ((X23) = (k6_relat_1 @ (k1_relat_1 @ X23)))
% 0.87/1.07          | (r2_hidden @ (sk_C_3 @ X23 @ (k1_relat_1 @ X23)) @ 
% 0.87/1.07             (k1_relat_1 @ X23)))),
% 0.87/1.07      inference('simplify', [status(thm)], ['1'])).
% 0.87/1.07  thf('3', plain,
% 0.87/1.07      (((r2_hidden @ (sk_C_3 @ sk_C_4 @ sk_A) @ (k1_relat_1 @ sk_C_4))
% 0.87/1.07        | ((sk_C_4) = (k6_relat_1 @ (k1_relat_1 @ sk_C_4)))
% 0.87/1.07        | ~ (v1_funct_1 @ sk_C_4)
% 0.87/1.07        | ~ (v1_relat_1 @ sk_C_4))),
% 0.87/1.07      inference('sup+', [status(thm)], ['0', '2'])).
% 0.87/1.07  thf('4', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('5', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('6', plain, ((v1_funct_1 @ sk_C_4)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('7', plain, ((v1_relat_1 @ sk_C_4)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('8', plain,
% 0.87/1.07      (((r2_hidden @ (sk_C_3 @ sk_C_4 @ sk_A) @ sk_A)
% 0.87/1.07        | ((sk_C_4) = (k6_relat_1 @ sk_A)))),
% 0.87/1.07      inference('demod', [status(thm)], ['3', '4', '5', '6', '7'])).
% 0.87/1.07  thf('9', plain, (((sk_C_4) != (k6_relat_1 @ sk_A))),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('10', plain, ((r2_hidden @ (sk_C_3 @ sk_C_4 @ sk_A) @ sk_A)),
% 0.87/1.07      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.87/1.07  thf('11', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf(t8_funct_1, axiom,
% 0.87/1.07    (![A:$i,B:$i,C:$i]:
% 0.87/1.07     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.87/1.07       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.87/1.07         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.87/1.07           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.87/1.07  thf('12', plain,
% 0.87/1.07      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.87/1.07         (~ (r2_hidden @ X25 @ (k1_relat_1 @ X26))
% 0.87/1.07          | ((X27) != (k1_funct_1 @ X26 @ X25))
% 0.87/1.07          | (r2_hidden @ (k4_tarski @ X25 @ X27) @ X26)
% 0.87/1.07          | ~ (v1_funct_1 @ X26)
% 0.87/1.07          | ~ (v1_relat_1 @ X26))),
% 0.87/1.07      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.87/1.07  thf('13', plain,
% 0.87/1.07      (![X25 : $i, X26 : $i]:
% 0.87/1.07         (~ (v1_relat_1 @ X26)
% 0.87/1.07          | ~ (v1_funct_1 @ X26)
% 0.87/1.07          | (r2_hidden @ (k4_tarski @ X25 @ (k1_funct_1 @ X26 @ X25)) @ X26)
% 0.87/1.07          | ~ (r2_hidden @ X25 @ (k1_relat_1 @ X26)))),
% 0.87/1.07      inference('simplify', [status(thm)], ['12'])).
% 0.87/1.07  thf('14', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         (~ (r2_hidden @ X0 @ sk_A)
% 0.87/1.07          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_B_1 @ X0)) @ sk_B_1)
% 0.87/1.07          | ~ (v1_funct_1 @ sk_B_1)
% 0.87/1.07          | ~ (v1_relat_1 @ sk_B_1))),
% 0.87/1.07      inference('sup-', [status(thm)], ['11', '13'])).
% 0.87/1.07  thf('15', plain, ((v1_funct_1 @ sk_B_1)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('16', plain, ((v1_relat_1 @ sk_B_1)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('17', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         (~ (r2_hidden @ X0 @ sk_A)
% 0.87/1.07          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_B_1 @ X0)) @ sk_B_1))),
% 0.87/1.07      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.87/1.07  thf('18', plain,
% 0.87/1.07      ((r2_hidden @ 
% 0.87/1.07        (k4_tarski @ (sk_C_3 @ sk_C_4 @ sk_A) @ 
% 0.87/1.07         (k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A))) @ 
% 0.87/1.07        sk_B_1)),
% 0.87/1.07      inference('sup-', [status(thm)], ['10', '17'])).
% 0.87/1.07  thf('19', plain, (((k5_relat_1 @ sk_C_4 @ sk_B_1) = (sk_B_1))),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf(d8_relat_1, axiom,
% 0.87/1.07    (![A:$i]:
% 0.87/1.07     ( ( v1_relat_1 @ A ) =>
% 0.87/1.07       ( ![B:$i]:
% 0.87/1.07         ( ( v1_relat_1 @ B ) =>
% 0.87/1.07           ( ![C:$i]:
% 0.87/1.07             ( ( v1_relat_1 @ C ) =>
% 0.87/1.07               ( ( ( C ) = ( k5_relat_1 @ A @ B ) ) <=>
% 0.87/1.07                 ( ![D:$i,E:$i]:
% 0.87/1.07                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.87/1.07                     ( ?[F:$i]:
% 0.87/1.07                       ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B ) & 
% 0.87/1.07                         ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.87/1.07  thf('20', plain,
% 0.87/1.07      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X10 : $i]:
% 0.87/1.07         (~ (v1_relat_1 @ X4)
% 0.87/1.07          | ((X6) != (k5_relat_1 @ X5 @ X4))
% 0.87/1.07          | (r2_hidden @ (k4_tarski @ (sk_F_1 @ X10 @ X7 @ X4 @ X5) @ X10) @ X4)
% 0.87/1.07          | ~ (r2_hidden @ (k4_tarski @ X7 @ X10) @ X6)
% 0.87/1.07          | ~ (v1_relat_1 @ X6)
% 0.87/1.07          | ~ (v1_relat_1 @ X5))),
% 0.87/1.07      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.87/1.07  thf('21', plain,
% 0.87/1.07      (![X4 : $i, X5 : $i, X7 : $i, X10 : $i]:
% 0.87/1.07         (~ (v1_relat_1 @ X5)
% 0.87/1.07          | ~ (v1_relat_1 @ (k5_relat_1 @ X5 @ X4))
% 0.87/1.07          | ~ (r2_hidden @ (k4_tarski @ X7 @ X10) @ (k5_relat_1 @ X5 @ X4))
% 0.87/1.07          | (r2_hidden @ (k4_tarski @ (sk_F_1 @ X10 @ X7 @ X4 @ X5) @ X10) @ X4)
% 0.87/1.07          | ~ (v1_relat_1 @ X4))),
% 0.87/1.07      inference('simplify', [status(thm)], ['20'])).
% 0.87/1.07  thf('22', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i]:
% 0.87/1.07         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_B_1)
% 0.87/1.07          | ~ (v1_relat_1 @ sk_B_1)
% 0.87/1.07          | (r2_hidden @ 
% 0.87/1.07             (k4_tarski @ (sk_F_1 @ X0 @ X1 @ sk_B_1 @ sk_C_4) @ X0) @ sk_B_1)
% 0.87/1.07          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_C_4 @ sk_B_1))
% 0.87/1.07          | ~ (v1_relat_1 @ sk_C_4))),
% 0.87/1.07      inference('sup-', [status(thm)], ['19', '21'])).
% 0.87/1.07  thf('23', plain, ((v1_relat_1 @ sk_B_1)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('24', plain, (((k5_relat_1 @ sk_C_4 @ sk_B_1) = (sk_B_1))),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('25', plain, ((v1_relat_1 @ sk_B_1)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('26', plain, ((v1_relat_1 @ sk_C_4)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('27', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i]:
% 0.87/1.07         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_B_1)
% 0.87/1.07          | (r2_hidden @ 
% 0.87/1.07             (k4_tarski @ (sk_F_1 @ X0 @ X1 @ sk_B_1 @ sk_C_4) @ X0) @ sk_B_1))),
% 0.87/1.07      inference('demod', [status(thm)], ['22', '23', '24', '25', '26'])).
% 0.87/1.07  thf('28', plain,
% 0.87/1.07      ((r2_hidden @ 
% 0.87/1.07        (k4_tarski @ 
% 0.87/1.07         (sk_F_1 @ (k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ 
% 0.87/1.07          (sk_C_3 @ sk_C_4 @ sk_A) @ sk_B_1 @ sk_C_4) @ 
% 0.87/1.07         (k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A))) @ 
% 0.87/1.07        sk_B_1)),
% 0.87/1.07      inference('sup-', [status(thm)], ['18', '27'])).
% 0.87/1.07  thf('29', plain,
% 0.87/1.07      ((r2_hidden @ 
% 0.87/1.07        (k4_tarski @ (sk_C_3 @ sk_C_4 @ sk_A) @ 
% 0.87/1.07         (k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A))) @ 
% 0.87/1.07        sk_B_1)),
% 0.87/1.07      inference('sup-', [status(thm)], ['10', '17'])).
% 0.87/1.07  thf('30', plain, (((k5_relat_1 @ sk_C_4 @ sk_B_1) = (sk_B_1))),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('31', plain,
% 0.87/1.07      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X10 : $i]:
% 0.87/1.07         (~ (v1_relat_1 @ X4)
% 0.87/1.07          | ((X6) != (k5_relat_1 @ X5 @ X4))
% 0.87/1.07          | (r2_hidden @ (k4_tarski @ X7 @ (sk_F_1 @ X10 @ X7 @ X4 @ X5)) @ X5)
% 0.87/1.07          | ~ (r2_hidden @ (k4_tarski @ X7 @ X10) @ X6)
% 0.87/1.07          | ~ (v1_relat_1 @ X6)
% 0.87/1.07          | ~ (v1_relat_1 @ X5))),
% 0.87/1.07      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.87/1.07  thf('32', plain,
% 0.87/1.07      (![X4 : $i, X5 : $i, X7 : $i, X10 : $i]:
% 0.87/1.07         (~ (v1_relat_1 @ X5)
% 0.87/1.07          | ~ (v1_relat_1 @ (k5_relat_1 @ X5 @ X4))
% 0.87/1.07          | ~ (r2_hidden @ (k4_tarski @ X7 @ X10) @ (k5_relat_1 @ X5 @ X4))
% 0.87/1.07          | (r2_hidden @ (k4_tarski @ X7 @ (sk_F_1 @ X10 @ X7 @ X4 @ X5)) @ X5)
% 0.87/1.07          | ~ (v1_relat_1 @ X4))),
% 0.87/1.07      inference('simplify', [status(thm)], ['31'])).
% 0.87/1.07  thf('33', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i]:
% 0.87/1.07         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_B_1)
% 0.87/1.07          | ~ (v1_relat_1 @ sk_B_1)
% 0.87/1.07          | (r2_hidden @ 
% 0.87/1.07             (k4_tarski @ X1 @ (sk_F_1 @ X0 @ X1 @ sk_B_1 @ sk_C_4)) @ sk_C_4)
% 0.87/1.07          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_C_4 @ sk_B_1))
% 0.87/1.07          | ~ (v1_relat_1 @ sk_C_4))),
% 0.87/1.07      inference('sup-', [status(thm)], ['30', '32'])).
% 0.87/1.07  thf('34', plain, ((v1_relat_1 @ sk_B_1)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('35', plain, (((k5_relat_1 @ sk_C_4 @ sk_B_1) = (sk_B_1))),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('36', plain, ((v1_relat_1 @ sk_B_1)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('37', plain, ((v1_relat_1 @ sk_C_4)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('38', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i]:
% 0.87/1.07         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_B_1)
% 0.87/1.07          | (r2_hidden @ 
% 0.87/1.07             (k4_tarski @ X1 @ (sk_F_1 @ X0 @ X1 @ sk_B_1 @ sk_C_4)) @ sk_C_4))),
% 0.87/1.07      inference('demod', [status(thm)], ['33', '34', '35', '36', '37'])).
% 0.87/1.07  thf('39', plain,
% 0.87/1.07      ((r2_hidden @ 
% 0.87/1.07        (k4_tarski @ (sk_C_3 @ sk_C_4 @ sk_A) @ 
% 0.87/1.07         (sk_F_1 @ (k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ 
% 0.87/1.07          (sk_C_3 @ sk_C_4 @ sk_A) @ sk_B_1 @ sk_C_4)) @ 
% 0.87/1.07        sk_C_4)),
% 0.87/1.07      inference('sup-', [status(thm)], ['29', '38'])).
% 0.87/1.07  thf('40', plain,
% 0.87/1.07      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.87/1.07         (~ (r2_hidden @ (k4_tarski @ X25 @ X27) @ X26)
% 0.87/1.07          | ((X27) = (k1_funct_1 @ X26 @ X25))
% 0.87/1.07          | ~ (v1_funct_1 @ X26)
% 0.87/1.07          | ~ (v1_relat_1 @ X26))),
% 0.87/1.07      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.87/1.07  thf('41', plain,
% 0.87/1.07      ((~ (v1_relat_1 @ sk_C_4)
% 0.87/1.07        | ~ (v1_funct_1 @ sk_C_4)
% 0.87/1.07        | ((sk_F_1 @ (k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ 
% 0.87/1.07            (sk_C_3 @ sk_C_4 @ sk_A) @ sk_B_1 @ sk_C_4)
% 0.87/1.07            = (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A))))),
% 0.87/1.07      inference('sup-', [status(thm)], ['39', '40'])).
% 0.87/1.07  thf('42', plain, ((v1_relat_1 @ sk_C_4)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('43', plain, ((v1_funct_1 @ sk_C_4)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('44', plain,
% 0.87/1.07      (((sk_F_1 @ (k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ 
% 0.87/1.07         (sk_C_3 @ sk_C_4 @ sk_A) @ sk_B_1 @ sk_C_4)
% 0.87/1.07         = (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)))),
% 0.87/1.07      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.87/1.07  thf('45', plain,
% 0.87/1.07      ((r2_hidden @ 
% 0.87/1.07        (k4_tarski @ (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ 
% 0.87/1.07         (k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A))) @ 
% 0.87/1.07        sk_B_1)),
% 0.87/1.07      inference('demod', [status(thm)], ['28', '44'])).
% 0.87/1.07  thf('46', plain,
% 0.87/1.07      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.87/1.07         (~ (r2_hidden @ (k4_tarski @ X25 @ X27) @ X26)
% 0.87/1.07          | ((X27) = (k1_funct_1 @ X26 @ X25))
% 0.87/1.07          | ~ (v1_funct_1 @ X26)
% 0.87/1.07          | ~ (v1_relat_1 @ X26))),
% 0.87/1.07      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.87/1.07  thf('47', plain,
% 0.87/1.07      ((~ (v1_relat_1 @ sk_B_1)
% 0.87/1.07        | ~ (v1_funct_1 @ sk_B_1)
% 0.87/1.07        | ((k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 0.87/1.07            = (k1_funct_1 @ sk_B_1 @ 
% 0.87/1.07               (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)))))),
% 0.87/1.07      inference('sup-', [status(thm)], ['45', '46'])).
% 0.87/1.07  thf('48', plain, ((v1_relat_1 @ sk_B_1)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('49', plain, ((v1_funct_1 @ sk_B_1)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('50', plain,
% 0.87/1.07      (((k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 0.87/1.07         = (k1_funct_1 @ sk_B_1 @ 
% 0.87/1.07            (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A))))),
% 0.87/1.07      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.87/1.07  thf('51', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf(d8_funct_1, axiom,
% 0.87/1.07    (![A:$i]:
% 0.87/1.07     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.87/1.07       ( ( v2_funct_1 @ A ) <=>
% 0.87/1.07         ( ![B:$i,C:$i]:
% 0.87/1.07           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.87/1.07               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.87/1.07               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.87/1.07             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.87/1.07  thf('52', plain,
% 0.87/1.07      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.87/1.07         (~ (v2_funct_1 @ X19)
% 0.87/1.07          | ~ (r2_hidden @ X20 @ (k1_relat_1 @ X19))
% 0.87/1.07          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X19))
% 0.87/1.07          | ((k1_funct_1 @ X19 @ X20) != (k1_funct_1 @ X19 @ X21))
% 0.87/1.07          | ((X20) = (X21))
% 0.87/1.07          | ~ (v1_funct_1 @ X19)
% 0.87/1.07          | ~ (v1_relat_1 @ X19))),
% 0.87/1.07      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.87/1.07  thf('53', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i]:
% 0.87/1.07         (~ (r2_hidden @ X0 @ sk_A)
% 0.87/1.07          | ~ (v1_relat_1 @ sk_B_1)
% 0.87/1.07          | ~ (v1_funct_1 @ sk_B_1)
% 0.87/1.07          | ((X0) = (X1))
% 0.87/1.07          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.87/1.07          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1))
% 0.87/1.07          | ~ (v2_funct_1 @ sk_B_1))),
% 0.87/1.07      inference('sup-', [status(thm)], ['51', '52'])).
% 0.87/1.07  thf('54', plain, ((v1_relat_1 @ sk_B_1)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('55', plain, ((v1_funct_1 @ sk_B_1)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('56', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('57', plain, ((v2_funct_1 @ sk_B_1)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('58', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i]:
% 0.87/1.07         (~ (r2_hidden @ X0 @ sk_A)
% 0.87/1.07          | ((X0) = (X1))
% 0.87/1.07          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.87/1.07          | ~ (r2_hidden @ X1 @ sk_A))),
% 0.87/1.07      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 0.87/1.07  thf('59', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         (((k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 0.87/1.07            != (k1_funct_1 @ sk_B_1 @ X0))
% 0.87/1.07          | ~ (r2_hidden @ X0 @ sk_A)
% 0.87/1.07          | ((k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) = (X0))
% 0.87/1.07          | ~ (r2_hidden @ (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ 
% 0.87/1.07               sk_A))),
% 0.87/1.07      inference('sup-', [status(thm)], ['50', '58'])).
% 0.87/1.07  thf('60', plain,
% 0.87/1.07      (![X23 : $i]:
% 0.87/1.07         (~ (v1_relat_1 @ X23)
% 0.87/1.07          | ~ (v1_funct_1 @ X23)
% 0.87/1.07          | ((X23) = (k6_relat_1 @ (k1_relat_1 @ X23)))
% 0.87/1.07          | (r2_hidden @ (sk_C_3 @ X23 @ (k1_relat_1 @ X23)) @ 
% 0.87/1.07             (k1_relat_1 @ X23)))),
% 0.87/1.07      inference('simplify', [status(thm)], ['1'])).
% 0.87/1.07  thf(d5_funct_1, axiom,
% 0.87/1.07    (![A:$i]:
% 0.87/1.07     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.87/1.07       ( ![B:$i]:
% 0.87/1.07         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.87/1.07           ( ![C:$i]:
% 0.87/1.07             ( ( r2_hidden @ C @ B ) <=>
% 0.87/1.07               ( ?[D:$i]:
% 0.87/1.07                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.87/1.07                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.87/1.07  thf('61', plain,
% 0.87/1.07      (![X13 : $i, X15 : $i, X17 : $i, X18 : $i]:
% 0.87/1.07         (((X15) != (k2_relat_1 @ X13))
% 0.87/1.07          | (r2_hidden @ X17 @ X15)
% 0.87/1.07          | ~ (r2_hidden @ X18 @ (k1_relat_1 @ X13))
% 0.87/1.07          | ((X17) != (k1_funct_1 @ X13 @ X18))
% 0.87/1.07          | ~ (v1_funct_1 @ X13)
% 0.87/1.07          | ~ (v1_relat_1 @ X13))),
% 0.87/1.07      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.87/1.07  thf('62', plain,
% 0.87/1.07      (![X13 : $i, X18 : $i]:
% 0.87/1.07         (~ (v1_relat_1 @ X13)
% 0.87/1.07          | ~ (v1_funct_1 @ X13)
% 0.87/1.07          | ~ (r2_hidden @ X18 @ (k1_relat_1 @ X13))
% 0.87/1.07          | (r2_hidden @ (k1_funct_1 @ X13 @ X18) @ (k2_relat_1 @ X13)))),
% 0.87/1.07      inference('simplify', [status(thm)], ['61'])).
% 0.87/1.07  thf('63', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         (((X0) = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.87/1.07          | ~ (v1_funct_1 @ X0)
% 0.87/1.07          | ~ (v1_relat_1 @ X0)
% 0.87/1.07          | (r2_hidden @ 
% 0.87/1.07             (k1_funct_1 @ X0 @ (sk_C_3 @ X0 @ (k1_relat_1 @ X0))) @ 
% 0.87/1.07             (k2_relat_1 @ X0))
% 0.87/1.07          | ~ (v1_funct_1 @ X0)
% 0.87/1.07          | ~ (v1_relat_1 @ X0))),
% 0.87/1.07      inference('sup-', [status(thm)], ['60', '62'])).
% 0.87/1.07  thf('64', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         ((r2_hidden @ (k1_funct_1 @ X0 @ (sk_C_3 @ X0 @ (k1_relat_1 @ X0))) @ 
% 0.87/1.07           (k2_relat_1 @ X0))
% 0.87/1.07          | ~ (v1_relat_1 @ X0)
% 0.87/1.07          | ~ (v1_funct_1 @ X0)
% 0.87/1.07          | ((X0) = (k6_relat_1 @ (k1_relat_1 @ X0))))),
% 0.87/1.07      inference('simplify', [status(thm)], ['63'])).
% 0.87/1.07  thf('65', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_4) @ sk_A)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf(d3_tarski, axiom,
% 0.87/1.07    (![A:$i,B:$i]:
% 0.87/1.07     ( ( r1_tarski @ A @ B ) <=>
% 0.87/1.07       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.87/1.07  thf('66', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.87/1.07         (~ (r2_hidden @ X0 @ X1)
% 0.87/1.07          | (r2_hidden @ X0 @ X2)
% 0.87/1.07          | ~ (r1_tarski @ X1 @ X2))),
% 0.87/1.07      inference('cnf', [status(esa)], [d3_tarski])).
% 0.87/1.07  thf('67', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_4)))),
% 0.87/1.07      inference('sup-', [status(thm)], ['65', '66'])).
% 0.87/1.07  thf('68', plain,
% 0.87/1.07      ((((sk_C_4) = (k6_relat_1 @ (k1_relat_1 @ sk_C_4)))
% 0.87/1.07        | ~ (v1_funct_1 @ sk_C_4)
% 0.87/1.07        | ~ (v1_relat_1 @ sk_C_4)
% 0.87/1.07        | (r2_hidden @ 
% 0.87/1.07           (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ (k1_relat_1 @ sk_C_4))) @ 
% 0.87/1.07           sk_A))),
% 0.87/1.07      inference('sup-', [status(thm)], ['64', '67'])).
% 0.87/1.07  thf('69', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('70', plain, ((v1_funct_1 @ sk_C_4)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('71', plain, ((v1_relat_1 @ sk_C_4)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('72', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('73', plain,
% 0.87/1.07      ((((sk_C_4) = (k6_relat_1 @ sk_A))
% 0.87/1.07        | (r2_hidden @ (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ sk_A))),
% 0.87/1.07      inference('demod', [status(thm)], ['68', '69', '70', '71', '72'])).
% 0.87/1.07  thf('74', plain, (((sk_C_4) != (k6_relat_1 @ sk_A))),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('75', plain,
% 0.87/1.07      ((r2_hidden @ (k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) @ sk_A)),
% 0.87/1.07      inference('simplify_reflect-', [status(thm)], ['73', '74'])).
% 0.87/1.07  thf('76', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         (((k1_funct_1 @ sk_B_1 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 0.87/1.07            != (k1_funct_1 @ sk_B_1 @ X0))
% 0.87/1.07          | ~ (r2_hidden @ X0 @ sk_A)
% 0.87/1.07          | ((k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A)) = (X0)))),
% 0.87/1.07      inference('demod', [status(thm)], ['59', '75'])).
% 0.87/1.07  thf('77', plain,
% 0.87/1.07      ((((k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 0.87/1.07          = (sk_C_3 @ sk_C_4 @ sk_A))
% 0.87/1.07        | ~ (r2_hidden @ (sk_C_3 @ sk_C_4 @ sk_A) @ sk_A))),
% 0.87/1.07      inference('eq_res', [status(thm)], ['76'])).
% 0.87/1.07  thf('78', plain, ((r2_hidden @ (sk_C_3 @ sk_C_4 @ sk_A) @ sk_A)),
% 0.87/1.07      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.87/1.07  thf('79', plain,
% 0.87/1.07      (((k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 0.87/1.07         = (sk_C_3 @ sk_C_4 @ sk_A))),
% 0.87/1.07      inference('demod', [status(thm)], ['77', '78'])).
% 0.87/1.07  thf('80', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('81', plain,
% 0.87/1.07      (![X22 : $i, X23 : $i]:
% 0.87/1.07         (((k1_relat_1 @ X23) != (X22))
% 0.87/1.07          | ((k1_funct_1 @ X23 @ (sk_C_3 @ X23 @ X22)) != (sk_C_3 @ X23 @ X22))
% 0.87/1.07          | ((X23) = (k6_relat_1 @ X22))
% 0.87/1.07          | ~ (v1_funct_1 @ X23)
% 0.87/1.07          | ~ (v1_relat_1 @ X23))),
% 0.87/1.07      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.87/1.07  thf('82', plain,
% 0.87/1.07      (![X23 : $i]:
% 0.87/1.07         (~ (v1_relat_1 @ X23)
% 0.87/1.07          | ~ (v1_funct_1 @ X23)
% 0.87/1.07          | ((X23) = (k6_relat_1 @ (k1_relat_1 @ X23)))
% 0.87/1.07          | ((k1_funct_1 @ X23 @ (sk_C_3 @ X23 @ (k1_relat_1 @ X23)))
% 0.87/1.07              != (sk_C_3 @ X23 @ (k1_relat_1 @ X23))))),
% 0.87/1.07      inference('simplify', [status(thm)], ['81'])).
% 0.87/1.07  thf('83', plain,
% 0.87/1.07      ((((k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 0.87/1.07          != (sk_C_3 @ sk_C_4 @ (k1_relat_1 @ sk_C_4)))
% 0.87/1.07        | ((sk_C_4) = (k6_relat_1 @ (k1_relat_1 @ sk_C_4)))
% 0.87/1.07        | ~ (v1_funct_1 @ sk_C_4)
% 0.87/1.07        | ~ (v1_relat_1 @ sk_C_4))),
% 0.87/1.07      inference('sup-', [status(thm)], ['80', '82'])).
% 0.87/1.07  thf('84', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('85', plain, (((k1_relat_1 @ sk_C_4) = (sk_A))),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('86', plain, ((v1_funct_1 @ sk_C_4)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('87', plain, ((v1_relat_1 @ sk_C_4)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('88', plain,
% 0.87/1.07      ((((k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 0.87/1.07          != (sk_C_3 @ sk_C_4 @ sk_A))
% 0.87/1.07        | ((sk_C_4) = (k6_relat_1 @ sk_A)))),
% 0.87/1.07      inference('demod', [status(thm)], ['83', '84', '85', '86', '87'])).
% 0.87/1.07  thf('89', plain, (((sk_C_4) != (k6_relat_1 @ sk_A))),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('90', plain,
% 0.87/1.07      (((k1_funct_1 @ sk_C_4 @ (sk_C_3 @ sk_C_4 @ sk_A))
% 0.87/1.07         != (sk_C_3 @ sk_C_4 @ sk_A))),
% 0.87/1.07      inference('simplify_reflect-', [status(thm)], ['88', '89'])).
% 0.87/1.07  thf('91', plain, ($false),
% 0.87/1.07      inference('simplify_reflect-', [status(thm)], ['79', '90'])).
% 0.87/1.07  
% 0.87/1.07  % SZS output end Refutation
% 0.87/1.07  
% 0.92/1.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
