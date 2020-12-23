%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FQ3z42yJUU

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:34 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 335 expanded)
%              Number of leaves         :   20 ( 100 expanded)
%              Depth                    :   23
%              Number of atoms          : 1241 (5061 expanded)
%              Number of equality atoms :   48 ( 503 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t17_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( ( ( k1_relat_1 @ B )
                = ( k1_relat_1 @ C ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_tarski @ A ) )
              & ( ( k2_relat_1 @ C )
                = ( k1_tarski @ A ) ) )
           => ( B = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ( ( ( ( k1_relat_1 @ B )
                  = ( k1_relat_1 @ C ) )
                & ( ( k2_relat_1 @ B )
                  = ( k1_tarski @ A ) )
                & ( ( k2_relat_1 @ C )
                  = ( k1_tarski @ A ) ) )
             => ( B = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_funct_1])).

thf('0',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X14 @ X15 ) @ ( sk_D @ X14 @ X15 ) ) @ X15 )
      | ( r1_tarski @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X26 @ X28 ) @ X27 )
      | ( r2_hidden @ X26 @ ( k1_relat_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_3 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_C_3 )
      | ( r1_tarski @ sk_C_3 @ X0 )
      | ~ ( v1_funct_1 @ sk_C_3 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_3 ) @ ( k1_relat_1 @ sk_B ) )
      | ( r1_tarski @ sk_C_3 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

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
    ! [X20: $i,X22: $i,X24: $i,X25: $i] :
      ( ( X22
       != ( k2_relat_1 @ X20 ) )
      | ( r2_hidden @ X24 @ X22 )
      | ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X20 ) )
      | ( X24
       != ( k1_funct_1 @ X20 @ X25 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('10',plain,(
    ! [X20: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X20 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X20 @ X25 ) @ ( k2_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C_1 @ X0 @ sk_C_3 ) ) @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C_1 @ X0 @ sk_C_3 ) ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('16',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( X6 = X3 )
      | ( X5
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('17',plain,(
    ! [X3: $i,X6: $i] :
      ( ( X6 = X3 )
      | ~ ( r2_hidden @ X6 @ ( k1_tarski @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ X0 @ sk_C_3 ) )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_3 ) @ ( k1_relat_1 @ sk_B ) )
      | ( r1_tarski @ sk_C_3 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('21',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X26 @ ( k1_relat_1 @ X27 ) )
      | ( X28
       != ( k1_funct_1 @ X27 @ X26 ) )
      | ( r2_hidden @ ( k4_tarski @ X26 @ X28 ) @ X27 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('22',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ~ ( v1_funct_1 @ X27 )
      | ( r2_hidden @ ( k4_tarski @ X26 @ ( k1_funct_1 @ X27 @ X26 ) ) @ X27 )
      | ~ ( r2_hidden @ X26 @ ( k1_relat_1 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_3 ) @ ( k1_funct_1 @ sk_B @ ( sk_C_1 @ X0 @ sk_C_3 ) ) ) @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_3 ) @ ( k1_funct_1 @ sk_B @ ( sk_C_1 @ X0 @ sk_C_3 ) ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_3 ) @ sk_A ) @ sk_B )
      | ( r1_tarski @ sk_C_3 @ X0 )
      | ( r1_tarski @ sk_C_3 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_3 ) @ sk_A ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X14 @ X15 ) @ ( sk_D @ X14 @ X15 ) ) @ X15 )
      | ( r1_tarski @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('30',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X26 @ X28 ) @ X27 )
      | ( X28
        = ( k1_funct_1 @ X27 @ X26 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_D @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_3 ) @ ( k1_relat_1 @ sk_B ) )
      | ( r1_tarski @ sk_C_3 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('34',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ~ ( v1_funct_1 @ X27 )
      | ( r2_hidden @ ( k4_tarski @ X26 @ ( k1_funct_1 @ X27 @ X26 ) ) @ X27 )
      | ~ ( r2_hidden @ X26 @ ( k1_relat_1 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C_3 @ X0 ) ) @ sk_C_3 )
      | ~ ( v1_funct_1 @ sk_C_3 )
      | ~ ( v1_relat_1 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C_3 @ X0 ) ) @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_3 ) @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_1 @ X0 @ sk_C_3 ) ) ) @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_3 ) @ ( sk_D @ X0 @ sk_C_3 ) ) @ sk_C_3 )
      | ~ ( v1_relat_1 @ sk_C_3 )
      | ( r1_tarski @ sk_C_3 @ X0 )
      | ~ ( v1_funct_1 @ sk_C_3 )
      | ( r1_tarski @ sk_C_3 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_3 ) @ ( sk_D @ X0 @ sk_C_3 ) ) @ sk_C_3 )
      | ( r1_tarski @ sk_C_3 @ X0 )
      | ( r1_tarski @ sk_C_3 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_3 ) @ ( sk_D @ X0 @ sk_C_3 ) ) @ sk_C_3 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X26 @ X28 ) @ X27 )
      | ( X28
        = ( k1_funct_1 @ X27 @ X26 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ~ ( v1_relat_1 @ sk_C_3 )
      | ~ ( v1_funct_1 @ sk_C_3 )
      | ( ( sk_D @ X0 @ sk_C_3 )
        = ( k1_funct_1 @ sk_C_3 @ ( sk_C_1 @ X0 @ sk_C_3 ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ( ( sk_D @ X0 @ sk_C_3 )
        = ( k1_funct_1 @ sk_C_3 @ ( sk_C_1 @ X0 @ sk_C_3 ) ) ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('52',plain,(
    ! [X20: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X20 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X20 @ X25 ) @ ( k2_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_C_3 ) @ ( k2_relat_1 @ sk_C_3 ) )
      | ( r1_tarski @ sk_C_3 @ X0 )
      | ~ ( v1_relat_1 @ sk_C_3 )
      | ( r1_tarski @ sk_C_3 @ X0 )
      | ~ ( v1_funct_1 @ sk_C_3 ) ) ),
    inference('sup+',[status(thm)],['50','54'])).

thf('56',plain,
    ( ( k2_relat_1 @ sk_C_3 )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k2_relat_1 @ sk_C_3 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_C_3 ) @ ( k2_relat_1 @ sk_B ) )
      | ( r1_tarski @ sk_C_3 @ X0 )
      | ( r1_tarski @ sk_C_3 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','58','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_C_3 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ( ( sk_D @ X0 @ sk_C_3 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X14 @ X15 ) @ ( sk_D @ X14 @ X15 ) ) @ X14 )
      | ( r1_tarski @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_3 ) @ sk_A ) @ X0 )
      | ( r1_tarski @ sk_C_3 @ X0 )
      | ~ ( v1_relat_1 @ sk_C_3 )
      | ( r1_tarski @ sk_C_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_3 ) @ sk_A ) @ X0 )
      | ( r1_tarski @ sk_C_3 @ X0 )
      | ( r1_tarski @ sk_C_3 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_3 ) @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( r1_tarski @ sk_C_3 @ sk_B )
    | ( r1_tarski @ sk_C_3 @ sk_B ) ),
    inference('sup-',[status(thm)],['28','69'])).

thf('71',plain,(
    r1_tarski @ sk_C_3 @ sk_B ),
    inference(simplify,[status(thm)],['70'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('72',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('73',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_3 )
    | ( sk_B = sk_C_3 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    sk_B != sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C_3 ) ),
    inference('simplify_reflect-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C_3 @ X0 ) ) @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ sk_B @ X0 )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_B ) @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_1 @ X0 @ sk_B ) ) ) @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_B ) @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_1 @ X0 @ sk_B ) ) ) @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X26 @ X28 ) @ X27 )
      | ( r2_hidden @ X26 @ ( k1_relat_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( v1_relat_1 @ sk_C_3 )
      | ~ ( v1_funct_1 @ sk_C_3 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['83','84','85','86'])).

thf('88',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X20: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X20 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X20 @ X25 ) @ ( k2_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_3 @ X0 ) @ ( k2_relat_1 @ sk_C_3 ) )
      | ~ ( v1_funct_1 @ sk_C_3 )
      | ~ ( v1_relat_1 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k2_relat_1 @ sk_C_3 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('92',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_3 @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['90','91','92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_1 @ X0 @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['87','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( k1_funct_1 @ sk_C_3 @ ( sk_C_1 @ X0 @ sk_B ) )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_B ) @ ( k1_funct_1 @ sk_C_3 @ ( sk_C_1 @ X0 @ sk_B ) ) ) @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_B ) @ sk_A ) @ sk_C_3 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_B ) @ sk_A ) @ sk_C_3 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ sk_B @ X0 )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( sk_D @ X0 @ sk_B )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( sk_D @ X0 @ sk_B )
        = sk_A ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X14 @ X15 ) @ ( sk_D @ X14 @ X15 ) ) @ X14 )
      | ( r1_tarski @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_B ) @ sk_A ) @ X0 )
      | ( r1_tarski @ sk_B @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_B ) @ sk_A ) @ X0 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ( r1_tarski @ sk_B @ sk_C_3 )
    | ( r1_tarski @ sk_B @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['100','114'])).

thf('116',plain,(
    r1_tarski @ sk_B @ sk_C_3 ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    $false ),
    inference(demod,[status(thm)],['75','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FQ3z42yJUU
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:27:03 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.63  % Solved by: fo/fo7.sh
% 0.46/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.63  % done 331 iterations in 0.178s
% 0.46/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.63  % SZS output start Refutation
% 0.46/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.63  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.46/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.63  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.46/0.63  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.46/0.63  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.46/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.63  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.46/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.63  thf(t17_funct_1, conjecture,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.63       ( ![C:$i]:
% 0.46/0.63         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.63           ( ( ( ( k1_relat_1 @ B ) = ( k1_relat_1 @ C ) ) & 
% 0.46/0.63               ( ( k2_relat_1 @ B ) = ( k1_tarski @ A ) ) & 
% 0.46/0.63               ( ( k2_relat_1 @ C ) = ( k1_tarski @ A ) ) ) =>
% 0.46/0.63             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.63    (~( ![A:$i,B:$i]:
% 0.46/0.63        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.63          ( ![C:$i]:
% 0.46/0.63            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.63              ( ( ( ( k1_relat_1 @ B ) = ( k1_relat_1 @ C ) ) & 
% 0.46/0.63                  ( ( k2_relat_1 @ B ) = ( k1_tarski @ A ) ) & 
% 0.46/0.63                  ( ( k2_relat_1 @ C ) = ( k1_tarski @ A ) ) ) =>
% 0.46/0.63                ( ( B ) = ( C ) ) ) ) ) ) )),
% 0.46/0.63    inference('cnf.neg', [status(esa)], [t17_funct_1])).
% 0.46/0.63  thf('0', plain, (((k1_relat_1 @ sk_B) = (k1_relat_1 @ sk_C_3))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(d3_relat_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( v1_relat_1 @ A ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( r1_tarski @ A @ B ) <=>
% 0.46/0.63           ( ![C:$i,D:$i]:
% 0.46/0.63             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.46/0.63               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.46/0.63  thf('1', plain,
% 0.46/0.63      (![X14 : $i, X15 : $i]:
% 0.46/0.63         ((r2_hidden @ 
% 0.46/0.63           (k4_tarski @ (sk_C_1 @ X14 @ X15) @ (sk_D @ X14 @ X15)) @ X15)
% 0.46/0.63          | (r1_tarski @ X15 @ X14)
% 0.46/0.63          | ~ (v1_relat_1 @ X15))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.46/0.63  thf(t8_funct_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.63       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.46/0.63         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.46/0.63           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.46/0.63  thf('2', plain,
% 0.46/0.63      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.63         (~ (r2_hidden @ (k4_tarski @ X26 @ X28) @ X27)
% 0.46/0.63          | (r2_hidden @ X26 @ (k1_relat_1 @ X27))
% 0.46/0.63          | ~ (v1_funct_1 @ X27)
% 0.46/0.63          | ~ (v1_relat_1 @ X27))),
% 0.46/0.63      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.46/0.63  thf('3', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X0)
% 0.46/0.63          | (r1_tarski @ X0 @ X1)
% 0.46/0.63          | ~ (v1_relat_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.63  thf('4', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k1_relat_1 @ X0))
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | (r1_tarski @ X0 @ X1)
% 0.46/0.63          | ~ (v1_relat_1 @ X0))),
% 0.46/0.63      inference('simplify', [status(thm)], ['3'])).
% 0.46/0.63  thf('5', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((r2_hidden @ (sk_C_1 @ X0 @ sk_C_3) @ (k1_relat_1 @ sk_B))
% 0.46/0.63          | ~ (v1_relat_1 @ sk_C_3)
% 0.46/0.63          | (r1_tarski @ sk_C_3 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ sk_C_3))),
% 0.46/0.63      inference('sup+', [status(thm)], ['0', '4'])).
% 0.46/0.63  thf('6', plain, ((v1_relat_1 @ sk_C_3)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('7', plain, ((v1_funct_1 @ sk_C_3)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('8', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((r2_hidden @ (sk_C_1 @ X0 @ sk_C_3) @ (k1_relat_1 @ sk_B))
% 0.46/0.63          | (r1_tarski @ sk_C_3 @ X0))),
% 0.46/0.63      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.46/0.63  thf(d5_funct_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.46/0.63           ( ![C:$i]:
% 0.46/0.63             ( ( r2_hidden @ C @ B ) <=>
% 0.46/0.63               ( ?[D:$i]:
% 0.46/0.63                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.46/0.63                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.46/0.63  thf('9', plain,
% 0.46/0.63      (![X20 : $i, X22 : $i, X24 : $i, X25 : $i]:
% 0.46/0.63         (((X22) != (k2_relat_1 @ X20))
% 0.46/0.63          | (r2_hidden @ X24 @ X22)
% 0.46/0.63          | ~ (r2_hidden @ X25 @ (k1_relat_1 @ X20))
% 0.46/0.63          | ((X24) != (k1_funct_1 @ X20 @ X25))
% 0.46/0.63          | ~ (v1_funct_1 @ X20)
% 0.46/0.63          | ~ (v1_relat_1 @ X20))),
% 0.46/0.63      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.46/0.63  thf('10', plain,
% 0.46/0.63      (![X20 : $i, X25 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X20)
% 0.46/0.63          | ~ (v1_funct_1 @ X20)
% 0.46/0.63          | ~ (r2_hidden @ X25 @ (k1_relat_1 @ X20))
% 0.46/0.63          | (r2_hidden @ (k1_funct_1 @ X20 @ X25) @ (k2_relat_1 @ X20)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['9'])).
% 0.47/0.63  thf('11', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((r1_tarski @ sk_C_3 @ X0)
% 0.47/0.63          | (r2_hidden @ (k1_funct_1 @ sk_B @ (sk_C_1 @ X0 @ sk_C_3)) @ 
% 0.47/0.63             (k2_relat_1 @ sk_B))
% 0.47/0.63          | ~ (v1_funct_1 @ sk_B)
% 0.47/0.63          | ~ (v1_relat_1 @ sk_B))),
% 0.47/0.63      inference('sup-', [status(thm)], ['8', '10'])).
% 0.47/0.63  thf('12', plain, ((v1_funct_1 @ sk_B)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('13', plain, ((v1_relat_1 @ sk_B)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('14', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((r1_tarski @ sk_C_3 @ X0)
% 0.47/0.63          | (r2_hidden @ (k1_funct_1 @ sk_B @ (sk_C_1 @ X0 @ sk_C_3)) @ 
% 0.47/0.63             (k2_relat_1 @ sk_B)))),
% 0.47/0.63      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.47/0.63  thf('15', plain, (((k2_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf(d1_tarski, axiom,
% 0.47/0.63    (![A:$i,B:$i]:
% 0.47/0.63     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.47/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.47/0.63  thf('16', plain,
% 0.47/0.63      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.47/0.63         (~ (r2_hidden @ X6 @ X5) | ((X6) = (X3)) | ((X5) != (k1_tarski @ X3)))),
% 0.47/0.63      inference('cnf', [status(esa)], [d1_tarski])).
% 0.47/0.63  thf('17', plain,
% 0.47/0.63      (![X3 : $i, X6 : $i]:
% 0.47/0.63         (((X6) = (X3)) | ~ (r2_hidden @ X6 @ (k1_tarski @ X3)))),
% 0.47/0.63      inference('simplify', [status(thm)], ['16'])).
% 0.47/0.63  thf('18', plain,
% 0.47/0.63      (![X0 : $i]: (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B)) | ((X0) = (sk_A)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['15', '17'])).
% 0.47/0.63  thf('19', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((r1_tarski @ sk_C_3 @ X0)
% 0.47/0.63          | ((k1_funct_1 @ sk_B @ (sk_C_1 @ X0 @ sk_C_3)) = (sk_A)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['14', '18'])).
% 0.47/0.63  thf('20', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((r2_hidden @ (sk_C_1 @ X0 @ sk_C_3) @ (k1_relat_1 @ sk_B))
% 0.47/0.63          | (r1_tarski @ sk_C_3 @ X0))),
% 0.47/0.63      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.47/0.63  thf('21', plain,
% 0.47/0.63      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.47/0.63         (~ (r2_hidden @ X26 @ (k1_relat_1 @ X27))
% 0.47/0.63          | ((X28) != (k1_funct_1 @ X27 @ X26))
% 0.47/0.63          | (r2_hidden @ (k4_tarski @ X26 @ X28) @ X27)
% 0.47/0.63          | ~ (v1_funct_1 @ X27)
% 0.47/0.63          | ~ (v1_relat_1 @ X27))),
% 0.47/0.63      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.47/0.63  thf('22', plain,
% 0.47/0.63      (![X26 : $i, X27 : $i]:
% 0.47/0.63         (~ (v1_relat_1 @ X27)
% 0.47/0.63          | ~ (v1_funct_1 @ X27)
% 0.47/0.63          | (r2_hidden @ (k4_tarski @ X26 @ (k1_funct_1 @ X27 @ X26)) @ X27)
% 0.47/0.63          | ~ (r2_hidden @ X26 @ (k1_relat_1 @ X27)))),
% 0.47/0.63      inference('simplify', [status(thm)], ['21'])).
% 0.47/0.63  thf('23', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((r1_tarski @ sk_C_3 @ X0)
% 0.47/0.63          | (r2_hidden @ 
% 0.47/0.63             (k4_tarski @ (sk_C_1 @ X0 @ sk_C_3) @ 
% 0.47/0.63              (k1_funct_1 @ sk_B @ (sk_C_1 @ X0 @ sk_C_3))) @ 
% 0.47/0.63             sk_B)
% 0.47/0.63          | ~ (v1_funct_1 @ sk_B)
% 0.47/0.63          | ~ (v1_relat_1 @ sk_B))),
% 0.47/0.63      inference('sup-', [status(thm)], ['20', '22'])).
% 0.47/0.63  thf('24', plain, ((v1_funct_1 @ sk_B)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('26', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((r1_tarski @ sk_C_3 @ X0)
% 0.47/0.63          | (r2_hidden @ 
% 0.47/0.63             (k4_tarski @ (sk_C_1 @ X0 @ sk_C_3) @ 
% 0.47/0.63              (k1_funct_1 @ sk_B @ (sk_C_1 @ X0 @ sk_C_3))) @ 
% 0.47/0.63             sk_B))),
% 0.47/0.63      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.47/0.63  thf('27', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((r2_hidden @ (k4_tarski @ (sk_C_1 @ X0 @ sk_C_3) @ sk_A) @ sk_B)
% 0.47/0.63          | (r1_tarski @ sk_C_3 @ X0)
% 0.47/0.63          | (r1_tarski @ sk_C_3 @ X0))),
% 0.47/0.63      inference('sup+', [status(thm)], ['19', '26'])).
% 0.47/0.63  thf('28', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((r1_tarski @ sk_C_3 @ X0)
% 0.47/0.63          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X0 @ sk_C_3) @ sk_A) @ sk_B))),
% 0.47/0.63      inference('simplify', [status(thm)], ['27'])).
% 0.47/0.63  thf('29', plain,
% 0.47/0.63      (![X14 : $i, X15 : $i]:
% 0.47/0.63         ((r2_hidden @ 
% 0.47/0.63           (k4_tarski @ (sk_C_1 @ X14 @ X15) @ (sk_D @ X14 @ X15)) @ X15)
% 0.47/0.63          | (r1_tarski @ X15 @ X14)
% 0.47/0.63          | ~ (v1_relat_1 @ X15))),
% 0.47/0.63      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.47/0.63  thf('30', plain,
% 0.47/0.63      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.47/0.63         (~ (r2_hidden @ (k4_tarski @ X26 @ X28) @ X27)
% 0.47/0.63          | ((X28) = (k1_funct_1 @ X27 @ X26))
% 0.47/0.63          | ~ (v1_funct_1 @ X27)
% 0.47/0.63          | ~ (v1_relat_1 @ X27))),
% 0.47/0.63      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.47/0.63  thf('31', plain,
% 0.47/0.63      (![X0 : $i, X1 : $i]:
% 0.47/0.63         (~ (v1_relat_1 @ X0)
% 0.47/0.63          | (r1_tarski @ X0 @ X1)
% 0.47/0.63          | ~ (v1_relat_1 @ X0)
% 0.47/0.63          | ~ (v1_funct_1 @ X0)
% 0.47/0.63          | ((sk_D @ X1 @ X0) = (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['29', '30'])).
% 0.47/0.63  thf('32', plain,
% 0.47/0.63      (![X0 : $i, X1 : $i]:
% 0.47/0.63         (((sk_D @ X1 @ X0) = (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)))
% 0.47/0.63          | ~ (v1_funct_1 @ X0)
% 0.47/0.63          | (r1_tarski @ X0 @ X1)
% 0.47/0.63          | ~ (v1_relat_1 @ X0))),
% 0.47/0.63      inference('simplify', [status(thm)], ['31'])).
% 0.47/0.63  thf('33', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((r2_hidden @ (sk_C_1 @ X0 @ sk_C_3) @ (k1_relat_1 @ sk_B))
% 0.47/0.63          | (r1_tarski @ sk_C_3 @ X0))),
% 0.47/0.63      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.47/0.63  thf('34', plain, (((k1_relat_1 @ sk_B) = (k1_relat_1 @ sk_C_3))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('35', plain,
% 0.47/0.63      (![X26 : $i, X27 : $i]:
% 0.47/0.63         (~ (v1_relat_1 @ X27)
% 0.47/0.63          | ~ (v1_funct_1 @ X27)
% 0.47/0.63          | (r2_hidden @ (k4_tarski @ X26 @ (k1_funct_1 @ X27 @ X26)) @ X27)
% 0.47/0.63          | ~ (r2_hidden @ X26 @ (k1_relat_1 @ X27)))),
% 0.47/0.63      inference('simplify', [status(thm)], ['21'])).
% 0.47/0.63  thf('36', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.47/0.63          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C_3 @ X0)) @ sk_C_3)
% 0.47/0.63          | ~ (v1_funct_1 @ sk_C_3)
% 0.47/0.63          | ~ (v1_relat_1 @ sk_C_3))),
% 0.47/0.63      inference('sup-', [status(thm)], ['34', '35'])).
% 0.47/0.63  thf('37', plain, ((v1_funct_1 @ sk_C_3)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('38', plain, ((v1_relat_1 @ sk_C_3)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('39', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.47/0.63          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C_3 @ X0)) @ sk_C_3))),
% 0.47/0.63      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.47/0.63  thf('40', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((r1_tarski @ sk_C_3 @ X0)
% 0.47/0.64          | (r2_hidden @ 
% 0.47/0.64             (k4_tarski @ (sk_C_1 @ X0 @ sk_C_3) @ 
% 0.47/0.64              (k1_funct_1 @ sk_C_3 @ (sk_C_1 @ X0 @ sk_C_3))) @ 
% 0.47/0.64             sk_C_3))),
% 0.47/0.64      inference('sup-', [status(thm)], ['33', '39'])).
% 0.47/0.64  thf('41', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((r2_hidden @ 
% 0.47/0.64           (k4_tarski @ (sk_C_1 @ X0 @ sk_C_3) @ (sk_D @ X0 @ sk_C_3)) @ sk_C_3)
% 0.47/0.64          | ~ (v1_relat_1 @ sk_C_3)
% 0.47/0.64          | (r1_tarski @ sk_C_3 @ X0)
% 0.47/0.64          | ~ (v1_funct_1 @ sk_C_3)
% 0.47/0.64          | (r1_tarski @ sk_C_3 @ X0))),
% 0.47/0.64      inference('sup+', [status(thm)], ['32', '40'])).
% 0.47/0.64  thf('42', plain, ((v1_relat_1 @ sk_C_3)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('43', plain, ((v1_funct_1 @ sk_C_3)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('44', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((r2_hidden @ 
% 0.47/0.64           (k4_tarski @ (sk_C_1 @ X0 @ sk_C_3) @ (sk_D @ X0 @ sk_C_3)) @ sk_C_3)
% 0.47/0.64          | (r1_tarski @ sk_C_3 @ X0)
% 0.47/0.64          | (r1_tarski @ sk_C_3 @ X0))),
% 0.47/0.64      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.47/0.64  thf('45', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((r1_tarski @ sk_C_3 @ X0)
% 0.47/0.64          | (r2_hidden @ 
% 0.47/0.64             (k4_tarski @ (sk_C_1 @ X0 @ sk_C_3) @ (sk_D @ X0 @ sk_C_3)) @ 
% 0.47/0.64             sk_C_3))),
% 0.47/0.64      inference('simplify', [status(thm)], ['44'])).
% 0.47/0.64  thf('46', plain,
% 0.47/0.64      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.47/0.64         (~ (r2_hidden @ (k4_tarski @ X26 @ X28) @ X27)
% 0.47/0.64          | ((X28) = (k1_funct_1 @ X27 @ X26))
% 0.47/0.64          | ~ (v1_funct_1 @ X27)
% 0.47/0.64          | ~ (v1_relat_1 @ X27))),
% 0.47/0.64      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.47/0.64  thf('47', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((r1_tarski @ sk_C_3 @ X0)
% 0.47/0.64          | ~ (v1_relat_1 @ sk_C_3)
% 0.47/0.64          | ~ (v1_funct_1 @ sk_C_3)
% 0.47/0.64          | ((sk_D @ X0 @ sk_C_3)
% 0.47/0.64              = (k1_funct_1 @ sk_C_3 @ (sk_C_1 @ X0 @ sk_C_3))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['45', '46'])).
% 0.47/0.64  thf('48', plain, ((v1_relat_1 @ sk_C_3)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('49', plain, ((v1_funct_1 @ sk_C_3)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('50', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((r1_tarski @ sk_C_3 @ X0)
% 0.47/0.64          | ((sk_D @ X0 @ sk_C_3)
% 0.47/0.64              = (k1_funct_1 @ sk_C_3 @ (sk_C_1 @ X0 @ sk_C_3))))),
% 0.47/0.64      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.47/0.64  thf('51', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k1_relat_1 @ X0))
% 0.47/0.64          | ~ (v1_funct_1 @ X0)
% 0.47/0.64          | (r1_tarski @ X0 @ X1)
% 0.47/0.64          | ~ (v1_relat_1 @ X0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['3'])).
% 0.47/0.64  thf('52', plain,
% 0.47/0.64      (![X20 : $i, X25 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X20)
% 0.47/0.64          | ~ (v1_funct_1 @ X20)
% 0.47/0.64          | ~ (r2_hidden @ X25 @ (k1_relat_1 @ X20))
% 0.47/0.64          | (r2_hidden @ (k1_funct_1 @ X20 @ X25) @ (k2_relat_1 @ X20)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['9'])).
% 0.47/0.64  thf('53', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X0)
% 0.47/0.64          | (r1_tarski @ X0 @ X1)
% 0.47/0.64          | ~ (v1_funct_1 @ X0)
% 0.47/0.64          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)) @ 
% 0.47/0.64             (k2_relat_1 @ X0))
% 0.47/0.64          | ~ (v1_funct_1 @ X0)
% 0.47/0.64          | ~ (v1_relat_1 @ X0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['51', '52'])).
% 0.47/0.64  thf('54', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((r2_hidden @ (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)) @ 
% 0.47/0.64           (k2_relat_1 @ X0))
% 0.47/0.64          | ~ (v1_funct_1 @ X0)
% 0.47/0.64          | (r1_tarski @ X0 @ X1)
% 0.47/0.64          | ~ (v1_relat_1 @ X0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['53'])).
% 0.47/0.64  thf('55', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((r2_hidden @ (sk_D @ X0 @ sk_C_3) @ (k2_relat_1 @ sk_C_3))
% 0.47/0.64          | (r1_tarski @ sk_C_3 @ X0)
% 0.47/0.64          | ~ (v1_relat_1 @ sk_C_3)
% 0.47/0.64          | (r1_tarski @ sk_C_3 @ X0)
% 0.47/0.64          | ~ (v1_funct_1 @ sk_C_3))),
% 0.47/0.64      inference('sup+', [status(thm)], ['50', '54'])).
% 0.47/0.64  thf('56', plain, (((k2_relat_1 @ sk_C_3) = (k1_tarski @ sk_A))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('57', plain, (((k2_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('58', plain, (((k2_relat_1 @ sk_B) = (k2_relat_1 @ sk_C_3))),
% 0.47/0.64      inference('sup+', [status(thm)], ['56', '57'])).
% 0.47/0.64  thf('59', plain, ((v1_relat_1 @ sk_C_3)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('60', plain, ((v1_funct_1 @ sk_C_3)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('61', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((r2_hidden @ (sk_D @ X0 @ sk_C_3) @ (k2_relat_1 @ sk_B))
% 0.47/0.64          | (r1_tarski @ sk_C_3 @ X0)
% 0.47/0.64          | (r1_tarski @ sk_C_3 @ X0))),
% 0.47/0.64      inference('demod', [status(thm)], ['55', '58', '59', '60'])).
% 0.47/0.64  thf('62', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((r1_tarski @ sk_C_3 @ X0)
% 0.47/0.64          | (r2_hidden @ (sk_D @ X0 @ sk_C_3) @ (k2_relat_1 @ sk_B)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['61'])).
% 0.47/0.64  thf('63', plain,
% 0.47/0.64      (![X0 : $i]: (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B)) | ((X0) = (sk_A)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['15', '17'])).
% 0.47/0.64  thf('64', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((r1_tarski @ sk_C_3 @ X0) | ((sk_D @ X0 @ sk_C_3) = (sk_A)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['62', '63'])).
% 0.47/0.64  thf('65', plain,
% 0.47/0.64      (![X14 : $i, X15 : $i]:
% 0.47/0.64         (~ (r2_hidden @ 
% 0.47/0.64             (k4_tarski @ (sk_C_1 @ X14 @ X15) @ (sk_D @ X14 @ X15)) @ X14)
% 0.47/0.64          | (r1_tarski @ X15 @ X14)
% 0.47/0.64          | ~ (v1_relat_1 @ X15))),
% 0.47/0.64      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.47/0.64  thf('66', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (r2_hidden @ (k4_tarski @ (sk_C_1 @ X0 @ sk_C_3) @ sk_A) @ X0)
% 0.47/0.64          | (r1_tarski @ sk_C_3 @ X0)
% 0.47/0.64          | ~ (v1_relat_1 @ sk_C_3)
% 0.47/0.64          | (r1_tarski @ sk_C_3 @ X0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['64', '65'])).
% 0.47/0.64  thf('67', plain, ((v1_relat_1 @ sk_C_3)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('68', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (r2_hidden @ (k4_tarski @ (sk_C_1 @ X0 @ sk_C_3) @ sk_A) @ X0)
% 0.47/0.64          | (r1_tarski @ sk_C_3 @ X0)
% 0.47/0.64          | (r1_tarski @ sk_C_3 @ X0))),
% 0.47/0.64      inference('demod', [status(thm)], ['66', '67'])).
% 0.47/0.64  thf('69', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((r1_tarski @ sk_C_3 @ X0)
% 0.47/0.64          | ~ (r2_hidden @ (k4_tarski @ (sk_C_1 @ X0 @ sk_C_3) @ sk_A) @ X0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['68'])).
% 0.47/0.64  thf('70', plain,
% 0.47/0.64      (((r1_tarski @ sk_C_3 @ sk_B) | (r1_tarski @ sk_C_3 @ sk_B))),
% 0.47/0.64      inference('sup-', [status(thm)], ['28', '69'])).
% 0.47/0.64  thf('71', plain, ((r1_tarski @ sk_C_3 @ sk_B)),
% 0.47/0.64      inference('simplify', [status(thm)], ['70'])).
% 0.47/0.64  thf(d10_xboole_0, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.64  thf('72', plain,
% 0.47/0.64      (![X0 : $i, X2 : $i]:
% 0.47/0.64         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.47/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.64  thf('73', plain, ((~ (r1_tarski @ sk_B @ sk_C_3) | ((sk_B) = (sk_C_3)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['71', '72'])).
% 0.47/0.64  thf('74', plain, (((sk_B) != (sk_C_3))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('75', plain, (~ (r1_tarski @ sk_B @ sk_C_3)),
% 0.47/0.64      inference('simplify_reflect-', [status(thm)], ['73', '74'])).
% 0.47/0.64  thf('76', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k1_relat_1 @ X0))
% 0.47/0.64          | ~ (v1_funct_1 @ X0)
% 0.47/0.64          | (r1_tarski @ X0 @ X1)
% 0.47/0.64          | ~ (v1_relat_1 @ X0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['3'])).
% 0.47/0.64  thf('77', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.47/0.64          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C_3 @ X0)) @ sk_C_3))),
% 0.47/0.64      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.47/0.64  thf('78', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ sk_B)
% 0.47/0.64          | (r1_tarski @ sk_B @ X0)
% 0.47/0.64          | ~ (v1_funct_1 @ sk_B)
% 0.47/0.64          | (r2_hidden @ 
% 0.47/0.64             (k4_tarski @ (sk_C_1 @ X0 @ sk_B) @ 
% 0.47/0.64              (k1_funct_1 @ sk_C_3 @ (sk_C_1 @ X0 @ sk_B))) @ 
% 0.47/0.64             sk_C_3))),
% 0.47/0.64      inference('sup-', [status(thm)], ['76', '77'])).
% 0.47/0.64  thf('79', plain, ((v1_relat_1 @ sk_B)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('80', plain, ((v1_funct_1 @ sk_B)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('81', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((r1_tarski @ sk_B @ X0)
% 0.47/0.64          | (r2_hidden @ 
% 0.47/0.64             (k4_tarski @ (sk_C_1 @ X0 @ sk_B) @ 
% 0.47/0.64              (k1_funct_1 @ sk_C_3 @ (sk_C_1 @ X0 @ sk_B))) @ 
% 0.47/0.64             sk_C_3))),
% 0.47/0.64      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.47/0.64  thf('82', plain,
% 0.47/0.64      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.47/0.64         (~ (r2_hidden @ (k4_tarski @ X26 @ X28) @ X27)
% 0.47/0.64          | (r2_hidden @ X26 @ (k1_relat_1 @ X27))
% 0.47/0.64          | ~ (v1_funct_1 @ X27)
% 0.47/0.64          | ~ (v1_relat_1 @ X27))),
% 0.47/0.64      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.47/0.64  thf('83', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((r1_tarski @ sk_B @ X0)
% 0.47/0.64          | ~ (v1_relat_1 @ sk_C_3)
% 0.47/0.64          | ~ (v1_funct_1 @ sk_C_3)
% 0.47/0.64          | (r2_hidden @ (sk_C_1 @ X0 @ sk_B) @ (k1_relat_1 @ sk_C_3)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['81', '82'])).
% 0.47/0.64  thf('84', plain, ((v1_relat_1 @ sk_C_3)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('85', plain, ((v1_funct_1 @ sk_C_3)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('86', plain, (((k1_relat_1 @ sk_B) = (k1_relat_1 @ sk_C_3))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('87', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((r1_tarski @ sk_B @ X0)
% 0.47/0.64          | (r2_hidden @ (sk_C_1 @ X0 @ sk_B) @ (k1_relat_1 @ sk_B)))),
% 0.47/0.64      inference('demod', [status(thm)], ['83', '84', '85', '86'])).
% 0.47/0.64  thf('88', plain, (((k1_relat_1 @ sk_B) = (k1_relat_1 @ sk_C_3))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('89', plain,
% 0.47/0.64      (![X20 : $i, X25 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X20)
% 0.47/0.64          | ~ (v1_funct_1 @ X20)
% 0.47/0.64          | ~ (r2_hidden @ X25 @ (k1_relat_1 @ X20))
% 0.47/0.64          | (r2_hidden @ (k1_funct_1 @ X20 @ X25) @ (k2_relat_1 @ X20)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['9'])).
% 0.47/0.64  thf('90', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.47/0.64          | (r2_hidden @ (k1_funct_1 @ sk_C_3 @ X0) @ (k2_relat_1 @ sk_C_3))
% 0.47/0.64          | ~ (v1_funct_1 @ sk_C_3)
% 0.47/0.64          | ~ (v1_relat_1 @ sk_C_3))),
% 0.47/0.64      inference('sup-', [status(thm)], ['88', '89'])).
% 0.47/0.64  thf('91', plain, (((k2_relat_1 @ sk_B) = (k2_relat_1 @ sk_C_3))),
% 0.47/0.64      inference('sup+', [status(thm)], ['56', '57'])).
% 0.47/0.64  thf('92', plain, ((v1_funct_1 @ sk_C_3)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('93', plain, ((v1_relat_1 @ sk_C_3)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('94', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.47/0.64          | (r2_hidden @ (k1_funct_1 @ sk_C_3 @ X0) @ (k2_relat_1 @ sk_B)))),
% 0.47/0.64      inference('demod', [status(thm)], ['90', '91', '92', '93'])).
% 0.47/0.64  thf('95', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((r1_tarski @ sk_B @ X0)
% 0.47/0.64          | (r2_hidden @ (k1_funct_1 @ sk_C_3 @ (sk_C_1 @ X0 @ sk_B)) @ 
% 0.47/0.64             (k2_relat_1 @ sk_B)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['87', '94'])).
% 0.47/0.64  thf('96', plain,
% 0.47/0.64      (![X0 : $i]: (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B)) | ((X0) = (sk_A)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['15', '17'])).
% 0.47/0.64  thf('97', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((r1_tarski @ sk_B @ X0)
% 0.47/0.64          | ((k1_funct_1 @ sk_C_3 @ (sk_C_1 @ X0 @ sk_B)) = (sk_A)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['95', '96'])).
% 0.47/0.64  thf('98', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((r1_tarski @ sk_B @ X0)
% 0.47/0.64          | (r2_hidden @ 
% 0.47/0.64             (k4_tarski @ (sk_C_1 @ X0 @ sk_B) @ 
% 0.47/0.64              (k1_funct_1 @ sk_C_3 @ (sk_C_1 @ X0 @ sk_B))) @ 
% 0.47/0.64             sk_C_3))),
% 0.47/0.64      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.47/0.64  thf('99', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((r2_hidden @ (k4_tarski @ (sk_C_1 @ X0 @ sk_B) @ sk_A) @ sk_C_3)
% 0.47/0.64          | (r1_tarski @ sk_B @ X0)
% 0.47/0.64          | (r1_tarski @ sk_B @ X0))),
% 0.47/0.64      inference('sup+', [status(thm)], ['97', '98'])).
% 0.47/0.64  thf('100', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((r1_tarski @ sk_B @ X0)
% 0.47/0.64          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X0 @ sk_B) @ sk_A) @ sk_C_3))),
% 0.47/0.64      inference('simplify', [status(thm)], ['99'])).
% 0.47/0.64  thf('101', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (((sk_D @ X1 @ X0) = (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)))
% 0.47/0.64          | ~ (v1_funct_1 @ X0)
% 0.47/0.64          | (r1_tarski @ X0 @ X1)
% 0.47/0.64          | ~ (v1_relat_1 @ X0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['31'])).
% 0.47/0.64  thf('102', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((r2_hidden @ (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)) @ 
% 0.47/0.64           (k2_relat_1 @ X0))
% 0.47/0.64          | ~ (v1_funct_1 @ X0)
% 0.47/0.64          | (r1_tarski @ X0 @ X1)
% 0.47/0.64          | ~ (v1_relat_1 @ X0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['53'])).
% 0.47/0.64  thf('103', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((r2_hidden @ (sk_D @ X1 @ X0) @ (k2_relat_1 @ X0))
% 0.47/0.64          | ~ (v1_relat_1 @ X0)
% 0.47/0.64          | (r1_tarski @ X0 @ X1)
% 0.47/0.64          | ~ (v1_funct_1 @ X0)
% 0.47/0.64          | ~ (v1_relat_1 @ X0)
% 0.47/0.64          | (r1_tarski @ X0 @ X1)
% 0.47/0.64          | ~ (v1_funct_1 @ X0))),
% 0.47/0.64      inference('sup+', [status(thm)], ['101', '102'])).
% 0.47/0.64  thf('104', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (~ (v1_funct_1 @ X0)
% 0.47/0.64          | (r1_tarski @ X0 @ X1)
% 0.47/0.64          | ~ (v1_relat_1 @ X0)
% 0.47/0.64          | (r2_hidden @ (sk_D @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['103'])).
% 0.47/0.64  thf('105', plain,
% 0.47/0.64      (![X0 : $i]: (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B)) | ((X0) = (sk_A)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['15', '17'])).
% 0.47/0.64  thf('106', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ sk_B)
% 0.47/0.64          | (r1_tarski @ sk_B @ X0)
% 0.47/0.64          | ~ (v1_funct_1 @ sk_B)
% 0.47/0.64          | ((sk_D @ X0 @ sk_B) = (sk_A)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['104', '105'])).
% 0.47/0.64  thf('107', plain, ((v1_relat_1 @ sk_B)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('108', plain, ((v1_funct_1 @ sk_B)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('109', plain,
% 0.47/0.64      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ((sk_D @ X0 @ sk_B) = (sk_A)))),
% 0.47/0.64      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.47/0.64  thf('110', plain,
% 0.47/0.64      (![X14 : $i, X15 : $i]:
% 0.47/0.64         (~ (r2_hidden @ 
% 0.47/0.64             (k4_tarski @ (sk_C_1 @ X14 @ X15) @ (sk_D @ X14 @ X15)) @ X14)
% 0.47/0.64          | (r1_tarski @ X15 @ X14)
% 0.47/0.64          | ~ (v1_relat_1 @ X15))),
% 0.47/0.64      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.47/0.64  thf('111', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (r2_hidden @ (k4_tarski @ (sk_C_1 @ X0 @ sk_B) @ sk_A) @ X0)
% 0.47/0.64          | (r1_tarski @ sk_B @ X0)
% 0.47/0.64          | ~ (v1_relat_1 @ sk_B)
% 0.47/0.64          | (r1_tarski @ sk_B @ X0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['109', '110'])).
% 0.47/0.64  thf('112', plain, ((v1_relat_1 @ sk_B)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('113', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (r2_hidden @ (k4_tarski @ (sk_C_1 @ X0 @ sk_B) @ sk_A) @ X0)
% 0.47/0.64          | (r1_tarski @ sk_B @ X0)
% 0.47/0.64          | (r1_tarski @ sk_B @ X0))),
% 0.47/0.64      inference('demod', [status(thm)], ['111', '112'])).
% 0.47/0.64  thf('114', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((r1_tarski @ sk_B @ X0)
% 0.47/0.64          | ~ (r2_hidden @ (k4_tarski @ (sk_C_1 @ X0 @ sk_B) @ sk_A) @ X0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['113'])).
% 0.47/0.64  thf('115', plain,
% 0.47/0.64      (((r1_tarski @ sk_B @ sk_C_3) | (r1_tarski @ sk_B @ sk_C_3))),
% 0.47/0.64      inference('sup-', [status(thm)], ['100', '114'])).
% 0.47/0.64  thf('116', plain, ((r1_tarski @ sk_B @ sk_C_3)),
% 0.47/0.64      inference('simplify', [status(thm)], ['115'])).
% 0.47/0.64  thf('117', plain, ($false), inference('demod', [status(thm)], ['75', '116'])).
% 0.47/0.64  
% 0.47/0.64  % SZS output end Refutation
% 0.47/0.64  
% 0.47/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
