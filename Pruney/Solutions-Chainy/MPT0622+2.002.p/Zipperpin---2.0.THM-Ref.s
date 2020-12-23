%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2Vrd7SOcbq

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:34 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 260 expanded)
%              Number of leaves         :   20 (  80 expanded)
%              Depth                    :   18
%              Number of atoms          : 1086 (3758 expanded)
%              Number of equality atoms :   43 ( 364 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('0',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X18 @ X19 ) @ ( sk_D @ X18 @ X19 ) ) @ X19 )
      | ( r1_tarski @ X19 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X25 @ X27 ) @ X26 )
      | ( r2_hidden @ X25 @ ( k1_relat_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

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

thf('4',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('5',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X24 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X24 @ X23 ) @ ( k2_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k2_relat_1 @ sk_C_2 )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','7','8','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ sk_B @ X0 )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ X0 @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ X0 @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
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

thf('18',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( X6 = X3 )
      | ( X5
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('19',plain,(
    ! [X3: $i,X6: $i] :
      ( ( X6 = X3 )
      | ~ ( r2_hidden @ X6 @ ( k1_tarski @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ X0 @ sk_B ) )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('23',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X26 ) )
      | ( X27
       != ( k1_funct_1 @ X26 @ X25 ) )
      | ( r2_hidden @ ( k4_tarski @ X25 @ X27 ) @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('25',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ( r2_hidden @ ( k4_tarski @ X25 @ ( k1_funct_1 @ X26 @ X25 ) ) @ X26 )
      | ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C_2 @ X0 ) ) @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C_2 @ X0 ) ) @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ sk_B @ X0 )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_B ) @ ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ X0 @ sk_B ) ) ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_B ) @ ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ X0 @ sk_B ) ) ) @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_B ) @ sk_A ) @ sk_C_2 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_B ) @ sk_A ) @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X18 @ X19 ) @ ( sk_D @ X18 @ X19 ) ) @ X19 )
      | ( r1_tarski @ X19 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('37',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X25 @ X27 ) @ X26 )
      | ( X27
        = ( k1_funct_1 @ X26 @ X25 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_D @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('41',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X24 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X24 @ X23 ) @ ( k2_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ sk_B @ X0 )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ X0 @ sk_B ) )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ X0 @ sk_B ) )
        = sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ X0 @ sk_B )
        = sk_A )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ sk_B @ X0 )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ X0 @ sk_B )
        = sk_A )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( sk_D @ X0 @ sk_B )
        = sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X18 @ X19 ) @ ( sk_D @ X18 @ X19 ) ) @ X18 )
      | ( r1_tarski @ X19 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_B ) @ sk_A ) @ X0 )
      | ( r1_tarski @ sk_B @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_B ) @ sk_A ) @ X0 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( r1_tarski @ sk_B @ sk_C_2 )
    | ( r1_tarski @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['35','58'])).

thf('60',plain,(
    r1_tarski @ sk_B @ sk_C_2 ),
    inference(simplify,[status(thm)],['59'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('61',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,
    ( ~ ( r1_tarski @ sk_C_2 @ sk_B )
    | ( sk_C_2 = sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    sk_B != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ~ ( r1_tarski @ sk_C_2 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ( r1_tarski @ sk_C_2 @ X0 )
      | ~ ( v1_funct_1 @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_B ) )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X24 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X24 @ X23 ) @ ( k2_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C_1 @ X0 @ sk_C_2 ) ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C_1 @ X0 @ sk_C_2 ) ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ X0 @ sk_C_2 ) )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_B ) )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('79',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ( r2_hidden @ ( k4_tarski @ X25 @ ( k1_funct_1 @ X26 @ X25 ) ) @ X26 )
      | ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_funct_1 @ sk_B @ ( sk_C_1 @ X0 @ sk_C_2 ) ) ) @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_funct_1 @ sk_B @ ( sk_C_1 @ X0 @ sk_C_2 ) ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A ) @ sk_B )
      | ( r1_tarski @ sk_C_2 @ X0 )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['77','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_C_2 ) @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ( r1_tarski @ sk_C_2 @ X0 )
      | ~ ( v1_funct_1 @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['86','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_C_2 ) @ ( k2_relat_1 @ sk_B ) )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( ( sk_D @ X0 @ sk_C_2 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X18 @ X19 ) @ ( sk_D @ X18 @ X19 ) ) @ X18 )
      | ( r1_tarski @ X19 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A ) @ X0 )
      | ( r1_tarski @ sk_C_2 @ X0 )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A ) @ X0 )
      | ( r1_tarski @ sk_C_2 @ X0 )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_B )
    | ( r1_tarski @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['85','101'])).

thf('103',plain,(
    r1_tarski @ sk_C_2 @ sk_B ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    $false ),
    inference(demod,[status(thm)],['64','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2Vrd7SOcbq
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:36:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.58  % Solved by: fo/fo7.sh
% 0.36/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.58  % done 249 iterations in 0.131s
% 0.36/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.58  % SZS output start Refutation
% 0.36/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.58  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.36/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.58  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.36/0.58  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.36/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.58  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.36/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.58  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.36/0.58  thf(d3_relat_1, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( v1_relat_1 @ A ) =>
% 0.36/0.58       ( ![B:$i]:
% 0.36/0.58         ( ( r1_tarski @ A @ B ) <=>
% 0.36/0.58           ( ![C:$i,D:$i]:
% 0.36/0.58             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.36/0.58               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.36/0.58  thf('0', plain,
% 0.36/0.58      (![X18 : $i, X19 : $i]:
% 0.36/0.58         ((r2_hidden @ 
% 0.36/0.58           (k4_tarski @ (sk_C_1 @ X18 @ X19) @ (sk_D @ X18 @ X19)) @ X19)
% 0.36/0.58          | (r1_tarski @ X19 @ X18)
% 0.36/0.58          | ~ (v1_relat_1 @ X19))),
% 0.36/0.58      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.36/0.58  thf(t8_funct_1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.36/0.58       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.36/0.58         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.36/0.58           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.36/0.58  thf('1', plain,
% 0.36/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.36/0.58         (~ (r2_hidden @ (k4_tarski @ X25 @ X27) @ X26)
% 0.36/0.58          | (r2_hidden @ X25 @ (k1_relat_1 @ X26))
% 0.36/0.58          | ~ (v1_funct_1 @ X26)
% 0.36/0.58          | ~ (v1_relat_1 @ X26))),
% 0.36/0.58      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.36/0.58  thf('2', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (~ (v1_relat_1 @ X0)
% 0.36/0.58          | (r1_tarski @ X0 @ X1)
% 0.36/0.58          | ~ (v1_relat_1 @ X0)
% 0.36/0.58          | ~ (v1_funct_1 @ X0)
% 0.36/0.58          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.58  thf('3', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k1_relat_1 @ X0))
% 0.36/0.58          | ~ (v1_funct_1 @ X0)
% 0.36/0.58          | (r1_tarski @ X0 @ X1)
% 0.36/0.58          | ~ (v1_relat_1 @ X0))),
% 0.36/0.58      inference('simplify', [status(thm)], ['2'])).
% 0.36/0.58  thf(t17_funct_1, conjecture,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.58       ( ![C:$i]:
% 0.36/0.58         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.36/0.58           ( ( ( ( k1_relat_1 @ B ) = ( k1_relat_1 @ C ) ) & 
% 0.36/0.58               ( ( k2_relat_1 @ B ) = ( k1_tarski @ A ) ) & 
% 0.36/0.58               ( ( k2_relat_1 @ C ) = ( k1_tarski @ A ) ) ) =>
% 0.36/0.58             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.36/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.58    (~( ![A:$i,B:$i]:
% 0.36/0.58        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.58          ( ![C:$i]:
% 0.36/0.58            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.36/0.58              ( ( ( ( k1_relat_1 @ B ) = ( k1_relat_1 @ C ) ) & 
% 0.36/0.58                  ( ( k2_relat_1 @ B ) = ( k1_tarski @ A ) ) & 
% 0.36/0.58                  ( ( k2_relat_1 @ C ) = ( k1_tarski @ A ) ) ) =>
% 0.36/0.58                ( ( B ) = ( C ) ) ) ) ) ) )),
% 0.36/0.58    inference('cnf.neg', [status(esa)], [t17_funct_1])).
% 0.36/0.58  thf('4', plain, (((k1_relat_1 @ sk_B) = (k1_relat_1 @ sk_C_2))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(t12_funct_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.58       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.36/0.58         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.36/0.58  thf('5', plain,
% 0.36/0.58      (![X23 : $i, X24 : $i]:
% 0.36/0.58         (~ (r2_hidden @ X23 @ (k1_relat_1 @ X24))
% 0.36/0.58          | (r2_hidden @ (k1_funct_1 @ X24 @ X23) @ (k2_relat_1 @ X24))
% 0.36/0.58          | ~ (v1_funct_1 @ X24)
% 0.36/0.58          | ~ (v1_relat_1 @ X24))),
% 0.36/0.58      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.36/0.58  thf('6', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.36/0.58          | ~ (v1_relat_1 @ sk_C_2)
% 0.36/0.58          | ~ (v1_funct_1 @ sk_C_2)
% 0.36/0.58          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.58  thf('7', plain, ((v1_relat_1 @ sk_C_2)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('8', plain, ((v1_funct_1 @ sk_C_2)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('9', plain, (((k2_relat_1 @ sk_C_2) = (k1_tarski @ sk_A))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('10', plain, (((k2_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('11', plain, (((k2_relat_1 @ sk_B) = (k2_relat_1 @ sk_C_2))),
% 0.36/0.58      inference('sup+', [status(thm)], ['9', '10'])).
% 0.36/0.58  thf('12', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.36/0.58          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_B)))),
% 0.36/0.58      inference('demod', [status(thm)], ['6', '7', '8', '11'])).
% 0.36/0.58  thf('13', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (~ (v1_relat_1 @ sk_B)
% 0.36/0.58          | (r1_tarski @ sk_B @ X0)
% 0.36/0.58          | ~ (v1_funct_1 @ sk_B)
% 0.36/0.58          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ X0 @ sk_B)) @ 
% 0.36/0.58             (k2_relat_1 @ sk_B)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['3', '12'])).
% 0.36/0.58  thf('14', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('15', plain, ((v1_funct_1 @ sk_B)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('16', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((r1_tarski @ sk_B @ X0)
% 0.36/0.58          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ X0 @ sk_B)) @ 
% 0.36/0.58             (k2_relat_1 @ sk_B)))),
% 0.36/0.58      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.36/0.58  thf('17', plain, (((k2_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(d1_tarski, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.36/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.36/0.58  thf('18', plain,
% 0.36/0.58      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.36/0.58         (~ (r2_hidden @ X6 @ X5) | ((X6) = (X3)) | ((X5) != (k1_tarski @ X3)))),
% 0.36/0.58      inference('cnf', [status(esa)], [d1_tarski])).
% 0.36/0.58  thf('19', plain,
% 0.36/0.58      (![X3 : $i, X6 : $i]:
% 0.36/0.58         (((X6) = (X3)) | ~ (r2_hidden @ X6 @ (k1_tarski @ X3)))),
% 0.36/0.58      inference('simplify', [status(thm)], ['18'])).
% 0.36/0.58  thf('20', plain,
% 0.36/0.58      (![X0 : $i]: (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B)) | ((X0) = (sk_A)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['17', '19'])).
% 0.36/0.58  thf('21', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((r1_tarski @ sk_B @ X0)
% 0.36/0.58          | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ X0 @ sk_B)) = (sk_A)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['16', '20'])).
% 0.36/0.58  thf('22', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k1_relat_1 @ X0))
% 0.36/0.58          | ~ (v1_funct_1 @ X0)
% 0.36/0.58          | (r1_tarski @ X0 @ X1)
% 0.36/0.58          | ~ (v1_relat_1 @ X0))),
% 0.36/0.58      inference('simplify', [status(thm)], ['2'])).
% 0.36/0.58  thf('23', plain, (((k1_relat_1 @ sk_B) = (k1_relat_1 @ sk_C_2))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('24', plain,
% 0.36/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.36/0.58         (~ (r2_hidden @ X25 @ (k1_relat_1 @ X26))
% 0.36/0.58          | ((X27) != (k1_funct_1 @ X26 @ X25))
% 0.36/0.58          | (r2_hidden @ (k4_tarski @ X25 @ X27) @ X26)
% 0.36/0.58          | ~ (v1_funct_1 @ X26)
% 0.36/0.58          | ~ (v1_relat_1 @ X26))),
% 0.36/0.58      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.36/0.58  thf('25', plain,
% 0.36/0.58      (![X25 : $i, X26 : $i]:
% 0.36/0.58         (~ (v1_relat_1 @ X26)
% 0.36/0.58          | ~ (v1_funct_1 @ X26)
% 0.36/0.58          | (r2_hidden @ (k4_tarski @ X25 @ (k1_funct_1 @ X26 @ X25)) @ X26)
% 0.36/0.58          | ~ (r2_hidden @ X25 @ (k1_relat_1 @ X26)))),
% 0.36/0.58      inference('simplify', [status(thm)], ['24'])).
% 0.36/0.58  thf('26', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.36/0.58          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C_2 @ X0)) @ sk_C_2)
% 0.36/0.58          | ~ (v1_funct_1 @ sk_C_2)
% 0.36/0.58          | ~ (v1_relat_1 @ sk_C_2))),
% 0.36/0.58      inference('sup-', [status(thm)], ['23', '25'])).
% 0.36/0.58  thf('27', plain, ((v1_funct_1 @ sk_C_2)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('28', plain, ((v1_relat_1 @ sk_C_2)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('29', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.36/0.58          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C_2 @ X0)) @ sk_C_2))),
% 0.36/0.58      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.36/0.58  thf('30', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (~ (v1_relat_1 @ sk_B)
% 0.36/0.58          | (r1_tarski @ sk_B @ X0)
% 0.36/0.58          | ~ (v1_funct_1 @ sk_B)
% 0.36/0.58          | (r2_hidden @ 
% 0.36/0.58             (k4_tarski @ (sk_C_1 @ X0 @ sk_B) @ 
% 0.36/0.58              (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ X0 @ sk_B))) @ 
% 0.36/0.58             sk_C_2))),
% 0.36/0.58      inference('sup-', [status(thm)], ['22', '29'])).
% 0.36/0.58  thf('31', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('32', plain, ((v1_funct_1 @ sk_B)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('33', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((r1_tarski @ sk_B @ X0)
% 0.36/0.58          | (r2_hidden @ 
% 0.36/0.58             (k4_tarski @ (sk_C_1 @ X0 @ sk_B) @ 
% 0.36/0.58              (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ X0 @ sk_B))) @ 
% 0.36/0.58             sk_C_2))),
% 0.36/0.58      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.36/0.58  thf('34', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((r2_hidden @ (k4_tarski @ (sk_C_1 @ X0 @ sk_B) @ sk_A) @ sk_C_2)
% 0.36/0.58          | (r1_tarski @ sk_B @ X0)
% 0.36/0.58          | (r1_tarski @ sk_B @ X0))),
% 0.36/0.58      inference('sup+', [status(thm)], ['21', '33'])).
% 0.36/0.58  thf('35', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((r1_tarski @ sk_B @ X0)
% 0.36/0.58          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X0 @ sk_B) @ sk_A) @ sk_C_2))),
% 0.36/0.58      inference('simplify', [status(thm)], ['34'])).
% 0.36/0.58  thf('36', plain,
% 0.36/0.58      (![X18 : $i, X19 : $i]:
% 0.36/0.58         ((r2_hidden @ 
% 0.36/0.58           (k4_tarski @ (sk_C_1 @ X18 @ X19) @ (sk_D @ X18 @ X19)) @ X19)
% 0.36/0.58          | (r1_tarski @ X19 @ X18)
% 0.36/0.58          | ~ (v1_relat_1 @ X19))),
% 0.36/0.58      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.36/0.58  thf('37', plain,
% 0.36/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.36/0.58         (~ (r2_hidden @ (k4_tarski @ X25 @ X27) @ X26)
% 0.36/0.58          | ((X27) = (k1_funct_1 @ X26 @ X25))
% 0.36/0.58          | ~ (v1_funct_1 @ X26)
% 0.36/0.58          | ~ (v1_relat_1 @ X26))),
% 0.36/0.58      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.36/0.58  thf('38', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (~ (v1_relat_1 @ X0)
% 0.36/0.58          | (r1_tarski @ X0 @ X1)
% 0.36/0.58          | ~ (v1_relat_1 @ X0)
% 0.36/0.58          | ~ (v1_funct_1 @ X0)
% 0.36/0.58          | ((sk_D @ X1 @ X0) = (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['36', '37'])).
% 0.36/0.58  thf('39', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (((sk_D @ X1 @ X0) = (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)))
% 0.36/0.58          | ~ (v1_funct_1 @ X0)
% 0.36/0.58          | (r1_tarski @ X0 @ X1)
% 0.36/0.58          | ~ (v1_relat_1 @ X0))),
% 0.36/0.58      inference('simplify', [status(thm)], ['38'])).
% 0.36/0.58  thf('40', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k1_relat_1 @ X0))
% 0.36/0.58          | ~ (v1_funct_1 @ X0)
% 0.36/0.58          | (r1_tarski @ X0 @ X1)
% 0.36/0.58          | ~ (v1_relat_1 @ X0))),
% 0.36/0.58      inference('simplify', [status(thm)], ['2'])).
% 0.36/0.58  thf('41', plain,
% 0.36/0.58      (![X23 : $i, X24 : $i]:
% 0.36/0.58         (~ (r2_hidden @ X23 @ (k1_relat_1 @ X24))
% 0.36/0.58          | (r2_hidden @ (k1_funct_1 @ X24 @ X23) @ (k2_relat_1 @ X24))
% 0.36/0.58          | ~ (v1_funct_1 @ X24)
% 0.36/0.58          | ~ (v1_relat_1 @ X24))),
% 0.36/0.58      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.36/0.58  thf('42', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (~ (v1_relat_1 @ X0)
% 0.36/0.58          | (r1_tarski @ X0 @ X1)
% 0.36/0.58          | ~ (v1_funct_1 @ X0)
% 0.36/0.58          | ~ (v1_relat_1 @ X0)
% 0.36/0.58          | ~ (v1_funct_1 @ X0)
% 0.36/0.58          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)) @ 
% 0.36/0.58             (k2_relat_1 @ X0)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['40', '41'])).
% 0.36/0.58  thf('43', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         ((r2_hidden @ (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)) @ 
% 0.36/0.58           (k2_relat_1 @ X0))
% 0.36/0.58          | ~ (v1_funct_1 @ X0)
% 0.36/0.58          | (r1_tarski @ X0 @ X1)
% 0.36/0.58          | ~ (v1_relat_1 @ X0))),
% 0.36/0.58      inference('simplify', [status(thm)], ['42'])).
% 0.36/0.58  thf('44', plain,
% 0.36/0.58      (![X0 : $i]: (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B)) | ((X0) = (sk_A)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['17', '19'])).
% 0.36/0.58  thf('45', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (~ (v1_relat_1 @ sk_B)
% 0.36/0.58          | (r1_tarski @ sk_B @ X0)
% 0.36/0.58          | ~ (v1_funct_1 @ sk_B)
% 0.36/0.58          | ((k1_funct_1 @ sk_B @ (sk_C_1 @ X0 @ sk_B)) = (sk_A)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['43', '44'])).
% 0.36/0.58  thf('46', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('47', plain, ((v1_funct_1 @ sk_B)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('48', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((r1_tarski @ sk_B @ X0)
% 0.36/0.58          | ((k1_funct_1 @ sk_B @ (sk_C_1 @ X0 @ sk_B)) = (sk_A)))),
% 0.36/0.58      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.36/0.58  thf('49', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (((sk_D @ X0 @ sk_B) = (sk_A))
% 0.36/0.58          | ~ (v1_relat_1 @ sk_B)
% 0.36/0.58          | (r1_tarski @ sk_B @ X0)
% 0.36/0.58          | ~ (v1_funct_1 @ sk_B)
% 0.36/0.58          | (r1_tarski @ sk_B @ X0))),
% 0.36/0.58      inference('sup+', [status(thm)], ['39', '48'])).
% 0.36/0.58  thf('50', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('51', plain, ((v1_funct_1 @ sk_B)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('52', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (((sk_D @ X0 @ sk_B) = (sk_A))
% 0.36/0.58          | (r1_tarski @ sk_B @ X0)
% 0.36/0.58          | (r1_tarski @ sk_B @ X0))),
% 0.36/0.58      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.36/0.58  thf('53', plain,
% 0.36/0.58      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ((sk_D @ X0 @ sk_B) = (sk_A)))),
% 0.36/0.58      inference('simplify', [status(thm)], ['52'])).
% 0.36/0.58  thf('54', plain,
% 0.36/0.58      (![X18 : $i, X19 : $i]:
% 0.36/0.58         (~ (r2_hidden @ 
% 0.36/0.58             (k4_tarski @ (sk_C_1 @ X18 @ X19) @ (sk_D @ X18 @ X19)) @ X18)
% 0.36/0.58          | (r1_tarski @ X19 @ X18)
% 0.36/0.58          | ~ (v1_relat_1 @ X19))),
% 0.36/0.58      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.36/0.58  thf('55', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (~ (r2_hidden @ (k4_tarski @ (sk_C_1 @ X0 @ sk_B) @ sk_A) @ X0)
% 0.36/0.58          | (r1_tarski @ sk_B @ X0)
% 0.36/0.58          | ~ (v1_relat_1 @ sk_B)
% 0.36/0.58          | (r1_tarski @ sk_B @ X0))),
% 0.36/0.58      inference('sup-', [status(thm)], ['53', '54'])).
% 0.36/0.58  thf('56', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('57', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (~ (r2_hidden @ (k4_tarski @ (sk_C_1 @ X0 @ sk_B) @ sk_A) @ X0)
% 0.36/0.58          | (r1_tarski @ sk_B @ X0)
% 0.36/0.58          | (r1_tarski @ sk_B @ X0))),
% 0.36/0.58      inference('demod', [status(thm)], ['55', '56'])).
% 0.36/0.58  thf('58', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((r1_tarski @ sk_B @ X0)
% 0.36/0.58          | ~ (r2_hidden @ (k4_tarski @ (sk_C_1 @ X0 @ sk_B) @ sk_A) @ X0))),
% 0.36/0.58      inference('simplify', [status(thm)], ['57'])).
% 0.36/0.58  thf('59', plain,
% 0.36/0.58      (((r1_tarski @ sk_B @ sk_C_2) | (r1_tarski @ sk_B @ sk_C_2))),
% 0.36/0.58      inference('sup-', [status(thm)], ['35', '58'])).
% 0.36/0.58  thf('60', plain, ((r1_tarski @ sk_B @ sk_C_2)),
% 0.36/0.58      inference('simplify', [status(thm)], ['59'])).
% 0.36/0.58  thf(d10_xboole_0, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.58  thf('61', plain,
% 0.36/0.58      (![X0 : $i, X2 : $i]:
% 0.36/0.58         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.36/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.58  thf('62', plain, ((~ (r1_tarski @ sk_C_2 @ sk_B) | ((sk_C_2) = (sk_B)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['60', '61'])).
% 0.36/0.58  thf('63', plain, (((sk_B) != (sk_C_2))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('64', plain, (~ (r1_tarski @ sk_C_2 @ sk_B)),
% 0.36/0.58      inference('simplify_reflect-', [status(thm)], ['62', '63'])).
% 0.36/0.58  thf('65', plain, (((k1_relat_1 @ sk_B) = (k1_relat_1 @ sk_C_2))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('66', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k1_relat_1 @ X0))
% 0.36/0.58          | ~ (v1_funct_1 @ X0)
% 0.36/0.58          | (r1_tarski @ X0 @ X1)
% 0.36/0.58          | ~ (v1_relat_1 @ X0))),
% 0.36/0.58      inference('simplify', [status(thm)], ['2'])).
% 0.36/0.58  thf('67', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_B))
% 0.36/0.58          | ~ (v1_relat_1 @ sk_C_2)
% 0.36/0.58          | (r1_tarski @ sk_C_2 @ X0)
% 0.36/0.58          | ~ (v1_funct_1 @ sk_C_2))),
% 0.36/0.58      inference('sup+', [status(thm)], ['65', '66'])).
% 0.36/0.58  thf('68', plain, ((v1_relat_1 @ sk_C_2)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('69', plain, ((v1_funct_1 @ sk_C_2)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('70', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_B))
% 0.36/0.58          | (r1_tarski @ sk_C_2 @ X0))),
% 0.36/0.58      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.36/0.58  thf('71', plain,
% 0.36/0.58      (![X23 : $i, X24 : $i]:
% 0.36/0.58         (~ (r2_hidden @ X23 @ (k1_relat_1 @ X24))
% 0.36/0.58          | (r2_hidden @ (k1_funct_1 @ X24 @ X23) @ (k2_relat_1 @ X24))
% 0.36/0.58          | ~ (v1_funct_1 @ X24)
% 0.36/0.58          | ~ (v1_relat_1 @ X24))),
% 0.36/0.58      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.36/0.58  thf('72', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((r1_tarski @ sk_C_2 @ X0)
% 0.36/0.58          | ~ (v1_relat_1 @ sk_B)
% 0.36/0.58          | ~ (v1_funct_1 @ sk_B)
% 0.36/0.58          | (r2_hidden @ (k1_funct_1 @ sk_B @ (sk_C_1 @ X0 @ sk_C_2)) @ 
% 0.36/0.58             (k2_relat_1 @ sk_B)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['70', '71'])).
% 0.36/0.58  thf('73', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('74', plain, ((v1_funct_1 @ sk_B)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('75', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((r1_tarski @ sk_C_2 @ X0)
% 0.36/0.58          | (r2_hidden @ (k1_funct_1 @ sk_B @ (sk_C_1 @ X0 @ sk_C_2)) @ 
% 0.36/0.58             (k2_relat_1 @ sk_B)))),
% 0.36/0.58      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.36/0.58  thf('76', plain,
% 0.36/0.58      (![X0 : $i]: (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B)) | ((X0) = (sk_A)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['17', '19'])).
% 0.36/0.58  thf('77', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((r1_tarski @ sk_C_2 @ X0)
% 0.36/0.58          | ((k1_funct_1 @ sk_B @ (sk_C_1 @ X0 @ sk_C_2)) = (sk_A)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['75', '76'])).
% 0.36/0.58  thf('78', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_B))
% 0.36/0.58          | (r1_tarski @ sk_C_2 @ X0))),
% 0.36/0.58      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.36/0.58  thf('79', plain,
% 0.36/0.58      (![X25 : $i, X26 : $i]:
% 0.36/0.58         (~ (v1_relat_1 @ X26)
% 0.36/0.58          | ~ (v1_funct_1 @ X26)
% 0.36/0.58          | (r2_hidden @ (k4_tarski @ X25 @ (k1_funct_1 @ X26 @ X25)) @ X26)
% 0.36/0.58          | ~ (r2_hidden @ X25 @ (k1_relat_1 @ X26)))),
% 0.36/0.58      inference('simplify', [status(thm)], ['24'])).
% 0.36/0.58  thf('80', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((r1_tarski @ sk_C_2 @ X0)
% 0.36/0.58          | (r2_hidden @ 
% 0.36/0.58             (k4_tarski @ (sk_C_1 @ X0 @ sk_C_2) @ 
% 0.36/0.58              (k1_funct_1 @ sk_B @ (sk_C_1 @ X0 @ sk_C_2))) @ 
% 0.36/0.58             sk_B)
% 0.36/0.58          | ~ (v1_funct_1 @ sk_B)
% 0.36/0.58          | ~ (v1_relat_1 @ sk_B))),
% 0.36/0.58      inference('sup-', [status(thm)], ['78', '79'])).
% 0.36/0.58  thf('81', plain, ((v1_funct_1 @ sk_B)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('82', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('83', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((r1_tarski @ sk_C_2 @ X0)
% 0.36/0.58          | (r2_hidden @ 
% 0.36/0.58             (k4_tarski @ (sk_C_1 @ X0 @ sk_C_2) @ 
% 0.36/0.58              (k1_funct_1 @ sk_B @ (sk_C_1 @ X0 @ sk_C_2))) @ 
% 0.36/0.58             sk_B))),
% 0.36/0.58      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.36/0.58  thf('84', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((r2_hidden @ (k4_tarski @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A) @ sk_B)
% 0.36/0.58          | (r1_tarski @ sk_C_2 @ X0)
% 0.36/0.58          | (r1_tarski @ sk_C_2 @ X0))),
% 0.36/0.58      inference('sup+', [status(thm)], ['77', '83'])).
% 0.36/0.58  thf('85', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((r1_tarski @ sk_C_2 @ X0)
% 0.36/0.58          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A) @ sk_B))),
% 0.36/0.58      inference('simplify', [status(thm)], ['84'])).
% 0.36/0.58  thf('86', plain, (((k2_relat_1 @ sk_B) = (k2_relat_1 @ sk_C_2))),
% 0.36/0.58      inference('sup+', [status(thm)], ['9', '10'])).
% 0.36/0.58  thf('87', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (((sk_D @ X1 @ X0) = (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)))
% 0.36/0.58          | ~ (v1_funct_1 @ X0)
% 0.36/0.58          | (r1_tarski @ X0 @ X1)
% 0.36/0.58          | ~ (v1_relat_1 @ X0))),
% 0.36/0.58      inference('simplify', [status(thm)], ['38'])).
% 0.36/0.58  thf('88', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         ((r2_hidden @ (k1_funct_1 @ X0 @ (sk_C_1 @ X1 @ X0)) @ 
% 0.36/0.58           (k2_relat_1 @ X0))
% 0.36/0.58          | ~ (v1_funct_1 @ X0)
% 0.36/0.58          | (r1_tarski @ X0 @ X1)
% 0.36/0.58          | ~ (v1_relat_1 @ X0))),
% 0.36/0.58      inference('simplify', [status(thm)], ['42'])).
% 0.36/0.58  thf('89', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         ((r2_hidden @ (sk_D @ X1 @ X0) @ (k2_relat_1 @ X0))
% 0.36/0.58          | ~ (v1_relat_1 @ X0)
% 0.36/0.58          | (r1_tarski @ X0 @ X1)
% 0.36/0.58          | ~ (v1_funct_1 @ X0)
% 0.36/0.58          | ~ (v1_relat_1 @ X0)
% 0.36/0.58          | (r1_tarski @ X0 @ X1)
% 0.36/0.58          | ~ (v1_funct_1 @ X0))),
% 0.36/0.58      inference('sup+', [status(thm)], ['87', '88'])).
% 0.36/0.58  thf('90', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (~ (v1_funct_1 @ X0)
% 0.36/0.58          | (r1_tarski @ X0 @ X1)
% 0.36/0.58          | ~ (v1_relat_1 @ X0)
% 0.36/0.58          | (r2_hidden @ (sk_D @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.36/0.58      inference('simplify', [status(thm)], ['89'])).
% 0.36/0.58  thf('91', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((r2_hidden @ (sk_D @ X0 @ sk_C_2) @ (k2_relat_1 @ sk_B))
% 0.36/0.58          | ~ (v1_relat_1 @ sk_C_2)
% 0.36/0.58          | (r1_tarski @ sk_C_2 @ X0)
% 0.36/0.58          | ~ (v1_funct_1 @ sk_C_2))),
% 0.36/0.58      inference('sup+', [status(thm)], ['86', '90'])).
% 0.36/0.58  thf('92', plain, ((v1_relat_1 @ sk_C_2)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('93', plain, ((v1_funct_1 @ sk_C_2)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('94', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((r2_hidden @ (sk_D @ X0 @ sk_C_2) @ (k2_relat_1 @ sk_B))
% 0.36/0.58          | (r1_tarski @ sk_C_2 @ X0))),
% 0.36/0.58      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.36/0.58  thf('95', plain,
% 0.36/0.58      (![X0 : $i]: (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B)) | ((X0) = (sk_A)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['17', '19'])).
% 0.36/0.58  thf('96', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((r1_tarski @ sk_C_2 @ X0) | ((sk_D @ X0 @ sk_C_2) = (sk_A)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['94', '95'])).
% 0.36/0.58  thf('97', plain,
% 0.36/0.58      (![X18 : $i, X19 : $i]:
% 0.36/0.58         (~ (r2_hidden @ 
% 0.36/0.58             (k4_tarski @ (sk_C_1 @ X18 @ X19) @ (sk_D @ X18 @ X19)) @ X18)
% 0.36/0.58          | (r1_tarski @ X19 @ X18)
% 0.36/0.58          | ~ (v1_relat_1 @ X19))),
% 0.36/0.58      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.36/0.58  thf('98', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (~ (r2_hidden @ (k4_tarski @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A) @ X0)
% 0.36/0.58          | (r1_tarski @ sk_C_2 @ X0)
% 0.36/0.58          | ~ (v1_relat_1 @ sk_C_2)
% 0.36/0.58          | (r1_tarski @ sk_C_2 @ X0))),
% 0.36/0.58      inference('sup-', [status(thm)], ['96', '97'])).
% 0.36/0.58  thf('99', plain, ((v1_relat_1 @ sk_C_2)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('100', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (~ (r2_hidden @ (k4_tarski @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A) @ X0)
% 0.36/0.58          | (r1_tarski @ sk_C_2 @ X0)
% 0.36/0.58          | (r1_tarski @ sk_C_2 @ X0))),
% 0.36/0.58      inference('demod', [status(thm)], ['98', '99'])).
% 0.36/0.58  thf('101', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((r1_tarski @ sk_C_2 @ X0)
% 0.36/0.58          | ~ (r2_hidden @ (k4_tarski @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A) @ X0))),
% 0.36/0.58      inference('simplify', [status(thm)], ['100'])).
% 0.36/0.58  thf('102', plain,
% 0.36/0.58      (((r1_tarski @ sk_C_2 @ sk_B) | (r1_tarski @ sk_C_2 @ sk_B))),
% 0.36/0.58      inference('sup-', [status(thm)], ['85', '101'])).
% 0.36/0.58  thf('103', plain, ((r1_tarski @ sk_C_2 @ sk_B)),
% 0.36/0.58      inference('simplify', [status(thm)], ['102'])).
% 0.36/0.58  thf('104', plain, ($false), inference('demod', [status(thm)], ['64', '103'])).
% 0.36/0.58  
% 0.36/0.58  % SZS output end Refutation
% 0.36/0.58  
% 0.36/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
