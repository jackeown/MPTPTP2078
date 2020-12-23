%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZSnjtMrtLw

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:59 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 216 expanded)
%              Number of leaves         :   18 (  68 expanded)
%              Depth                    :   20
%              Number of atoms          :  941 (3041 expanded)
%              Number of equality atoms :   70 ( 221 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X4: $i] :
      ( ( X4
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X4 @ X0 )
        = X0 )
      | ( r2_hidden @ ( sk_C @ X4 @ X0 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k11_relat_1 @ X6 @ X7 )
        = ( k9_relat_1 @ X6 @ ( k1_tarski @ X7 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k9_relat_1 @ X11 @ X9 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X9 @ X10 ) @ X9 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ ( k1_tarski @ X0 ) @ X2 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ ( k1_tarski @ X0 ) @ X2 ) @ ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ X2 )
        = X2 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ ( k1_tarski @ X0 ) @ ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('7',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k11_relat_1 @ X2 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C @ ( k11_relat_1 @ X2 @ X0 ) @ X1 )
        = X1 )
      | ( ( sk_D @ X2 @ ( k1_tarski @ X0 ) @ ( sk_C @ ( k11_relat_1 @ X2 @ X0 ) @ X1 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i,X4: $i] :
      ( ( X4
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X4 @ X0 )
        = X0 )
      | ( r2_hidden @ ( sk_C @ X4 @ X0 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k11_relat_1 @ X6 @ X7 )
        = ( k9_relat_1 @ X6 @ ( k1_tarski @ X7 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('11',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k9_relat_1 @ X11 @ X9 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X11 @ X9 @ X10 ) @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ ( k1_tarski @ X0 ) @ X2 ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ ( k1_tarski @ X0 ) @ X2 ) @ X2 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ X2 )
        = X2 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ ( k1_tarski @ X0 ) @ ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X1 )
      | ( ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ X2 )
        = X2 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ X2 )
        = X2 ) ) ),
    inference('sup+',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ X2 )
        = X2 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X25 @ X27 ) @ X26 )
      | ( X27
        = ( k1_funct_1 @ X26 @ X25 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k11_relat_1 @ X0 @ X2 ) @ X1 )
        = X1 )
      | ( ( k11_relat_1 @ X0 @ X2 )
        = ( k1_tarski @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_C @ ( k11_relat_1 @ X0 @ X2 ) @ X1 )
        = ( k1_funct_1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k11_relat_1 @ X0 @ X2 ) @ X1 )
        = ( k1_funct_1 @ X0 @ X2 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X2 )
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C @ ( k11_relat_1 @ X0 @ X2 ) @ X1 )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k11_relat_1 @ X6 @ X7 )
        = ( k9_relat_1 @ X6 @ ( k1_tarski @ X7 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('22',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t117_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
         => ( ( k11_relat_1 @ B @ A )
            = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t117_funct_1])).

thf('23',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
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

thf('26',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
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
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ X11 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X11 ) )
      | ( r2_hidden @ X10 @ ( k9_relat_1 @ X11 @ X9 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ X0 ) )
      | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ X0 ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','34'])).

thf('36',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k11_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['20','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k11_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k11_relat_1 @ X0 @ X2 ) @ X1 )
        = ( k1_funct_1 @ X0 @ X2 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X2 )
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C @ ( k11_relat_1 @ X0 @ X2 ) @ X1 )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ X1 @ X0 )
       != X2 )
      | ( ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ X2 )
        = X2 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(eq_fact,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X1 @ X0 ) ) )
      | ( ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ ( k1_funct_1 @ X1 @ X0 ) )
        = ( k1_funct_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X4: $i] :
      ( ( X4
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X4 @ X0 )
       != X0 )
      | ~ ( r2_hidden @ ( sk_C @ X4 @ X0 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ X1 @ X0 ) @ ( k11_relat_1 @ X1 @ X0 ) )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ ( k1_funct_1 @ X1 @ X0 ) )
       != ( k1_funct_1 @ X1 @ X0 ) )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ ( k1_funct_1 @ X1 @ X0 ) )
       != ( k1_funct_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X1 @ X0 ) @ ( k11_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( sk_C @ ( k11_relat_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ( ( sk_C @ ( k11_relat_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ( sk_C @ ( k11_relat_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) )
 != ( k1_funct_1 @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_A )
     != ( k1_funct_1 @ sk_B @ sk_A ) )
    | ( ( sk_C @ ( k11_relat_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_B @ sk_A ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_A )
     != ( k1_funct_1 @ sk_B @ sk_A ) )
    | ( ( sk_C @ ( k11_relat_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_B @ sk_A ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ( ( sk_C @ ( k11_relat_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ( sk_C @ ( k11_relat_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) )
 != ( k1_funct_1 @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

thf('57',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['55','56','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZSnjtMrtLw
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:27:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.26/1.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.26/1.52  % Solved by: fo/fo7.sh
% 1.26/1.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.26/1.52  % done 608 iterations in 1.055s
% 1.26/1.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.26/1.52  % SZS output start Refutation
% 1.26/1.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.26/1.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.26/1.52  thf(sk_B_type, type, sk_B: $i).
% 1.26/1.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.26/1.52  thf(sk_A_type, type, sk_A: $i).
% 1.26/1.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.26/1.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.26/1.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.26/1.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.26/1.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.26/1.52  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 1.26/1.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.26/1.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.26/1.52  thf(d1_tarski, axiom,
% 1.26/1.52    (![A:$i,B:$i]:
% 1.26/1.52     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.26/1.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.26/1.52  thf('0', plain,
% 1.26/1.52      (![X0 : $i, X4 : $i]:
% 1.26/1.52         (((X4) = (k1_tarski @ X0))
% 1.26/1.52          | ((sk_C @ X4 @ X0) = (X0))
% 1.26/1.52          | (r2_hidden @ (sk_C @ X4 @ X0) @ X4))),
% 1.26/1.52      inference('cnf', [status(esa)], [d1_tarski])).
% 1.26/1.52  thf(d16_relat_1, axiom,
% 1.26/1.52    (![A:$i]:
% 1.26/1.52     ( ( v1_relat_1 @ A ) =>
% 1.26/1.52       ( ![B:$i]:
% 1.26/1.52         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 1.26/1.52  thf('1', plain,
% 1.26/1.52      (![X6 : $i, X7 : $i]:
% 1.26/1.52         (((k11_relat_1 @ X6 @ X7) = (k9_relat_1 @ X6 @ (k1_tarski @ X7)))
% 1.26/1.52          | ~ (v1_relat_1 @ X6))),
% 1.26/1.52      inference('cnf', [status(esa)], [d16_relat_1])).
% 1.26/1.52  thf(t143_relat_1, axiom,
% 1.26/1.52    (![A:$i,B:$i,C:$i]:
% 1.26/1.52     ( ( v1_relat_1 @ C ) =>
% 1.26/1.52       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 1.26/1.52         ( ?[D:$i]:
% 1.26/1.52           ( ( r2_hidden @ D @ B ) & 
% 1.26/1.52             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 1.26/1.52             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 1.26/1.52  thf('2', plain,
% 1.26/1.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.26/1.52         (~ (r2_hidden @ X10 @ (k9_relat_1 @ X11 @ X9))
% 1.26/1.52          | (r2_hidden @ (sk_D @ X11 @ X9 @ X10) @ X9)
% 1.26/1.52          | ~ (v1_relat_1 @ X11))),
% 1.26/1.52      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.26/1.52  thf('3', plain,
% 1.26/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.26/1.52         (~ (r2_hidden @ X2 @ (k11_relat_1 @ X1 @ X0))
% 1.26/1.52          | ~ (v1_relat_1 @ X1)
% 1.26/1.52          | ~ (v1_relat_1 @ X1)
% 1.26/1.52          | (r2_hidden @ (sk_D @ X1 @ (k1_tarski @ X0) @ X2) @ (k1_tarski @ X0)))),
% 1.26/1.52      inference('sup-', [status(thm)], ['1', '2'])).
% 1.26/1.52  thf('4', plain,
% 1.26/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.26/1.52         ((r2_hidden @ (sk_D @ X1 @ (k1_tarski @ X0) @ X2) @ (k1_tarski @ X0))
% 1.26/1.52          | ~ (v1_relat_1 @ X1)
% 1.26/1.52          | ~ (r2_hidden @ X2 @ (k11_relat_1 @ X1 @ X0)))),
% 1.26/1.52      inference('simplify', [status(thm)], ['3'])).
% 1.26/1.52  thf('5', plain,
% 1.26/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.26/1.52         (((sk_C @ (k11_relat_1 @ X1 @ X0) @ X2) = (X2))
% 1.26/1.52          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ X2))
% 1.26/1.52          | ~ (v1_relat_1 @ X1)
% 1.26/1.52          | (r2_hidden @ 
% 1.26/1.52             (sk_D @ X1 @ (k1_tarski @ X0) @ 
% 1.26/1.52              (sk_C @ (k11_relat_1 @ X1 @ X0) @ X2)) @ 
% 1.26/1.52             (k1_tarski @ X0)))),
% 1.26/1.52      inference('sup-', [status(thm)], ['0', '4'])).
% 1.26/1.52  thf('6', plain,
% 1.26/1.52      (![X0 : $i, X2 : $i, X3 : $i]:
% 1.26/1.52         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 1.26/1.52      inference('cnf', [status(esa)], [d1_tarski])).
% 1.26/1.52  thf('7', plain,
% 1.26/1.52      (![X0 : $i, X3 : $i]:
% 1.26/1.52         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 1.26/1.52      inference('simplify', [status(thm)], ['6'])).
% 1.26/1.52  thf('8', plain,
% 1.26/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.26/1.52         (~ (v1_relat_1 @ X2)
% 1.26/1.52          | ((k11_relat_1 @ X2 @ X0) = (k1_tarski @ X1))
% 1.26/1.52          | ((sk_C @ (k11_relat_1 @ X2 @ X0) @ X1) = (X1))
% 1.26/1.52          | ((sk_D @ X2 @ (k1_tarski @ X0) @ 
% 1.26/1.52              (sk_C @ (k11_relat_1 @ X2 @ X0) @ X1)) = (X0)))),
% 1.26/1.52      inference('sup-', [status(thm)], ['5', '7'])).
% 1.26/1.52  thf('9', plain,
% 1.26/1.52      (![X0 : $i, X4 : $i]:
% 1.26/1.52         (((X4) = (k1_tarski @ X0))
% 1.26/1.52          | ((sk_C @ X4 @ X0) = (X0))
% 1.26/1.52          | (r2_hidden @ (sk_C @ X4 @ X0) @ X4))),
% 1.26/1.52      inference('cnf', [status(esa)], [d1_tarski])).
% 1.26/1.52  thf('10', plain,
% 1.26/1.52      (![X6 : $i, X7 : $i]:
% 1.26/1.52         (((k11_relat_1 @ X6 @ X7) = (k9_relat_1 @ X6 @ (k1_tarski @ X7)))
% 1.26/1.52          | ~ (v1_relat_1 @ X6))),
% 1.26/1.52      inference('cnf', [status(esa)], [d16_relat_1])).
% 1.26/1.52  thf('11', plain,
% 1.26/1.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.26/1.52         (~ (r2_hidden @ X10 @ (k9_relat_1 @ X11 @ X9))
% 1.26/1.52          | (r2_hidden @ (k4_tarski @ (sk_D @ X11 @ X9 @ X10) @ X10) @ X11)
% 1.26/1.52          | ~ (v1_relat_1 @ X11))),
% 1.26/1.52      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.26/1.52  thf('12', plain,
% 1.26/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.26/1.52         (~ (r2_hidden @ X2 @ (k11_relat_1 @ X1 @ X0))
% 1.26/1.52          | ~ (v1_relat_1 @ X1)
% 1.26/1.52          | ~ (v1_relat_1 @ X1)
% 1.26/1.52          | (r2_hidden @ 
% 1.26/1.52             (k4_tarski @ (sk_D @ X1 @ (k1_tarski @ X0) @ X2) @ X2) @ X1))),
% 1.26/1.52      inference('sup-', [status(thm)], ['10', '11'])).
% 1.26/1.52  thf('13', plain,
% 1.26/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.26/1.52         ((r2_hidden @ 
% 1.26/1.52           (k4_tarski @ (sk_D @ X1 @ (k1_tarski @ X0) @ X2) @ X2) @ X1)
% 1.26/1.52          | ~ (v1_relat_1 @ X1)
% 1.26/1.52          | ~ (r2_hidden @ X2 @ (k11_relat_1 @ X1 @ X0)))),
% 1.26/1.52      inference('simplify', [status(thm)], ['12'])).
% 1.26/1.52  thf('14', plain,
% 1.26/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.26/1.52         (((sk_C @ (k11_relat_1 @ X1 @ X0) @ X2) = (X2))
% 1.26/1.52          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ X2))
% 1.26/1.52          | ~ (v1_relat_1 @ X1)
% 1.26/1.52          | (r2_hidden @ 
% 1.26/1.52             (k4_tarski @ 
% 1.26/1.52              (sk_D @ X1 @ (k1_tarski @ X0) @ 
% 1.26/1.52               (sk_C @ (k11_relat_1 @ X1 @ X0) @ X2)) @ 
% 1.26/1.52              (sk_C @ (k11_relat_1 @ X1 @ X0) @ X2)) @ 
% 1.26/1.52             X1))),
% 1.26/1.52      inference('sup-', [status(thm)], ['9', '13'])).
% 1.26/1.52  thf('15', plain,
% 1.26/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.26/1.52         ((r2_hidden @ 
% 1.26/1.52           (k4_tarski @ X0 @ (sk_C @ (k11_relat_1 @ X1 @ X0) @ X2)) @ X1)
% 1.26/1.52          | ((sk_C @ (k11_relat_1 @ X1 @ X0) @ X2) = (X2))
% 1.26/1.52          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ X2))
% 1.26/1.52          | ~ (v1_relat_1 @ X1)
% 1.26/1.52          | ~ (v1_relat_1 @ X1)
% 1.26/1.52          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ X2))
% 1.26/1.52          | ((sk_C @ (k11_relat_1 @ X1 @ X0) @ X2) = (X2)))),
% 1.26/1.52      inference('sup+', [status(thm)], ['8', '14'])).
% 1.26/1.52  thf('16', plain,
% 1.26/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.26/1.52         (~ (v1_relat_1 @ X1)
% 1.26/1.52          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ X2))
% 1.26/1.52          | ((sk_C @ (k11_relat_1 @ X1 @ X0) @ X2) = (X2))
% 1.26/1.52          | (r2_hidden @ 
% 1.26/1.52             (k4_tarski @ X0 @ (sk_C @ (k11_relat_1 @ X1 @ X0) @ X2)) @ X1))),
% 1.26/1.52      inference('simplify', [status(thm)], ['15'])).
% 1.26/1.52  thf(t8_funct_1, axiom,
% 1.26/1.52    (![A:$i,B:$i,C:$i]:
% 1.26/1.52     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.26/1.52       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 1.26/1.52         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 1.26/1.52           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 1.26/1.52  thf('17', plain,
% 1.26/1.52      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.26/1.52         (~ (r2_hidden @ (k4_tarski @ X25 @ X27) @ X26)
% 1.26/1.52          | ((X27) = (k1_funct_1 @ X26 @ X25))
% 1.26/1.52          | ~ (v1_funct_1 @ X26)
% 1.26/1.52          | ~ (v1_relat_1 @ X26))),
% 1.26/1.52      inference('cnf', [status(esa)], [t8_funct_1])).
% 1.26/1.52  thf('18', plain,
% 1.26/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.26/1.52         (((sk_C @ (k11_relat_1 @ X0 @ X2) @ X1) = (X1))
% 1.26/1.52          | ((k11_relat_1 @ X0 @ X2) = (k1_tarski @ X1))
% 1.26/1.52          | ~ (v1_relat_1 @ X0)
% 1.26/1.52          | ~ (v1_relat_1 @ X0)
% 1.26/1.52          | ~ (v1_funct_1 @ X0)
% 1.26/1.52          | ((sk_C @ (k11_relat_1 @ X0 @ X2) @ X1) = (k1_funct_1 @ X0 @ X2)))),
% 1.26/1.52      inference('sup-', [status(thm)], ['16', '17'])).
% 1.26/1.52  thf('19', plain,
% 1.26/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.26/1.52         (((sk_C @ (k11_relat_1 @ X0 @ X2) @ X1) = (k1_funct_1 @ X0 @ X2))
% 1.26/1.52          | ~ (v1_funct_1 @ X0)
% 1.26/1.52          | ~ (v1_relat_1 @ X0)
% 1.26/1.52          | ((k11_relat_1 @ X0 @ X2) = (k1_tarski @ X1))
% 1.26/1.52          | ((sk_C @ (k11_relat_1 @ X0 @ X2) @ X1) = (X1)))),
% 1.26/1.52      inference('simplify', [status(thm)], ['18'])).
% 1.26/1.52  thf('20', plain,
% 1.26/1.52      (![X6 : $i, X7 : $i]:
% 1.26/1.52         (((k11_relat_1 @ X6 @ X7) = (k9_relat_1 @ X6 @ (k1_tarski @ X7)))
% 1.26/1.52          | ~ (v1_relat_1 @ X6))),
% 1.26/1.52      inference('cnf', [status(esa)], [d16_relat_1])).
% 1.26/1.52  thf('21', plain,
% 1.26/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.26/1.52         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 1.26/1.52      inference('cnf', [status(esa)], [d1_tarski])).
% 1.26/1.52  thf('22', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.26/1.52      inference('simplify', [status(thm)], ['21'])).
% 1.26/1.52  thf(t117_funct_1, conjecture,
% 1.26/1.52    (![A:$i,B:$i]:
% 1.26/1.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.26/1.52       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 1.26/1.52         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 1.26/1.52  thf(zf_stmt_0, negated_conjecture,
% 1.26/1.52    (~( ![A:$i,B:$i]:
% 1.26/1.52        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.26/1.52          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 1.26/1.52            ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 1.26/1.52    inference('cnf.neg', [status(esa)], [t117_funct_1])).
% 1.26/1.52  thf('23', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.26/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.52  thf('24', plain,
% 1.26/1.52      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.26/1.52         (~ (r2_hidden @ X25 @ (k1_relat_1 @ X26))
% 1.26/1.52          | ((X27) != (k1_funct_1 @ X26 @ X25))
% 1.26/1.52          | (r2_hidden @ (k4_tarski @ X25 @ X27) @ X26)
% 1.26/1.52          | ~ (v1_funct_1 @ X26)
% 1.26/1.52          | ~ (v1_relat_1 @ X26))),
% 1.26/1.52      inference('cnf', [status(esa)], [t8_funct_1])).
% 1.26/1.52  thf('25', plain,
% 1.26/1.52      (![X25 : $i, X26 : $i]:
% 1.26/1.52         (~ (v1_relat_1 @ X26)
% 1.26/1.52          | ~ (v1_funct_1 @ X26)
% 1.26/1.52          | (r2_hidden @ (k4_tarski @ X25 @ (k1_funct_1 @ X26 @ X25)) @ X26)
% 1.26/1.52          | ~ (r2_hidden @ X25 @ (k1_relat_1 @ X26)))),
% 1.26/1.52      inference('simplify', [status(thm)], ['24'])).
% 1.26/1.52  thf('26', plain,
% 1.26/1.52      (((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 1.26/1.52        | ~ (v1_funct_1 @ sk_B)
% 1.26/1.52        | ~ (v1_relat_1 @ sk_B))),
% 1.26/1.52      inference('sup-', [status(thm)], ['23', '25'])).
% 1.26/1.52  thf('27', plain, ((v1_funct_1 @ sk_B)),
% 1.26/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.52  thf('28', plain, ((v1_relat_1 @ sk_B)),
% 1.26/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.52  thf('29', plain,
% 1.26/1.52      ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)),
% 1.26/1.52      inference('demod', [status(thm)], ['26', '27', '28'])).
% 1.26/1.52  thf('30', plain,
% 1.26/1.52      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.26/1.52         (~ (r2_hidden @ X8 @ X9)
% 1.26/1.52          | ~ (r2_hidden @ (k4_tarski @ X8 @ X10) @ X11)
% 1.26/1.52          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ X11))
% 1.26/1.52          | (r2_hidden @ X10 @ (k9_relat_1 @ X11 @ X9))
% 1.26/1.52          | ~ (v1_relat_1 @ X11))),
% 1.26/1.52      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.26/1.52  thf('31', plain,
% 1.26/1.52      (![X0 : $i]:
% 1.26/1.52         (~ (v1_relat_1 @ sk_B)
% 1.26/1.52          | (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ X0))
% 1.26/1.52          | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))
% 1.26/1.52          | ~ (r2_hidden @ sk_A @ X0))),
% 1.26/1.52      inference('sup-', [status(thm)], ['29', '30'])).
% 1.26/1.52  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 1.26/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.52  thf('33', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.26/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.52  thf('34', plain,
% 1.26/1.52      (![X0 : $i]:
% 1.26/1.52         ((r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ X0))
% 1.26/1.52          | ~ (r2_hidden @ sk_A @ X0))),
% 1.26/1.52      inference('demod', [status(thm)], ['31', '32', '33'])).
% 1.26/1.52  thf('35', plain,
% 1.26/1.52      ((r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 1.26/1.52        (k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)))),
% 1.26/1.52      inference('sup-', [status(thm)], ['22', '34'])).
% 1.26/1.52  thf('36', plain,
% 1.26/1.52      (((r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k11_relat_1 @ sk_B @ sk_A))
% 1.26/1.52        | ~ (v1_relat_1 @ sk_B))),
% 1.26/1.52      inference('sup+', [status(thm)], ['20', '35'])).
% 1.26/1.52  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 1.26/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.52  thf('38', plain,
% 1.26/1.52      ((r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k11_relat_1 @ sk_B @ sk_A))),
% 1.26/1.52      inference('demod', [status(thm)], ['36', '37'])).
% 1.26/1.52  thf('39', plain,
% 1.26/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.26/1.52         (((sk_C @ (k11_relat_1 @ X0 @ X2) @ X1) = (k1_funct_1 @ X0 @ X2))
% 1.26/1.52          | ~ (v1_funct_1 @ X0)
% 1.26/1.52          | ~ (v1_relat_1 @ X0)
% 1.26/1.52          | ((k11_relat_1 @ X0 @ X2) = (k1_tarski @ X1))
% 1.26/1.52          | ((sk_C @ (k11_relat_1 @ X0 @ X2) @ X1) = (X1)))),
% 1.26/1.52      inference('simplify', [status(thm)], ['18'])).
% 1.26/1.52  thf('40', plain,
% 1.26/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.26/1.52         (((k1_funct_1 @ X1 @ X0) != (X2))
% 1.26/1.52          | ((sk_C @ (k11_relat_1 @ X1 @ X0) @ X2) = (X2))
% 1.26/1.52          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ X2))
% 1.26/1.52          | ~ (v1_relat_1 @ X1)
% 1.26/1.52          | ~ (v1_funct_1 @ X1))),
% 1.26/1.52      inference('eq_fact', [status(thm)], ['39'])).
% 1.26/1.52  thf('41', plain,
% 1.26/1.52      (![X0 : $i, X1 : $i]:
% 1.26/1.52         (~ (v1_funct_1 @ X1)
% 1.26/1.52          | ~ (v1_relat_1 @ X1)
% 1.26/1.52          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ (k1_funct_1 @ X1 @ X0)))
% 1.26/1.52          | ((sk_C @ (k11_relat_1 @ X1 @ X0) @ (k1_funct_1 @ X1 @ X0))
% 1.26/1.52              = (k1_funct_1 @ X1 @ X0)))),
% 1.26/1.52      inference('simplify', [status(thm)], ['40'])).
% 1.26/1.52  thf('42', plain,
% 1.26/1.52      (![X0 : $i, X4 : $i]:
% 1.26/1.52         (((X4) = (k1_tarski @ X0))
% 1.26/1.52          | ((sk_C @ X4 @ X0) != (X0))
% 1.26/1.52          | ~ (r2_hidden @ (sk_C @ X4 @ X0) @ X4))),
% 1.26/1.52      inference('cnf', [status(esa)], [d1_tarski])).
% 1.26/1.52  thf('43', plain,
% 1.26/1.52      (![X0 : $i, X1 : $i]:
% 1.26/1.52         (~ (r2_hidden @ (k1_funct_1 @ X1 @ X0) @ (k11_relat_1 @ X1 @ X0))
% 1.26/1.52          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ (k1_funct_1 @ X1 @ X0)))
% 1.26/1.52          | ~ (v1_relat_1 @ X1)
% 1.26/1.52          | ~ (v1_funct_1 @ X1)
% 1.26/1.52          | ((sk_C @ (k11_relat_1 @ X1 @ X0) @ (k1_funct_1 @ X1 @ X0))
% 1.26/1.52              != (k1_funct_1 @ X1 @ X0))
% 1.26/1.52          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ (k1_funct_1 @ X1 @ X0))))),
% 1.26/1.52      inference('sup-', [status(thm)], ['41', '42'])).
% 1.26/1.52  thf('44', plain,
% 1.26/1.52      (![X0 : $i, X1 : $i]:
% 1.26/1.52         (((sk_C @ (k11_relat_1 @ X1 @ X0) @ (k1_funct_1 @ X1 @ X0))
% 1.26/1.52            != (k1_funct_1 @ X1 @ X0))
% 1.26/1.52          | ~ (v1_funct_1 @ X1)
% 1.26/1.52          | ~ (v1_relat_1 @ X1)
% 1.26/1.52          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ (k1_funct_1 @ X1 @ X0)))
% 1.26/1.52          | ~ (r2_hidden @ (k1_funct_1 @ X1 @ X0) @ (k11_relat_1 @ X1 @ X0)))),
% 1.26/1.52      inference('simplify', [status(thm)], ['43'])).
% 1.26/1.52  thf('45', plain,
% 1.26/1.52      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 1.26/1.52        | ~ (v1_relat_1 @ sk_B)
% 1.26/1.52        | ~ (v1_funct_1 @ sk_B)
% 1.26/1.52        | ((sk_C @ (k11_relat_1 @ sk_B @ sk_A) @ (k1_funct_1 @ sk_B @ sk_A))
% 1.26/1.52            != (k1_funct_1 @ sk_B @ sk_A)))),
% 1.26/1.52      inference('sup-', [status(thm)], ['38', '44'])).
% 1.26/1.52  thf('46', plain, ((v1_relat_1 @ sk_B)),
% 1.26/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.52  thf('47', plain, ((v1_funct_1 @ sk_B)),
% 1.26/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.52  thf('48', plain,
% 1.26/1.52      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 1.26/1.52        | ((sk_C @ (k11_relat_1 @ sk_B @ sk_A) @ (k1_funct_1 @ sk_B @ sk_A))
% 1.26/1.52            != (k1_funct_1 @ sk_B @ sk_A)))),
% 1.26/1.52      inference('demod', [status(thm)], ['45', '46', '47'])).
% 1.26/1.52  thf('49', plain,
% 1.26/1.52      (((k11_relat_1 @ sk_B @ sk_A) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 1.26/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.52  thf('50', plain,
% 1.26/1.52      (((sk_C @ (k11_relat_1 @ sk_B @ sk_A) @ (k1_funct_1 @ sk_B @ sk_A))
% 1.26/1.52         != (k1_funct_1 @ sk_B @ sk_A))),
% 1.26/1.52      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 1.26/1.52  thf('51', plain,
% 1.26/1.52      ((((k1_funct_1 @ sk_B @ sk_A) != (k1_funct_1 @ sk_B @ sk_A))
% 1.26/1.52        | ((sk_C @ (k11_relat_1 @ sk_B @ sk_A) @ (k1_funct_1 @ sk_B @ sk_A))
% 1.26/1.52            = (k1_funct_1 @ sk_B @ sk_A))
% 1.26/1.52        | ((k11_relat_1 @ sk_B @ sk_A)
% 1.26/1.52            = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 1.26/1.52        | ~ (v1_relat_1 @ sk_B)
% 1.26/1.52        | ~ (v1_funct_1 @ sk_B))),
% 1.26/1.52      inference('sup-', [status(thm)], ['19', '50'])).
% 1.26/1.52  thf('52', plain, ((v1_relat_1 @ sk_B)),
% 1.26/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.52  thf('53', plain, ((v1_funct_1 @ sk_B)),
% 1.26/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.52  thf('54', plain,
% 1.26/1.52      ((((k1_funct_1 @ sk_B @ sk_A) != (k1_funct_1 @ sk_B @ sk_A))
% 1.26/1.52        | ((sk_C @ (k11_relat_1 @ sk_B @ sk_A) @ (k1_funct_1 @ sk_B @ sk_A))
% 1.26/1.52            = (k1_funct_1 @ sk_B @ sk_A))
% 1.26/1.52        | ((k11_relat_1 @ sk_B @ sk_A)
% 1.26/1.52            = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 1.26/1.52      inference('demod', [status(thm)], ['51', '52', '53'])).
% 1.26/1.52  thf('55', plain,
% 1.26/1.52      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 1.26/1.52        | ((sk_C @ (k11_relat_1 @ sk_B @ sk_A) @ (k1_funct_1 @ sk_B @ sk_A))
% 1.26/1.52            = (k1_funct_1 @ sk_B @ sk_A)))),
% 1.26/1.52      inference('simplify', [status(thm)], ['54'])).
% 1.26/1.52  thf('56', plain,
% 1.26/1.52      (((sk_C @ (k11_relat_1 @ sk_B @ sk_A) @ (k1_funct_1 @ sk_B @ sk_A))
% 1.26/1.52         != (k1_funct_1 @ sk_B @ sk_A))),
% 1.26/1.52      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 1.26/1.52  thf('57', plain,
% 1.26/1.52      (((k11_relat_1 @ sk_B @ sk_A) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 1.26/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.52  thf('58', plain, ($false),
% 1.26/1.52      inference('simplify_reflect-', [status(thm)], ['55', '56', '57'])).
% 1.26/1.52  
% 1.26/1.52  % SZS output end Refutation
% 1.26/1.52  
% 1.26/1.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
