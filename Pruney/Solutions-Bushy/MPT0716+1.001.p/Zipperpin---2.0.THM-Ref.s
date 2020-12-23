%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0716+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dHunyd96wE

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:22 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 203 expanded)
%              Number of leaves         :   21 (  68 expanded)
%              Depth                    :   18
%              Number of atoms          : 1308 (3087 expanded)
%              Number of equality atoms :    9 (  14 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t171_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ! [C: $i] :
              ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) )
            <=> ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) )
                & ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ! [C: $i] :
                ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) )
              <=> ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) )
                  & ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t171_funct_1])).

thf('0',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ X16 )
      | ( r2_hidden @ ( sk_C @ X16 @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X15 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
        | ~ ( r2_hidden @ X0 @ sk_C_1 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

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

thf('7',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ ( k5_relat_1 @ X17 @ X19 ) ) )
      | ( r2_hidden @ X18 @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('8',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ~ ( v1_relat_1 @ sk_B )
        | ~ ( v1_funct_1 @ sk_B )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_A ) )
        | ~ ( v1_funct_1 @ sk_A )
        | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['8','9','10','11','12'])).

thf('14',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ X16 )
      | ~ ( r2_hidden @ ( sk_C @ X16 @ X14 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,
    ( ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
      | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
   <= ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['17'])).

thf('21',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ X16 )
      | ( r2_hidden @ ( sk_C @ X16 @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ X16 )
      | ( r2_hidden @ ( sk_C @ X16 @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X15 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ sk_C_1 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf(d12_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_funct_1 @ A )
        & ( v1_relat_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) )
                  & ( r2_hidden @ E @ B )
                  & ( D
                    = ( k1_funct_1 @ A @ E ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( D
          = ( k1_funct_1 @ A @ E ) )
        & ( r2_hidden @ E @ B )
        & ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ) )).

thf('27',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X4 ) )
      | ~ ( r2_hidden @ X1 @ X3 )
      | ( X2
       != ( k1_funct_1 @ X4 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('28',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X1 @ X3 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X4 ) )
      | ( zip_tseitin_0 @ X1 @ ( k1_funct_1 @ X4 @ X1 ) @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ( zip_tseitin_0 @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_C_1 ) ) @ X1 @ sk_A )
        | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X1 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ( zip_tseitin_0 @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_C_1 ) ) @ sk_C_1 @ sk_A )
        | ( r1_tarski @ sk_C_1 @ X0 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_C_1 ) ) @ sk_C_1 @ sk_A )
        | ( r1_tarski @ sk_C_1 @ X0 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) )).

thf('32',plain,(
    ! [X6: $i,X7: $i,X9: $i,X11: $i,X12: $i] :
      ( ( X9
       != ( k9_relat_1 @ X7 @ X6 ) )
      | ( r2_hidden @ X11 @ X9 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X6 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('33',plain,(
    ! [X6: $i,X7: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X6 @ X7 )
      | ( r2_hidden @ X11 @ ( k9_relat_1 @ X7 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_C_1 ) ) @ ( k9_relat_1 @ sk_A @ sk_C_1 ) )
        | ~ ( v1_funct_1 @ sk_A )
        | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_C_1 ) ) @ ( k9_relat_1 @ sk_A @ sk_C_1 ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
    | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X15 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_A @ sk_C_1 ) ) )
   <= ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_C_1 ) ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
      & ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','41'])).

thf('43',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ X17 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X17 @ X18 ) @ ( k1_relat_1 @ X19 ) )
      | ( r2_hidden @ X18 @ ( k1_relat_1 @ ( k5_relat_1 @ X17 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ~ ( v1_relat_1 @ sk_B )
        | ~ ( v1_funct_1 @ sk_B )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
        | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_A ) )
        | ~ ( v1_funct_1 @ sk_A )
        | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
      & ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
        | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_A ) ) )
   <= ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
      & ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['44','45','46','47','48'])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
        | ( r1_tarski @ sk_C_1 @ X0 ) )
   <= ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
      & ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ X16 )
      | ~ ( r2_hidden @ ( sk_C @ X16 @ X14 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('53',plain,
    ( ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
      | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
      & ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
      & ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['17'])).

thf('56',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['38'])).

thf('58',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ X16 )
      | ( r2_hidden @ ( sk_C @ X16 @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('59',plain,(
    ! [X6: $i,X7: $i,X9: $i,X10: $i] :
      ( ( X9
       != ( k9_relat_1 @ X7 @ X6 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X10 @ X6 @ X7 ) @ X10 @ X6 @ X7 )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('60',plain,(
    ! [X6: $i,X7: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k9_relat_1 @ X7 @ X6 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X10 @ X6 @ X7 ) @ X10 @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_C @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X2
        = ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ X2 )
      | ( ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) )
        = ( k1_funct_1 @ X0 @ ( sk_E_1 @ ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) ) @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_C @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ X3 )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
        | ~ ( r2_hidden @ X0 @ sk_C_1 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('68',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_C_1 ) @ X1 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 )
        | ( r2_hidden @ ( sk_E_1 @ ( sk_C @ X1 @ ( k9_relat_1 @ X0 @ sk_C_1 ) ) @ sk_C_1 @ X0 ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ ( k5_relat_1 @ X17 @ X19 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X17 @ X18 ) @ ( k1_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('70',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_C_1 ) @ X1 )
        | ~ ( v1_relat_1 @ sk_B )
        | ~ ( v1_funct_1 @ sk_B )
        | ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_E_1 @ ( sk_C @ X1 @ ( k9_relat_1 @ X0 @ sk_C_1 ) ) @ sk_C_1 @ X0 ) ) @ ( k1_relat_1 @ sk_B ) )
        | ~ ( v1_funct_1 @ sk_A )
        | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_C_1 ) @ X1 )
        | ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_E_1 @ ( sk_C @ X1 @ ( k9_relat_1 @ X0 @ sk_C_1 ) ) @ sk_C_1 @ X0 ) ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['70','71','72','73','74'])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ X0 @ ( k9_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ sk_B ) )
        | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ X0 )
        | ~ ( v1_funct_1 @ sk_A )
        | ~ ( v1_relat_1 @ sk_A )
        | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ X0 )
        | ~ ( v1_funct_1 @ sk_A )
        | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['63','75'])).

thf('77',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ X0 @ ( k9_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ sk_B ) )
        | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ X0 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['76','77','78','79','80'])).

thf('82',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k9_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ X16 )
      | ~ ( r2_hidden @ ( sk_C @ X16 @ X14 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('84',plain,
    ( ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
      | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['17'])).

thf('87',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','19','20','56','57','87'])).


%------------------------------------------------------------------------------
