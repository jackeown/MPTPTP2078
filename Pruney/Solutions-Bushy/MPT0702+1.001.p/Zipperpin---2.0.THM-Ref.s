%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0702+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Y2Lre9klcn

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:21 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 199 expanded)
%              Number of leaves         :   21 (  67 expanded)
%              Depth                    :   24
%              Number of atoms          :  790 (2576 expanded)
%              Number of equality atoms :   23 (  39 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t157_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( v2_funct_1 @ C ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
            & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
            & ( v2_funct_1 @ C ) )
         => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t157_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ X16 )
      | ( r2_hidden @ ( sk_C @ X16 @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ X16 )
      | ( r2_hidden @ ( sk_C @ X16 @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X15 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

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

thf('7',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X4 ) )
      | ~ ( r2_hidden @ X1 @ X3 )
      | ( X2
       != ( k1_funct_1 @ X4 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X1 @ X3 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X4 ) )
      | ( zip_tseitin_0 @ X1 @ ( k1_funct_1 @ X4 @ X1 ) @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( zip_tseitin_0 @ ( sk_C @ X0 @ sk_A ) @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_A ) ) @ X1 @ sk_C_2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( zip_tseitin_0 @ ( sk_C @ X0 @ sk_A ) @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_A ) ) @ sk_A @ sk_C_2 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_C @ X0 @ sk_A ) @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_A ) ) @ sk_A @ sk_C_2 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

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

thf('12',plain,(
    ! [X6: $i,X7: $i,X9: $i,X11: $i,X12: $i] :
      ( ( X9
       != ( k9_relat_1 @ X7 @ X6 ) )
      | ( r2_hidden @ X11 @ X9 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X6 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('13',plain,(
    ! [X6: $i,X7: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X6 @ X7 )
      | ( r2_hidden @ X11 @ ( k9_relat_1 @ X7 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_A ) ) @ ( k9_relat_1 @ sk_C_2 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_A ) ) @ ( k9_relat_1 @ sk_C_2 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C_2 @ sk_A ) @ ( k9_relat_1 @ sk_C_2 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X15 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_C_2 @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_C_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_A ) ) @ ( k9_relat_1 @ sk_C_2 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X6: $i,X7: $i,X9: $i,X10: $i] :
      ( ( X9
       != ( k9_relat_1 @ X7 @ X6 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X10 @ X6 @ X7 ) @ X10 @ X6 @ X7 )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('23',plain,(
    ! [X6: $i,X7: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k9_relat_1 @ X7 @ X6 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X10 @ X6 @ X7 ) @ X10 @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_A ) ) @ sk_B_1 @ sk_C_2 ) @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_A ) ) @ sk_B_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_A ) ) @ sk_B_1 @ sk_C_2 ) @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_A ) ) @ sk_B_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X2
        = ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_A ) )
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E_1 @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_A ) ) @ sk_B_1 @ sk_C_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_A ) ) @ sk_B_1 @ sk_C_2 ) @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_A ) ) @ sk_B_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_E_1 @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_A ) ) @ sk_B_1 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

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

thf('33',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ X17 ) )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X17 ) )
      | ( ( k1_funct_1 @ X17 @ X18 )
       != ( k1_funct_1 @ X17 @ X19 ) )
      | ( X18 = X19 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( ( sk_E_1 @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_A ) ) @ sk_B_1 @ sk_C_2 )
        = X1 )
      | ( ( k1_funct_1 @ sk_C_2 @ ( sk_E_1 @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_A ) ) @ sk_B_1 @ sk_C_2 ) )
       != ( k1_funct_1 @ sk_C_2 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( v2_funct_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( ( sk_E_1 @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_A ) ) @ sk_B_1 @ sk_C_2 )
        = X1 )
      | ( ( k1_funct_1 @ sk_C_2 @ ( sk_E_1 @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_A ) ) @ sk_B_1 @ sk_C_2 ) )
       != ( k1_funct_1 @ sk_C_2 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_A ) )
       != ( k1_funct_1 @ sk_C_2 @ X1 ) )
      | ( r1_tarski @ sk_A @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_E_1 @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_A ) ) @ sk_B_1 @ sk_C_2 )
        = X1 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_E_1 @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_A ) ) @ sk_B_1 @ sk_C_2 )
        = X1 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( r1_tarski @ sk_A @ X0 )
      | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_A ) )
       != ( k1_funct_1 @ sk_C_2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_E_1 @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_A ) ) @ sk_B_1 @ sk_C_2 )
        = ( sk_C @ X0 @ sk_A ) ) ) ),
    inference(eq_res,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( sk_E_1 @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_A ) ) @ sk_B_1 @ sk_C_2 )
        = ( sk_C @ X0 @ sk_A ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_A ) ) @ sk_B_1 @ sk_C_2 ) @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_A ) ) @ sk_B_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ X3 )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_E_1 @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ X0 @ sk_A ) ) @ sk_B_1 @ sk_C_2 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ X16 )
      | ~ ( r2_hidden @ ( sk_C @ X16 @ X14 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('50',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
    | ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['0','51'])).


%------------------------------------------------------------------------------
