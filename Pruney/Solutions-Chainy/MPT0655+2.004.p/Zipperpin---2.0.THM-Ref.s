%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XUElVpD2vj

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 102 expanded)
%              Number of leaves         :   17 (  37 expanded)
%              Depth                    :   25
%              Number of atoms          :  828 (1158 expanded)
%              Number of equality atoms :   27 (  37 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('1',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('2',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('3',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

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

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_B @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_B @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t57_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_relat_1 @ X5 ) )
      | ( X6
        = ( k1_funct_1 @ X5 @ ( k1_funct_1 @ ( k2_funct_1 @ X5 ) @ X6 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t57_funct_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_B @ ( k2_funct_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( sk_B @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ ( k2_funct_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( sk_B @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('15',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_C @ X0 ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('17',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('18',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('19',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_relat_1 @ X5 ) )
      | ( X6
        = ( k1_funct_1 @ X5 @ ( k1_funct_1 @ ( k2_funct_1 @ X5 ) @ X6 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t57_funct_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_C @ ( k2_funct_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( sk_C @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k2_funct_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( sk_C @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k2_funct_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( sk_B @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( sk_C @ ( k2_funct_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( sk_B @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_C @ ( k2_funct_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( sk_B @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( sk_C @ ( k2_funct_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( sk_B @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_C @ ( k2_funct_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( sk_B @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( sk_C @ ( k2_funct_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( sk_B @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k2_funct_1 @ X0 ) )
        = ( sk_B @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( sk_C @ ( k2_funct_1 @ X0 ) )
        = ( sk_B @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf(t62_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v2_funct_1 @ A )
         => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_funct_1])).

thf('37',plain,(
    ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( sk_C @ ( k2_funct_1 @ sk_A ) )
      = ( sk_B @ ( k2_funct_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( sk_C @ ( k2_funct_1 @ sk_A ) )
    = ( sk_B @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != ( sk_C @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('44',plain,
    ( ( ( sk_B @ ( k2_funct_1 @ sk_A ) )
     != ( sk_B @ ( k2_funct_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['52','53','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XUElVpD2vj
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:42:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 40 iterations in 0.036s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.49  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.49  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i > $i).
% 0.21/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.49  thf(dt_k2_funct_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.49       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.21/0.49         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (![X3 : $i]:
% 0.21/0.49         ((v1_funct_1 @ (k2_funct_1 @ X3))
% 0.21/0.49          | ~ (v1_funct_1 @ X3)
% 0.21/0.49          | ~ (v1_relat_1 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X3 : $i]:
% 0.21/0.49         ((v1_relat_1 @ (k2_funct_1 @ X3))
% 0.21/0.49          | ~ (v1_funct_1 @ X3)
% 0.21/0.49          | ~ (v1_relat_1 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X3 : $i]:
% 0.21/0.49         ((v1_funct_1 @ (k2_funct_1 @ X3))
% 0.21/0.49          | ~ (v1_funct_1 @ X3)
% 0.21/0.49          | ~ (v1_relat_1 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X3 : $i]:
% 0.21/0.49         ((v1_relat_1 @ (k2_funct_1 @ X3))
% 0.21/0.49          | ~ (v1_funct_1 @ X3)
% 0.21/0.49          | ~ (v1_relat_1 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.49  thf(t55_funct_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.49       ( ( v2_funct_1 @ A ) =>
% 0.21/0.49         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.21/0.49           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X4 : $i]:
% 0.21/0.49         (~ (v2_funct_1 @ X4)
% 0.21/0.49          | ((k2_relat_1 @ X4) = (k1_relat_1 @ (k2_funct_1 @ X4)))
% 0.21/0.49          | ~ (v1_funct_1 @ X4)
% 0.21/0.49          | ~ (v1_relat_1 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.21/0.49  thf(d8_funct_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.49       ( ( v2_funct_1 @ A ) <=>
% 0.21/0.49         ( ![B:$i,C:$i]:
% 0.21/0.49           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.49               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.49               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.21/0.49             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ (sk_B @ X0) @ (k1_relat_1 @ X0))
% 0.21/0.49          | (v2_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ (sk_B @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v2_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | ~ (v2_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | (r2_hidden @ (sk_B @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '6'])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ (sk_B @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 0.21/0.49          | ~ (v2_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | ~ (v2_funct_1 @ X0)
% 0.21/0.49          | (r2_hidden @ (sk_B @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '8'])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ (sk_B @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 0.21/0.49          | ~ (v2_funct_1 @ X0)
% 0.21/0.49          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.49  thf(t57_funct_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.49       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.21/0.49         ( ( ( A ) =
% 0.21/0.49             ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.21/0.49           ( ( A ) =
% 0.21/0.49             ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ))).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i]:
% 0.21/0.49         (~ (v2_funct_1 @ X5)
% 0.21/0.49          | ~ (r2_hidden @ X6 @ (k2_relat_1 @ X5))
% 0.21/0.49          | ((X6) = (k1_funct_1 @ X5 @ (k1_funct_1 @ (k2_funct_1 @ X5) @ X6)))
% 0.21/0.49          | ~ (v1_funct_1 @ X5)
% 0.21/0.49          | ~ (v1_relat_1 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [t57_funct_1])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | ~ (v2_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ((sk_B @ (k2_funct_1 @ X0))
% 0.21/0.49              = (k1_funct_1 @ X0 @ 
% 0.21/0.49                 (k1_funct_1 @ (k2_funct_1 @ X0) @ (sk_B @ (k2_funct_1 @ X0)))))
% 0.21/0.49          | ~ (v2_funct_1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((sk_B @ (k2_funct_1 @ X0))
% 0.21/0.49            = (k1_funct_1 @ X0 @ 
% 0.21/0.49               (k1_funct_1 @ (k2_funct_1 @ X0) @ (sk_B @ (k2_funct_1 @ X0)))))
% 0.21/0.49          | ~ (v2_funct_1 @ X0)
% 0.21/0.49          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X3 : $i]:
% 0.21/0.49         ((v1_relat_1 @ (k2_funct_1 @ X3))
% 0.21/0.49          | ~ (v1_funct_1 @ X3)
% 0.21/0.49          | ~ (v1_relat_1 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X3 : $i]:
% 0.21/0.49         ((v1_funct_1 @ (k2_funct_1 @ X3))
% 0.21/0.49          | ~ (v1_funct_1 @ X3)
% 0.21/0.49          | ~ (v1_relat_1 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k1_funct_1 @ X0 @ (sk_B @ X0)) = (k1_funct_1 @ X0 @ (sk_C @ X0)))
% 0.21/0.49          | (v2_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X3 : $i]:
% 0.21/0.49         ((v1_funct_1 @ (k2_funct_1 @ X3))
% 0.21/0.49          | ~ (v1_funct_1 @ X3)
% 0.21/0.49          | ~ (v1_relat_1 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X3 : $i]:
% 0.21/0.49         ((v1_relat_1 @ (k2_funct_1 @ X3))
% 0.21/0.49          | ~ (v1_funct_1 @ X3)
% 0.21/0.49          | ~ (v1_relat_1 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X4 : $i]:
% 0.21/0.49         (~ (v2_funct_1 @ X4)
% 0.21/0.49          | ((k2_relat_1 @ X4) = (k1_relat_1 @ (k2_funct_1 @ X4)))
% 0.21/0.49          | ~ (v1_funct_1 @ X4)
% 0.21/0.49          | ~ (v1_relat_1 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ (sk_C @ X0) @ (k1_relat_1 @ X0))
% 0.21/0.49          | (v2_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ (sk_C @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v2_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | ~ (v2_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | (r2_hidden @ (sk_C @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '21'])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ (sk_C @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 0.21/0.49          | ~ (v2_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | ~ (v2_funct_1 @ X0)
% 0.21/0.49          | (r2_hidden @ (sk_C @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['17', '23'])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ (sk_C @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 0.21/0.49          | ~ (v2_funct_1 @ X0)
% 0.21/0.49          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i]:
% 0.21/0.49         (~ (v2_funct_1 @ X5)
% 0.21/0.49          | ~ (r2_hidden @ X6 @ (k2_relat_1 @ X5))
% 0.21/0.49          | ((X6) = (k1_funct_1 @ X5 @ (k1_funct_1 @ (k2_funct_1 @ X5) @ X6)))
% 0.21/0.49          | ~ (v1_funct_1 @ X5)
% 0.21/0.49          | ~ (v1_relat_1 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [t57_funct_1])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | ~ (v2_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ((sk_C @ (k2_funct_1 @ X0))
% 0.21/0.49              = (k1_funct_1 @ X0 @ 
% 0.21/0.49                 (k1_funct_1 @ (k2_funct_1 @ X0) @ (sk_C @ (k2_funct_1 @ X0)))))
% 0.21/0.49          | ~ (v2_funct_1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((sk_C @ (k2_funct_1 @ X0))
% 0.21/0.49            = (k1_funct_1 @ X0 @ 
% 0.21/0.49               (k1_funct_1 @ (k2_funct_1 @ X0) @ (sk_C @ (k2_funct_1 @ X0)))))
% 0.21/0.49          | ~ (v2_funct_1 @ X0)
% 0.21/0.49          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((sk_C @ (k2_funct_1 @ X0))
% 0.21/0.49            = (k1_funct_1 @ X0 @ 
% 0.21/0.49               (k1_funct_1 @ (k2_funct_1 @ X0) @ (sk_B @ (k2_funct_1 @ X0)))))
% 0.21/0.49          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | ~ (v2_funct_1 @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['16', '28'])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v2_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | ((sk_C @ (k2_funct_1 @ X0))
% 0.21/0.49              = (k1_funct_1 @ X0 @ 
% 0.21/0.49                 (k1_funct_1 @ (k2_funct_1 @ X0) @ (sk_B @ (k2_funct_1 @ X0))))))),
% 0.21/0.49      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ((sk_C @ (k2_funct_1 @ X0))
% 0.21/0.49              = (k1_funct_1 @ X0 @ 
% 0.21/0.49                 (k1_funct_1 @ (k2_funct_1 @ X0) @ (sk_B @ (k2_funct_1 @ X0)))))
% 0.21/0.49          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v2_funct_1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['15', '30'])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v2_funct_1 @ X0)
% 0.21/0.49          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | ((sk_C @ (k2_funct_1 @ X0))
% 0.21/0.49              = (k1_funct_1 @ X0 @ 
% 0.21/0.49                 (k1_funct_1 @ (k2_funct_1 @ X0) @ (sk_B @ (k2_funct_1 @ X0)))))
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['31'])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ((sk_C @ (k2_funct_1 @ X0))
% 0.21/0.49              = (k1_funct_1 @ X0 @ 
% 0.21/0.49                 (k1_funct_1 @ (k2_funct_1 @ X0) @ (sk_B @ (k2_funct_1 @ X0)))))
% 0.21/0.49          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | ~ (v2_funct_1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['14', '32'])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v2_funct_1 @ X0)
% 0.21/0.49          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | ((sk_C @ (k2_funct_1 @ X0))
% 0.21/0.49              = (k1_funct_1 @ X0 @ 
% 0.21/0.49                 (k1_funct_1 @ (k2_funct_1 @ X0) @ (sk_B @ (k2_funct_1 @ X0)))))
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['33'])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((sk_C @ (k2_funct_1 @ X0)) = (sk_B @ (k2_funct_1 @ X0)))
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | ~ (v2_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | ~ (v2_funct_1 @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['13', '34'])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v2_funct_1 @ X0)
% 0.21/0.49          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ((sk_C @ (k2_funct_1 @ X0)) = (sk_B @ (k2_funct_1 @ X0))))),
% 0.21/0.49      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.49  thf(t62_funct_1, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.49       ( ( v2_funct_1 @ A ) => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.49          ( ( v2_funct_1 @ A ) => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t62_funct_1])).
% 0.21/0.49  thf('37', plain, (~ (v2_funct_1 @ (k2_funct_1 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      ((((sk_C @ (k2_funct_1 @ sk_A)) = (sk_B @ (k2_funct_1 @ sk_A)))
% 0.21/0.49        | ~ (v1_relat_1 @ sk_A)
% 0.21/0.49        | ~ (v1_funct_1 @ sk_A)
% 0.21/0.49        | ~ (v2_funct_1 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.49  thf('39', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('40', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('41', plain, ((v2_funct_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      (((sk_C @ (k2_funct_1 @ sk_A)) = (sk_B @ (k2_funct_1 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((sk_B @ X0) != (sk_C @ X0))
% 0.21/0.49          | (v2_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      ((((sk_B @ (k2_funct_1 @ sk_A)) != (sk_B @ (k2_funct_1 @ sk_A)))
% 0.21/0.49        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.21/0.49        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.21/0.49        | (v2_funct_1 @ (k2_funct_1 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (((v2_funct_1 @ (k2_funct_1 @ sk_A))
% 0.21/0.49        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.21/0.49        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.49  thf('46', plain, (~ (v2_funct_1 @ (k2_funct_1 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('47', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.21/0.49        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A)))),
% 0.21/0.49      inference('clc', [status(thm)], ['45', '46'])).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.49        | ~ (v1_funct_1 @ sk_A)
% 0.21/0.49        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '47'])).
% 0.21/0.49  thf('49', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('50', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('51', plain, (~ (v1_funct_1 @ (k2_funct_1 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.21/0.49  thf('52', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_funct_1 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '51'])).
% 0.21/0.49  thf('53', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('54', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('55', plain, ($false),
% 0.21/0.49      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
