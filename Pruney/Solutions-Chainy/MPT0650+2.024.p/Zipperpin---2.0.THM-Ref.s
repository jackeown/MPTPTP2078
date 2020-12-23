%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.b84C0ruTpw

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 160 expanded)
%              Number of leaves         :   28 (  59 expanded)
%              Depth                    :   18
%              Number of atoms          :  934 (2365 expanded)
%              Number of equality atoms :   58 ( 153 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('1',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t54_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_funct_1 @ A )
        & ( v1_relat_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ! [B: $i] :
            ( ( ( v1_funct_1 @ B )
              & ( v1_relat_1 @ B ) )
           => ( ( B
                = ( k2_funct_1 @ A ) )
            <=> ( ! [C: $i,D: $i] :
                    ( ( ( ( D
                          = ( k1_funct_1 @ B @ C ) )
                        & ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) )
                     => ( ( C
                          = ( k1_funct_1 @ A @ D ) )
                        & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) )
                    & ( ( ( C
                          = ( k1_funct_1 @ A @ D ) )
                        & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) )
                     => ( ( D
                          = ( k1_funct_1 @ B @ C ) )
                        & ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) ) )
                & ( ( k1_relat_1 @ B )
                  = ( k2_relat_1 @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_3 @ D @ C @ B @ A )
    <=> ( ( zip_tseitin_2 @ D @ C @ A )
       => ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) )
          & ( D
            = ( k1_funct_1 @ B @ C ) ) ) ) ) )).

thf(zf_stmt_2,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_2 @ D @ C @ A )
    <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
        & ( C
          = ( k1_funct_1 @ A @ D ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ D @ C @ B @ A )
    <=> ( ( zip_tseitin_0 @ D @ C @ B @ A )
       => ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
          & ( C
            = ( k1_funct_1 @ A @ D ) ) ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B @ A )
    <=> ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) )
        & ( D
          = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf(zf_stmt_8,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ( ( B
                = ( k2_funct_1 @ A ) )
            <=> ( ( ( k1_relat_1 @ B )
                  = ( k2_relat_1 @ A ) )
                & ! [C: $i,D: $i] :
                    ( ( zip_tseitin_3 @ D @ C @ B @ A )
                    & ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( X24
       != ( k2_funct_1 @ X23 ) )
      | ( zip_tseitin_1 @ X25 @ X26 @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('3',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( zip_tseitin_1 @ X25 @ X26 @ ( k2_funct_1 @ X23 ) @ X23 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v2_funct_1 @ X23 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( zip_tseitin_1 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_1 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t57_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )).

thf(zf_stmt_9,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( v2_funct_1 @ B )
            & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) )
         => ( ( A
              = ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) )
            & ( A
              = ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t57_funct_1])).

thf('8',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('9',plain,(
    ! [X4: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X6 @ X4 @ X7 @ X8 )
      | ( X6
       != ( k1_funct_1 @ X7 @ X4 ) )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('10',plain,(
    ! [X4: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X8 ) )
      | ( zip_tseitin_0 @ ( k1_funct_1 @ X7 @ X4 ) @ X4 @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( k1_funct_1 @ X0 @ sk_A ) @ sk_A @ X0 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( X10
        = ( k1_funct_1 @ X12 @ X9 ) )
      | ~ ( zip_tseitin_1 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ ( k1_funct_1 @ X0 @ sk_A ) @ sk_A @ X0 @ sk_B )
      | ( sk_A
        = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_A
      = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('16',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('17',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('18',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('21',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('24',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( X24
       != ( k2_funct_1 @ X23 ) )
      | ( ( k1_relat_1 @ X24 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('25',plain,(
    ! [X23: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X23 ) )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v2_funct_1 @ X23 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t23_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A )
              = ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X3 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X2 @ X3 ) ) )
      | ~ ( r2_hidden @ X3 @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X2 ) @ X1 )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','31'])).

thf('33',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('34',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('39',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['19','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('43',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('46',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(split,[status(esa)],['45'])).

thf('47',plain,
    ( ( ( sk_A
       != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('49',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('50',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','50'])).

thf('52',plain,
    ( $false
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('54',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['45'])).

thf('55',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
    | ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['45'])).

thf('58',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['52','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.b84C0ruTpw
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:19:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 55 iterations in 0.031s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.49  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $i > $o).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.20/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.49  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.20/0.49  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.49  thf(dt_k2_funct_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.49       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.20/0.49         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.49  thf(t54_funct_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.20/0.49       ( ( v2_funct_1 @ A ) =>
% 0.20/0.49         ( ![B:$i]:
% 0.20/0.49           ( ( ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) =>
% 0.20/0.49             ( ( ( B ) = ( k2_funct_1 @ A ) ) <=>
% 0.20/0.49               ( ( ![C:$i,D:$i]:
% 0.20/0.49                   ( ( ( ( ( D ) = ( k1_funct_1 @ B @ C ) ) & 
% 0.20/0.49                         ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) =>
% 0.20/0.49                       ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.20/0.49                         ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) & 
% 0.20/0.49                     ( ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.20/0.49                         ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) =>
% 0.20/0.49                       ( ( ( D ) = ( k1_funct_1 @ B @ C ) ) & 
% 0.20/0.49                         ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) ) ) ) & 
% 0.20/0.49                 ( ( k1_relat_1 @ B ) = ( k2_relat_1 @ A ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, type, zip_tseitin_3 : $i > $i > $i > $i > $o).
% 0.20/0.49  thf(zf_stmt_1, axiom,
% 0.20/0.49    (![D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.49     ( ( zip_tseitin_3 @ D @ C @ B @ A ) <=>
% 0.20/0.49       ( ( zip_tseitin_2 @ D @ C @ A ) =>
% 0.20/0.49         ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) & 
% 0.20/0.49           ( ( D ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.20/0.49  thf(zf_stmt_3, axiom,
% 0.20/0.49    (![D:$i,C:$i,A:$i]:
% 0.20/0.49     ( ( zip_tseitin_2 @ D @ C @ A ) <=>
% 0.20/0.49       ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.49         ( ( C ) = ( k1_funct_1 @ A @ D ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.20/0.49  thf(zf_stmt_5, axiom,
% 0.20/0.49    (![D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.49     ( ( zip_tseitin_1 @ D @ C @ B @ A ) <=>
% 0.20/0.49       ( ( zip_tseitin_0 @ D @ C @ B @ A ) =>
% 0.20/0.49         ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.49           ( ( C ) = ( k1_funct_1 @ A @ D ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.49  thf(zf_stmt_7, axiom,
% 0.20/0.49    (![D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.49     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.20/0.49       ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) & 
% 0.20/0.49         ( ( D ) = ( k1_funct_1 @ B @ C ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_8, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.49       ( ( v2_funct_1 @ A ) =>
% 0.20/0.49         ( ![B:$i]:
% 0.20/0.49           ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.49             ( ( ( B ) = ( k2_funct_1 @ A ) ) <=>
% 0.20/0.49               ( ( ( k1_relat_1 @ B ) = ( k2_relat_1 @ A ) ) & 
% 0.20/0.49                 ( ![C:$i,D:$i]:
% 0.20/0.49                   ( ( zip_tseitin_3 @ D @ C @ B @ A ) & 
% 0.20/0.49                     ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.49         (~ (v2_funct_1 @ X23)
% 0.20/0.49          | ~ (v1_relat_1 @ X24)
% 0.20/0.49          | ~ (v1_funct_1 @ X24)
% 0.20/0.49          | ((X24) != (k2_funct_1 @ X23))
% 0.20/0.49          | (zip_tseitin_1 @ X25 @ X26 @ X24 @ X23)
% 0.20/0.49          | ~ (v1_funct_1 @ X23)
% 0.20/0.49          | ~ (v1_relat_1 @ X23))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X23 : $i, X25 : $i, X26 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X23)
% 0.20/0.49          | ~ (v1_funct_1 @ X23)
% 0.20/0.49          | (zip_tseitin_1 @ X25 @ X26 @ (k2_funct_1 @ X23) @ X23)
% 0.20/0.49          | ~ (v1_funct_1 @ (k2_funct_1 @ X23))
% 0.20/0.49          | ~ (v1_relat_1 @ (k2_funct_1 @ X23))
% 0.20/0.49          | ~ (v2_funct_1 @ X23))),
% 0.20/0.49      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (v2_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.49          | (zip_tseitin_1 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '3'])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         ((zip_tseitin_1 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.49          | ~ (v2_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (v2_funct_1 @ X0)
% 0.20/0.49          | (zip_tseitin_1 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '5'])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         ((zip_tseitin_1 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.20/0.49          | ~ (v2_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.49  thf(t57_funct_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.49       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.20/0.49         ( ( ( A ) =
% 0.20/0.49             ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.20/0.49           ( ( A ) =
% 0.20/0.49             ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_9, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i]:
% 0.20/0.49        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.49          ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.20/0.49            ( ( ( A ) =
% 0.20/0.49                ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.20/0.49              ( ( A ) =
% 0.20/0.49                ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t57_funct_1])).
% 0.20/0.49  thf('8', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X4 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.49         ((zip_tseitin_0 @ X6 @ X4 @ X7 @ X8)
% 0.20/0.49          | ((X6) != (k1_funct_1 @ X7 @ X4))
% 0.20/0.49          | ~ (r2_hidden @ X4 @ (k2_relat_1 @ X8)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X4 : $i, X7 : $i, X8 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X4 @ (k2_relat_1 @ X8))
% 0.20/0.49          | (zip_tseitin_0 @ (k1_funct_1 @ X7 @ X4) @ X4 @ X7 @ X8))),
% 0.20/0.49      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (zip_tseitin_0 @ (k1_funct_1 @ X0 @ sk_A) @ sk_A @ X0 @ sk_B)),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '10'])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.49         (~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.20/0.49          | ((X10) = (k1_funct_1 @ X12 @ X9))
% 0.20/0.49          | ~ (zip_tseitin_1 @ X9 @ X10 @ X11 @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (zip_tseitin_1 @ (k1_funct_1 @ X0 @ sk_A) @ sk_A @ X0 @ sk_B)
% 0.20/0.49          | ((sk_A) = (k1_funct_1 @ sk_B @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.49        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.49        | ~ (v2_funct_1 @ sk_B)
% 0.20/0.49        | ((sk_A)
% 0.20/0.49            = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['7', '13'])).
% 0.20/0.49  thf('15', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.49  thf('16', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.49  thf('17', plain, ((v2_funct_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (((sk_A)
% 0.20/0.49         = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.49  thf('21', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X23 : $i, X24 : $i]:
% 0.20/0.49         (~ (v2_funct_1 @ X23)
% 0.20/0.49          | ~ (v1_relat_1 @ X24)
% 0.20/0.49          | ~ (v1_funct_1 @ X24)
% 0.20/0.49          | ((X24) != (k2_funct_1 @ X23))
% 0.20/0.49          | ((k1_relat_1 @ X24) = (k2_relat_1 @ X23))
% 0.20/0.49          | ~ (v1_funct_1 @ X23)
% 0.20/0.49          | ~ (v1_relat_1 @ X23))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X23 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X23)
% 0.20/0.49          | ~ (v1_funct_1 @ X23)
% 0.20/0.49          | ((k1_relat_1 @ (k2_funct_1 @ X23)) = (k2_relat_1 @ X23))
% 0.20/0.49          | ~ (v1_funct_1 @ (k2_funct_1 @ X23))
% 0.20/0.49          | ~ (v1_relat_1 @ (k2_funct_1 @ X23))
% 0.20/0.49          | ~ (v2_funct_1 @ X23))),
% 0.20/0.49      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (v2_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.49          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['23', '25'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.20/0.49          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.49          | ~ (v2_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (v2_funct_1 @ X0)
% 0.20/0.49          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['22', '27'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.20/0.49          | ~ (v2_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.49  thf(t23_funct_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.49           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.49             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.20/0.49               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X1)
% 0.20/0.49          | ~ (v1_funct_1 @ X1)
% 0.20/0.49          | ((k1_funct_1 @ (k5_relat_1 @ X2 @ X1) @ X3)
% 0.20/0.49              = (k1_funct_1 @ X1 @ (k1_funct_1 @ X2 @ X3)))
% 0.20/0.49          | ~ (r2_hidden @ X3 @ (k1_relat_1 @ X2))
% 0.20/0.49          | ~ (v1_funct_1 @ X2)
% 0.20/0.49          | ~ (v1_relat_1 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.20/0.49          | ~ (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (v2_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.49          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.49          | ((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X2) @ X1)
% 0.20/0.49              = (k1_funct_1 @ X2 @ (k1_funct_1 @ (k2_funct_1 @ X0) @ X1)))
% 0.20/0.49          | ~ (v1_funct_1 @ X2)
% 0.20/0.49          | ~ (v1_relat_1 @ X2))),
% 0.20/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ sk_A)
% 0.20/0.49              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 0.20/0.49          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.20/0.49          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.20/0.49          | ~ (v2_funct_1 @ sk_B)
% 0.20/0.49          | ~ (v1_funct_1 @ sk_B)
% 0.20/0.49          | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['21', '31'])).
% 0.20/0.49  thf('33', plain, ((v2_funct_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.49  thf('34', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.49  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ sk_A)
% 0.20/0.49              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 0.20/0.49          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.20/0.49          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.20/0.49      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ sk_B)
% 0.20/0.49          | ~ (v1_funct_1 @ sk_B)
% 0.20/0.49          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.20/0.49          | ((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ sk_A)
% 0.20/0.49              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['20', '36'])).
% 0.20/0.49  thf('38', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.49  thf('39', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.20/0.49          | ((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ sk_A)
% 0.20/0.49              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ sk_B)
% 0.20/0.49          | ~ (v1_funct_1 @ sk_B)
% 0.20/0.49          | ~ (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ sk_A)
% 0.20/0.49              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['19', '40'])).
% 0.20/0.49  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.49  thf('43', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ sk_A)
% 0.20/0.49              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.20/0.49      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      ((((sk_A)
% 0.20/0.49          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 0.20/0.49        | ((sk_A)
% 0.20/0.49            != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      ((((sk_A)
% 0.20/0.49          != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))
% 0.20/0.49         <= (~
% 0.20/0.49             (((sk_A)
% 0.20/0.49                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.20/0.49                   sk_A))))),
% 0.20/0.49      inference('split', [status(esa)], ['45'])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      (((((sk_A)
% 0.20/0.49           != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 0.20/0.49         | ~ (v1_funct_1 @ sk_B)
% 0.20/0.49         | ~ (v1_relat_1 @ sk_B)))
% 0.20/0.49         <= (~
% 0.20/0.49             (((sk_A)
% 0.20/0.49                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.20/0.49                   sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['44', '46'])).
% 0.20/0.49  thf('48', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.49  thf('49', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.49  thf('50', plain,
% 0.20/0.49      ((((sk_A)
% 0.20/0.49          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))
% 0.20/0.49         <= (~
% 0.20/0.49             (((sk_A)
% 0.20/0.49                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.20/0.49                   sk_A))))),
% 0.20/0.49      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.20/0.49  thf('51', plain,
% 0.20/0.49      ((((sk_A) != (sk_A)))
% 0.20/0.49         <= (~
% 0.20/0.49             (((sk_A)
% 0.20/0.49                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.20/0.49                   sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['18', '50'])).
% 0.20/0.49  thf('52', plain,
% 0.20/0.49      (($false)
% 0.20/0.49         <= (~
% 0.20/0.49             (((sk_A)
% 0.20/0.49                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.20/0.49                   sk_A))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['51'])).
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      (((sk_A)
% 0.20/0.49         = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 0.20/0.49  thf('54', plain,
% 0.20/0.49      ((((sk_A)
% 0.20/0.49          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))
% 0.20/0.49         <= (~
% 0.20/0.49             (((sk_A)
% 0.20/0.49                = (k1_funct_1 @ sk_B @ 
% 0.20/0.49                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.20/0.49      inference('split', [status(esa)], ['45'])).
% 0.20/0.49  thf('55', plain,
% 0.20/0.49      ((((sk_A) != (sk_A)))
% 0.20/0.49         <= (~
% 0.20/0.49             (((sk_A)
% 0.20/0.49                = (k1_funct_1 @ sk_B @ 
% 0.20/0.49                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.49  thf('56', plain,
% 0.20/0.49      ((((sk_A)
% 0.20/0.49          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['55'])).
% 0.20/0.49  thf('57', plain,
% 0.20/0.49      (~
% 0.20/0.49       (((sk_A)
% 0.20/0.49          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A))) | 
% 0.20/0.49       ~
% 0.20/0.49       (((sk_A)
% 0.20/0.49          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.20/0.49      inference('split', [status(esa)], ['45'])).
% 0.20/0.49  thf('58', plain,
% 0.20/0.49      (~
% 0.20/0.49       (((sk_A)
% 0.20/0.49          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['56', '57'])).
% 0.20/0.49  thf('59', plain, ($false),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['52', '58'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
