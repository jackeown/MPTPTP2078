%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ffvaJroG4I

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 166 expanded)
%              Number of leaves         :   29 (  61 expanded)
%              Depth                    :   27
%              Number of atoms          : 1316 (2084 expanded)
%              Number of equality atoms :   39 (  61 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
      ( ( v1_relat_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('3',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
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

thf('4',plain,(
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

thf('5',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( zip_tseitin_1 @ X25 @ X26 @ ( k2_funct_1 @ X23 ) @ X23 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v2_funct_1 @ X23 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( zip_tseitin_1 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_1 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X28: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relat_1 @ X28 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
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

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_B @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_B @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X4: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X6 @ X4 @ X7 @ X8 )
      | ( X6
       != ( k1_funct_1 @ X7 @ X4 ) )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('20',plain,(
    ! [X4: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X8 ) )
      | ( zip_tseitin_0 @ ( k1_funct_1 @ X7 @ X4 ) @ X4 @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_0 @ ( k1_funct_1 @ X1 @ ( sk_B @ ( k2_funct_1 @ X0 ) ) ) @ ( sk_B @ ( k2_funct_1 @ X0 ) ) @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( X10
        = ( k1_funct_1 @ X12 @ X9 ) )
      | ~ ( zip_tseitin_1 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( zip_tseitin_1 @ ( k1_funct_1 @ X1 @ ( sk_B @ ( k2_funct_1 @ X0 ) ) ) @ ( sk_B @ ( k2_funct_1 @ X0 ) ) @ X1 @ X0 )
      | ( ( sk_B @ ( k2_funct_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ ( sk_B @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( sk_B @ ( k2_funct_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( sk_B @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( sk_B @ ( k2_funct_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( sk_B @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('27',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_C @ X0 ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('29',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('30',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('31',plain,(
    ! [X28: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relat_1 @ X28 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X4: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X8 ) )
      | ( zip_tseitin_0 @ ( k1_funct_1 @ X7 @ X4 ) @ X4 @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_0 @ ( k1_funct_1 @ X1 @ ( sk_C @ ( k2_funct_1 @ X0 ) ) ) @ ( sk_C @ ( k2_funct_1 @ X0 ) ) @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( sk_B @ ( k2_funct_1 @ X0 ) ) ) @ ( sk_C @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( zip_tseitin_0 @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( sk_B @ ( k2_funct_1 @ X0 ) ) ) @ ( sk_C @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( zip_tseitin_0 @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( sk_B @ ( k2_funct_1 @ X0 ) ) ) @ ( sk_C @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( zip_tseitin_0 @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( sk_B @ ( k2_funct_1 @ X0 ) ) ) @ ( sk_C @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( zip_tseitin_0 @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( sk_B @ ( k2_funct_1 @ X0 ) ) ) @ ( sk_C @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( zip_tseitin_0 @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( sk_B @ ( k2_funct_1 @ X0 ) ) ) @ ( sk_C @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X6
        = ( k1_funct_1 @ X7 @ X4 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X4 @ X7 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( sk_B @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( sk_C @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_0 @ ( k1_funct_1 @ X1 @ ( sk_C @ ( k2_funct_1 @ X0 ) ) ) @ ( sk_C @ ( k2_funct_1 @ X0 ) ) @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('50',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( X10
        = ( k1_funct_1 @ X12 @ X9 ) )
      | ~ ( zip_tseitin_1 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( zip_tseitin_1 @ ( k1_funct_1 @ X1 @ ( sk_C @ ( k2_funct_1 @ X0 ) ) ) @ ( sk_C @ ( k2_funct_1 @ X0 ) ) @ X1 @ X0 )
      | ( ( sk_C @ ( k2_funct_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ X1 @ ( sk_C @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( sk_C @ ( k2_funct_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( sk_C @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( sk_C @ ( k2_funct_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( sk_C @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k2_funct_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( sk_B @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( sk_C @ ( k2_funct_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( sk_B @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k2_funct_1 @ X0 ) )
        = ( sk_B @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( sk_C @ ( k2_funct_1 @ X0 ) )
        = ( sk_B @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf(t62_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf(zf_stmt_9,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v2_funct_1 @ A )
         => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_funct_1])).

thf('58',plain,(
    ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('59',plain,
    ( ( ( sk_C @ ( k2_funct_1 @ sk_A ) )
      = ( sk_B @ ( k2_funct_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('61',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('62',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('63',plain,
    ( ( sk_C @ ( k2_funct_1 @ sk_A ) )
    = ( sk_B @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != ( sk_C @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('65',plain,
    ( ( ( sk_B @ ( k2_funct_1 @ sk_A ) )
     != ( sk_B @ ( k2_funct_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('71',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('72',plain,(
    ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('75',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['73','74','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ffvaJroG4I
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:54:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 133 iterations in 0.087s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.55  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $i > $o).
% 0.21/0.55  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.21/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.55  thf(sk_C_type, type, sk_C: $i > $i).
% 0.21/0.55  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.55  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.55  thf(dt_k2_funct_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.55       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.21/0.55         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.21/0.55  thf('0', plain,
% 0.21/0.55      (![X3 : $i]:
% 0.21/0.55         ((v1_funct_1 @ (k2_funct_1 @ X3))
% 0.21/0.55          | ~ (v1_funct_1 @ X3)
% 0.21/0.55          | ~ (v1_relat_1 @ X3))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (![X3 : $i]:
% 0.21/0.55         ((v1_relat_1 @ (k2_funct_1 @ X3))
% 0.21/0.55          | ~ (v1_funct_1 @ X3)
% 0.21/0.55          | ~ (v1_relat_1 @ X3))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X3 : $i]:
% 0.21/0.55         ((v1_relat_1 @ (k2_funct_1 @ X3))
% 0.21/0.55          | ~ (v1_funct_1 @ X3)
% 0.21/0.55          | ~ (v1_relat_1 @ X3))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X3 : $i]:
% 0.21/0.55         ((v1_funct_1 @ (k2_funct_1 @ X3))
% 0.21/0.55          | ~ (v1_funct_1 @ X3)
% 0.21/0.55          | ~ (v1_relat_1 @ X3))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.55  thf(t54_funct_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.21/0.55       ( ( v2_funct_1 @ A ) =>
% 0.21/0.55         ( ![B:$i]:
% 0.21/0.55           ( ( ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) =>
% 0.21/0.55             ( ( ( B ) = ( k2_funct_1 @ A ) ) <=>
% 0.21/0.55               ( ( ![C:$i,D:$i]:
% 0.21/0.55                   ( ( ( ( ( D ) = ( k1_funct_1 @ B @ C ) ) & 
% 0.21/0.55                         ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) =>
% 0.21/0.55                       ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.21/0.55                         ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) & 
% 0.21/0.55                     ( ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.21/0.55                         ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) =>
% 0.21/0.55                       ( ( ( D ) = ( k1_funct_1 @ B @ C ) ) & 
% 0.21/0.55                         ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) ) ) ) & 
% 0.21/0.55                 ( ( k1_relat_1 @ B ) = ( k2_relat_1 @ A ) ) ) ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, type, zip_tseitin_3 : $i > $i > $i > $i > $o).
% 0.21/0.55  thf(zf_stmt_1, axiom,
% 0.21/0.55    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.55     ( ( zip_tseitin_3 @ D @ C @ B @ A ) <=>
% 0.21/0.55       ( ( zip_tseitin_2 @ D @ C @ A ) =>
% 0.21/0.55         ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) & 
% 0.21/0.55           ( ( D ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.21/0.55  thf(zf_stmt_3, axiom,
% 0.21/0.55    (![D:$i,C:$i,A:$i]:
% 0.21/0.55     ( ( zip_tseitin_2 @ D @ C @ A ) <=>
% 0.21/0.55       ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.55         ( ( C ) = ( k1_funct_1 @ A @ D ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.21/0.55  thf(zf_stmt_5, axiom,
% 0.21/0.55    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.55     ( ( zip_tseitin_1 @ D @ C @ B @ A ) <=>
% 0.21/0.55       ( ( zip_tseitin_0 @ D @ C @ B @ A ) =>
% 0.21/0.55         ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.55           ( ( C ) = ( k1_funct_1 @ A @ D ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.55  thf(zf_stmt_7, axiom,
% 0.21/0.55    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.55     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.21/0.55       ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) & 
% 0.21/0.55         ( ( D ) = ( k1_funct_1 @ B @ C ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_8, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.55       ( ( v2_funct_1 @ A ) =>
% 0.21/0.55         ( ![B:$i]:
% 0.21/0.55           ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.55             ( ( ( B ) = ( k2_funct_1 @ A ) ) <=>
% 0.21/0.55               ( ( ( k1_relat_1 @ B ) = ( k2_relat_1 @ A ) ) & 
% 0.21/0.55                 ( ![C:$i,D:$i]:
% 0.21/0.55                   ( ( zip_tseitin_3 @ D @ C @ B @ A ) & 
% 0.21/0.55                     ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.55         (~ (v2_funct_1 @ X23)
% 0.21/0.55          | ~ (v1_relat_1 @ X24)
% 0.21/0.55          | ~ (v1_funct_1 @ X24)
% 0.21/0.55          | ((X24) != (k2_funct_1 @ X23))
% 0.21/0.55          | (zip_tseitin_1 @ X25 @ X26 @ X24 @ X23)
% 0.21/0.55          | ~ (v1_funct_1 @ X23)
% 0.21/0.55          | ~ (v1_relat_1 @ X23))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X23 : $i, X25 : $i, X26 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X23)
% 0.21/0.55          | ~ (v1_funct_1 @ X23)
% 0.21/0.55          | (zip_tseitin_1 @ X25 @ X26 @ (k2_funct_1 @ X23) @ X23)
% 0.21/0.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X23))
% 0.21/0.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X23))
% 0.21/0.55          | ~ (v2_funct_1 @ X23))),
% 0.21/0.55      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | (zip_tseitin_1 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         ((zip_tseitin_1 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | (zip_tseitin_1 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '7'])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         ((zip_tseitin_1 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X3 : $i]:
% 0.21/0.55         ((v1_funct_1 @ (k2_funct_1 @ X3))
% 0.21/0.55          | ~ (v1_funct_1 @ X3)
% 0.21/0.55          | ~ (v1_relat_1 @ X3))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X3 : $i]:
% 0.21/0.55         ((v1_relat_1 @ (k2_funct_1 @ X3))
% 0.21/0.55          | ~ (v1_funct_1 @ X3)
% 0.21/0.55          | ~ (v1_relat_1 @ X3))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.55  thf(t55_funct_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.55       ( ( v2_funct_1 @ A ) =>
% 0.21/0.55         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.21/0.55           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X28 : $i]:
% 0.21/0.55         (~ (v2_funct_1 @ X28)
% 0.21/0.55          | ((k2_relat_1 @ X28) = (k1_relat_1 @ (k2_funct_1 @ X28)))
% 0.21/0.55          | ~ (v1_funct_1 @ X28)
% 0.21/0.55          | ~ (v1_relat_1 @ X28))),
% 0.21/0.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.21/0.55  thf(d8_funct_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.55       ( ( v2_funct_1 @ A ) <=>
% 0.21/0.55         ( ![B:$i,C:$i]:
% 0.21/0.55           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.55               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.55               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.21/0.55             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r2_hidden @ (sk_B @ X0) @ (k1_relat_1 @ X0))
% 0.21/0.55          | (v2_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r2_hidden @ (sk_B @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | (r2_hidden @ (sk_B @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['11', '14'])).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r2_hidden @ (sk_B @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | (r2_hidden @ (sk_B @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['10', '16'])).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r2_hidden @ (sk_B @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X4 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.55         ((zip_tseitin_0 @ X6 @ X4 @ X7 @ X8)
% 0.21/0.55          | ((X6) != (k1_funct_1 @ X7 @ X4))
% 0.21/0.55          | ~ (r2_hidden @ X4 @ (k2_relat_1 @ X8)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      (![X4 : $i, X7 : $i, X8 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X4 @ (k2_relat_1 @ X8))
% 0.21/0.55          | (zip_tseitin_0 @ (k1_funct_1 @ X7 @ X4) @ X4 @ X7 @ X8))),
% 0.21/0.55      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | (zip_tseitin_0 @ (k1_funct_1 @ X1 @ (sk_B @ (k2_funct_1 @ X0))) @ 
% 0.21/0.55             (sk_B @ (k2_funct_1 @ X0)) @ X1 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['18', '20'])).
% 0.21/0.55  thf('22', plain,
% 0.21/0.55      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.55         (~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.21/0.55          | ((X10) = (k1_funct_1 @ X12 @ X9))
% 0.21/0.55          | ~ (zip_tseitin_1 @ X9 @ X10 @ X11 @ X12))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.55  thf('23', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (v2_funct_1 @ X0)
% 0.21/0.55          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (zip_tseitin_1 @ 
% 0.21/0.55               (k1_funct_1 @ X1 @ (sk_B @ (k2_funct_1 @ X0))) @ 
% 0.21/0.55               (sk_B @ (k2_funct_1 @ X0)) @ X1 @ X0)
% 0.21/0.55          | ((sk_B @ (k2_funct_1 @ X0))
% 0.21/0.55              = (k1_funct_1 @ X0 @ 
% 0.21/0.55                 (k1_funct_1 @ X1 @ (sk_B @ (k2_funct_1 @ X0))))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | ((sk_B @ (k2_funct_1 @ X0))
% 0.21/0.55              = (k1_funct_1 @ X0 @ 
% 0.21/0.55                 (k1_funct_1 @ (k2_funct_1 @ X0) @ (sk_B @ (k2_funct_1 @ X0)))))
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v2_funct_1 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['9', '23'])).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ((sk_B @ (k2_funct_1 @ X0))
% 0.21/0.55              = (k1_funct_1 @ X0 @ 
% 0.21/0.55                 (k1_funct_1 @ (k2_funct_1 @ X0) @ (sk_B @ (k2_funct_1 @ X0)))))
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      (![X3 : $i]:
% 0.21/0.55         ((v1_relat_1 @ (k2_funct_1 @ X3))
% 0.21/0.55          | ~ (v1_funct_1 @ X3)
% 0.21/0.55          | ~ (v1_relat_1 @ X3))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      (![X3 : $i]:
% 0.21/0.55         ((v1_funct_1 @ (k2_funct_1 @ X3))
% 0.21/0.55          | ~ (v1_funct_1 @ X3)
% 0.21/0.55          | ~ (v1_relat_1 @ X3))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k1_funct_1 @ X0 @ (sk_B @ X0)) = (k1_funct_1 @ X0 @ (sk_C @ X0)))
% 0.21/0.55          | (v2_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.55  thf('29', plain,
% 0.21/0.55      (![X3 : $i]:
% 0.21/0.55         ((v1_funct_1 @ (k2_funct_1 @ X3))
% 0.21/0.55          | ~ (v1_funct_1 @ X3)
% 0.21/0.55          | ~ (v1_relat_1 @ X3))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.55  thf('30', plain,
% 0.21/0.55      (![X3 : $i]:
% 0.21/0.55         ((v1_relat_1 @ (k2_funct_1 @ X3))
% 0.21/0.55          | ~ (v1_funct_1 @ X3)
% 0.21/0.55          | ~ (v1_relat_1 @ X3))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.55  thf('31', plain,
% 0.21/0.55      (![X28 : $i]:
% 0.21/0.55         (~ (v2_funct_1 @ X28)
% 0.21/0.55          | ((k2_relat_1 @ X28) = (k1_relat_1 @ (k2_funct_1 @ X28)))
% 0.21/0.55          | ~ (v1_funct_1 @ X28)
% 0.21/0.55          | ~ (v1_relat_1 @ X28))),
% 0.21/0.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.21/0.55  thf('32', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r2_hidden @ (sk_C @ X0) @ (k1_relat_1 @ X0))
% 0.21/0.55          | (v2_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.55  thf('33', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r2_hidden @ (sk_C @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['31', '32'])).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | (r2_hidden @ (sk_C @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['30', '33'])).
% 0.21/0.55  thf('35', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r2_hidden @ (sk_C @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['34'])).
% 0.21/0.55  thf('36', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | (r2_hidden @ (sk_C @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['29', '35'])).
% 0.21/0.55  thf('37', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r2_hidden @ (sk_C @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.55  thf('38', plain,
% 0.21/0.55      (![X4 : $i, X7 : $i, X8 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X4 @ (k2_relat_1 @ X8))
% 0.21/0.55          | (zip_tseitin_0 @ (k1_funct_1 @ X7 @ X4) @ X4 @ X7 @ X8))),
% 0.21/0.55      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.55  thf('39', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | (zip_tseitin_0 @ (k1_funct_1 @ X1 @ (sk_C @ (k2_funct_1 @ X0))) @ 
% 0.21/0.55             (sk_C @ (k2_funct_1 @ X0)) @ X1 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.55  thf('40', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((zip_tseitin_0 @ 
% 0.21/0.55           (k1_funct_1 @ (k2_funct_1 @ X0) @ (sk_B @ (k2_funct_1 @ X0))) @ 
% 0.21/0.55           (sk_C @ (k2_funct_1 @ X0)) @ (k2_funct_1 @ X0) @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['28', '39'])).
% 0.21/0.55  thf('41', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | (zip_tseitin_0 @ 
% 0.21/0.55             (k1_funct_1 @ (k2_funct_1 @ X0) @ (sk_B @ (k2_funct_1 @ X0))) @ 
% 0.21/0.55             (sk_C @ (k2_funct_1 @ X0)) @ (k2_funct_1 @ X0) @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['40'])).
% 0.21/0.55  thf('42', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | (zip_tseitin_0 @ 
% 0.21/0.55             (k1_funct_1 @ (k2_funct_1 @ X0) @ (sk_B @ (k2_funct_1 @ X0))) @ 
% 0.21/0.55             (sk_C @ (k2_funct_1 @ X0)) @ (k2_funct_1 @ X0) @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['27', '41'])).
% 0.21/0.55  thf('43', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v2_funct_1 @ X0)
% 0.21/0.55          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | (zip_tseitin_0 @ 
% 0.21/0.55             (k1_funct_1 @ (k2_funct_1 @ X0) @ (sk_B @ (k2_funct_1 @ X0))) @ 
% 0.21/0.55             (sk_C @ (k2_funct_1 @ X0)) @ (k2_funct_1 @ X0) @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['42'])).
% 0.21/0.55  thf('44', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | (zip_tseitin_0 @ 
% 0.21/0.55             (k1_funct_1 @ (k2_funct_1 @ X0) @ (sk_B @ (k2_funct_1 @ X0))) @ 
% 0.21/0.55             (sk_C @ (k2_funct_1 @ X0)) @ (k2_funct_1 @ X0) @ X0)
% 0.21/0.55          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v2_funct_1 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['26', '43'])).
% 0.21/0.55  thf('45', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v2_funct_1 @ X0)
% 0.21/0.55          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | (zip_tseitin_0 @ 
% 0.21/0.55             (k1_funct_1 @ (k2_funct_1 @ X0) @ (sk_B @ (k2_funct_1 @ X0))) @ 
% 0.21/0.55             (sk_C @ (k2_funct_1 @ X0)) @ (k2_funct_1 @ X0) @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.55  thf('46', plain,
% 0.21/0.55      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.55         (((X6) = (k1_funct_1 @ X7 @ X4))
% 0.21/0.55          | ~ (zip_tseitin_0 @ X6 @ X4 @ X7 @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.21/0.55  thf('47', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | ((k1_funct_1 @ (k2_funct_1 @ X0) @ (sk_B @ (k2_funct_1 @ X0)))
% 0.21/0.55              = (k1_funct_1 @ (k2_funct_1 @ X0) @ (sk_C @ (k2_funct_1 @ X0)))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.55  thf('48', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         ((zip_tseitin_1 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.55  thf('49', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | (zip_tseitin_0 @ (k1_funct_1 @ X1 @ (sk_C @ (k2_funct_1 @ X0))) @ 
% 0.21/0.55             (sk_C @ (k2_funct_1 @ X0)) @ X1 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.55  thf('50', plain,
% 0.21/0.55      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.55         (~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.21/0.55          | ((X10) = (k1_funct_1 @ X12 @ X9))
% 0.21/0.55          | ~ (zip_tseitin_1 @ X9 @ X10 @ X11 @ X12))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.55  thf('51', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (v2_funct_1 @ X0)
% 0.21/0.55          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (zip_tseitin_1 @ 
% 0.21/0.55               (k1_funct_1 @ X1 @ (sk_C @ (k2_funct_1 @ X0))) @ 
% 0.21/0.55               (sk_C @ (k2_funct_1 @ X0)) @ X1 @ X0)
% 0.21/0.55          | ((sk_C @ (k2_funct_1 @ X0))
% 0.21/0.55              = (k1_funct_1 @ X0 @ 
% 0.21/0.55                 (k1_funct_1 @ X1 @ (sk_C @ (k2_funct_1 @ X0))))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.55  thf('52', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | ((sk_C @ (k2_funct_1 @ X0))
% 0.21/0.55              = (k1_funct_1 @ X0 @ 
% 0.21/0.55                 (k1_funct_1 @ (k2_funct_1 @ X0) @ (sk_C @ (k2_funct_1 @ X0)))))
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v2_funct_1 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['48', '51'])).
% 0.21/0.55  thf('53', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ((sk_C @ (k2_funct_1 @ X0))
% 0.21/0.55              = (k1_funct_1 @ X0 @ 
% 0.21/0.55                 (k1_funct_1 @ (k2_funct_1 @ X0) @ (sk_C @ (k2_funct_1 @ X0)))))
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['52'])).
% 0.21/0.55  thf('54', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((sk_C @ (k2_funct_1 @ X0))
% 0.21/0.55            = (k1_funct_1 @ X0 @ 
% 0.21/0.55               (k1_funct_1 @ (k2_funct_1 @ X0) @ (sk_B @ (k2_funct_1 @ X0)))))
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['47', '53'])).
% 0.21/0.55  thf('55', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | ((sk_C @ (k2_funct_1 @ X0))
% 0.21/0.55              = (k1_funct_1 @ X0 @ 
% 0.21/0.55                 (k1_funct_1 @ (k2_funct_1 @ X0) @ (sk_B @ (k2_funct_1 @ X0))))))),
% 0.21/0.55      inference('simplify', [status(thm)], ['54'])).
% 0.21/0.55  thf('56', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((sk_C @ (k2_funct_1 @ X0)) = (sk_B @ (k2_funct_1 @ X0)))
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['25', '55'])).
% 0.21/0.55  thf('57', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ((sk_C @ (k2_funct_1 @ X0)) = (sk_B @ (k2_funct_1 @ X0))))),
% 0.21/0.55      inference('simplify', [status(thm)], ['56'])).
% 0.21/0.55  thf(t62_funct_1, conjecture,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.55       ( ( v2_funct_1 @ A ) => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_9, negated_conjecture,
% 0.21/0.55    (~( ![A:$i]:
% 0.21/0.55        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.55          ( ( v2_funct_1 @ A ) => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t62_funct_1])).
% 0.21/0.55  thf('58', plain, (~ (v2_funct_1 @ (k2_funct_1 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.55  thf('59', plain,
% 0.21/0.55      ((((sk_C @ (k2_funct_1 @ sk_A)) = (sk_B @ (k2_funct_1 @ sk_A)))
% 0.21/0.55        | ~ (v1_relat_1 @ sk_A)
% 0.21/0.55        | ~ (v1_funct_1 @ sk_A)
% 0.21/0.55        | ~ (v2_funct_1 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.55  thf('60', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.55  thf('61', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.55  thf('62', plain, ((v2_funct_1 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.55  thf('63', plain,
% 0.21/0.55      (((sk_C @ (k2_funct_1 @ sk_A)) = (sk_B @ (k2_funct_1 @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 0.21/0.55  thf('64', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((sk_B @ X0) != (sk_C @ X0))
% 0.21/0.55          | (v2_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.55  thf('65', plain,
% 0.21/0.55      ((((sk_B @ (k2_funct_1 @ sk_A)) != (sk_B @ (k2_funct_1 @ sk_A)))
% 0.21/0.55        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.21/0.55        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.21/0.55        | (v2_funct_1 @ (k2_funct_1 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['63', '64'])).
% 0.21/0.55  thf('66', plain,
% 0.21/0.55      (((v2_funct_1 @ (k2_funct_1 @ sk_A))
% 0.21/0.55        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.21/0.55        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['65'])).
% 0.21/0.55  thf('67', plain, (~ (v2_funct_1 @ (k2_funct_1 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.55  thf('68', plain,
% 0.21/0.55      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.21/0.55        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A)))),
% 0.21/0.55      inference('clc', [status(thm)], ['66', '67'])).
% 0.21/0.55  thf('69', plain,
% 0.21/0.55      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.55        | ~ (v1_funct_1 @ sk_A)
% 0.21/0.55        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['1', '68'])).
% 0.21/0.55  thf('70', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.55  thf('71', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.55  thf('72', plain, (~ (v1_funct_1 @ (k2_funct_1 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.21/0.55  thf('73', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_funct_1 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['0', '72'])).
% 0.21/0.55  thf('74', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.55  thf('75', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.55  thf('76', plain, ($false),
% 0.21/0.55      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
