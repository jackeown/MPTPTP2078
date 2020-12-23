%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tp4CIvpxSb

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:51 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 160 expanded)
%              Number of leaves         :   39 (  64 expanded)
%              Depth                    :   24
%              Number of atoms          :  671 (1296 expanded)
%              Number of equality atoms :   78 ( 134 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t172_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k10_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t172_relat_1])).

thf('0',plain,(
    ( k10_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('2',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X34 @ X35 ) @ ( k1_relat_1 @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k10_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('6',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('7',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k10_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(fc7_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ) )).

thf('9',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X30 @ X31 ) @ ( k4_tarski @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[fc7_relat_1])).

thf(t61_setfam_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t61_setfam_1])).

thf(t10_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ~ ( ( B != k1_xboole_0 )
          & ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ~ ( r2_hidden @ C @ B ) ) ) ) )).

thf('11',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X25 @ X26 ) @ X25 )
      | ( X25 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('13',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( X9 = X6 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('14',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9 = X6 )
      | ~ ( r2_hidden @ X9 @ ( k1_tarski @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( sk_C_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t61_setfam_1])).

thf('17',plain,(
    ! [X25: $i,X26: $i] :
      ( ( m1_subset_1 @ ( sk_C_1 @ X25 @ X26 ) @ X26 )
      | ( X25 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_C_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k1_tarski @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('21',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( v1_relat_1 @ X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k1_tarski @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','22'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('25',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k1_tarski @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','22'])).

thf(t43_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( ( C = k1_xboole_0 )
            & ( B
              = ( k1_tarski @ A ) ) )
        & ~ ( ( C
              = ( k1_tarski @ A ) )
            & ( B = k1_xboole_0 ) )
        & ~ ( ( C
              = ( k1_tarski @ A ) )
            & ( B
              = ( k1_tarski @ A ) ) )
        & ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( B
          = ( k1_tarski @ A ) )
        & ( C
          = ( k1_tarski @ A ) ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( B = k1_xboole_0 )
        & ( C
          = ( k1_tarski @ A ) ) ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
     => ( ( B
          = ( k1_tarski @ A ) )
        & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_7,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( zip_tseitin_2 @ C @ B @ A )
        & ~ ( zip_tseitin_1 @ C @ B @ A )
        & ~ ( zip_tseitin_0 @ C @ B @ A ) ) )).

thf('26',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_tarski @ X24 )
       != ( k2_xboole_0 @ X22 @ X23 ) )
      | ( zip_tseitin_2 @ X23 @ X22 @ X24 )
      | ( zip_tseitin_1 @ X23 @ X22 @ X24 )
      | ( zip_tseitin_0 @ X23 @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k2_xboole_0 @ X1 @ X0 ) )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X1 @ k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ X1 @ k1_xboole_0 )
      | ( zip_tseitin_2 @ X0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != X0 )
      | ( zip_tseitin_2 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 @ k1_xboole_0 )
      | ( zip_tseitin_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 @ k1_xboole_0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X1 ) @ k1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_1 @ ( k3_xboole_0 @ k1_xboole_0 @ X1 ) @ k1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_2 @ ( k3_xboole_0 @ k1_xboole_0 @ X1 ) @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X21
        = ( k1_tarski @ X19 ) )
      | ~ ( zip_tseitin_2 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
        = ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X17
        = ( k1_tarski @ X18 ) )
      | ~ ( zip_tseitin_1 @ X17 @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
        = ( k1_tarski @ k1_xboole_0 ) )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
        = ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
        = ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X15 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
        = ( k1_tarski @ k1_xboole_0 ) )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k1_tarski @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','22'])).

thf(t18_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf('40',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X12 = X11 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X11 ) )
       != ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t18_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
       != ( k1_tarski @ k1_xboole_0 ) )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ k1_xboole_0 ) )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0 = X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
       != ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k1_tarski @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','22'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ( k10_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','48'])).

thf('50',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','49'])).

thf('51',plain,(
    $false ),
    inference(simplify,[status(thm)],['50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tp4CIvpxSb
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 21:00:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.35/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.54  % Solved by: fo/fo7.sh
% 0.35/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.54  % done 119 iterations in 0.077s
% 0.35/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.54  % SZS output start Refutation
% 0.35/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.35/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.54  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.35/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.35/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.54  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.35/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.35/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.54  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.35/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.35/0.54  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.35/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.35/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.54  thf(t172_relat_1, conjecture,
% 0.35/0.54    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.35/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.54    (~( ![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.35/0.54    inference('cnf.neg', [status(esa)], [t172_relat_1])).
% 0.35/0.54  thf('0', plain, (((k10_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(t60_relat_1, axiom,
% 0.35/0.54    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.35/0.54     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.35/0.54  thf('1', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.35/0.54  thf(t167_relat_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( v1_relat_1 @ B ) =>
% 0.35/0.54       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.35/0.54  thf('2', plain,
% 0.35/0.54      (![X34 : $i, X35 : $i]:
% 0.35/0.54         ((r1_tarski @ (k10_relat_1 @ X34 @ X35) @ (k1_relat_1 @ X34))
% 0.35/0.54          | ~ (v1_relat_1 @ X34))),
% 0.35/0.54      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.35/0.54  thf(d10_xboole_0, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.35/0.54  thf('3', plain,
% 0.35/0.54      (![X0 : $i, X2 : $i]:
% 0.35/0.54         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.35/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.35/0.54  thf('4', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (~ (v1_relat_1 @ X0)
% 0.35/0.54          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.35/0.54          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.35/0.54  thf('5', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (r1_tarski @ k1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ X0))
% 0.35/0.54          | ((k1_relat_1 @ k1_xboole_0) = (k10_relat_1 @ k1_xboole_0 @ X0))
% 0.35/0.54          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['1', '4'])).
% 0.35/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.35/0.54  thf('6', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.35/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.35/0.54  thf('7', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.35/0.54  thf('8', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((k1_xboole_0) = (k10_relat_1 @ k1_xboole_0 @ X0))
% 0.35/0.54          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.35/0.54      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.35/0.54  thf(fc7_relat_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.54     ( v1_relat_1 @
% 0.35/0.54       ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ))).
% 0.35/0.54  thf('9', plain,
% 0.35/0.54      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.35/0.54         (v1_relat_1 @ 
% 0.35/0.54          (k2_tarski @ (k4_tarski @ X30 @ X31) @ (k4_tarski @ X32 @ X33)))),
% 0.35/0.54      inference('cnf', [status(esa)], [fc7_relat_1])).
% 0.35/0.54  thf(t61_setfam_1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( m1_subset_1 @
% 0.35/0.54       ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.35/0.54  thf('10', plain,
% 0.35/0.54      (![X27 : $i]:
% 0.35/0.54         (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 0.35/0.54          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X27)))),
% 0.35/0.54      inference('cnf', [status(esa)], [t61_setfam_1])).
% 0.35/0.54  thf(t10_subset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.54       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.35/0.54            ( ![C:$i]:
% 0.35/0.54              ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.35/0.54  thf('11', plain,
% 0.35/0.54      (![X25 : $i, X26 : $i]:
% 0.35/0.54         ((r2_hidden @ (sk_C_1 @ X25 @ X26) @ X25)
% 0.35/0.54          | ((X25) = (k1_xboole_0))
% 0.35/0.54          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 0.35/0.54      inference('cnf', [status(esa)], [t10_subset_1])).
% 0.35/0.54  thf('12', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))
% 0.35/0.54          | (r2_hidden @ 
% 0.35/0.54             (sk_C_1 @ (k1_tarski @ k1_xboole_0) @ (k1_zfmisc_1 @ X0)) @ 
% 0.35/0.54             (k1_tarski @ k1_xboole_0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.35/0.54  thf(d1_tarski, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.35/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.35/0.54  thf('13', plain,
% 0.35/0.54      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X9 @ X8) | ((X9) = (X6)) | ((X8) != (k1_tarski @ X6)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d1_tarski])).
% 0.35/0.54  thf('14', plain,
% 0.35/0.54      (![X6 : $i, X9 : $i]:
% 0.35/0.54         (((X9) = (X6)) | ~ (r2_hidden @ X9 @ (k1_tarski @ X6)))),
% 0.35/0.54      inference('simplify', [status(thm)], ['13'])).
% 0.35/0.54  thf('15', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))
% 0.35/0.54          | ((sk_C_1 @ (k1_tarski @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))
% 0.35/0.54              = (k1_xboole_0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['12', '14'])).
% 0.35/0.54  thf('16', plain,
% 0.35/0.54      (![X27 : $i]:
% 0.35/0.54         (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 0.35/0.54          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X27)))),
% 0.35/0.54      inference('cnf', [status(esa)], [t61_setfam_1])).
% 0.35/0.54  thf('17', plain,
% 0.35/0.54      (![X25 : $i, X26 : $i]:
% 0.35/0.54         ((m1_subset_1 @ (sk_C_1 @ X25 @ X26) @ X26)
% 0.35/0.54          | ((X25) = (k1_xboole_0))
% 0.35/0.54          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 0.35/0.54      inference('cnf', [status(esa)], [t10_subset_1])).
% 0.35/0.54  thf('18', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))
% 0.35/0.54          | (m1_subset_1 @ 
% 0.35/0.54             (sk_C_1 @ (k1_tarski @ k1_xboole_0) @ (k1_zfmisc_1 @ X0)) @ 
% 0.35/0.54             (k1_zfmisc_1 @ X0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.35/0.54  thf('19', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.35/0.54          | ((k1_tarski @ k1_xboole_0) = (k1_xboole_0))
% 0.35/0.54          | ((k1_tarski @ k1_xboole_0) = (k1_xboole_0)))),
% 0.35/0.54      inference('sup+', [status(thm)], ['15', '18'])).
% 0.35/0.54  thf('20', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))
% 0.35/0.54          | (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 0.35/0.54      inference('simplify', [status(thm)], ['19'])).
% 0.35/0.54  thf(cc2_relat_1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( v1_relat_1 @ A ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.35/0.54  thf('21', plain,
% 0.35/0.54      (![X28 : $i, X29 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 0.35/0.54          | (v1_relat_1 @ X28)
% 0.35/0.54          | ~ (v1_relat_1 @ X29))),
% 0.35/0.54      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.35/0.54  thf('22', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))
% 0.35/0.54          | ~ (v1_relat_1 @ X0)
% 0.35/0.54          | (v1_relat_1 @ k1_xboole_0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.35/0.54  thf('23', plain,
% 0.35/0.54      (((v1_relat_1 @ k1_xboole_0)
% 0.35/0.54        | ((k1_tarski @ k1_xboole_0) = (k1_xboole_0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['9', '22'])).
% 0.35/0.54  thf(t22_xboole_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.35/0.54  thf('24', plain,
% 0.35/0.54      (![X3 : $i, X4 : $i]:
% 0.35/0.54         ((k2_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)) = (X3))),
% 0.35/0.54      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.35/0.54  thf('25', plain,
% 0.35/0.54      (((v1_relat_1 @ k1_xboole_0)
% 0.35/0.54        | ((k1_tarski @ k1_xboole_0) = (k1_xboole_0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['9', '22'])).
% 0.35/0.54  thf(t43_zfmisc_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ~( ( ~( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) = ( k1_tarski @ A ) ) ) ) & 
% 0.35/0.54          ( ~( ( ( C ) = ( k1_tarski @ A ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.35/0.54          ( ~( ( ( C ) = ( k1_tarski @ A ) ) & ( ( B ) = ( k1_tarski @ A ) ) ) ) & 
% 0.35/0.54          ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_1, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.35/0.54  thf(zf_stmt_2, axiom,
% 0.35/0.54    (![C:$i,B:$i,A:$i]:
% 0.35/0.54     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.35/0.54       ( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.35/0.54  thf(zf_stmt_4, axiom,
% 0.35/0.54    (![C:$i,B:$i,A:$i]:
% 0.35/0.54     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.35/0.54       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_5, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.35/0.54  thf(zf_stmt_6, axiom,
% 0.35/0.54    (![C:$i,B:$i,A:$i]:
% 0.35/0.54     ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.35/0.54       ( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_7, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.35/0.54          ( ~( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.35/0.54          ( ~( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.35/0.54          ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ))).
% 0.35/0.54  thf('26', plain,
% 0.35/0.54      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.35/0.54         (((k1_tarski @ X24) != (k2_xboole_0 @ X22 @ X23))
% 0.35/0.54          | (zip_tseitin_2 @ X23 @ X22 @ X24)
% 0.35/0.54          | (zip_tseitin_1 @ X23 @ X22 @ X24)
% 0.35/0.54          | (zip_tseitin_0 @ X23 @ X22 @ X24))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.35/0.54  thf('27', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (((k1_xboole_0) != (k2_xboole_0 @ X1 @ X0))
% 0.35/0.54          | (v1_relat_1 @ k1_xboole_0)
% 0.35/0.54          | (zip_tseitin_0 @ X0 @ X1 @ k1_xboole_0)
% 0.35/0.54          | (zip_tseitin_1 @ X0 @ X1 @ k1_xboole_0)
% 0.35/0.54          | (zip_tseitin_2 @ X0 @ X1 @ k1_xboole_0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['25', '26'])).
% 0.35/0.54  thf('28', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (((k1_xboole_0) != (X0))
% 0.35/0.54          | (zip_tseitin_2 @ (k3_xboole_0 @ X0 @ X1) @ X0 @ k1_xboole_0)
% 0.35/0.54          | (zip_tseitin_1 @ (k3_xboole_0 @ X0 @ X1) @ X0 @ k1_xboole_0)
% 0.35/0.54          | (zip_tseitin_0 @ (k3_xboole_0 @ X0 @ X1) @ X0 @ k1_xboole_0)
% 0.35/0.54          | (v1_relat_1 @ k1_xboole_0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['24', '27'])).
% 0.35/0.54  thf('29', plain,
% 0.35/0.54      (![X1 : $i]:
% 0.35/0.54         ((v1_relat_1 @ k1_xboole_0)
% 0.35/0.54          | (zip_tseitin_0 @ (k3_xboole_0 @ k1_xboole_0 @ X1) @ k1_xboole_0 @ 
% 0.35/0.54             k1_xboole_0)
% 0.35/0.54          | (zip_tseitin_1 @ (k3_xboole_0 @ k1_xboole_0 @ X1) @ k1_xboole_0 @ 
% 0.35/0.54             k1_xboole_0)
% 0.35/0.54          | (zip_tseitin_2 @ (k3_xboole_0 @ k1_xboole_0 @ X1) @ k1_xboole_0 @ 
% 0.35/0.54             k1_xboole_0))),
% 0.35/0.54      inference('simplify', [status(thm)], ['28'])).
% 0.35/0.54  thf('30', plain,
% 0.35/0.54      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.35/0.54         (((X21) = (k1_tarski @ X19)) | ~ (zip_tseitin_2 @ X21 @ X20 @ X19))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.35/0.54  thf('31', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((zip_tseitin_1 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0 @ 
% 0.35/0.54           k1_xboole_0)
% 0.35/0.54          | (zip_tseitin_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0 @ 
% 0.35/0.54             k1_xboole_0)
% 0.35/0.54          | (v1_relat_1 @ k1_xboole_0)
% 0.35/0.54          | ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_tarski @ k1_xboole_0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.35/0.54  thf('32', plain,
% 0.35/0.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.35/0.54         (((X17) = (k1_tarski @ X18)) | ~ (zip_tseitin_1 @ X17 @ X16 @ X18))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.35/0.54  thf('33', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_tarski @ k1_xboole_0))
% 0.35/0.54          | (v1_relat_1 @ k1_xboole_0)
% 0.35/0.54          | (zip_tseitin_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0 @ 
% 0.35/0.54             k1_xboole_0)
% 0.35/0.54          | ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_tarski @ k1_xboole_0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.35/0.54  thf('34', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((zip_tseitin_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0 @ 
% 0.35/0.54           k1_xboole_0)
% 0.35/0.54          | (v1_relat_1 @ k1_xboole_0)
% 0.35/0.54          | ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_tarski @ k1_xboole_0)))),
% 0.35/0.54      inference('simplify', [status(thm)], ['33'])).
% 0.35/0.54  thf('35', plain,
% 0.35/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.35/0.54         (((X15) = (k1_xboole_0)) | ~ (zip_tseitin_0 @ X15 @ X14 @ X13))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.35/0.54  thf('36', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_tarski @ k1_xboole_0))
% 0.35/0.54          | (v1_relat_1 @ k1_xboole_0)
% 0.35/0.54          | ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['34', '35'])).
% 0.35/0.54  thf('37', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.35/0.54          | (v1_relat_1 @ k1_xboole_0)
% 0.35/0.54          | ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.35/0.54          | (v1_relat_1 @ k1_xboole_0))),
% 0.35/0.54      inference('sup+', [status(thm)], ['23', '36'])).
% 0.35/0.54  thf('38', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((v1_relat_1 @ k1_xboole_0)
% 0.35/0.54          | ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.35/0.54      inference('simplify', [status(thm)], ['37'])).
% 0.35/0.54  thf('39', plain,
% 0.35/0.54      (((v1_relat_1 @ k1_xboole_0)
% 0.35/0.54        | ((k1_tarski @ k1_xboole_0) = (k1_xboole_0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['9', '22'])).
% 0.35/0.54  thf(t18_zfmisc_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.35/0.54         ( k1_tarski @ A ) ) =>
% 0.35/0.54       ( ( A ) = ( B ) ) ))).
% 0.35/0.54  thf('40', plain,
% 0.35/0.54      (![X11 : $i, X12 : $i]:
% 0.35/0.54         (((X12) = (X11))
% 0.35/0.54          | ((k3_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X11))
% 0.35/0.54              != (k1_tarski @ X12)))),
% 0.35/0.54      inference('cnf', [status(esa)], [t18_zfmisc_1])).
% 0.35/0.54  thf('41', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.35/0.54            != (k1_tarski @ k1_xboole_0))
% 0.35/0.54          | (v1_relat_1 @ k1_xboole_0)
% 0.35/0.54          | ((k1_xboole_0) = (X0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['39', '40'])).
% 0.35/0.54  thf('42', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((k1_xboole_0) != (k1_tarski @ k1_xboole_0))
% 0.35/0.54          | (v1_relat_1 @ k1_xboole_0)
% 0.35/0.54          | ((k1_xboole_0) = (X0))
% 0.35/0.54          | (v1_relat_1 @ k1_xboole_0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['38', '41'])).
% 0.35/0.54  thf('43', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((k1_xboole_0) = (X0))
% 0.35/0.54          | (v1_relat_1 @ k1_xboole_0)
% 0.35/0.54          | ((k1_xboole_0) != (k1_tarski @ k1_xboole_0)))),
% 0.35/0.54      inference('simplify', [status(thm)], ['42'])).
% 0.35/0.54  thf('44', plain,
% 0.35/0.54      (((v1_relat_1 @ k1_xboole_0)
% 0.35/0.54        | ((k1_tarski @ k1_xboole_0) = (k1_xboole_0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['9', '22'])).
% 0.35/0.54  thf('45', plain,
% 0.35/0.54      (![X0 : $i]: ((v1_relat_1 @ k1_xboole_0) | ((k1_xboole_0) = (X0)))),
% 0.35/0.54      inference('clc', [status(thm)], ['43', '44'])).
% 0.35/0.54  thf('46', plain, (((k10_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('47', plain,
% 0.35/0.54      ((((k1_xboole_0) != (k1_xboole_0)) | (v1_relat_1 @ k1_xboole_0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['45', '46'])).
% 0.35/0.54  thf('48', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.35/0.54      inference('simplify', [status(thm)], ['47'])).
% 0.35/0.54  thf('49', plain,
% 0.35/0.54      (![X0 : $i]: ((k1_xboole_0) = (k10_relat_1 @ k1_xboole_0 @ X0))),
% 0.35/0.54      inference('demod', [status(thm)], ['8', '48'])).
% 0.35/0.54  thf('50', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.35/0.54      inference('demod', [status(thm)], ['0', '49'])).
% 0.35/0.54  thf('51', plain, ($false), inference('simplify', [status(thm)], ['50'])).
% 0.35/0.54  
% 0.35/0.54  % SZS output end Refutation
% 0.35/0.54  
% 0.35/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
