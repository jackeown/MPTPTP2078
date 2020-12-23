%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dStMISCvTS

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 386 expanded)
%              Number of leaves         :   54 ( 148 expanded)
%              Depth                    :   23
%              Number of atoms          :  689 (2032 expanded)
%              Number of equality atoms :   91 ( 278 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $o )).

thf(v4_ordinal1_type,type,(
    v4_ordinal1: $i > $o )).

thf(k6_numbers_type,type,(
    k6_numbers: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(t18_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_relat_1 @ C ) )
           => ~ ( ( r1_tarski @ ( k2_relat_1 @ C ) @ A )
                & ( B
                  = ( k1_relat_1 @ C ) ) ) )
        & ~ ( ( B != k1_xboole_0 )
            & ( A = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( ( zip_tseitin_0 @ C )
       => ~ ( zip_tseitin_1 @ C @ B @ A ) )
     => ( zip_tseitin_2 @ C @ B @ A ) ) )).

thf('0',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( zip_tseitin_2 @ X35 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( zip_tseitin_2 @ X35 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_1,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_3 @ B @ A )
     => ( ( A = k1_xboole_0 )
        & ( B != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( B
          = ( k1_relat_1 @ C ) )
        & ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [C: $i] :
      ( ( zip_tseitin_0 @ C )
     => ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) ) ) )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( zip_tseitin_3 @ B @ A )
        & ! [C: $i] :
            ( zip_tseitin_2 @ C @ B @ A ) ) )).

thf('2',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_3 @ X40 @ X41 )
      | ~ ( zip_tseitin_2 @ ( sk_C_1 @ X40 @ X41 ) @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ ( sk_C_1 @ X1 @ X0 ) @ X1 @ X0 )
      | ( zip_tseitin_3 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X33
        = ( k1_relat_1 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X1 @ X0 )
      | ( X1
        = ( k1_relat_1 @ ( sk_C_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('6',plain,(
    ! [X30: $i] :
      ( ( ( k1_relat_1 @ X30 )
       != k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('7',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('8',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('9',plain,(
    ! [X30: $i] :
      ( ( ( k1_relat_1 @ X30 )
       != o_0_0_xboole_0 )
      | ( X30 = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != o_0_0_xboole_0 )
      | ( zip_tseitin_3 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X0 @ X1 ) )
      | ( ( sk_C_1 @ X0 @ X1 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X1: $i] :
      ( ( ( sk_C_1 @ o_0_0_xboole_0 @ X1 )
        = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ o_0_0_xboole_0 @ X1 ) )
      | ( zip_tseitin_3 @ o_0_0_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( zip_tseitin_2 @ X35 @ X36 @ X37 )
      | ( zip_tseitin_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_3 @ X40 @ X41 )
      | ~ ( zip_tseitin_2 @ ( sk_C_1 @ X40 @ X41 ) @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_C_1 @ X1 @ X0 ) )
      | ( zip_tseitin_3 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X31: $i] :
      ( ( v1_relat_1 @ X31 )
      | ~ ( zip_tseitin_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X1 @ X0 )
      | ( v1_relat_1 @ ( sk_C_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X1: $i] :
      ( ( zip_tseitin_3 @ o_0_0_xboole_0 @ X1 )
      | ( ( sk_C_1 @ o_0_0_xboole_0 @ X1 )
        = o_0_0_xboole_0 ) ) ),
    inference(clc,[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X38: $i,X39: $i] :
      ( ( X39 != k1_xboole_0 )
      | ~ ( zip_tseitin_3 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('19',plain,(
    ! [X38: $i] :
      ~ ( zip_tseitin_3 @ k1_xboole_0 @ X38 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('21',plain,(
    ! [X38: $i] :
      ~ ( zip_tseitin_3 @ o_0_0_xboole_0 @ X38 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X1: $i] :
      ( ( sk_C_1 @ o_0_0_xboole_0 @ X1 )
      = o_0_0_xboole_0 ) ),
    inference(clc,[status(thm)],['17','21'])).

thf('23',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_3 @ X40 @ X41 )
      | ~ ( zip_tseitin_2 @ ( sk_C_1 @ X40 @ X41 ) @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ o_0_0_xboole_0 @ o_0_0_xboole_0 @ X0 )
      | ( zip_tseitin_3 @ o_0_0_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X38: $i] :
      ~ ( zip_tseitin_3 @ o_0_0_xboole_0 @ X38 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('26',plain,(
    ! [X0: $i] :
      ~ ( zip_tseitin_2 @ o_0_0_xboole_0 @ o_0_0_xboole_0 @ X0 ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['0','26'])).

thf('28',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X32 ) @ X34 )
      | ~ ( zip_tseitin_1 @ X32 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ o_0_0_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('30',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(redefinition_k6_numbers,axiom,(
    k6_numbers = k1_xboole_0 )).

thf('31',plain,(
    k6_numbers = k1_xboole_0 ),
    inference(cnf,[status(esa)],[redefinition_k6_numbers])).

thf('32',plain,(
    k6_numbers = k1_xboole_0 ),
    inference(cnf,[status(esa)],[redefinition_k6_numbers])).

thf('33',plain,
    ( ( k2_relat_1 @ k6_numbers )
    = k6_numbers ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    k6_numbers = k1_xboole_0 ),
    inference(cnf,[status(esa)],[redefinition_k6_numbers])).

thf('35',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('36',plain,(
    k6_numbers = o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    k6_numbers = o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['34','35'])).

thf('38',plain,
    ( ( k2_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['33','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ o_0_0_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['29','38'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('40',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ( r2_hidden @ X14 @ X16 )
      | ( X16
       != ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('41',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('42',plain,(
    ! [X46: $i] :
      ( ( k9_setfam_1 @ X46 )
      = ( k1_zfmisc_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('43',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ ( k9_setfam_1 @ X15 ) )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r2_hidden @ o_0_0_xboole_0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf(t13_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ k1_xboole_0 @ A )
       => ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) )
          = k1_xboole_0 ) ) ) )).

thf('45',plain,(
    ! [X48: $i] :
      ( ~ ( r2_hidden @ k1_xboole_0 @ X48 )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ X48 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow_1])).

thf('46',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('47',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('48',plain,(
    ! [X48: $i] :
      ( ~ ( r2_hidden @ o_0_0_xboole_0 @ X48 )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ X48 ) )
        = o_0_0_xboole_0 )
      | ( v1_xboole_0 @ X48 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','48'])).

thf(t4_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ) )).

thf('50',plain,(
    ! [X49: $i] :
      ( ( k3_yellow_1 @ X49 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k3_yellow_0 @ ( k3_yellow_1 @ X0 ) )
        = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t18_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) )
      = k1_xboole_0 ) )).

thf(zf_stmt_9,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t18_yellow_1])).

thf('52',plain,(
    ( k3_yellow_0 @ ( k3_yellow_1 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('53',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('54',plain,(
    ( k3_yellow_0 @ ( k3_yellow_1 @ sk_A ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['55'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('57',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('58',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k9_setfam_1 @ sk_A )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,
    ( ( k9_setfam_1 @ sk_A )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['56','59'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('62',plain,(
    ! [X25: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('63',plain,(
    ! [X46: $i] :
      ( ( k9_setfam_1 @ X46 )
      = ( k1_zfmisc_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('64',plain,(
    ! [X25: $i] :
      ( ( k3_tarski @ ( k9_setfam_1 @ X25 ) )
      = X25 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf(d6_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v4_ordinal1 @ A )
    <=> ( A
        = ( k3_tarski @ A ) ) ) )).

thf('65',plain,(
    ! [X43: $i] :
      ( ( X43
        = ( k3_tarski @ X43 ) )
      | ~ ( v4_ordinal1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[d6_ordinal1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k9_setfam_1 @ X0 )
        = X0 )
      | ~ ( v4_ordinal1 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v4_ordinal1 @ o_0_0_xboole_0 )
    | ( ( k9_setfam_1 @ sk_A )
      = sk_A ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('68',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('69',plain,(
    k6_numbers = k1_xboole_0 ),
    inference(cnf,[status(esa)],[redefinition_k6_numbers])).

thf('70',plain,(
    k6_numbers = k1_xboole_0 ),
    inference(cnf,[status(esa)],[redefinition_k6_numbers])).

thf('71',plain,
    ( ( k3_tarski @ k6_numbers )
    = k6_numbers ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    k6_numbers = o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['34','35'])).

thf('73',plain,(
    k6_numbers = o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['34','35'])).

thf('74',plain,
    ( ( k3_tarski @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X44: $i] :
      ( ( v4_ordinal1 @ X44 )
      | ( X44
       != ( k3_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[d6_ordinal1])).

thf('76',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( v4_ordinal1 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v4_ordinal1 @ o_0_0_xboole_0 ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( k9_setfam_1 @ sk_A )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['56','59'])).

thf('79',plain,(
    o_0_0_xboole_0 = sk_A ),
    inference(demod,[status(thm)],['67','77','78'])).

thf('80',plain,
    ( ( k9_setfam_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['60','79'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('81',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('82',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ ( k9_setfam_1 @ X15 ) )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('84',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    r2_hidden @ o_0_0_xboole_0 @ o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['80','84'])).

thf(t52_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k6_subset_1 @ ( k1_ordinal1 @ A ) @ ( k1_tarski @ A ) )
      = A ) )).

thf('86',plain,(
    ! [X45: $i] :
      ( ( k6_subset_1 @ ( k1_ordinal1 @ X45 ) @ ( k1_tarski @ X45 ) )
      = X45 ) ),
    inference(cnf,[status(esa)],[t52_ordinal1])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('87',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X19 != X21 )
      | ~ ( r2_hidden @ X19 @ ( k4_xboole_0 @ X20 @ ( k1_tarski @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('88',plain,(
    ! [X20: $i,X21: $i] :
      ~ ( r2_hidden @ X21 @ ( k4_xboole_0 @ X20 @ ( k1_tarski @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('89',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k6_subset_1 @ X26 @ X27 )
      = ( k4_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('90',plain,(
    ! [X20: $i,X21: $i] :
      ~ ( r2_hidden @ X21 @ ( k6_subset_1 @ X20 @ ( k1_tarski @ X21 ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['86','90'])).

thf('92',plain,(
    $false ),
    inference('sup-',[status(thm)],['85','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dStMISCvTS
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:49:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 213 iterations in 0.070s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.21/0.53  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.21/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.53  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.53  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $o).
% 0.21/0.53  thf(v4_ordinal1_type, type, v4_ordinal1: $i > $o).
% 0.21/0.53  thf(k6_numbers_type, type, k6_numbers: $i).
% 0.21/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.53  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.53  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.21/0.53  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.21/0.53  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.21/0.53  thf(t18_funct_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ~( ( ![C:$i]:
% 0.21/0.53            ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 0.21/0.53              ( ~( ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) & 
% 0.21/0.53                   ( ( B ) = ( k1_relat_1 @ C ) ) ) ) ) ) & 
% 0.21/0.53          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, axiom,
% 0.21/0.53    (![C:$i,B:$i,A:$i]:
% 0.21/0.53     ( ( ( zip_tseitin_0 @ C ) => ( ~( zip_tseitin_1 @ C @ B @ A ) ) ) =>
% 0.21/0.53       ( zip_tseitin_2 @ C @ B @ A ) ))).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.21/0.53         ((zip_tseitin_2 @ X35 @ X36 @ X37) | (zip_tseitin_1 @ X35 @ X36 @ X37))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.21/0.53         ((zip_tseitin_2 @ X35 @ X36 @ X37) | (zip_tseitin_1 @ X35 @ X36 @ X37))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(zf_stmt_1, type, zip_tseitin_3 : $i > $i > $o).
% 0.21/0.53  thf(zf_stmt_2, axiom,
% 0.21/0.53    (![B:$i,A:$i]:
% 0.21/0.53     ( ( zip_tseitin_3 @ B @ A ) =>
% 0.21/0.53       ( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.21/0.53  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.53  thf(zf_stmt_5, axiom,
% 0.21/0.53    (![C:$i,B:$i,A:$i]:
% 0.21/0.53     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.53       ( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.21/0.53         ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ))).
% 0.21/0.53  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $o).
% 0.21/0.53  thf(zf_stmt_7, axiom,
% 0.21/0.53    (![C:$i]:
% 0.21/0.53     ( ( zip_tseitin_0 @ C ) => ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) ))).
% 0.21/0.53  thf(zf_stmt_8, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ~( ( ~( zip_tseitin_3 @ B @ A ) ) & 
% 0.21/0.53          ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X40 : $i, X41 : $i]:
% 0.21/0.53         ((zip_tseitin_3 @ X40 @ X41)
% 0.21/0.53          | ~ (zip_tseitin_2 @ (sk_C_1 @ X40 @ X41) @ X40 @ X41))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((zip_tseitin_1 @ (sk_C_1 @ X1 @ X0) @ X1 @ X0)
% 0.21/0.53          | (zip_tseitin_3 @ X1 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.21/0.53         (((X33) = (k1_relat_1 @ X32)) | ~ (zip_tseitin_1 @ X32 @ X33 @ X34))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((zip_tseitin_3 @ X1 @ X0)
% 0.21/0.53          | ((X1) = (k1_relat_1 @ (sk_C_1 @ X1 @ X0))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.53  thf(t64_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.53           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.53         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X30 : $i]:
% 0.21/0.53         (((k1_relat_1 @ X30) != (k1_xboole_0))
% 0.21/0.53          | ((X30) = (k1_xboole_0))
% 0.21/0.53          | ~ (v1_relat_1 @ X30))),
% 0.21/0.53      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.53  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.21/0.53  thf('7', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.21/0.53  thf('8', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X30 : $i]:
% 0.21/0.53         (((k1_relat_1 @ X30) != (o_0_0_xboole_0))
% 0.21/0.53          | ((X30) = (o_0_0_xboole_0))
% 0.21/0.53          | ~ (v1_relat_1 @ X30))),
% 0.21/0.53      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (((X0) != (o_0_0_xboole_0))
% 0.21/0.53          | (zip_tseitin_3 @ X0 @ X1)
% 0.21/0.53          | ~ (v1_relat_1 @ (sk_C_1 @ X0 @ X1))
% 0.21/0.53          | ((sk_C_1 @ X0 @ X1) = (o_0_0_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '9'])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X1 : $i]:
% 0.21/0.53         (((sk_C_1 @ o_0_0_xboole_0 @ X1) = (o_0_0_xboole_0))
% 0.21/0.53          | ~ (v1_relat_1 @ (sk_C_1 @ o_0_0_xboole_0 @ X1))
% 0.21/0.53          | (zip_tseitin_3 @ o_0_0_xboole_0 @ X1))),
% 0.21/0.53      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.21/0.53         ((zip_tseitin_2 @ X35 @ X36 @ X37) | (zip_tseitin_0 @ X35))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X40 : $i, X41 : $i]:
% 0.21/0.53         ((zip_tseitin_3 @ X40 @ X41)
% 0.21/0.53          | ~ (zip_tseitin_2 @ (sk_C_1 @ X40 @ X41) @ X40 @ X41))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((zip_tseitin_0 @ (sk_C_1 @ X1 @ X0)) | (zip_tseitin_3 @ X1 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X31 : $i]: ((v1_relat_1 @ X31) | ~ (zip_tseitin_0 @ X31))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((zip_tseitin_3 @ X1 @ X0) | (v1_relat_1 @ (sk_C_1 @ X1 @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X1 : $i]:
% 0.21/0.53         ((zip_tseitin_3 @ o_0_0_xboole_0 @ X1)
% 0.21/0.53          | ((sk_C_1 @ o_0_0_xboole_0 @ X1) = (o_0_0_xboole_0)))),
% 0.21/0.53      inference('clc', [status(thm)], ['11', '16'])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X38 : $i, X39 : $i]:
% 0.21/0.53         (((X39) != (k1_xboole_0)) | ~ (zip_tseitin_3 @ X39 @ X38))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.53  thf('19', plain, (![X38 : $i]: ~ (zip_tseitin_3 @ k1_xboole_0 @ X38)),
% 0.21/0.53      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.53  thf('20', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.21/0.53  thf('21', plain, (![X38 : $i]: ~ (zip_tseitin_3 @ o_0_0_xboole_0 @ X38)),
% 0.21/0.53      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (![X1 : $i]: ((sk_C_1 @ o_0_0_xboole_0 @ X1) = (o_0_0_xboole_0))),
% 0.21/0.53      inference('clc', [status(thm)], ['17', '21'])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X40 : $i, X41 : $i]:
% 0.21/0.53         ((zip_tseitin_3 @ X40 @ X41)
% 0.21/0.53          | ~ (zip_tseitin_2 @ (sk_C_1 @ X40 @ X41) @ X40 @ X41))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (zip_tseitin_2 @ o_0_0_xboole_0 @ o_0_0_xboole_0 @ X0)
% 0.21/0.53          | (zip_tseitin_3 @ o_0_0_xboole_0 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.53  thf('25', plain, (![X38 : $i]: ~ (zip_tseitin_3 @ o_0_0_xboole_0 @ X38)),
% 0.21/0.53      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (![X0 : $i]: ~ (zip_tseitin_2 @ o_0_0_xboole_0 @ o_0_0_xboole_0 @ X0)),
% 0.21/0.53      inference('clc', [status(thm)], ['24', '25'])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (![X0 : $i]: (zip_tseitin_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 @ X0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '26'])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.21/0.53         ((r1_tarski @ (k2_relat_1 @ X32) @ X34)
% 0.21/0.53          | ~ (zip_tseitin_1 @ X32 @ X33 @ X34))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ o_0_0_xboole_0) @ X0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.53  thf(t60_relat_1, axiom,
% 0.21/0.53    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.53     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.53  thf('30', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.53  thf(redefinition_k6_numbers, axiom, (( k6_numbers ) = ( k1_xboole_0 ))).
% 0.21/0.53  thf('31', plain, (((k6_numbers) = (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_k6_numbers])).
% 0.21/0.53  thf('32', plain, (((k6_numbers) = (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_k6_numbers])).
% 0.21/0.53  thf('33', plain, (((k2_relat_1 @ k6_numbers) = (k6_numbers))),
% 0.21/0.53      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.21/0.53  thf('34', plain, (((k6_numbers) = (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_k6_numbers])).
% 0.21/0.53  thf('35', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.21/0.53  thf('36', plain, (((k6_numbers) = (o_0_0_xboole_0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['34', '35'])).
% 0.21/0.53  thf('37', plain, (((k6_numbers) = (o_0_0_xboole_0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['34', '35'])).
% 0.21/0.53  thf('38', plain, (((k2_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.21/0.53      inference('demod', [status(thm)], ['33', '36', '37'])).
% 0.21/0.53  thf('39', plain, (![X0 : $i]: (r1_tarski @ o_0_0_xboole_0 @ X0)),
% 0.21/0.53      inference('demod', [status(thm)], ['29', '38'])).
% 0.21/0.53  thf(d1_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X14 @ X15)
% 0.21/0.53          | (r2_hidden @ X14 @ X16)
% 0.21/0.53          | ((X16) != (k1_zfmisc_1 @ X15)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      (![X14 : $i, X15 : $i]:
% 0.21/0.53         ((r2_hidden @ X14 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X14 @ X15))),
% 0.21/0.53      inference('simplify', [status(thm)], ['40'])).
% 0.21/0.53  thf(redefinition_k9_setfam_1, axiom,
% 0.21/0.53    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.53  thf('42', plain, (![X46 : $i]: ((k9_setfam_1 @ X46) = (k1_zfmisc_1 @ X46))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.53  thf('43', plain,
% 0.21/0.53      (![X14 : $i, X15 : $i]:
% 0.21/0.53         ((r2_hidden @ X14 @ (k9_setfam_1 @ X15)) | ~ (r1_tarski @ X14 @ X15))),
% 0.21/0.53      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      (![X0 : $i]: (r2_hidden @ o_0_0_xboole_0 @ (k9_setfam_1 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['39', '43'])).
% 0.21/0.53  thf(t13_yellow_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.53       ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.21/0.53         ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      (![X48 : $i]:
% 0.21/0.53         (~ (r2_hidden @ k1_xboole_0 @ X48)
% 0.21/0.53          | ((k3_yellow_0 @ (k2_yellow_1 @ X48)) = (k1_xboole_0))
% 0.21/0.53          | (v1_xboole_0 @ X48))),
% 0.21/0.53      inference('cnf', [status(esa)], [t13_yellow_1])).
% 0.21/0.53  thf('46', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.21/0.53  thf('47', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.21/0.53  thf('48', plain,
% 0.21/0.53      (![X48 : $i]:
% 0.21/0.53         (~ (r2_hidden @ o_0_0_xboole_0 @ X48)
% 0.21/0.53          | ((k3_yellow_0 @ (k2_yellow_1 @ X48)) = (o_0_0_xboole_0))
% 0.21/0.53          | (v1_xboole_0 @ X48))),
% 0.21/0.53      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.21/0.53          | ((k3_yellow_0 @ (k2_yellow_1 @ (k9_setfam_1 @ X0)))
% 0.21/0.53              = (o_0_0_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['44', '48'])).
% 0.21/0.53  thf(t4_yellow_1, axiom,
% 0.21/0.53    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ))).
% 0.21/0.53  thf('50', plain,
% 0.21/0.53      (![X49 : $i]: ((k3_yellow_1 @ X49) = (k2_yellow_1 @ (k9_setfam_1 @ X49)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.21/0.53  thf('51', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.21/0.53          | ((k3_yellow_0 @ (k3_yellow_1 @ X0)) = (o_0_0_xboole_0)))),
% 0.21/0.53      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.53  thf(t18_yellow_1, conjecture,
% 0.21/0.53    (![A:$i]: ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( k1_xboole_0 ) ))).
% 0.21/0.53  thf(zf_stmt_9, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]: ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t18_yellow_1])).
% 0.21/0.53  thf('52', plain, (((k3_yellow_0 @ (k3_yellow_1 @ sk_A)) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.53  thf('53', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.21/0.53  thf('54', plain,
% 0.21/0.53      (((k3_yellow_0 @ (k3_yellow_1 @ sk_A)) != (o_0_0_xboole_0))),
% 0.21/0.53      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.53  thf('55', plain,
% 0.21/0.53      ((((o_0_0_xboole_0) != (o_0_0_xboole_0))
% 0.21/0.53        | (v1_xboole_0 @ (k9_setfam_1 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['51', '54'])).
% 0.21/0.53  thf('56', plain, ((v1_xboole_0 @ (k9_setfam_1 @ sk_A))),
% 0.21/0.53      inference('simplify', [status(thm)], ['55'])).
% 0.21/0.53  thf(l13_xboole_0, axiom,
% 0.21/0.53    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.53  thf('57', plain,
% 0.21/0.53      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.53  thf('58', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.21/0.53  thf('59', plain,
% 0.21/0.53      (![X0 : $i]: (((X0) = (o_0_0_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['57', '58'])).
% 0.21/0.53  thf('60', plain, (((k9_setfam_1 @ sk_A) = (o_0_0_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['56', '59'])).
% 0.21/0.53  thf('61', plain, (((k9_setfam_1 @ sk_A) = (o_0_0_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['56', '59'])).
% 0.21/0.53  thf(t99_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.21/0.53  thf('62', plain, (![X25 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X25)) = (X25))),
% 0.21/0.53      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.21/0.53  thf('63', plain, (![X46 : $i]: ((k9_setfam_1 @ X46) = (k1_zfmisc_1 @ X46))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.53  thf('64', plain, (![X25 : $i]: ((k3_tarski @ (k9_setfam_1 @ X25)) = (X25))),
% 0.21/0.53      inference('demod', [status(thm)], ['62', '63'])).
% 0.21/0.53  thf(d6_ordinal1, axiom,
% 0.21/0.53    (![A:$i]: ( ( v4_ordinal1 @ A ) <=> ( ( A ) = ( k3_tarski @ A ) ) ))).
% 0.21/0.53  thf('65', plain,
% 0.21/0.53      (![X43 : $i]: (((X43) = (k3_tarski @ X43)) | ~ (v4_ordinal1 @ X43))),
% 0.21/0.53      inference('cnf', [status(esa)], [d6_ordinal1])).
% 0.21/0.53  thf('66', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k9_setfam_1 @ X0) = (X0)) | ~ (v4_ordinal1 @ (k9_setfam_1 @ X0)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['64', '65'])).
% 0.21/0.53  thf('67', plain,
% 0.21/0.53      ((~ (v4_ordinal1 @ o_0_0_xboole_0) | ((k9_setfam_1 @ sk_A) = (sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['61', '66'])).
% 0.21/0.53  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.21/0.53  thf('68', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.21/0.53  thf('69', plain, (((k6_numbers) = (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_k6_numbers])).
% 0.21/0.53  thf('70', plain, (((k6_numbers) = (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_k6_numbers])).
% 0.21/0.53  thf('71', plain, (((k3_tarski @ k6_numbers) = (k6_numbers))),
% 0.21/0.53      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.21/0.53  thf('72', plain, (((k6_numbers) = (o_0_0_xboole_0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['34', '35'])).
% 0.21/0.53  thf('73', plain, (((k6_numbers) = (o_0_0_xboole_0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['34', '35'])).
% 0.21/0.53  thf('74', plain, (((k3_tarski @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.21/0.53      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.21/0.53  thf('75', plain,
% 0.21/0.53      (![X44 : $i]: ((v4_ordinal1 @ X44) | ((X44) != (k3_tarski @ X44)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d6_ordinal1])).
% 0.21/0.53  thf('76', plain,
% 0.21/0.53      ((((o_0_0_xboole_0) != (o_0_0_xboole_0)) | (v4_ordinal1 @ o_0_0_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['74', '75'])).
% 0.21/0.53  thf('77', plain, ((v4_ordinal1 @ o_0_0_xboole_0)),
% 0.21/0.53      inference('simplify', [status(thm)], ['76'])).
% 0.21/0.53  thf('78', plain, (((k9_setfam_1 @ sk_A) = (o_0_0_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['56', '59'])).
% 0.21/0.53  thf('79', plain, (((o_0_0_xboole_0) = (sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['67', '77', '78'])).
% 0.21/0.53  thf('80', plain, (((k9_setfam_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.21/0.53      inference('demod', [status(thm)], ['60', '79'])).
% 0.21/0.53  thf(d10_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.53  thf('81', plain,
% 0.21/0.53      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.53  thf('82', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.21/0.53      inference('simplify', [status(thm)], ['81'])).
% 0.21/0.53  thf('83', plain,
% 0.21/0.53      (![X14 : $i, X15 : $i]:
% 0.21/0.53         ((r2_hidden @ X14 @ (k9_setfam_1 @ X15)) | ~ (r1_tarski @ X14 @ X15))),
% 0.21/0.53      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.53  thf('84', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k9_setfam_1 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['82', '83'])).
% 0.21/0.53  thf('85', plain, ((r2_hidden @ o_0_0_xboole_0 @ o_0_0_xboole_0)),
% 0.21/0.53      inference('sup+', [status(thm)], ['80', '84'])).
% 0.21/0.53  thf(t52_ordinal1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( k6_subset_1 @ ( k1_ordinal1 @ A ) @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.21/0.53  thf('86', plain,
% 0.21/0.53      (![X45 : $i]:
% 0.21/0.53         ((k6_subset_1 @ (k1_ordinal1 @ X45) @ (k1_tarski @ X45)) = (X45))),
% 0.21/0.53      inference('cnf', [status(esa)], [t52_ordinal1])).
% 0.21/0.53  thf(t64_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.21/0.53       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.21/0.53  thf('87', plain,
% 0.21/0.53      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.53         (((X19) != (X21))
% 0.21/0.53          | ~ (r2_hidden @ X19 @ (k4_xboole_0 @ X20 @ (k1_tarski @ X21))))),
% 0.21/0.53      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.21/0.53  thf('88', plain,
% 0.21/0.53      (![X20 : $i, X21 : $i]:
% 0.21/0.53         ~ (r2_hidden @ X21 @ (k4_xboole_0 @ X20 @ (k1_tarski @ X21)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['87'])).
% 0.21/0.53  thf(redefinition_k6_subset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.53  thf('89', plain,
% 0.21/0.53      (![X26 : $i, X27 : $i]:
% 0.21/0.53         ((k6_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.53  thf('90', plain,
% 0.21/0.53      (![X20 : $i, X21 : $i]:
% 0.21/0.53         ~ (r2_hidden @ X21 @ (k6_subset_1 @ X20 @ (k1_tarski @ X21)))),
% 0.21/0.53      inference('demod', [status(thm)], ['88', '89'])).
% 0.21/0.53  thf('91', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ X0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['86', '90'])).
% 0.21/0.53  thf('92', plain, ($false), inference('sup-', [status(thm)], ['85', '91'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
