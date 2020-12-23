%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hJpeLs3PvA

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:13 EST 2020

% Result     : Theorem 0.96s
% Output     : Refutation 0.96s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 154 expanded)
%              Number of leaves         :   47 (  67 expanded)
%              Depth                    :   19
%              Number of atoms          :  751 (1026 expanded)
%              Number of equality atoms :   85 ( 117 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i > $i )).

thf(t18_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t18_yellow_1])).

thf('0',plain,(
    ( k3_yellow_0 @ ( k3_yellow_1 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( ( zip_tseitin_1 @ C )
       => ~ ( zip_tseitin_2 @ C @ B @ A ) )
     => ( zip_tseitin_3 @ C @ B @ A ) ) )).

thf('1',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( zip_tseitin_3 @ X53 @ X54 @ X55 )
      | ( zip_tseitin_2 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( zip_tseitin_3 @ X53 @ X54 @ X55 )
      | ( zip_tseitin_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(zf_stmt_2,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_4 @ B @ A )
     => ( ( A = k1_xboole_0 )
        & ( B != k1_xboole_0 ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(zf_stmt_5,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( B
          = ( k1_relat_1 @ C ) )
        & ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) )).

thf(zf_stmt_7,type,(
    zip_tseitin_1: $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [C: $i] :
      ( ( zip_tseitin_1 @ C )
     => ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) ) ) )).

thf(zf_stmt_9,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( zip_tseitin_4 @ B @ A )
        & ! [C: $i] :
            ( zip_tseitin_3 @ C @ B @ A ) ) )).

thf('3',plain,(
    ! [X58: $i,X59: $i] :
      ( ( zip_tseitin_4 @ X58 @ X59 )
      | ~ ( zip_tseitin_3 @ ( sk_C_1 @ X58 @ X59 ) @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ( zip_tseitin_4 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X49: $i] :
      ( ( v1_relat_1 @ X49 )
      | ~ ( zip_tseitin_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('6',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( zip_tseitin_3 @ X53 @ X54 @ X55 )
      | ( zip_tseitin_2 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,(
    ! [X58: $i,X59: $i] :
      ( ( zip_tseitin_4 @ X58 @ X59 )
      | ~ ( zip_tseitin_3 @ ( sk_C_1 @ X58 @ X59 ) @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_2 @ ( sk_C_1 @ X1 @ X0 ) @ X1 @ X0 )
      | ( zip_tseitin_4 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X51
        = ( k1_relat_1 @ X50 ) )
      | ~ ( zip_tseitin_2 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_4 @ X1 @ X0 )
      | ( X1
        = ( k1_relat_1 @ ( sk_C_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('11',plain,(
    ! [X48: $i] :
      ( ( ( k1_relat_1 @ X48 )
       != k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( zip_tseitin_4 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X0 @ X1 ) )
      | ( ( sk_C_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X1: $i] :
      ( ( ( sk_C_1 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ k1_xboole_0 @ X1 ) )
      | ( zip_tseitin_4 @ k1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X56: $i,X57: $i] :
      ( ( X57 != k1_xboole_0 )
      | ~ ( zip_tseitin_4 @ X57 @ X56 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,(
    ! [X56: $i] :
      ~ ( zip_tseitin_4 @ k1_xboole_0 @ X56 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X1: $i] :
      ( ~ ( v1_relat_1 @ ( sk_C_1 @ k1_xboole_0 @ X1 ) )
      | ( ( sk_C_1 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ( ( sk_C_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_4 @ k1_xboole_0 @ X0 )
      | ( ( sk_C_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','17'])).

thf('19',plain,(
    ! [X56: $i] :
      ~ ( zip_tseitin_4 @ k1_xboole_0 @ X56 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X58: $i,X59: $i] :
      ( ( zip_tseitin_4 @ X58 @ X59 )
      | ~ ( zip_tseitin_3 @ ( sk_C_1 @ X58 @ X59 ) @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_3 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( zip_tseitin_4 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X56: $i] :
      ~ ( zip_tseitin_4 @ k1_xboole_0 @ X56 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('24',plain,(
    ! [X0: $i] :
      ~ ( zip_tseitin_3 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['1','24'])).

thf('26',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X50 ) @ X52 )
      | ~ ( zip_tseitin_2 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('28',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('30',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ X30 @ X31 )
      | ( r2_hidden @ X30 @ X32 )
      | ( X32
       != ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('31',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r2_hidden @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( r1_tarski @ X30 @ X31 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('32',plain,(
    ! [X65: $i] :
      ( ( k9_setfam_1 @ X65 )
      = ( k1_zfmisc_1 @ X65 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('33',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r2_hidden @ X30 @ ( k9_setfam_1 @ X31 ) )
      | ~ ( r1_tarski @ X30 @ X31 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf(s3_funct_1__e15_31__wellord2,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ B @ C )
            = ( k1_tarski @ C ) ) )
      & ( ( k1_relat_1 @ B )
        = A )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('35',plain,(
    ! [X63: $i] :
      ( ( k1_relat_1 @ ( sk_B_2 @ X63 ) )
      = X63 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e15_31__wellord2])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('36',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k11_relat_1 @ X46 @ X47 )
        = k1_xboole_0 )
      | ( r2_hidden @ X47 @ ( k1_relat_1 @ X46 ) )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf(t13_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ k1_xboole_0 @ A )
       => ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) )
          = k1_xboole_0 ) ) ) )).

thf('37',plain,(
    ! [X67: $i] :
      ( ~ ( r2_hidden @ k1_xboole_0 @ X67 )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ X67 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( k1_relat_1 @ X0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ ( sk_B_2 @ X0 ) ) )
      | ( ( k11_relat_1 @ ( sk_B_2 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B_2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X63: $i] :
      ( ( k1_relat_1 @ ( sk_B_2 @ X63 ) )
      = X63 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e15_31__wellord2])).

thf('41',plain,(
    ! [X63: $i] :
      ( v1_relat_1 @ ( sk_B_2 @ X63 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e15_31__wellord2])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ X0 )
      | ( ( k11_relat_1 @ ( sk_B_2 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X63: $i] :
      ( ( k1_relat_1 @ ( sk_B_2 @ X63 ) )
      = X63 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e15_31__wellord2])).

thf('44',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ X47 @ ( k1_relat_1 @ X46 ) )
      | ( ( k11_relat_1 @ X46 @ X47 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( sk_B_2 @ X0 ) )
      | ( ( k11_relat_1 @ ( sk_B_2 @ X0 ) @ X1 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X63: $i] :
      ( v1_relat_1 @ ( sk_B_2 @ X63 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e15_31__wellord2])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( ( k11_relat_1 @ ( sk_B_2 @ X0 ) @ X1 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v1_xboole_0 @ X0 )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ k1_xboole_0 @ X0 )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('50',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('51',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('52',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ X47 @ ( k1_relat_1 @ X46 ) )
      | ( ( k11_relat_1 @ X46 @ X47 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X63: $i] :
      ( ( k1_relat_1 @ ( sk_B_2 @ X63 ) )
      = X63 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e15_31__wellord2])).

thf('55',plain,(
    ! [X48: $i] :
      ( ( ( k1_relat_1 @ X48 )
       != k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B_2 @ X0 ) )
      | ( ( sk_B_2 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X63: $i] :
      ( v1_relat_1 @ ( sk_B_2 @ X63 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e15_31__wellord2])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_B_2 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( sk_B_2 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X63: $i] :
      ( v1_relat_1 @ ( sk_B_2 @ X63 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e15_31__wellord2])).

thf('61',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['53','61'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('63',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k2_zfmisc_1 @ X41 @ X42 )
        = k1_xboole_0 )
      | ( X42 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('64',plain,(
    ! [X41: $i] :
      ( ( k2_zfmisc_1 @ X41 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('65',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('66',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r2_hidden @ X30 @ ( k9_setfam_1 @ X31 ) )
      | ~ ( r1_tarski @ X30 @ X31 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('68',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf(t203_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k11_relat_1 @ ( k2_zfmisc_1 @ B @ C ) @ A )
        = C ) ) )).

thf('69',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( r2_hidden @ X43 @ X44 )
      | ( ( k11_relat_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) @ X43 )
        = X45 ) ) ),
    inference(cnf,[status(esa)],[t203_relat_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k11_relat_1 @ ( k2_zfmisc_1 @ ( k9_setfam_1 @ X0 ) @ X1 ) @ X0 )
      = X1 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( k1_xboole_0 != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['62','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ k1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['49','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','75'])).

thf(t4_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ) )).

thf('77',plain,(
    ! [X68: $i] :
      ( ( k3_yellow_1 @ X68 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X68 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k3_yellow_0 @ ( k3_yellow_1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','78'])).

thf('80',plain,(
    $false ),
    inference(simplify,[status(thm)],['79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hJpeLs3PvA
% 0.13/0.35  % Computer   : n003.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:34:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.96/1.16  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.96/1.16  % Solved by: fo/fo7.sh
% 0.96/1.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.96/1.16  % done 1302 iterations in 0.695s
% 0.96/1.16  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.96/1.16  % SZS output start Refutation
% 0.96/1.16  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.96/1.16  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.96/1.16  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.96/1.16  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.96/1.16  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.96/1.16  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $o).
% 0.96/1.16  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.96/1.16  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.96/1.16  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.96/1.16  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.96/1.16  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.96/1.16  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.96/1.16  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.96/1.16  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.96/1.16  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.96/1.16  thf(sk_A_type, type, sk_A: $i).
% 0.96/1.16  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.96/1.16  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $o).
% 0.96/1.16  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.96/1.16  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.96/1.16  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.96/1.16  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.96/1.16  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.96/1.16  thf(sk_B_2_type, type, sk_B_2: $i > $i).
% 0.96/1.16  thf(t18_yellow_1, conjecture,
% 0.96/1.16    (![A:$i]: ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( k1_xboole_0 ) ))).
% 0.96/1.16  thf(zf_stmt_0, negated_conjecture,
% 0.96/1.16    (~( ![A:$i]: ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) )),
% 0.96/1.16    inference('cnf.neg', [status(esa)], [t18_yellow_1])).
% 0.96/1.16  thf('0', plain, (((k3_yellow_0 @ (k3_yellow_1 @ sk_A)) != (k1_xboole_0))),
% 0.96/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.16  thf(t18_funct_1, axiom,
% 0.96/1.16    (![A:$i,B:$i]:
% 0.96/1.16     ( ~( ( ![C:$i]:
% 0.96/1.16            ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 0.96/1.16              ( ~( ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) & 
% 0.96/1.16                   ( ( B ) = ( k1_relat_1 @ C ) ) ) ) ) ) & 
% 0.96/1.16          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.96/1.16  thf(zf_stmt_1, axiom,
% 0.96/1.16    (![C:$i,B:$i,A:$i]:
% 0.96/1.16     ( ( ( zip_tseitin_1 @ C ) => ( ~( zip_tseitin_2 @ C @ B @ A ) ) ) =>
% 0.96/1.16       ( zip_tseitin_3 @ C @ B @ A ) ))).
% 0.96/1.16  thf('1', plain,
% 0.96/1.16      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.96/1.16         ((zip_tseitin_3 @ X53 @ X54 @ X55) | (zip_tseitin_2 @ X53 @ X54 @ X55))),
% 0.96/1.16      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.96/1.16  thf('2', plain,
% 0.96/1.16      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.96/1.16         ((zip_tseitin_3 @ X53 @ X54 @ X55) | (zip_tseitin_1 @ X53))),
% 0.96/1.16      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.96/1.16  thf(zf_stmt_2, type, zip_tseitin_4 : $i > $i > $o).
% 0.96/1.16  thf(zf_stmt_3, axiom,
% 0.96/1.16    (![B:$i,A:$i]:
% 0.96/1.16     ( ( zip_tseitin_4 @ B @ A ) =>
% 0.96/1.16       ( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 0.96/1.16  thf(zf_stmt_4, type, zip_tseitin_3 : $i > $i > $i > $o).
% 0.96/1.16  thf(zf_stmt_5, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.96/1.16  thf(zf_stmt_6, axiom,
% 0.96/1.16    (![C:$i,B:$i,A:$i]:
% 0.96/1.16     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.96/1.16       ( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.96/1.16         ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ))).
% 0.96/1.16  thf(zf_stmt_7, type, zip_tseitin_1 : $i > $o).
% 0.96/1.16  thf(zf_stmt_8, axiom,
% 0.96/1.16    (![C:$i]:
% 0.96/1.16     ( ( zip_tseitin_1 @ C ) => ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) ))).
% 0.96/1.16  thf(zf_stmt_9, axiom,
% 0.96/1.16    (![A:$i,B:$i]:
% 0.96/1.16     ( ~( ( ~( zip_tseitin_4 @ B @ A ) ) & 
% 0.96/1.16          ( ![C:$i]: ( zip_tseitin_3 @ C @ B @ A ) ) ) ))).
% 0.96/1.16  thf('3', plain,
% 0.96/1.16      (![X58 : $i, X59 : $i]:
% 0.96/1.16         ((zip_tseitin_4 @ X58 @ X59)
% 0.96/1.16          | ~ (zip_tseitin_3 @ (sk_C_1 @ X58 @ X59) @ X58 @ X59))),
% 0.96/1.16      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.96/1.16  thf('4', plain,
% 0.96/1.16      (![X0 : $i, X1 : $i]:
% 0.96/1.16         ((zip_tseitin_1 @ (sk_C_1 @ X1 @ X0)) | (zip_tseitin_4 @ X1 @ X0))),
% 0.96/1.16      inference('sup-', [status(thm)], ['2', '3'])).
% 0.96/1.16  thf('5', plain,
% 0.96/1.16      (![X49 : $i]: ((v1_relat_1 @ X49) | ~ (zip_tseitin_1 @ X49))),
% 0.96/1.16      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.96/1.16  thf('6', plain,
% 0.96/1.16      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.96/1.16         ((zip_tseitin_3 @ X53 @ X54 @ X55) | (zip_tseitin_2 @ X53 @ X54 @ X55))),
% 0.96/1.16      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.96/1.16  thf('7', plain,
% 0.96/1.16      (![X58 : $i, X59 : $i]:
% 0.96/1.16         ((zip_tseitin_4 @ X58 @ X59)
% 0.96/1.16          | ~ (zip_tseitin_3 @ (sk_C_1 @ X58 @ X59) @ X58 @ X59))),
% 0.96/1.16      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.96/1.16  thf('8', plain,
% 0.96/1.16      (![X0 : $i, X1 : $i]:
% 0.96/1.16         ((zip_tseitin_2 @ (sk_C_1 @ X1 @ X0) @ X1 @ X0)
% 0.96/1.16          | (zip_tseitin_4 @ X1 @ X0))),
% 0.96/1.16      inference('sup-', [status(thm)], ['6', '7'])).
% 0.96/1.16  thf('9', plain,
% 0.96/1.16      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.96/1.16         (((X51) = (k1_relat_1 @ X50)) | ~ (zip_tseitin_2 @ X50 @ X51 @ X52))),
% 0.96/1.16      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.96/1.16  thf('10', plain,
% 0.96/1.16      (![X0 : $i, X1 : $i]:
% 0.96/1.16         ((zip_tseitin_4 @ X1 @ X0)
% 0.96/1.16          | ((X1) = (k1_relat_1 @ (sk_C_1 @ X1 @ X0))))),
% 0.96/1.16      inference('sup-', [status(thm)], ['8', '9'])).
% 0.96/1.16  thf(t64_relat_1, axiom,
% 0.96/1.16    (![A:$i]:
% 0.96/1.16     ( ( v1_relat_1 @ A ) =>
% 0.96/1.16       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.96/1.16           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.96/1.16         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.96/1.16  thf('11', plain,
% 0.96/1.16      (![X48 : $i]:
% 0.96/1.16         (((k1_relat_1 @ X48) != (k1_xboole_0))
% 0.96/1.16          | ((X48) = (k1_xboole_0))
% 0.96/1.16          | ~ (v1_relat_1 @ X48))),
% 0.96/1.16      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.96/1.16  thf('12', plain,
% 0.96/1.16      (![X0 : $i, X1 : $i]:
% 0.96/1.16         (((X0) != (k1_xboole_0))
% 0.96/1.16          | (zip_tseitin_4 @ X0 @ X1)
% 0.96/1.16          | ~ (v1_relat_1 @ (sk_C_1 @ X0 @ X1))
% 0.96/1.16          | ((sk_C_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.96/1.16      inference('sup-', [status(thm)], ['10', '11'])).
% 0.96/1.16  thf('13', plain,
% 0.96/1.16      (![X1 : $i]:
% 0.96/1.16         (((sk_C_1 @ k1_xboole_0 @ X1) = (k1_xboole_0))
% 0.96/1.16          | ~ (v1_relat_1 @ (sk_C_1 @ k1_xboole_0 @ X1))
% 0.96/1.16          | (zip_tseitin_4 @ k1_xboole_0 @ X1))),
% 0.96/1.16      inference('simplify', [status(thm)], ['12'])).
% 0.96/1.16  thf('14', plain,
% 0.96/1.16      (![X56 : $i, X57 : $i]:
% 0.96/1.16         (((X57) != (k1_xboole_0)) | ~ (zip_tseitin_4 @ X57 @ X56))),
% 0.96/1.16      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.96/1.16  thf('15', plain, (![X56 : $i]: ~ (zip_tseitin_4 @ k1_xboole_0 @ X56)),
% 0.96/1.16      inference('simplify', [status(thm)], ['14'])).
% 0.96/1.16  thf('16', plain,
% 0.96/1.16      (![X1 : $i]:
% 0.96/1.16         (~ (v1_relat_1 @ (sk_C_1 @ k1_xboole_0 @ X1))
% 0.96/1.16          | ((sk_C_1 @ k1_xboole_0 @ X1) = (k1_xboole_0)))),
% 0.96/1.16      inference('clc', [status(thm)], ['13', '15'])).
% 0.96/1.16  thf('17', plain,
% 0.96/1.16      (![X0 : $i]:
% 0.96/1.16         (~ (zip_tseitin_1 @ (sk_C_1 @ k1_xboole_0 @ X0))
% 0.96/1.16          | ((sk_C_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.96/1.16      inference('sup-', [status(thm)], ['5', '16'])).
% 0.96/1.16  thf('18', plain,
% 0.96/1.16      (![X0 : $i]:
% 0.96/1.16         ((zip_tseitin_4 @ k1_xboole_0 @ X0)
% 0.96/1.16          | ((sk_C_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.96/1.16      inference('sup-', [status(thm)], ['4', '17'])).
% 0.96/1.16  thf('19', plain, (![X56 : $i]: ~ (zip_tseitin_4 @ k1_xboole_0 @ X56)),
% 0.96/1.16      inference('simplify', [status(thm)], ['14'])).
% 0.96/1.16  thf('20', plain, (![X0 : $i]: ((sk_C_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.96/1.16      inference('clc', [status(thm)], ['18', '19'])).
% 0.96/1.16  thf('21', plain,
% 0.96/1.16      (![X58 : $i, X59 : $i]:
% 0.96/1.16         ((zip_tseitin_4 @ X58 @ X59)
% 0.96/1.16          | ~ (zip_tseitin_3 @ (sk_C_1 @ X58 @ X59) @ X58 @ X59))),
% 0.96/1.16      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.96/1.16  thf('22', plain,
% 0.96/1.16      (![X0 : $i]:
% 0.96/1.16         (~ (zip_tseitin_3 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.96/1.16          | (zip_tseitin_4 @ k1_xboole_0 @ X0))),
% 0.96/1.16      inference('sup-', [status(thm)], ['20', '21'])).
% 0.96/1.16  thf('23', plain, (![X56 : $i]: ~ (zip_tseitin_4 @ k1_xboole_0 @ X56)),
% 0.96/1.16      inference('simplify', [status(thm)], ['14'])).
% 0.96/1.16  thf('24', plain,
% 0.96/1.16      (![X0 : $i]: ~ (zip_tseitin_3 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.96/1.16      inference('clc', [status(thm)], ['22', '23'])).
% 0.96/1.16  thf('25', plain,
% 0.96/1.16      (![X0 : $i]: (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.96/1.16      inference('sup-', [status(thm)], ['1', '24'])).
% 0.96/1.16  thf('26', plain,
% 0.96/1.16      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.96/1.16         ((r1_tarski @ (k2_relat_1 @ X50) @ X52)
% 0.96/1.16          | ~ (zip_tseitin_2 @ X50 @ X51 @ X52))),
% 0.96/1.16      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.96/1.16  thf('27', plain, (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 0.96/1.16      inference('sup-', [status(thm)], ['25', '26'])).
% 0.96/1.16  thf(t60_relat_1, axiom,
% 0.96/1.16    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.96/1.16     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.96/1.16  thf('28', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.96/1.16      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.96/1.16  thf('29', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.96/1.16      inference('demod', [status(thm)], ['27', '28'])).
% 0.96/1.16  thf(d1_zfmisc_1, axiom,
% 0.96/1.16    (![A:$i,B:$i]:
% 0.96/1.16     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.96/1.16       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.96/1.16  thf('30', plain,
% 0.96/1.16      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.96/1.16         (~ (r1_tarski @ X30 @ X31)
% 0.96/1.16          | (r2_hidden @ X30 @ X32)
% 0.96/1.16          | ((X32) != (k1_zfmisc_1 @ X31)))),
% 0.96/1.16      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.96/1.16  thf('31', plain,
% 0.96/1.16      (![X30 : $i, X31 : $i]:
% 0.96/1.16         ((r2_hidden @ X30 @ (k1_zfmisc_1 @ X31)) | ~ (r1_tarski @ X30 @ X31))),
% 0.96/1.16      inference('simplify', [status(thm)], ['30'])).
% 0.96/1.16  thf(redefinition_k9_setfam_1, axiom,
% 0.96/1.16    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.96/1.16  thf('32', plain, (![X65 : $i]: ((k9_setfam_1 @ X65) = (k1_zfmisc_1 @ X65))),
% 0.96/1.16      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.96/1.16  thf('33', plain,
% 0.96/1.16      (![X30 : $i, X31 : $i]:
% 0.96/1.16         ((r2_hidden @ X30 @ (k9_setfam_1 @ X31)) | ~ (r1_tarski @ X30 @ X31))),
% 0.96/1.16      inference('demod', [status(thm)], ['31', '32'])).
% 0.96/1.16  thf('34', plain,
% 0.96/1.16      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k9_setfam_1 @ X0))),
% 0.96/1.16      inference('sup-', [status(thm)], ['29', '33'])).
% 0.96/1.16  thf(s3_funct_1__e15_31__wellord2, axiom,
% 0.96/1.16    (![A:$i]:
% 0.96/1.16     ( ?[B:$i]:
% 0.96/1.16       ( ( ![C:$i]:
% 0.96/1.16           ( ( r2_hidden @ C @ A ) =>
% 0.96/1.16             ( ( k1_funct_1 @ B @ C ) = ( k1_tarski @ C ) ) ) ) & 
% 0.96/1.16         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.96/1.16         ( v1_relat_1 @ B ) ) ))).
% 0.96/1.16  thf('35', plain, (![X63 : $i]: ((k1_relat_1 @ (sk_B_2 @ X63)) = (X63))),
% 0.96/1.16      inference('cnf', [status(esa)], [s3_funct_1__e15_31__wellord2])).
% 0.96/1.16  thf(t205_relat_1, axiom,
% 0.96/1.16    (![A:$i,B:$i]:
% 0.96/1.16     ( ( v1_relat_1 @ B ) =>
% 0.96/1.16       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.96/1.16         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.96/1.16  thf('36', plain,
% 0.96/1.16      (![X46 : $i, X47 : $i]:
% 0.96/1.16         (((k11_relat_1 @ X46 @ X47) = (k1_xboole_0))
% 0.96/1.16          | (r2_hidden @ X47 @ (k1_relat_1 @ X46))
% 0.96/1.16          | ~ (v1_relat_1 @ X46))),
% 0.96/1.16      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.96/1.16  thf(t13_yellow_1, axiom,
% 0.96/1.16    (![A:$i]:
% 0.96/1.16     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.96/1.16       ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.96/1.16         ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ))).
% 0.96/1.16  thf('37', plain,
% 0.96/1.16      (![X67 : $i]:
% 0.96/1.16         (~ (r2_hidden @ k1_xboole_0 @ X67)
% 0.96/1.16          | ((k3_yellow_0 @ (k2_yellow_1 @ X67)) = (k1_xboole_0))
% 0.96/1.16          | (v1_xboole_0 @ X67))),
% 0.96/1.16      inference('cnf', [status(esa)], [t13_yellow_1])).
% 0.96/1.16  thf('38', plain,
% 0.96/1.16      (![X0 : $i]:
% 0.96/1.16         (~ (v1_relat_1 @ X0)
% 0.96/1.16          | ((k11_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.96/1.16          | (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.96/1.16          | ((k3_yellow_0 @ (k2_yellow_1 @ (k1_relat_1 @ X0))) = (k1_xboole_0)))),
% 0.96/1.16      inference('sup-', [status(thm)], ['36', '37'])).
% 0.96/1.16  thf('39', plain,
% 0.96/1.16      (![X0 : $i]:
% 0.96/1.16         (((k3_yellow_0 @ (k2_yellow_1 @ X0)) = (k1_xboole_0))
% 0.96/1.16          | (v1_xboole_0 @ (k1_relat_1 @ (sk_B_2 @ X0)))
% 0.96/1.16          | ((k11_relat_1 @ (sk_B_2 @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.96/1.16          | ~ (v1_relat_1 @ (sk_B_2 @ X0)))),
% 0.96/1.16      inference('sup+', [status(thm)], ['35', '38'])).
% 0.96/1.16  thf('40', plain, (![X63 : $i]: ((k1_relat_1 @ (sk_B_2 @ X63)) = (X63))),
% 0.96/1.16      inference('cnf', [status(esa)], [s3_funct_1__e15_31__wellord2])).
% 0.96/1.16  thf('41', plain, (![X63 : $i]: (v1_relat_1 @ (sk_B_2 @ X63))),
% 0.96/1.16      inference('cnf', [status(esa)], [s3_funct_1__e15_31__wellord2])).
% 0.96/1.16  thf('42', plain,
% 0.96/1.16      (![X0 : $i]:
% 0.96/1.16         (((k3_yellow_0 @ (k2_yellow_1 @ X0)) = (k1_xboole_0))
% 0.96/1.16          | (v1_xboole_0 @ X0)
% 0.96/1.16          | ((k11_relat_1 @ (sk_B_2 @ X0) @ k1_xboole_0) = (k1_xboole_0)))),
% 0.96/1.16      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.96/1.16  thf('43', plain, (![X63 : $i]: ((k1_relat_1 @ (sk_B_2 @ X63)) = (X63))),
% 0.96/1.16      inference('cnf', [status(esa)], [s3_funct_1__e15_31__wellord2])).
% 0.96/1.16  thf('44', plain,
% 0.96/1.16      (![X46 : $i, X47 : $i]:
% 0.96/1.16         (~ (r2_hidden @ X47 @ (k1_relat_1 @ X46))
% 0.96/1.16          | ((k11_relat_1 @ X46 @ X47) != (k1_xboole_0))
% 0.96/1.16          | ~ (v1_relat_1 @ X46))),
% 0.96/1.16      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.96/1.16  thf('45', plain,
% 0.96/1.16      (![X0 : $i, X1 : $i]:
% 0.96/1.16         (~ (r2_hidden @ X1 @ X0)
% 0.96/1.16          | ~ (v1_relat_1 @ (sk_B_2 @ X0))
% 0.96/1.16          | ((k11_relat_1 @ (sk_B_2 @ X0) @ X1) != (k1_xboole_0)))),
% 0.96/1.16      inference('sup-', [status(thm)], ['43', '44'])).
% 0.96/1.16  thf('46', plain, (![X63 : $i]: (v1_relat_1 @ (sk_B_2 @ X63))),
% 0.96/1.16      inference('cnf', [status(esa)], [s3_funct_1__e15_31__wellord2])).
% 0.96/1.16  thf('47', plain,
% 0.96/1.16      (![X0 : $i, X1 : $i]:
% 0.96/1.16         (~ (r2_hidden @ X1 @ X0)
% 0.96/1.16          | ((k11_relat_1 @ (sk_B_2 @ X0) @ X1) != (k1_xboole_0)))),
% 0.96/1.16      inference('demod', [status(thm)], ['45', '46'])).
% 0.96/1.16  thf('48', plain,
% 0.96/1.16      (![X0 : $i]:
% 0.96/1.16         (((k1_xboole_0) != (k1_xboole_0))
% 0.96/1.16          | (v1_xboole_0 @ X0)
% 0.96/1.16          | ((k3_yellow_0 @ (k2_yellow_1 @ X0)) = (k1_xboole_0))
% 0.96/1.16          | ~ (r2_hidden @ k1_xboole_0 @ X0))),
% 0.96/1.16      inference('sup-', [status(thm)], ['42', '47'])).
% 0.96/1.16  thf('49', plain,
% 0.96/1.16      (![X0 : $i]:
% 0.96/1.16         (~ (r2_hidden @ k1_xboole_0 @ X0)
% 0.96/1.16          | ((k3_yellow_0 @ (k2_yellow_1 @ X0)) = (k1_xboole_0))
% 0.96/1.16          | (v1_xboole_0 @ X0))),
% 0.96/1.16      inference('simplify', [status(thm)], ['48'])).
% 0.96/1.16  thf(l13_xboole_0, axiom,
% 0.96/1.16    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.96/1.16  thf('50', plain,
% 0.96/1.16      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.96/1.16      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.96/1.16  thf('51', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.96/1.16      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.96/1.16  thf('52', plain,
% 0.96/1.16      (![X46 : $i, X47 : $i]:
% 0.96/1.16         (~ (r2_hidden @ X47 @ (k1_relat_1 @ X46))
% 0.96/1.16          | ((k11_relat_1 @ X46 @ X47) != (k1_xboole_0))
% 0.96/1.16          | ~ (v1_relat_1 @ X46))),
% 0.96/1.16      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.96/1.16  thf('53', plain,
% 0.96/1.16      (![X0 : $i]:
% 0.96/1.16         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.96/1.16          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.96/1.16          | ((k11_relat_1 @ k1_xboole_0 @ X0) != (k1_xboole_0)))),
% 0.96/1.16      inference('sup-', [status(thm)], ['51', '52'])).
% 0.96/1.16  thf('54', plain, (![X63 : $i]: ((k1_relat_1 @ (sk_B_2 @ X63)) = (X63))),
% 0.96/1.16      inference('cnf', [status(esa)], [s3_funct_1__e15_31__wellord2])).
% 0.96/1.16  thf('55', plain,
% 0.96/1.16      (![X48 : $i]:
% 0.96/1.16         (((k1_relat_1 @ X48) != (k1_xboole_0))
% 0.96/1.16          | ((X48) = (k1_xboole_0))
% 0.96/1.16          | ~ (v1_relat_1 @ X48))),
% 0.96/1.16      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.96/1.16  thf('56', plain,
% 0.96/1.16      (![X0 : $i]:
% 0.96/1.16         (((X0) != (k1_xboole_0))
% 0.96/1.16          | ~ (v1_relat_1 @ (sk_B_2 @ X0))
% 0.96/1.16          | ((sk_B_2 @ X0) = (k1_xboole_0)))),
% 0.96/1.16      inference('sup-', [status(thm)], ['54', '55'])).
% 0.96/1.16  thf('57', plain, (![X63 : $i]: (v1_relat_1 @ (sk_B_2 @ X63))),
% 0.96/1.16      inference('cnf', [status(esa)], [s3_funct_1__e15_31__wellord2])).
% 0.96/1.16  thf('58', plain,
% 0.96/1.16      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B_2 @ X0) = (k1_xboole_0)))),
% 0.96/1.16      inference('demod', [status(thm)], ['56', '57'])).
% 0.96/1.16  thf('59', plain, (((sk_B_2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.96/1.16      inference('simplify', [status(thm)], ['58'])).
% 0.96/1.16  thf('60', plain, (![X63 : $i]: (v1_relat_1 @ (sk_B_2 @ X63))),
% 0.96/1.16      inference('cnf', [status(esa)], [s3_funct_1__e15_31__wellord2])).
% 0.96/1.16  thf('61', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.96/1.16      inference('sup+', [status(thm)], ['59', '60'])).
% 0.96/1.16  thf('62', plain,
% 0.96/1.16      (![X0 : $i]:
% 0.96/1.16         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.96/1.16          | ((k11_relat_1 @ k1_xboole_0 @ X0) != (k1_xboole_0)))),
% 0.96/1.16      inference('demod', [status(thm)], ['53', '61'])).
% 0.96/1.16  thf(t113_zfmisc_1, axiom,
% 0.96/1.16    (![A:$i,B:$i]:
% 0.96/1.16     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.96/1.16       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.96/1.16  thf('63', plain,
% 0.96/1.16      (![X41 : $i, X42 : $i]:
% 0.96/1.16         (((k2_zfmisc_1 @ X41 @ X42) = (k1_xboole_0))
% 0.96/1.16          | ((X42) != (k1_xboole_0)))),
% 0.96/1.16      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.96/1.16  thf('64', plain,
% 0.96/1.16      (![X41 : $i]: ((k2_zfmisc_1 @ X41 @ k1_xboole_0) = (k1_xboole_0))),
% 0.96/1.16      inference('simplify', [status(thm)], ['63'])).
% 0.96/1.16  thf(d10_xboole_0, axiom,
% 0.96/1.16    (![A:$i,B:$i]:
% 0.96/1.16     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.96/1.16  thf('65', plain,
% 0.96/1.16      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.96/1.16      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.96/1.16  thf('66', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.96/1.16      inference('simplify', [status(thm)], ['65'])).
% 0.96/1.16  thf('67', plain,
% 0.96/1.16      (![X30 : $i, X31 : $i]:
% 0.96/1.16         ((r2_hidden @ X30 @ (k9_setfam_1 @ X31)) | ~ (r1_tarski @ X30 @ X31))),
% 0.96/1.16      inference('demod', [status(thm)], ['31', '32'])).
% 0.96/1.16  thf('68', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k9_setfam_1 @ X0))),
% 0.96/1.16      inference('sup-', [status(thm)], ['66', '67'])).
% 0.96/1.16  thf(t203_relat_1, axiom,
% 0.96/1.16    (![A:$i,B:$i,C:$i]:
% 0.96/1.16     ( ( r2_hidden @ A @ B ) =>
% 0.96/1.16       ( ( k11_relat_1 @ ( k2_zfmisc_1 @ B @ C ) @ A ) = ( C ) ) ))).
% 0.96/1.16  thf('69', plain,
% 0.96/1.16      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.96/1.16         (~ (r2_hidden @ X43 @ X44)
% 0.96/1.16          | ((k11_relat_1 @ (k2_zfmisc_1 @ X44 @ X45) @ X43) = (X45)))),
% 0.96/1.16      inference('cnf', [status(esa)], [t203_relat_1])).
% 0.96/1.16  thf('70', plain,
% 0.96/1.16      (![X0 : $i, X1 : $i]:
% 0.96/1.16         ((k11_relat_1 @ (k2_zfmisc_1 @ (k9_setfam_1 @ X0) @ X1) @ X0) = (X1))),
% 0.96/1.16      inference('sup-', [status(thm)], ['68', '69'])).
% 0.96/1.16  thf('71', plain,
% 0.96/1.16      (![X0 : $i]: ((k11_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.96/1.16      inference('sup+', [status(thm)], ['64', '70'])).
% 0.96/1.16  thf('72', plain,
% 0.96/1.16      (![X0 : $i]:
% 0.96/1.16         (~ (r2_hidden @ X0 @ k1_xboole_0) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.96/1.16      inference('demod', [status(thm)], ['62', '71'])).
% 0.96/1.16  thf('73', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.96/1.16      inference('simplify', [status(thm)], ['72'])).
% 0.96/1.16  thf('74', plain,
% 0.96/1.16      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.96/1.16      inference('sup-', [status(thm)], ['50', '73'])).
% 0.96/1.16  thf('75', plain,
% 0.96/1.16      (![X0 : $i]:
% 0.96/1.16         (((k3_yellow_0 @ (k2_yellow_1 @ X0)) = (k1_xboole_0))
% 0.96/1.16          | ~ (r2_hidden @ k1_xboole_0 @ X0))),
% 0.96/1.16      inference('clc', [status(thm)], ['49', '74'])).
% 0.96/1.16  thf('76', plain,
% 0.96/1.16      (![X0 : $i]:
% 0.96/1.16         ((k3_yellow_0 @ (k2_yellow_1 @ (k9_setfam_1 @ X0))) = (k1_xboole_0))),
% 0.96/1.16      inference('sup-', [status(thm)], ['34', '75'])).
% 0.96/1.16  thf(t4_yellow_1, axiom,
% 0.96/1.16    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ))).
% 0.96/1.16  thf('77', plain,
% 0.96/1.16      (![X68 : $i]: ((k3_yellow_1 @ X68) = (k2_yellow_1 @ (k9_setfam_1 @ X68)))),
% 0.96/1.16      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.96/1.16  thf('78', plain,
% 0.96/1.16      (![X0 : $i]: ((k3_yellow_0 @ (k3_yellow_1 @ X0)) = (k1_xboole_0))),
% 0.96/1.16      inference('demod', [status(thm)], ['76', '77'])).
% 0.96/1.16  thf('79', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.96/1.16      inference('demod', [status(thm)], ['0', '78'])).
% 0.96/1.16  thf('80', plain, ($false), inference('simplify', [status(thm)], ['79'])).
% 0.96/1.16  
% 0.96/1.16  % SZS output end Refutation
% 0.96/1.16  
% 0.96/1.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
