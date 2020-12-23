%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uK4TQtuT04

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:42 EST 2020

% Result     : Theorem 11.47s
% Output     : Refutation 11.47s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 596 expanded)
%              Number of leaves         :   47 ( 191 expanded)
%              Depth                    :   18
%              Number of atoms          : 1491 (6072 expanded)
%              Number of equality atoms :  156 ( 735 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_5_type,type,(
    sk_D_5: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_7_type,type,(
    sk_D_7: $i > $i > $i )).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X86: $i] :
      ( ( r1_tarski @ X86 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X86 ) @ ( k2_relat_1 @ X86 ) ) )
      | ~ ( v1_relat_1 @ X86 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t23_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( C
          = ( k1_tarski @ ( k4_tarski @ A @ B ) ) )
       => ( ( ( k1_relat_1 @ C )
            = ( k1_tarski @ A ) )
          & ( ( k2_relat_1 @ C )
            = ( k1_tarski @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( C
            = ( k1_tarski @ ( k4_tarski @ A @ B ) ) )
         => ( ( ( k1_relat_1 @ C )
              = ( k1_tarski @ A ) )
            & ( ( k2_relat_1 @ C )
              = ( k1_tarski @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_relat_1])).

thf('1',plain,
    ( sk_C_5
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) )
    <=> ( ( A = C )
        & ( B = D ) ) ) )).

thf('2',plain,(
    ! [X56: $i,X57: $i,X58: $i,X60: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X57 @ X58 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X56 ) @ ( k1_tarski @ X60 ) ) )
      | ( X58 != X60 )
      | ( X57 != X56 ) ) ),
    inference(cnf,[status(esa)],[t34_zfmisc_1])).

thf('3',plain,(
    ! [X56: $i,X60: $i] :
      ( r2_hidden @ ( k4_tarski @ X56 @ X60 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X56 ) @ ( k1_tarski @ X60 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ X0 ) @ ( k2_zfmisc_1 @ sk_C_5 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf(t129_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf('5',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( r2_hidden @ X51 @ X52 )
      | ~ ( r2_hidden @ ( k4_tarski @ X51 @ X53 ) @ ( k2_zfmisc_1 @ X52 @ ( k1_tarski @ X54 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('6',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_5 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('7',plain,(
    ! [X68: $i,X69: $i,X70: $i,X71: $i] :
      ( ~ ( r1_tarski @ X68 @ X69 )
      | ( r2_hidden @ ( k4_tarski @ X70 @ X71 ) @ X69 )
      | ~ ( r2_hidden @ ( k4_tarski @ X70 @ X71 ) @ X68 )
      | ~ ( v1_relat_1 @ X68 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_5 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_C_5 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_C_5 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_C_5 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_5 ) @ ( k2_relat_1 @ sk_C_5 ) ) ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_5 ) @ ( k2_relat_1 @ sk_C_5 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X67: $i,X68: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X67 @ X68 ) @ ( sk_D_3 @ X67 @ X68 ) ) @ X68 )
      | ( r1_tarski @ X68 @ X67 )
      | ~ ( v1_relat_1 @ X68 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('15',plain,
    ( sk_C_5
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ( X57 = X56 )
      | ~ ( r2_hidden @ ( k4_tarski @ X57 @ X58 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X56 ) @ ( k1_tarski @ X59 ) ) ) ) ),
    inference(cnf,[status(esa)],[t34_zfmisc_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('17',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('18',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X61 ) @ ( k2_tarski @ X62 @ X63 ) )
      = ( k2_tarski @ ( k4_tarski @ X61 @ X62 ) @ ( k4_tarski @ X61 @ X63 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('19',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ( X57 = X56 )
      | ~ ( r2_hidden @ ( k4_tarski @ X57 @ X58 ) @ ( k1_tarski @ ( k4_tarski @ X56 @ X59 ) ) ) ) ),
    inference(demod,[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_5 )
      | ( X1 = sk_A ) ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_5 )
      | ( r1_tarski @ sk_C_5 @ X0 )
      | ( ( sk_C_2 @ X0 @ sk_C_5 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['14','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_5 @ X0 )
      | ( ( sk_C_2 @ X0 @ sk_C_5 )
        = sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X67: $i,X68: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X67 @ X68 ) @ ( sk_D_3 @ X67 @ X68 ) ) @ X68 )
      | ( r1_tarski @ X68 @ X67 )
      | ~ ( v1_relat_1 @ X68 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('28',plain,
    ( sk_C_5
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('30',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('31',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( X53 = X54 )
      | ~ ( r2_hidden @ ( k4_tarski @ X51 @ X53 ) @ ( k2_zfmisc_1 @ X52 @ ( k1_tarski @ X54 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) )
      | ( X2 = X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( X2 = X0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_5 )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_5 )
      | ( r1_tarski @ sk_C_5 @ X0 )
      | ( ( sk_D_3 @ X0 @ sk_C_5 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['27','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_5 @ X0 )
      | ( ( sk_D_3 @ X0 @ sk_C_5 )
        = sk_B ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X67: $i,X68: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X67 @ X68 ) @ ( sk_D_3 @ X67 @ X68 ) ) @ X67 )
      | ( r1_tarski @ X68 @ X67 )
      | ~ ( v1_relat_1 @ X68 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X0 @ sk_C_5 ) @ sk_B ) @ X0 )
      | ( r1_tarski @ sk_C_5 @ X0 )
      | ~ ( v1_relat_1 @ sk_C_5 )
      | ( r1_tarski @ sk_C_5 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X0 @ sk_C_5 ) @ sk_B ) @ X0 )
      | ( r1_tarski @ sk_C_5 @ X0 )
      | ( r1_tarski @ sk_C_5 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_5 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X0 @ sk_C_5 ) @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ X0 )
      | ( r1_tarski @ sk_C_5 @ X0 )
      | ( r1_tarski @ sk_C_5 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_5 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    r1_tarski @ sk_C_5 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_5 ) @ ( k2_relat_1 @ sk_C_5 ) ) ),
    inference('sup-',[status(thm)],['13','44'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('46',plain,(
    ! [X14: $i,X16: $i] :
      ( ( X14 = X16 )
      | ~ ( r1_tarski @ X16 @ X14 )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_5 ) @ ( k2_relat_1 @ sk_C_5 ) ) @ sk_C_5 )
    | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_5 ) @ ( k2_relat_1 @ sk_C_5 ) )
      = sk_C_5 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(l44_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('48',plain,(
    ! [X45: $i,X46: $i] :
      ( ( X45 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X46 @ X45 ) @ X45 )
      | ( X45
        = ( k1_tarski @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('49',plain,(
    ! [X81: $i,X82: $i,X83: $i] :
      ( ~ ( r2_hidden @ X83 @ X82 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_7 @ X83 @ X81 ) @ X83 ) @ X81 )
      | ( X82
       != ( k2_relat_1 @ X81 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('50',plain,(
    ! [X81: $i,X83: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_7 @ X83 @ X81 ) @ X83 ) @ X81 )
      | ~ ( r2_hidden @ X83 @ ( k2_relat_1 @ X81 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_7 @ ( sk_C_1 @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( sk_C_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_5 )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_C_5 )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_C_5 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C_1 @ X0 @ ( k2_relat_1 @ sk_C_5 ) )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X45: $i,X46: $i] :
      ( ( X45 = k1_xboole_0 )
      | ( ( sk_C_1 @ X46 @ X45 )
       != X46 )
      | ( X45
        = ( k1_tarski @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( sk_B != X0 )
      | ( ( k2_relat_1 @ sk_C_5 )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_C_5 )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_C_5 )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_C_5 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k2_relat_1 @ sk_C_5 )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C_5 )
      = ( k1_tarski @ sk_B ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( ( k1_relat_1 @ sk_C_5 )
     != ( k1_tarski @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C_5 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( k2_relat_1 @ sk_C_5 )
     != ( k1_tarski @ sk_B ) )
   <= ( ( k2_relat_1 @ sk_C_5 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['57'])).

thf('59',plain,(
    ! [X45: $i,X46: $i] :
      ( ( X45 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X46 @ X45 ) @ X45 )
      | ( X45
        = ( k1_tarski @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('60',plain,(
    ! [X74: $i,X75: $i,X76: $i] :
      ( ~ ( r2_hidden @ X76 @ X75 )
      | ( r2_hidden @ ( k4_tarski @ X76 @ ( sk_D_5 @ X76 @ X74 ) ) @ X74 )
      | ( X75
       != ( k1_relat_1 @ X74 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('61',plain,(
    ! [X74: $i,X76: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X76 @ ( sk_D_5 @ X76 @ X74 ) ) @ X74 )
      | ~ ( r2_hidden @ X76 @ ( k1_relat_1 @ X74 ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_5 @ ( sk_C_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_5 )
      | ( X1 = sk_A ) ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_C_5 )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C_5 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C_1 @ X0 @ ( k1_relat_1 @ sk_C_5 ) )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X45: $i,X46: $i] :
      ( ( X45 = k1_xboole_0 )
      | ( ( sk_C_1 @ X46 @ X45 )
       != X46 )
      | ( X45
        = ( k1_tarski @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ( ( k1_relat_1 @ sk_C_5 )
        = ( k1_tarski @ X0 ) )
      | ( ( k1_relat_1 @ sk_C_5 )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C_5 )
        = ( k1_tarski @ X0 ) )
      | ( ( k1_relat_1 @ sk_C_5 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k1_relat_1 @ sk_C_5 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_5 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( ( k1_relat_1 @ sk_C_5 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k1_relat_1 @ sk_C_5 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['57'])).

thf('69',plain,
    ( ( ( ( k1_relat_1 @ sk_C_5 )
       != ( k1_relat_1 @ sk_C_5 ) )
      | ( ( k1_relat_1 @ sk_C_5 )
        = k1_xboole_0 ) )
   <= ( ( k1_relat_1 @ sk_C_5 )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k1_relat_1 @ sk_C_5 )
      = k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_C_5 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X86: $i] :
      ( ( r1_tarski @ X86 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X86 ) @ ( k2_relat_1 @ X86 ) ) )
      | ~ ( v1_relat_1 @ X86 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('72',plain,(
    ! [X14: $i,X16: $i] :
      ( ( X14 = X16 )
      | ~ ( r1_tarski @ X16 @ X14 )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) @ X0 )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ sk_C_5 ) ) @ sk_C_5 )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_5 ) @ ( k2_relat_1 @ sk_C_5 ) )
        = sk_C_5 )
      | ~ ( v1_relat_1 @ sk_C_5 ) )
   <= ( ( k1_relat_1 @ sk_C_5 )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf(d2_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('75',plain,(
    ! [X36: $i,X37: $i,X40: $i] :
      ( ( X40
        = ( k2_zfmisc_1 @ X37 @ X36 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X40 @ X36 @ X37 ) @ ( sk_E @ X40 @ X36 @ X37 ) @ ( sk_D_2 @ X40 @ X36 @ X37 ) @ X36 @ X37 )
      | ( r2_hidden @ ( sk_D_2 @ X40 @ X36 @ X37 ) @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('76',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ X27 @ X31 )
      | ~ ( zip_tseitin_0 @ X28 @ X27 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('78',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('79',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('80',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['78','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['81'])).

thf('85',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( sk_C_5
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('88',plain,(
    ! [X47: $i,X49: $i,X50: $i] :
      ( ( r1_tarski @ X49 @ ( k2_tarski @ X47 @ X50 ) )
      | ( X49 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('89',plain,(
    ! [X47: $i,X50: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k2_tarski @ X47 @ X50 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['87','89'])).

thf('91',plain,(
    r1_tarski @ k1_xboole_0 @ sk_C_5 ),
    inference('sup+',[status(thm)],['86','90'])).

thf('92',plain,
    ( ( ( k1_relat_1 @ sk_C_5 )
      = k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_C_5 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('93',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('94',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( k1_xboole_0 = sk_C_5 )
   <= ( ( k1_relat_1 @ sk_C_5 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','85','91','92','93','94'])).

thf('96',plain,
    ( sk_C_5
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('98',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('99',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X20 @ X19 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('100',plain,(
    ! [X65: $i,X66: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X65 @ X66 ) )
      = ( k3_xboole_0 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X65: $i,X66: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X65 @ X66 ) )
      = ( k3_xboole_0 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('104',plain,(
    ! [X17: $i] :
      ( ( k3_xboole_0 @ X17 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
        = ( k1_tarski @ B ) )
     => ( r2_hidden @ B @ A ) ) )).

thf('107',plain,(
    ! [X43: $i,X44: $i] :
      ( ( r2_hidden @ X43 @ X44 )
      | ( ( k3_xboole_0 @ X44 @ ( k1_tarski @ X43 ) )
       != ( k1_tarski @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[l29_zfmisc_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['105','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['98','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['81'])).

thf('112',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k2_tarski @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','112'])).

thf('114',plain,(
    k1_xboole_0 != sk_C_5 ),
    inference('sup-',[status(thm)],['96','113'])).

thf('115',plain,
    ( ( k1_relat_1 @ sk_C_5 )
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['95','114'])).

thf('116',plain,
    ( ( ( k2_relat_1 @ sk_C_5 )
     != ( k1_tarski @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C_5 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['57'])).

thf('117',plain,(
    ( k2_relat_1 @ sk_C_5 )
 != ( k1_tarski @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['115','116'])).

thf('118',plain,(
    ( k2_relat_1 @ sk_C_5 )
 != ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['58','117'])).

thf('119',plain,
    ( ( k2_relat_1 @ sk_C_5 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['56','118'])).

thf('120',plain,(
    ! [X36: $i,X37: $i,X40: $i] :
      ( ( X40
        = ( k2_zfmisc_1 @ X37 @ X36 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X40 @ X36 @ X37 ) @ ( sk_E @ X40 @ X36 @ X37 ) @ ( sk_D_2 @ X40 @ X36 @ X37 ) @ X36 @ X37 )
      | ( r2_hidden @ ( sk_D_2 @ X40 @ X36 @ X37 ) @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('121',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ X28 @ X30 )
      | ~ ( zip_tseitin_0 @ X28 @ X27 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['81'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['81'])).

thf('126',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    r1_tarski @ k1_xboole_0 @ sk_C_5 ),
    inference('sup+',[status(thm)],['86','90'])).

thf('128',plain,
    ( ( k2_relat_1 @ sk_C_5 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['56','118'])).

thf('129',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('130',plain,(
    k1_xboole_0 = sk_C_5 ),
    inference(demod,[status(thm)],['47','119','126','127','128','129'])).

thf('131',plain,(
    k1_xboole_0 != sk_C_5 ),
    inference('sup-',[status(thm)],['96','113'])).

thf('132',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['130','131'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uK4TQtuT04
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:04:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 11.47/11.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 11.47/11.66  % Solved by: fo/fo7.sh
% 11.47/11.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.47/11.66  % done 8676 iterations in 11.203s
% 11.47/11.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 11.47/11.66  % SZS output start Refutation
% 11.47/11.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 11.47/11.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 11.47/11.66  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i).
% 11.47/11.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 11.47/11.66  thf(sk_A_type, type, sk_A: $i).
% 11.47/11.66  thf(sk_C_5_type, type, sk_C_5: $i).
% 11.47/11.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 11.47/11.66  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 11.47/11.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 11.47/11.66  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 11.47/11.66  thf(sk_D_5_type, type, sk_D_5: $i > $i > $i).
% 11.47/11.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 11.47/11.66  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 11.47/11.66  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 11.47/11.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 11.47/11.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 11.47/11.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 11.47/11.66  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 11.47/11.66  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 11.47/11.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 11.47/11.66  thf(sk_B_type, type, sk_B: $i).
% 11.47/11.66  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 11.47/11.66  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 11.47/11.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 11.47/11.66  thf(sk_D_7_type, type, sk_D_7: $i > $i > $i).
% 11.47/11.66  thf(t21_relat_1, axiom,
% 11.47/11.66    (![A:$i]:
% 11.47/11.66     ( ( v1_relat_1 @ A ) =>
% 11.47/11.66       ( r1_tarski @
% 11.47/11.66         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 11.47/11.66  thf('0', plain,
% 11.47/11.66      (![X86 : $i]:
% 11.47/11.66         ((r1_tarski @ X86 @ 
% 11.47/11.66           (k2_zfmisc_1 @ (k1_relat_1 @ X86) @ (k2_relat_1 @ X86)))
% 11.47/11.66          | ~ (v1_relat_1 @ X86))),
% 11.47/11.66      inference('cnf', [status(esa)], [t21_relat_1])).
% 11.47/11.66  thf(t23_relat_1, conjecture,
% 11.47/11.66    (![A:$i,B:$i,C:$i]:
% 11.47/11.66     ( ( v1_relat_1 @ C ) =>
% 11.47/11.66       ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 11.47/11.66         ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 11.47/11.66           ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ))).
% 11.47/11.66  thf(zf_stmt_0, negated_conjecture,
% 11.47/11.66    (~( ![A:$i,B:$i,C:$i]:
% 11.47/11.66        ( ( v1_relat_1 @ C ) =>
% 11.47/11.66          ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 11.47/11.66            ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 11.47/11.66              ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ) )),
% 11.47/11.66    inference('cnf.neg', [status(esa)], [t23_relat_1])).
% 11.47/11.66  thf('1', plain, (((sk_C_5) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 11.47/11.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.47/11.66  thf(t34_zfmisc_1, axiom,
% 11.47/11.66    (![A:$i,B:$i,C:$i,D:$i]:
% 11.47/11.66     ( ( r2_hidden @
% 11.47/11.66         ( k4_tarski @ A @ B ) @ 
% 11.47/11.66         ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 11.47/11.66       ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ))).
% 11.47/11.66  thf('2', plain,
% 11.47/11.66      (![X56 : $i, X57 : $i, X58 : $i, X60 : $i]:
% 11.47/11.66         ((r2_hidden @ (k4_tarski @ X57 @ X58) @ 
% 11.47/11.66           (k2_zfmisc_1 @ (k1_tarski @ X56) @ (k1_tarski @ X60)))
% 11.47/11.66          | ((X58) != (X60))
% 11.47/11.66          | ((X57) != (X56)))),
% 11.47/11.66      inference('cnf', [status(esa)], [t34_zfmisc_1])).
% 11.47/11.66  thf('3', plain,
% 11.47/11.66      (![X56 : $i, X60 : $i]:
% 11.47/11.66         (r2_hidden @ (k4_tarski @ X56 @ X60) @ 
% 11.47/11.66          (k2_zfmisc_1 @ (k1_tarski @ X56) @ (k1_tarski @ X60)))),
% 11.47/11.66      inference('simplify', [status(thm)], ['2'])).
% 11.47/11.66  thf('4', plain,
% 11.47/11.66      (![X0 : $i]:
% 11.47/11.66         (r2_hidden @ (k4_tarski @ (k4_tarski @ sk_A @ sk_B) @ X0) @ 
% 11.47/11.66          (k2_zfmisc_1 @ sk_C_5 @ (k1_tarski @ X0)))),
% 11.47/11.66      inference('sup+', [status(thm)], ['1', '3'])).
% 11.47/11.66  thf(t129_zfmisc_1, axiom,
% 11.47/11.66    (![A:$i,B:$i,C:$i,D:$i]:
% 11.47/11.66     ( ( r2_hidden @
% 11.47/11.66         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 11.47/11.66       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 11.47/11.66  thf('5', plain,
% 11.47/11.66      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 11.47/11.66         ((r2_hidden @ X51 @ X52)
% 11.47/11.66          | ~ (r2_hidden @ (k4_tarski @ X51 @ X53) @ 
% 11.47/11.66               (k2_zfmisc_1 @ X52 @ (k1_tarski @ X54))))),
% 11.47/11.66      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 11.47/11.66  thf('6', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_5)),
% 11.47/11.66      inference('sup-', [status(thm)], ['4', '5'])).
% 11.47/11.66  thf(d3_relat_1, axiom,
% 11.47/11.66    (![A:$i]:
% 11.47/11.66     ( ( v1_relat_1 @ A ) =>
% 11.47/11.66       ( ![B:$i]:
% 11.47/11.66         ( ( r1_tarski @ A @ B ) <=>
% 11.47/11.66           ( ![C:$i,D:$i]:
% 11.47/11.66             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 11.47/11.66               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 11.47/11.66  thf('7', plain,
% 11.47/11.66      (![X68 : $i, X69 : $i, X70 : $i, X71 : $i]:
% 11.47/11.66         (~ (r1_tarski @ X68 @ X69)
% 11.47/11.66          | (r2_hidden @ (k4_tarski @ X70 @ X71) @ X69)
% 11.47/11.66          | ~ (r2_hidden @ (k4_tarski @ X70 @ X71) @ X68)
% 11.47/11.66          | ~ (v1_relat_1 @ X68))),
% 11.47/11.66      inference('cnf', [status(esa)], [d3_relat_1])).
% 11.47/11.66  thf('8', plain,
% 11.47/11.66      (![X0 : $i]:
% 11.47/11.66         (~ (v1_relat_1 @ sk_C_5)
% 11.47/11.66          | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ X0)
% 11.47/11.66          | ~ (r1_tarski @ sk_C_5 @ X0))),
% 11.47/11.66      inference('sup-', [status(thm)], ['6', '7'])).
% 11.47/11.66  thf('9', plain, ((v1_relat_1 @ sk_C_5)),
% 11.47/11.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.47/11.66  thf('10', plain,
% 11.47/11.66      (![X0 : $i]:
% 11.47/11.66         ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ X0)
% 11.47/11.66          | ~ (r1_tarski @ sk_C_5 @ X0))),
% 11.47/11.66      inference('demod', [status(thm)], ['8', '9'])).
% 11.47/11.66  thf('11', plain,
% 11.47/11.66      ((~ (v1_relat_1 @ sk_C_5)
% 11.47/11.66        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 11.47/11.66           (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_5) @ (k2_relat_1 @ sk_C_5))))),
% 11.47/11.66      inference('sup-', [status(thm)], ['0', '10'])).
% 11.47/11.66  thf('12', plain, ((v1_relat_1 @ sk_C_5)),
% 11.47/11.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.47/11.66  thf('13', plain,
% 11.47/11.66      ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 11.47/11.66        (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_5) @ (k2_relat_1 @ sk_C_5)))),
% 11.47/11.66      inference('demod', [status(thm)], ['11', '12'])).
% 11.47/11.66  thf('14', plain,
% 11.47/11.66      (![X67 : $i, X68 : $i]:
% 11.47/11.66         ((r2_hidden @ 
% 11.47/11.66           (k4_tarski @ (sk_C_2 @ X67 @ X68) @ (sk_D_3 @ X67 @ X68)) @ X68)
% 11.47/11.66          | (r1_tarski @ X68 @ X67)
% 11.47/11.66          | ~ (v1_relat_1 @ X68))),
% 11.47/11.66      inference('cnf', [status(esa)], [d3_relat_1])).
% 11.47/11.66  thf('15', plain, (((sk_C_5) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 11.47/11.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.47/11.66  thf('16', plain,
% 11.47/11.66      (![X56 : $i, X57 : $i, X58 : $i, X59 : $i]:
% 11.47/11.66         (((X57) = (X56))
% 11.47/11.66          | ~ (r2_hidden @ (k4_tarski @ X57 @ X58) @ 
% 11.47/11.66               (k2_zfmisc_1 @ (k1_tarski @ X56) @ (k1_tarski @ X59))))),
% 11.47/11.66      inference('cnf', [status(esa)], [t34_zfmisc_1])).
% 11.47/11.66  thf(t69_enumset1, axiom,
% 11.47/11.66    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 11.47/11.66  thf('17', plain,
% 11.47/11.66      (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 11.47/11.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 11.47/11.66  thf(t36_zfmisc_1, axiom,
% 11.47/11.66    (![A:$i,B:$i,C:$i]:
% 11.47/11.66     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 11.47/11.66         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 11.47/11.66       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 11.47/11.66         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 11.47/11.66  thf('18', plain,
% 11.47/11.66      (![X61 : $i, X62 : $i, X63 : $i]:
% 11.47/11.66         ((k2_zfmisc_1 @ (k1_tarski @ X61) @ (k2_tarski @ X62 @ X63))
% 11.47/11.66           = (k2_tarski @ (k4_tarski @ X61 @ X62) @ (k4_tarski @ X61 @ X63)))),
% 11.47/11.66      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 11.47/11.66  thf('19', plain,
% 11.47/11.66      (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 11.47/11.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 11.47/11.66  thf('20', plain,
% 11.47/11.66      (![X0 : $i, X1 : $i]:
% 11.47/11.66         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 11.47/11.66           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 11.47/11.66      inference('sup+', [status(thm)], ['18', '19'])).
% 11.47/11.66  thf('21', plain,
% 11.47/11.66      (![X0 : $i, X1 : $i]:
% 11.47/11.66         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 11.47/11.66           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 11.47/11.66      inference('sup+', [status(thm)], ['17', '20'])).
% 11.47/11.66  thf('22', plain,
% 11.47/11.66      (![X56 : $i, X57 : $i, X58 : $i, X59 : $i]:
% 11.47/11.66         (((X57) = (X56))
% 11.47/11.66          | ~ (r2_hidden @ (k4_tarski @ X57 @ X58) @ 
% 11.47/11.66               (k1_tarski @ (k4_tarski @ X56 @ X59))))),
% 11.47/11.66      inference('demod', [status(thm)], ['16', '21'])).
% 11.47/11.66  thf('23', plain,
% 11.47/11.66      (![X0 : $i, X1 : $i]:
% 11.47/11.66         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_5) | ((X1) = (sk_A)))),
% 11.47/11.66      inference('sup-', [status(thm)], ['15', '22'])).
% 11.47/11.66  thf('24', plain,
% 11.47/11.66      (![X0 : $i]:
% 11.47/11.66         (~ (v1_relat_1 @ sk_C_5)
% 11.47/11.66          | (r1_tarski @ sk_C_5 @ X0)
% 11.47/11.66          | ((sk_C_2 @ X0 @ sk_C_5) = (sk_A)))),
% 11.47/11.66      inference('sup-', [status(thm)], ['14', '23'])).
% 11.47/11.66  thf('25', plain, ((v1_relat_1 @ sk_C_5)),
% 11.47/11.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.47/11.66  thf('26', plain,
% 11.47/11.66      (![X0 : $i]:
% 11.47/11.66         ((r1_tarski @ sk_C_5 @ X0) | ((sk_C_2 @ X0 @ sk_C_5) = (sk_A)))),
% 11.47/11.66      inference('demod', [status(thm)], ['24', '25'])).
% 11.47/11.66  thf('27', plain,
% 11.47/11.66      (![X67 : $i, X68 : $i]:
% 11.47/11.66         ((r2_hidden @ 
% 11.47/11.66           (k4_tarski @ (sk_C_2 @ X67 @ X68) @ (sk_D_3 @ X67 @ X68)) @ X68)
% 11.47/11.66          | (r1_tarski @ X68 @ X67)
% 11.47/11.66          | ~ (v1_relat_1 @ X68))),
% 11.47/11.66      inference('cnf', [status(esa)], [d3_relat_1])).
% 11.47/11.66  thf('28', plain, (((sk_C_5) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 11.47/11.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.47/11.66  thf('29', plain,
% 11.47/11.66      (![X0 : $i, X1 : $i]:
% 11.47/11.66         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 11.47/11.66           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 11.47/11.66      inference('sup+', [status(thm)], ['18', '19'])).
% 11.47/11.66  thf('30', plain,
% 11.47/11.66      (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 11.47/11.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 11.47/11.66  thf('31', plain,
% 11.47/11.66      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 11.47/11.66         (((X53) = (X54))
% 11.47/11.66          | ~ (r2_hidden @ (k4_tarski @ X51 @ X53) @ 
% 11.47/11.66               (k2_zfmisc_1 @ X52 @ (k1_tarski @ X54))))),
% 11.47/11.66      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 11.47/11.66  thf('32', plain,
% 11.47/11.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.47/11.66         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 11.47/11.66             (k2_zfmisc_1 @ X1 @ (k2_tarski @ X0 @ X0)))
% 11.47/11.66          | ((X2) = (X0)))),
% 11.47/11.66      inference('sup-', [status(thm)], ['30', '31'])).
% 11.47/11.66  thf('33', plain,
% 11.47/11.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.47/11.66         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 11.47/11.66             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 11.47/11.66          | ((X2) = (X0)))),
% 11.47/11.66      inference('sup-', [status(thm)], ['29', '32'])).
% 11.47/11.66  thf('34', plain,
% 11.47/11.66      (![X0 : $i, X1 : $i]:
% 11.47/11.66         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_5) | ((X0) = (sk_B)))),
% 11.47/11.66      inference('sup-', [status(thm)], ['28', '33'])).
% 11.47/11.66  thf('35', plain,
% 11.47/11.66      (![X0 : $i]:
% 11.47/11.66         (~ (v1_relat_1 @ sk_C_5)
% 11.47/11.66          | (r1_tarski @ sk_C_5 @ X0)
% 11.47/11.66          | ((sk_D_3 @ X0 @ sk_C_5) = (sk_B)))),
% 11.47/11.66      inference('sup-', [status(thm)], ['27', '34'])).
% 11.47/11.66  thf('36', plain, ((v1_relat_1 @ sk_C_5)),
% 11.47/11.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.47/11.66  thf('37', plain,
% 11.47/11.66      (![X0 : $i]:
% 11.47/11.66         ((r1_tarski @ sk_C_5 @ X0) | ((sk_D_3 @ X0 @ sk_C_5) = (sk_B)))),
% 11.47/11.66      inference('demod', [status(thm)], ['35', '36'])).
% 11.47/11.66  thf('38', plain,
% 11.47/11.66      (![X67 : $i, X68 : $i]:
% 11.47/11.66         (~ (r2_hidden @ 
% 11.47/11.66             (k4_tarski @ (sk_C_2 @ X67 @ X68) @ (sk_D_3 @ X67 @ X68)) @ X67)
% 11.47/11.66          | (r1_tarski @ X68 @ X67)
% 11.47/11.66          | ~ (v1_relat_1 @ X68))),
% 11.47/11.66      inference('cnf', [status(esa)], [d3_relat_1])).
% 11.47/11.66  thf('39', plain,
% 11.47/11.66      (![X0 : $i]:
% 11.47/11.66         (~ (r2_hidden @ (k4_tarski @ (sk_C_2 @ X0 @ sk_C_5) @ sk_B) @ X0)
% 11.47/11.66          | (r1_tarski @ sk_C_5 @ X0)
% 11.47/11.66          | ~ (v1_relat_1 @ sk_C_5)
% 11.47/11.66          | (r1_tarski @ sk_C_5 @ X0))),
% 11.47/11.66      inference('sup-', [status(thm)], ['37', '38'])).
% 11.47/11.66  thf('40', plain, ((v1_relat_1 @ sk_C_5)),
% 11.47/11.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.47/11.66  thf('41', plain,
% 11.47/11.66      (![X0 : $i]:
% 11.47/11.66         (~ (r2_hidden @ (k4_tarski @ (sk_C_2 @ X0 @ sk_C_5) @ sk_B) @ X0)
% 11.47/11.66          | (r1_tarski @ sk_C_5 @ X0)
% 11.47/11.66          | (r1_tarski @ sk_C_5 @ X0))),
% 11.47/11.66      inference('demod', [status(thm)], ['39', '40'])).
% 11.47/11.66  thf('42', plain,
% 11.47/11.66      (![X0 : $i]:
% 11.47/11.66         ((r1_tarski @ sk_C_5 @ X0)
% 11.47/11.66          | ~ (r2_hidden @ (k4_tarski @ (sk_C_2 @ X0 @ sk_C_5) @ sk_B) @ X0))),
% 11.47/11.66      inference('simplify', [status(thm)], ['41'])).
% 11.47/11.66  thf('43', plain,
% 11.47/11.66      (![X0 : $i]:
% 11.47/11.66         (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ X0)
% 11.47/11.66          | (r1_tarski @ sk_C_5 @ X0)
% 11.47/11.66          | (r1_tarski @ sk_C_5 @ X0))),
% 11.47/11.66      inference('sup-', [status(thm)], ['26', '42'])).
% 11.47/11.66  thf('44', plain,
% 11.47/11.66      (![X0 : $i]:
% 11.47/11.66         ((r1_tarski @ sk_C_5 @ X0)
% 11.47/11.66          | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ X0))),
% 11.47/11.66      inference('simplify', [status(thm)], ['43'])).
% 11.47/11.66  thf('45', plain,
% 11.47/11.66      ((r1_tarski @ sk_C_5 @ 
% 11.47/11.66        (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_5) @ (k2_relat_1 @ sk_C_5)))),
% 11.47/11.66      inference('sup-', [status(thm)], ['13', '44'])).
% 11.47/11.66  thf(d10_xboole_0, axiom,
% 11.47/11.66    (![A:$i,B:$i]:
% 11.47/11.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 11.47/11.66  thf('46', plain,
% 11.47/11.66      (![X14 : $i, X16 : $i]:
% 11.47/11.66         (((X14) = (X16))
% 11.47/11.66          | ~ (r1_tarski @ X16 @ X14)
% 11.47/11.66          | ~ (r1_tarski @ X14 @ X16))),
% 11.47/11.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 11.47/11.66  thf('47', plain,
% 11.47/11.66      ((~ (r1_tarski @ 
% 11.47/11.66           (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_5) @ (k2_relat_1 @ sk_C_5)) @ 
% 11.47/11.66           sk_C_5)
% 11.47/11.66        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_C_5) @ (k2_relat_1 @ sk_C_5))
% 11.47/11.66            = (sk_C_5)))),
% 11.47/11.66      inference('sup-', [status(thm)], ['45', '46'])).
% 11.47/11.66  thf(l44_zfmisc_1, axiom,
% 11.47/11.66    (![A:$i,B:$i]:
% 11.47/11.66     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 11.47/11.66          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 11.47/11.66  thf('48', plain,
% 11.47/11.66      (![X45 : $i, X46 : $i]:
% 11.47/11.66         (((X45) = (k1_xboole_0))
% 11.47/11.66          | (r2_hidden @ (sk_C_1 @ X46 @ X45) @ X45)
% 11.47/11.66          | ((X45) = (k1_tarski @ X46)))),
% 11.47/11.66      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 11.47/11.66  thf(d5_relat_1, axiom,
% 11.47/11.66    (![A:$i,B:$i]:
% 11.47/11.66     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 11.47/11.66       ( ![C:$i]:
% 11.47/11.66         ( ( r2_hidden @ C @ B ) <=>
% 11.47/11.66           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 11.47/11.66  thf('49', plain,
% 11.47/11.66      (![X81 : $i, X82 : $i, X83 : $i]:
% 11.47/11.66         (~ (r2_hidden @ X83 @ X82)
% 11.47/11.66          | (r2_hidden @ (k4_tarski @ (sk_D_7 @ X83 @ X81) @ X83) @ X81)
% 11.47/11.66          | ((X82) != (k2_relat_1 @ X81)))),
% 11.47/11.66      inference('cnf', [status(esa)], [d5_relat_1])).
% 11.47/11.66  thf('50', plain,
% 11.47/11.66      (![X81 : $i, X83 : $i]:
% 11.47/11.66         ((r2_hidden @ (k4_tarski @ (sk_D_7 @ X83 @ X81) @ X83) @ X81)
% 11.47/11.66          | ~ (r2_hidden @ X83 @ (k2_relat_1 @ X81)))),
% 11.47/11.66      inference('simplify', [status(thm)], ['49'])).
% 11.47/11.66  thf('51', plain,
% 11.47/11.66      (![X0 : $i, X1 : $i]:
% 11.47/11.66         (((k2_relat_1 @ X0) = (k1_tarski @ X1))
% 11.47/11.66          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 11.47/11.66          | (r2_hidden @ 
% 11.47/11.66             (k4_tarski @ (sk_D_7 @ (sk_C_1 @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 11.47/11.66              (sk_C_1 @ X1 @ (k2_relat_1 @ X0))) @ 
% 11.47/11.66             X0))),
% 11.47/11.66      inference('sup-', [status(thm)], ['48', '50'])).
% 11.47/11.66  thf('52', plain,
% 11.47/11.66      (![X0 : $i, X1 : $i]:
% 11.47/11.66         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_5) | ((X0) = (sk_B)))),
% 11.47/11.66      inference('sup-', [status(thm)], ['28', '33'])).
% 11.47/11.66  thf('53', plain,
% 11.47/11.66      (![X0 : $i]:
% 11.47/11.66         (((k2_relat_1 @ sk_C_5) = (k1_xboole_0))
% 11.47/11.66          | ((k2_relat_1 @ sk_C_5) = (k1_tarski @ X0))
% 11.47/11.66          | ((sk_C_1 @ X0 @ (k2_relat_1 @ sk_C_5)) = (sk_B)))),
% 11.47/11.66      inference('sup-', [status(thm)], ['51', '52'])).
% 11.47/11.66  thf('54', plain,
% 11.47/11.66      (![X45 : $i, X46 : $i]:
% 11.47/11.66         (((X45) = (k1_xboole_0))
% 11.47/11.66          | ((sk_C_1 @ X46 @ X45) != (X46))
% 11.47/11.66          | ((X45) = (k1_tarski @ X46)))),
% 11.47/11.66      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 11.47/11.66  thf('55', plain,
% 11.47/11.66      (![X0 : $i]:
% 11.47/11.66         (((sk_B) != (X0))
% 11.47/11.66          | ((k2_relat_1 @ sk_C_5) = (k1_tarski @ X0))
% 11.47/11.66          | ((k2_relat_1 @ sk_C_5) = (k1_xboole_0))
% 11.47/11.66          | ((k2_relat_1 @ sk_C_5) = (k1_tarski @ X0))
% 11.47/11.66          | ((k2_relat_1 @ sk_C_5) = (k1_xboole_0)))),
% 11.47/11.66      inference('sup-', [status(thm)], ['53', '54'])).
% 11.47/11.66  thf('56', plain,
% 11.47/11.66      ((((k2_relat_1 @ sk_C_5) = (k1_xboole_0))
% 11.47/11.66        | ((k2_relat_1 @ sk_C_5) = (k1_tarski @ sk_B)))),
% 11.47/11.66      inference('simplify', [status(thm)], ['55'])).
% 11.47/11.66  thf('57', plain,
% 11.47/11.66      ((((k1_relat_1 @ sk_C_5) != (k1_tarski @ sk_A))
% 11.47/11.66        | ((k2_relat_1 @ sk_C_5) != (k1_tarski @ sk_B)))),
% 11.47/11.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.47/11.66  thf('58', plain,
% 11.47/11.66      ((((k2_relat_1 @ sk_C_5) != (k1_tarski @ sk_B)))
% 11.47/11.66         <= (~ (((k2_relat_1 @ sk_C_5) = (k1_tarski @ sk_B))))),
% 11.47/11.66      inference('split', [status(esa)], ['57'])).
% 11.47/11.66  thf('59', plain,
% 11.47/11.66      (![X45 : $i, X46 : $i]:
% 11.47/11.66         (((X45) = (k1_xboole_0))
% 11.47/11.66          | (r2_hidden @ (sk_C_1 @ X46 @ X45) @ X45)
% 11.47/11.66          | ((X45) = (k1_tarski @ X46)))),
% 11.47/11.66      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 11.47/11.66  thf(d4_relat_1, axiom,
% 11.47/11.66    (![A:$i,B:$i]:
% 11.47/11.66     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 11.47/11.66       ( ![C:$i]:
% 11.47/11.66         ( ( r2_hidden @ C @ B ) <=>
% 11.47/11.66           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 11.47/11.66  thf('60', plain,
% 11.47/11.66      (![X74 : $i, X75 : $i, X76 : $i]:
% 11.47/11.66         (~ (r2_hidden @ X76 @ X75)
% 11.47/11.66          | (r2_hidden @ (k4_tarski @ X76 @ (sk_D_5 @ X76 @ X74)) @ X74)
% 11.47/11.66          | ((X75) != (k1_relat_1 @ X74)))),
% 11.47/11.66      inference('cnf', [status(esa)], [d4_relat_1])).
% 11.47/11.66  thf('61', plain,
% 11.47/11.66      (![X74 : $i, X76 : $i]:
% 11.47/11.66         ((r2_hidden @ (k4_tarski @ X76 @ (sk_D_5 @ X76 @ X74)) @ X74)
% 11.47/11.66          | ~ (r2_hidden @ X76 @ (k1_relat_1 @ X74)))),
% 11.47/11.66      inference('simplify', [status(thm)], ['60'])).
% 11.47/11.66  thf('62', plain,
% 11.47/11.66      (![X0 : $i, X1 : $i]:
% 11.47/11.66         (((k1_relat_1 @ X0) = (k1_tarski @ X1))
% 11.47/11.66          | ((k1_relat_1 @ X0) = (k1_xboole_0))
% 11.47/11.66          | (r2_hidden @ 
% 11.47/11.66             (k4_tarski @ (sk_C_1 @ X1 @ (k1_relat_1 @ X0)) @ 
% 11.47/11.66              (sk_D_5 @ (sk_C_1 @ X1 @ (k1_relat_1 @ X0)) @ X0)) @ 
% 11.47/11.66             X0))),
% 11.47/11.66      inference('sup-', [status(thm)], ['59', '61'])).
% 11.47/11.66  thf('63', plain,
% 11.47/11.66      (![X0 : $i, X1 : $i]:
% 11.47/11.66         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_5) | ((X1) = (sk_A)))),
% 11.47/11.66      inference('sup-', [status(thm)], ['15', '22'])).
% 11.47/11.66  thf('64', plain,
% 11.47/11.66      (![X0 : $i]:
% 11.47/11.66         (((k1_relat_1 @ sk_C_5) = (k1_xboole_0))
% 11.47/11.66          | ((k1_relat_1 @ sk_C_5) = (k1_tarski @ X0))
% 11.47/11.66          | ((sk_C_1 @ X0 @ (k1_relat_1 @ sk_C_5)) = (sk_A)))),
% 11.47/11.66      inference('sup-', [status(thm)], ['62', '63'])).
% 11.47/11.66  thf('65', plain,
% 11.47/11.66      (![X45 : $i, X46 : $i]:
% 11.47/11.66         (((X45) = (k1_xboole_0))
% 11.47/11.66          | ((sk_C_1 @ X46 @ X45) != (X46))
% 11.47/11.66          | ((X45) = (k1_tarski @ X46)))),
% 11.47/11.66      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 11.47/11.66  thf('66', plain,
% 11.47/11.66      (![X0 : $i]:
% 11.47/11.66         (((sk_A) != (X0))
% 11.47/11.66          | ((k1_relat_1 @ sk_C_5) = (k1_tarski @ X0))
% 11.47/11.66          | ((k1_relat_1 @ sk_C_5) = (k1_xboole_0))
% 11.47/11.66          | ((k1_relat_1 @ sk_C_5) = (k1_tarski @ X0))
% 11.47/11.66          | ((k1_relat_1 @ sk_C_5) = (k1_xboole_0)))),
% 11.47/11.66      inference('sup-', [status(thm)], ['64', '65'])).
% 11.47/11.66  thf('67', plain,
% 11.47/11.66      ((((k1_relat_1 @ sk_C_5) = (k1_xboole_0))
% 11.47/11.66        | ((k1_relat_1 @ sk_C_5) = (k1_tarski @ sk_A)))),
% 11.47/11.66      inference('simplify', [status(thm)], ['66'])).
% 11.47/11.66  thf('68', plain,
% 11.47/11.66      ((((k1_relat_1 @ sk_C_5) != (k1_tarski @ sk_A)))
% 11.47/11.66         <= (~ (((k1_relat_1 @ sk_C_5) = (k1_tarski @ sk_A))))),
% 11.47/11.66      inference('split', [status(esa)], ['57'])).
% 11.47/11.66  thf('69', plain,
% 11.47/11.66      (((((k1_relat_1 @ sk_C_5) != (k1_relat_1 @ sk_C_5))
% 11.47/11.66         | ((k1_relat_1 @ sk_C_5) = (k1_xboole_0))))
% 11.47/11.66         <= (~ (((k1_relat_1 @ sk_C_5) = (k1_tarski @ sk_A))))),
% 11.47/11.66      inference('sup-', [status(thm)], ['67', '68'])).
% 11.47/11.66  thf('70', plain,
% 11.47/11.66      ((((k1_relat_1 @ sk_C_5) = (k1_xboole_0)))
% 11.47/11.66         <= (~ (((k1_relat_1 @ sk_C_5) = (k1_tarski @ sk_A))))),
% 11.47/11.66      inference('simplify', [status(thm)], ['69'])).
% 11.47/11.66  thf('71', plain,
% 11.47/11.66      (![X86 : $i]:
% 11.47/11.66         ((r1_tarski @ X86 @ 
% 11.47/11.66           (k2_zfmisc_1 @ (k1_relat_1 @ X86) @ (k2_relat_1 @ X86)))
% 11.47/11.66          | ~ (v1_relat_1 @ X86))),
% 11.47/11.66      inference('cnf', [status(esa)], [t21_relat_1])).
% 11.47/11.66  thf('72', plain,
% 11.47/11.66      (![X14 : $i, X16 : $i]:
% 11.47/11.66         (((X14) = (X16))
% 11.47/11.66          | ~ (r1_tarski @ X16 @ X14)
% 11.47/11.66          | ~ (r1_tarski @ X14 @ X16))),
% 11.47/11.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 11.47/11.66  thf('73', plain,
% 11.47/11.66      (![X0 : $i]:
% 11.47/11.66         (~ (v1_relat_1 @ X0)
% 11.47/11.66          | ~ (r1_tarski @ 
% 11.47/11.66               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ X0)
% 11.47/11.66          | ((k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) = (X0)))),
% 11.47/11.66      inference('sup-', [status(thm)], ['71', '72'])).
% 11.47/11.66  thf('74', plain,
% 11.47/11.66      (((~ (r1_tarski @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_relat_1 @ sk_C_5)) @ 
% 11.47/11.66            sk_C_5)
% 11.47/11.66         | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_C_5) @ (k2_relat_1 @ sk_C_5))
% 11.47/11.66             = (sk_C_5))
% 11.47/11.66         | ~ (v1_relat_1 @ sk_C_5)))
% 11.47/11.66         <= (~ (((k1_relat_1 @ sk_C_5) = (k1_tarski @ sk_A))))),
% 11.47/11.66      inference('sup-', [status(thm)], ['70', '73'])).
% 11.47/11.66  thf(d2_zfmisc_1, axiom,
% 11.47/11.66    (![A:$i,B:$i,C:$i]:
% 11.47/11.66     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 11.47/11.66       ( ![D:$i]:
% 11.47/11.66         ( ( r2_hidden @ D @ C ) <=>
% 11.47/11.66           ( ?[E:$i,F:$i]:
% 11.47/11.66             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 11.47/11.66               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 11.47/11.66  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 11.47/11.66  thf(zf_stmt_2, axiom,
% 11.47/11.66    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 11.47/11.66     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 11.47/11.66       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 11.47/11.66         ( r2_hidden @ E @ A ) ) ))).
% 11.47/11.66  thf(zf_stmt_3, axiom,
% 11.47/11.66    (![A:$i,B:$i,C:$i]:
% 11.47/11.66     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 11.47/11.66       ( ![D:$i]:
% 11.47/11.66         ( ( r2_hidden @ D @ C ) <=>
% 11.47/11.66           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 11.47/11.66  thf('75', plain,
% 11.47/11.66      (![X36 : $i, X37 : $i, X40 : $i]:
% 11.47/11.66         (((X40) = (k2_zfmisc_1 @ X37 @ X36))
% 11.47/11.66          | (zip_tseitin_0 @ (sk_F @ X40 @ X36 @ X37) @ 
% 11.47/11.66             (sk_E @ X40 @ X36 @ X37) @ (sk_D_2 @ X40 @ X36 @ X37) @ X36 @ X37)
% 11.47/11.66          | (r2_hidden @ (sk_D_2 @ X40 @ X36 @ X37) @ X40))),
% 11.47/11.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 11.47/11.66  thf('76', plain,
% 11.47/11.66      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 11.47/11.66         ((r2_hidden @ X27 @ X31)
% 11.47/11.66          | ~ (zip_tseitin_0 @ X28 @ X27 @ X29 @ X30 @ X31))),
% 11.47/11.66      inference('cnf', [status(esa)], [zf_stmt_2])).
% 11.47/11.66  thf('77', plain,
% 11.47/11.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.47/11.66         ((r2_hidden @ (sk_D_2 @ X2 @ X1 @ X0) @ X2)
% 11.47/11.66          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 11.47/11.66          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 11.47/11.66      inference('sup-', [status(thm)], ['75', '76'])).
% 11.47/11.66  thf(t3_boole, axiom,
% 11.47/11.66    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 11.47/11.66  thf('78', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 11.47/11.66      inference('cnf', [status(esa)], [t3_boole])).
% 11.47/11.66  thf(d5_xboole_0, axiom,
% 11.47/11.66    (![A:$i,B:$i,C:$i]:
% 11.47/11.66     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 11.47/11.66       ( ![D:$i]:
% 11.47/11.66         ( ( r2_hidden @ D @ C ) <=>
% 11.47/11.66           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 11.47/11.66  thf('79', plain,
% 11.47/11.66      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 11.47/11.66         (~ (r2_hidden @ X10 @ X9)
% 11.47/11.66          | ~ (r2_hidden @ X10 @ X8)
% 11.47/11.66          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 11.47/11.66      inference('cnf', [status(esa)], [d5_xboole_0])).
% 11.47/11.66  thf('80', plain,
% 11.47/11.66      (![X7 : $i, X8 : $i, X10 : $i]:
% 11.47/11.66         (~ (r2_hidden @ X10 @ X8)
% 11.47/11.66          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 11.47/11.66      inference('simplify', [status(thm)], ['79'])).
% 11.47/11.66  thf('81', plain,
% 11.47/11.66      (![X0 : $i, X1 : $i]:
% 11.47/11.66         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 11.47/11.66      inference('sup-', [status(thm)], ['78', '80'])).
% 11.47/11.66  thf('82', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 11.47/11.66      inference('condensation', [status(thm)], ['81'])).
% 11.47/11.66  thf('83', plain,
% 11.47/11.66      (![X0 : $i, X1 : $i]:
% 11.47/11.66         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 11.47/11.66          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 11.47/11.66      inference('sup-', [status(thm)], ['77', '82'])).
% 11.47/11.66  thf('84', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 11.47/11.66      inference('condensation', [status(thm)], ['81'])).
% 11.47/11.66  thf('85', plain,
% 11.47/11.66      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 11.47/11.66      inference('sup-', [status(thm)], ['83', '84'])).
% 11.47/11.66  thf('86', plain, (((sk_C_5) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 11.47/11.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.47/11.66  thf('87', plain,
% 11.47/11.66      (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 11.47/11.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 11.47/11.66  thf(l45_zfmisc_1, axiom,
% 11.47/11.66    (![A:$i,B:$i,C:$i]:
% 11.47/11.66     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 11.47/11.66       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 11.47/11.66            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 11.47/11.66  thf('88', plain,
% 11.47/11.66      (![X47 : $i, X49 : $i, X50 : $i]:
% 11.47/11.66         ((r1_tarski @ X49 @ (k2_tarski @ X47 @ X50))
% 11.47/11.66          | ((X49) != (k1_xboole_0)))),
% 11.47/11.66      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 11.47/11.66  thf('89', plain,
% 11.47/11.66      (![X47 : $i, X50 : $i]:
% 11.47/11.66         (r1_tarski @ k1_xboole_0 @ (k2_tarski @ X47 @ X50))),
% 11.47/11.66      inference('simplify', [status(thm)], ['88'])).
% 11.47/11.66  thf('90', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))),
% 11.47/11.66      inference('sup+', [status(thm)], ['87', '89'])).
% 11.47/11.66  thf('91', plain, ((r1_tarski @ k1_xboole_0 @ sk_C_5)),
% 11.47/11.66      inference('sup+', [status(thm)], ['86', '90'])).
% 11.47/11.66  thf('92', plain,
% 11.47/11.66      ((((k1_relat_1 @ sk_C_5) = (k1_xboole_0)))
% 11.47/11.66         <= (~ (((k1_relat_1 @ sk_C_5) = (k1_tarski @ sk_A))))),
% 11.47/11.66      inference('simplify', [status(thm)], ['69'])).
% 11.47/11.66  thf('93', plain,
% 11.47/11.66      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 11.47/11.66      inference('sup-', [status(thm)], ['83', '84'])).
% 11.47/11.66  thf('94', plain, ((v1_relat_1 @ sk_C_5)),
% 11.47/11.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.47/11.66  thf('95', plain,
% 11.47/11.66      ((((k1_xboole_0) = (sk_C_5)))
% 11.47/11.66         <= (~ (((k1_relat_1 @ sk_C_5) = (k1_tarski @ sk_A))))),
% 11.47/11.66      inference('demod', [status(thm)], ['74', '85', '91', '92', '93', '94'])).
% 11.47/11.66  thf('96', plain, (((sk_C_5) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 11.47/11.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.47/11.66  thf('97', plain,
% 11.47/11.66      (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 11.47/11.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 11.47/11.66  thf('98', plain,
% 11.47/11.66      (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 11.47/11.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 11.47/11.66  thf(commutativity_k2_tarski, axiom,
% 11.47/11.66    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 11.47/11.66  thf('99', plain,
% 11.47/11.66      (![X19 : $i, X20 : $i]:
% 11.47/11.66         ((k2_tarski @ X20 @ X19) = (k2_tarski @ X19 @ X20))),
% 11.47/11.66      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 11.47/11.66  thf(t12_setfam_1, axiom,
% 11.47/11.66    (![A:$i,B:$i]:
% 11.47/11.66     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 11.47/11.66  thf('100', plain,
% 11.47/11.66      (![X65 : $i, X66 : $i]:
% 11.47/11.66         ((k1_setfam_1 @ (k2_tarski @ X65 @ X66)) = (k3_xboole_0 @ X65 @ X66))),
% 11.47/11.66      inference('cnf', [status(esa)], [t12_setfam_1])).
% 11.47/11.66  thf('101', plain,
% 11.47/11.66      (![X0 : $i, X1 : $i]:
% 11.47/11.66         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 11.47/11.66      inference('sup+', [status(thm)], ['99', '100'])).
% 11.47/11.66  thf('102', plain,
% 11.47/11.66      (![X65 : $i, X66 : $i]:
% 11.47/11.66         ((k1_setfam_1 @ (k2_tarski @ X65 @ X66)) = (k3_xboole_0 @ X65 @ X66))),
% 11.47/11.66      inference('cnf', [status(esa)], [t12_setfam_1])).
% 11.47/11.66  thf('103', plain,
% 11.47/11.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 11.47/11.66      inference('sup+', [status(thm)], ['101', '102'])).
% 11.47/11.66  thf(t2_boole, axiom,
% 11.47/11.66    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 11.47/11.66  thf('104', plain,
% 11.47/11.66      (![X17 : $i]: ((k3_xboole_0 @ X17 @ k1_xboole_0) = (k1_xboole_0))),
% 11.47/11.66      inference('cnf', [status(esa)], [t2_boole])).
% 11.47/11.66  thf('105', plain,
% 11.47/11.66      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 11.47/11.66      inference('sup+', [status(thm)], ['103', '104'])).
% 11.47/11.66  thf('106', plain,
% 11.47/11.66      (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 11.47/11.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 11.47/11.66  thf(l29_zfmisc_1, axiom,
% 11.47/11.66    (![A:$i,B:$i]:
% 11.47/11.66     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 11.47/11.66       ( r2_hidden @ B @ A ) ))).
% 11.47/11.66  thf('107', plain,
% 11.47/11.66      (![X43 : $i, X44 : $i]:
% 11.47/11.66         ((r2_hidden @ X43 @ X44)
% 11.47/11.66          | ((k3_xboole_0 @ X44 @ (k1_tarski @ X43)) != (k1_tarski @ X43)))),
% 11.47/11.66      inference('cnf', [status(esa)], [l29_zfmisc_1])).
% 11.47/11.66  thf('108', plain,
% 11.47/11.66      (![X0 : $i, X1 : $i]:
% 11.47/11.66         (((k3_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0)) != (k1_tarski @ X0))
% 11.47/11.66          | (r2_hidden @ X0 @ X1))),
% 11.47/11.66      inference('sup-', [status(thm)], ['106', '107'])).
% 11.47/11.66  thf('109', plain,
% 11.47/11.66      (![X0 : $i]:
% 11.47/11.66         (((k1_xboole_0) != (k1_tarski @ X0)) | (r2_hidden @ X0 @ k1_xboole_0))),
% 11.47/11.66      inference('sup-', [status(thm)], ['105', '108'])).
% 11.47/11.66  thf('110', plain,
% 11.47/11.66      (![X0 : $i]:
% 11.47/11.66         (((k1_xboole_0) != (k2_tarski @ X0 @ X0))
% 11.47/11.66          | (r2_hidden @ X0 @ k1_xboole_0))),
% 11.47/11.66      inference('sup-', [status(thm)], ['98', '109'])).
% 11.47/11.66  thf('111', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 11.47/11.66      inference('condensation', [status(thm)], ['81'])).
% 11.47/11.66  thf('112', plain, (![X0 : $i]: ((k1_xboole_0) != (k2_tarski @ X0 @ X0))),
% 11.47/11.66      inference('clc', [status(thm)], ['110', '111'])).
% 11.47/11.66  thf('113', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 11.47/11.66      inference('sup-', [status(thm)], ['97', '112'])).
% 11.47/11.66  thf('114', plain, (((k1_xboole_0) != (sk_C_5))),
% 11.47/11.66      inference('sup-', [status(thm)], ['96', '113'])).
% 11.47/11.66  thf('115', plain, ((((k1_relat_1 @ sk_C_5) = (k1_tarski @ sk_A)))),
% 11.47/11.66      inference('simplify_reflect-', [status(thm)], ['95', '114'])).
% 11.47/11.66  thf('116', plain,
% 11.47/11.66      (~ (((k2_relat_1 @ sk_C_5) = (k1_tarski @ sk_B))) | 
% 11.47/11.66       ~ (((k1_relat_1 @ sk_C_5) = (k1_tarski @ sk_A)))),
% 11.47/11.66      inference('split', [status(esa)], ['57'])).
% 11.47/11.66  thf('117', plain, (~ (((k2_relat_1 @ sk_C_5) = (k1_tarski @ sk_B)))),
% 11.47/11.66      inference('sat_resolution*', [status(thm)], ['115', '116'])).
% 11.47/11.66  thf('118', plain, (((k2_relat_1 @ sk_C_5) != (k1_tarski @ sk_B))),
% 11.47/11.66      inference('simpl_trail', [status(thm)], ['58', '117'])).
% 11.47/11.66  thf('119', plain, (((k2_relat_1 @ sk_C_5) = (k1_xboole_0))),
% 11.47/11.66      inference('simplify_reflect-', [status(thm)], ['56', '118'])).
% 11.47/11.66  thf('120', plain,
% 11.47/11.66      (![X36 : $i, X37 : $i, X40 : $i]:
% 11.47/11.66         (((X40) = (k2_zfmisc_1 @ X37 @ X36))
% 11.47/11.66          | (zip_tseitin_0 @ (sk_F @ X40 @ X36 @ X37) @ 
% 11.47/11.66             (sk_E @ X40 @ X36 @ X37) @ (sk_D_2 @ X40 @ X36 @ X37) @ X36 @ X37)
% 11.47/11.66          | (r2_hidden @ (sk_D_2 @ X40 @ X36 @ X37) @ X40))),
% 11.47/11.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 11.47/11.66  thf('121', plain,
% 11.47/11.66      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 11.47/11.66         ((r2_hidden @ X28 @ X30)
% 11.47/11.66          | ~ (zip_tseitin_0 @ X28 @ X27 @ X29 @ X30 @ X31))),
% 11.47/11.66      inference('cnf', [status(esa)], [zf_stmt_2])).
% 11.47/11.66  thf('122', plain,
% 11.47/11.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.47/11.66         ((r2_hidden @ (sk_D_2 @ X2 @ X1 @ X0) @ X2)
% 11.47/11.66          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 11.47/11.66          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 11.47/11.66      inference('sup-', [status(thm)], ['120', '121'])).
% 11.47/11.66  thf('123', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 11.47/11.66      inference('condensation', [status(thm)], ['81'])).
% 11.47/11.66  thf('124', plain,
% 11.47/11.66      (![X0 : $i, X1 : $i]:
% 11.47/11.66         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ X1)
% 11.47/11.66          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 11.47/11.66      inference('sup-', [status(thm)], ['122', '123'])).
% 11.47/11.66  thf('125', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 11.47/11.66      inference('condensation', [status(thm)], ['81'])).
% 11.47/11.66  thf('126', plain,
% 11.47/11.66      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 11.47/11.66      inference('sup-', [status(thm)], ['124', '125'])).
% 11.47/11.66  thf('127', plain, ((r1_tarski @ k1_xboole_0 @ sk_C_5)),
% 11.47/11.66      inference('sup+', [status(thm)], ['86', '90'])).
% 11.47/11.66  thf('128', plain, (((k2_relat_1 @ sk_C_5) = (k1_xboole_0))),
% 11.47/11.66      inference('simplify_reflect-', [status(thm)], ['56', '118'])).
% 11.47/11.66  thf('129', plain,
% 11.47/11.66      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 11.47/11.66      inference('sup-', [status(thm)], ['124', '125'])).
% 11.47/11.66  thf('130', plain, (((k1_xboole_0) = (sk_C_5))),
% 11.47/11.66      inference('demod', [status(thm)],
% 11.47/11.66                ['47', '119', '126', '127', '128', '129'])).
% 11.47/11.66  thf('131', plain, (((k1_xboole_0) != (sk_C_5))),
% 11.47/11.66      inference('sup-', [status(thm)], ['96', '113'])).
% 11.47/11.66  thf('132', plain, ($false),
% 11.47/11.66      inference('simplify_reflect-', [status(thm)], ['130', '131'])).
% 11.47/11.66  
% 11.47/11.66  % SZS output end Refutation
% 11.47/11.66  
% 11.50/11.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
