%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0366+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dbUInbVRtS

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:54 EST 2020

% Result     : Theorem 55.04s
% Output     : Refutation 55.04s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 252 expanded)
%              Number of leaves         :   41 (  96 expanded)
%              Depth                    :   17
%              Number of atoms          :  927 (1768 expanded)
%              Number of equality atoms :   97 ( 171 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_C_20_type,type,(
    sk_C_20: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_8_type,type,(
    sk_B_8: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_16_type,type,(
    sk_D_16: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t47_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ A ) ) )
         => ! [D: $i] :
              ( ( m1_subset_1 @ ( D @ ( k1_zfmisc_1 @ A ) ) )
             => ( ( ( r1_tarski @ ( B @ C ) )
                  & ( r1_xboole_0 @ ( D @ C ) ) )
               => ( r1_tarski @ ( B @ ( k3_subset_1 @ ( A @ D ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ A ) ) )
           => ! [D: $i] :
                ( ( m1_subset_1 @ ( D @ ( k1_zfmisc_1 @ A ) ) )
               => ( ( ( r1_tarski @ ( B @ C ) )
                    & ( r1_xboole_0 @ ( D @ C ) ) )
                 => ( r1_tarski @ ( B @ ( k3_subset_1 @ ( A @ D ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t47_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( sk_B_8 @ ( k3_subset_1 @ ( sk_A_2 @ sk_D_16 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ ( sk_D_16 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k3_subset_1 @ ( A @ B ) )
        = ( k4_xboole_0 @ ( A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X1474: $i,X1475: $i] :
      ( ( ( k3_subset_1 @ ( X1474 @ X1475 ) )
        = ( k4_xboole_0 @ ( X1474 @ X1475 ) ) )
      | ~ ( m1_subset_1 @ ( X1475 @ ( k1_zfmisc_1 @ X1474 ) ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ ( A @ B ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('3',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X1474: $i,X1475: $i] :
      ( ( ( k3_subset_1 @ ( X1474 @ X1475 ) )
        = ( k6_subset_1 @ ( X1474 @ X1475 ) ) )
      | ~ ( m1_subset_1 @ ( X1475 @ ( k1_zfmisc_1 @ X1474 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k3_subset_1 @ ( sk_A_2 @ sk_D_16 ) )
    = ( k6_subset_1 @ ( sk_A_2 @ sk_D_16 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ~ ( r1_tarski @ ( sk_B_8 @ ( k6_subset_1 @ ( sk_A_2 @ sk_D_16 ) ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ ( sk_D_16 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X1477: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1477 @ ( k1_zfmisc_1 @ X1477 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('9',plain,(
    ! [X1473: $i] :
      ( ( k2_subset_1 @ X1473 )
      = X1473 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('10',plain,(
    ! [X1477: $i] :
      ( m1_subset_1 @ ( X1477 @ ( k1_zfmisc_1 @ X1477 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X1474: $i,X1475: $i] :
      ( ( ( k3_subset_1 @ ( X1474 @ X1475 ) )
        = ( k6_subset_1 @ ( X1474 @ X1475 ) ) )
      | ~ ( m1_subset_1 @ ( X1475 @ ( k1_zfmisc_1 @ X1474 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( X0 @ X0 ) )
      = ( k6_subset_1 @ ( X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('13',plain,(
    ! [X78: $i,X79: $i] :
      ( ( r1_tarski @ ( X78 @ X79 ) )
      | ( X78 != X79 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X79: $i] :
      ( r1_tarski @ ( X79 @ X79 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('15',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('16',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('17',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( X0 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ ( X0 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( X0 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['12','20'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( r1_tarski @ ( B @ C ) )
          <=> ( r1_tarski @ ( k3_subset_1 @ ( A @ C ) @ ( k3_subset_1 @ ( A @ B ) ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X1555: $i,X1556: $i,X1557: $i] :
      ( ~ ( m1_subset_1 @ ( X1555 @ ( k1_zfmisc_1 @ X1556 ) ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ ( X1556 @ X1555 ) @ ( k3_subset_1 @ ( X1556 @ X1557 ) ) ) )
      | ( r1_tarski @ ( X1557 @ X1555 ) )
      | ~ ( m1_subset_1 @ ( X1557 @ ( k1_zfmisc_1 @ X1556 ) ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( o_0_0_xboole_0 @ ( k3_subset_1 @ ( X1 @ X0 ) ) ) )
      | ~ ( m1_subset_1 @ ( X0 @ ( k1_zfmisc_1 @ X1 ) ) )
      | ( r1_tarski @ ( X0 @ X1 ) )
      | ~ ( m1_subset_1 @ ( X1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_xboole_0 @ A ) ) )).

thf('24',plain,(
    ! [X216: $i] :
      ( r1_tarski @ ( k1_xboole_0 @ X216 ) ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('25',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('26',plain,(
    ! [X216: $i] :
      ( r1_tarski @ ( o_0_0_xboole_0 @ X216 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X1477: $i] :
      ( m1_subset_1 @ ( X1477 @ ( k1_zfmisc_1 @ X1477 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( X0 @ ( k1_zfmisc_1 @ X1 ) ) )
      | ( r1_tarski @ ( X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['23','26','27'])).

thf('29',plain,(
    r1_tarski @ ( sk_D_16 @ sk_A_2 ) ),
    inference('sup-',[status(thm)],['7','28'])).

thf('30',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('31',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('32',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k6_subset_1 @ ( X88 @ X90 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k6_subset_1 @ ( sk_D_16 @ sk_A_2 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['29','32'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ ( k4_xboole_0 @ ( B @ A ) ) ) ) ) )).

thf('34',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k5_xboole_0 @ ( X35 @ X36 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X35 @ X36 ) @ ( k4_xboole_0 @ ( X36 @ X35 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('35',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('36',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('37',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k5_xboole_0 @ ( X35 @ X36 ) )
      = ( k2_xboole_0 @ ( k6_subset_1 @ ( X35 @ X36 ) @ ( k6_subset_1 @ ( X36 @ X35 ) ) ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ( k5_xboole_0 @ ( sk_D_16 @ sk_A_2 ) )
    = ( k2_xboole_0 @ ( o_0_0_xboole_0 @ ( k6_subset_1 @ ( sk_A_2 @ sk_D_16 ) ) ) ) ),
    inference('sup+',[status(thm)],['33','37'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ ( A @ k1_xboole_0 ) )
      = A ) )).

thf('39',plain,(
    ! [X183: $i] :
      ( ( k2_xboole_0 @ ( X183 @ k1_xboole_0 ) )
      = X183 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('40',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('41',plain,(
    ! [X183: $i] :
      ( ( k2_xboole_0 @ ( X183 @ o_0_0_xboole_0 ) )
      = X183 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('42',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k5_xboole_0 @ ( sk_D_16 @ sk_A_2 ) )
    = ( k6_subset_1 @ ( sk_A_2 @ sk_D_16 ) ) ),
    inference(demod,[status(thm)],['38','43'])).

thf('45',plain,(
    r1_xboole_0 @ ( sk_D_16 @ sk_C_20 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
     => ( r1_xboole_0 @ ( B @ A ) ) ) )).

thf('46',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_xboole_0 @ ( X47 @ X48 ) )
      | ~ ( r1_xboole_0 @ ( X48 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('47',plain,(
    r1_xboole_0 @ ( sk_C_20 @ sk_D_16 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k3_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 ) ) )).

thf('48',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('49',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('50',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k3_xboole_0 @ ( sk_C_20 @ sk_D_16 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['47','50'])).

thf(t102_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( A @ ( k5_xboole_0 @ ( B @ C ) ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ C ) ) ) ) ) )).

thf('52',plain,(
    ! [X108: $i,X109: $i,X110: $i] :
      ( ( k4_xboole_0 @ ( X108 @ ( k5_xboole_0 @ ( X109 @ X110 ) ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X108 @ ( k2_xboole_0 @ ( X109 @ X110 ) ) ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ ( X108 @ X109 ) @ X110 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t102_xboole_1])).

thf('53',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('54',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('55',plain,(
    ! [X108: $i,X109: $i,X110: $i] :
      ( ( k6_subset_1 @ ( X108 @ ( k5_xboole_0 @ ( X109 @ X110 ) ) ) )
      = ( k2_xboole_0 @ ( k6_subset_1 @ ( X108 @ ( k2_xboole_0 @ ( X109 @ X110 ) ) ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ ( X108 @ X109 ) @ X110 ) ) ) ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ ( sk_C_20 @ ( k5_xboole_0 @ ( sk_D_16 @ X0 ) ) ) )
      = ( k2_xboole_0 @ ( k6_subset_1 @ ( sk_C_20 @ ( k2_xboole_0 @ ( sk_D_16 @ X0 ) ) ) @ ( k3_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['51','55'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('57',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ ( A @ k1_xboole_0 ) )
      = k1_xboole_0 ) )).

thf('58',plain,(
    ! [X215: $i] :
      ( ( k3_xboole_0 @ ( X215 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('59',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('60',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('61',plain,(
    ! [X215: $i] :
      ( ( k3_xboole_0 @ ( X215 @ o_0_0_xboole_0 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','61'])).

thf('63',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ ( sk_C_20 @ ( k5_xboole_0 @ ( sk_D_16 @ X0 ) ) ) )
      = ( k6_subset_1 @ ( sk_C_20 @ ( k2_xboole_0 @ ( sk_D_16 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['56','62','63','64'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ C ) )
      = ( k4_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('66',plain,(
    ! [X248: $i,X249: $i,X250: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( X248 @ X249 ) @ X250 ) )
      = ( k4_xboole_0 @ ( X248 @ ( k2_xboole_0 @ ( X249 @ X250 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('67',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('68',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('69',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('70',plain,(
    ! [X248: $i,X249: $i,X250: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ ( X248 @ X249 ) @ X250 ) )
      = ( k6_subset_1 @ ( X248 @ ( k2_xboole_0 @ ( X249 @ X250 ) ) ) ) ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,
    ( ( k3_xboole_0 @ ( sk_C_20 @ sk_D_16 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['47','50'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( A @ B ) )
      = ( k5_xboole_0 @ ( A @ ( k3_xboole_0 @ ( A @ B ) ) ) ) ) )).

thf('72',plain,(
    ! [X104: $i,X105: $i] :
      ( ( k4_xboole_0 @ ( X104 @ X105 ) )
      = ( k5_xboole_0 @ ( X104 @ ( k3_xboole_0 @ ( X104 @ X105 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('73',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('74',plain,(
    ! [X104: $i,X105: $i] :
      ( ( k6_subset_1 @ ( X104 @ X105 ) )
      = ( k5_xboole_0 @ ( X104 @ ( k3_xboole_0 @ ( X104 @ X105 ) ) ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k6_subset_1 @ ( sk_C_20 @ sk_D_16 ) )
    = ( k5_xboole_0 @ ( sk_C_20 @ o_0_0_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['71','74'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ ( A @ B ) )
      = ( k5_xboole_0 @ ( B @ A ) ) ) )).

thf('76',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( X9 @ X8 ) )
      = ( k5_xboole_0 @ ( X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ ( A @ k1_xboole_0 ) )
      = A ) )).

thf('77',plain,(
    ! [X302: $i] :
      ( ( k5_xboole_0 @ ( X302 @ k1_xboole_0 ) )
      = X302 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('78',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('79',plain,(
    ! [X302: $i] :
      ( ( k5_xboole_0 @ ( X302 @ o_0_0_xboole_0 ) )
      = X302 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( X9 @ X8 ) )
      = ( k5_xboole_0 @ ( X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k6_subset_1 @ ( sk_C_20 @ sk_D_16 ) )
    = sk_C_20 ),
    inference(demod,[status(thm)],['75','76','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ ( sk_C_20 @ ( k5_xboole_0 @ ( sk_D_16 @ X0 ) ) ) )
      = ( k6_subset_1 @ ( sk_C_20 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['65','70','82'])).

thf('84',plain,
    ( ( k6_subset_1 @ ( sk_C_20 @ ( k6_subset_1 @ ( sk_A_2 @ sk_D_16 ) ) ) )
    = ( k6_subset_1 @ ( sk_C_20 @ sk_A_2 ) ) ),
    inference('sup+',[status(thm)],['44','83'])).

thf('85',plain,(
    m1_subset_1 @ ( sk_C_20 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( X0 @ ( k1_zfmisc_1 @ X1 ) ) )
      | ( r1_tarski @ ( X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['23','26','27'])).

thf('87',plain,(
    r1_tarski @ ( sk_C_20 @ sk_A_2 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k6_subset_1 @ ( X88 @ X90 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('89',plain,
    ( ( k6_subset_1 @ ( sk_C_20 @ sk_A_2 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k6_subset_1 @ ( sk_C_20 @ ( k6_subset_1 @ ( sk_A_2 @ sk_D_16 ) ) ) )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['84','89'])).

thf('91',plain,(
    ! [X88: $i,X89: $i] :
      ( ( r1_tarski @ ( X88 @ X89 ) )
      | ( ( k4_xboole_0 @ ( X88 @ X89 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('92',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('93',plain,(
    ! [X88: $i,X89: $i] :
      ( ( r1_tarski @ ( X88 @ X89 ) )
      | ( ( k4_xboole_0 @ ( X88 @ X89 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('95',plain,(
    ! [X88: $i,X89: $i] :
      ( ( r1_tarski @ ( X88 @ X89 ) )
      | ( ( k6_subset_1 @ ( X88 @ X89 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( r1_tarski @ ( sk_C_20 @ ( k6_subset_1 @ ( sk_A_2 @ sk_D_16 ) ) ) ) ),
    inference('sup-',[status(thm)],['90','95'])).

thf('97',plain,(
    r1_tarski @ ( sk_C_20 @ ( k6_subset_1 @ ( sk_A_2 @ sk_D_16 ) ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    r1_tarski @ ( sk_B_8 @ sk_C_20 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( A @ B ) )
        = B ) ) )).

thf('99',plain,(
    ! [X161: $i,X162: $i] :
      ( ( ( k2_xboole_0 @ ( X162 @ X161 ) )
        = X161 )
      | ~ ( r1_tarski @ ( X162 @ X161 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('100',plain,
    ( ( k2_xboole_0 @ ( sk_B_8 @ sk_C_20 ) )
    = sk_C_20 ),
    inference('sup-',[status(thm)],['98','99'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( A @ B ) @ C ) )
     => ( r1_tarski @ ( A @ C ) ) ) )).

thf('101',plain,(
    ! [X158: $i,X159: $i,X160: $i] :
      ( ( r1_tarski @ ( X158 @ X159 ) )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( X158 @ X160 ) @ X159 ) ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( sk_C_20 @ X0 ) )
      | ( r1_tarski @ ( sk_B_8 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    r1_tarski @ ( sk_B_8 @ ( k6_subset_1 @ ( sk_A_2 @ sk_D_16 ) ) ) ),
    inference('sup-',[status(thm)],['97','102'])).

thf('104',plain,(
    $false ),
    inference(demod,[status(thm)],['6','103'])).

%------------------------------------------------------------------------------
