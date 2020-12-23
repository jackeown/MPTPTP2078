%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1012+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wVOALvTFti

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:05 EST 2020

% Result     : Theorem 54.24s
% Output     : Refutation 54.24s
% Verified   : 
% Statistics : Number of formulae       :   71 (  88 expanded)
%              Number of leaves         :   33 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :  438 ( 696 expanded)
%              Number of equality atoms :   45 (  61 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_16_type,type,(
    sk_A_16: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(zip_tseitin_98_type,type,(
    zip_tseitin_98: $i > $i > $i > $o )).

thf(sk_D_76_type,type,(
    sk_D_76: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_97_type,type,(
    zip_tseitin_97: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_98_type,type,(
    sk_B_98: $i )).

thf(sk_C_16_type,type,(
    sk_C_16: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ ( C @ ( A @ B ) ) )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ ( C @ ( A @ B ) ) )
          <=> ( A
              = ( k1_relset_1 @ ( A @ ( B @ C ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_97 @ ( B @ A ) ) ) )).

thf('0',plain,(
    ! [X4642: $i,X4643: $i] :
      ( ( zip_tseitin_97 @ ( X4642 @ X4643 ) )
      | ( X4642 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,(
    ! [X4642: $i,X4643: $i] :
      ( ( zip_tseitin_97 @ ( X4642 @ X4643 ) )
      | ( X4642 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t67_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ ( B @ ( A @ A ) ) )
        & ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ A ) ) ) ) ) )
     => ( ( k1_relset_1 @ ( A @ ( A @ B ) ) )
        = A ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ ( B @ ( A @ A ) ) )
          & ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ A ) ) ) ) ) )
       => ( ( k1_relset_1 @ ( A @ ( A @ B ) ) )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t67_funct_2])).

thf('3',plain,(
    m1_subset_1 @ ( sk_B_98 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_A_16 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(zf_stmt_2,type,(
    zip_tseitin_98: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_98 @ ( C @ ( B @ A ) ) )
     => ( ( v1_funct_2 @ ( C @ ( A @ B ) ) )
      <=> ( A
          = ( k1_relset_1 @ ( A @ ( B @ C ) ) ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_97: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( ( zip_tseitin_97 @ ( B @ A ) )
         => ( zip_tseitin_98 @ ( C @ ( B @ A ) ) ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ ( C @ ( A @ B ) ) )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X4647: $i,X4648: $i,X4649: $i] :
      ( ~ ( zip_tseitin_97 @ ( X4647 @ X4648 ) )
      | ( zip_tseitin_98 @ ( X4649 @ ( X4647 @ X4648 ) ) )
      | ~ ( m1_subset_1 @ ( X4649 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X4648 @ X4647 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('5',plain,
    ( ( zip_tseitin_98 @ ( sk_B_98 @ ( sk_A_16 @ sk_A_16 ) ) )
    | ~ ( zip_tseitin_97 @ ( sk_A_16 @ sk_A_16 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_2 @ ( sk_B_98 @ ( sk_A_16 @ sk_A_16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,(
    ! [X4644: $i,X4645: $i,X4646: $i] :
      ( ~ ( v1_funct_2 @ ( X4646 @ ( X4644 @ X4645 ) ) )
      | ( X4644
        = ( k1_relset_1 @ ( X4644 @ ( X4645 @ X4646 ) ) ) )
      | ~ ( zip_tseitin_98 @ ( X4646 @ ( X4645 @ X4644 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('8',plain,
    ( ~ ( zip_tseitin_98 @ ( sk_B_98 @ ( sk_A_16 @ sk_A_16 ) ) )
    | ( sk_A_16
      = ( k1_relset_1 @ ( sk_A_16 @ ( sk_A_16 @ sk_B_98 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ ( sk_B_98 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_A_16 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( k1_relset_1 @ ( A @ ( B @ C ) ) )
        = ( k1_relat_1 @ C ) ) ) )).

thf('10',plain,(
    ! [X3595: $i,X3596: $i,X3597: $i] :
      ( ( ( k1_relset_1 @ ( X3596 @ ( X3597 @ X3595 ) ) )
        = ( k1_relat_1 @ X3595 ) )
      | ~ ( m1_subset_1 @ ( X3595 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X3596 @ X3597 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('11',plain,
    ( ( k1_relset_1 @ ( sk_A_16 @ ( sk_A_16 @ sk_B_98 ) ) )
    = ( k1_relat_1 @ sk_B_98 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( zip_tseitin_98 @ ( sk_B_98 @ ( sk_A_16 @ sk_A_16 ) ) )
    | ( sk_A_16
      = ( k1_relat_1 @ sk_B_98 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    ( k1_relset_1 @ ( sk_A_16 @ ( sk_A_16 @ sk_B_98 ) ) )
 != sk_A_16 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('14',plain,
    ( ( k1_relset_1 @ ( sk_A_16 @ ( sk_A_16 @ sk_B_98 ) ) )
    = ( k1_relat_1 @ sk_B_98 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('15',plain,(
    ( k1_relat_1 @ sk_B_98 )
 != sk_A_16 ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( zip_tseitin_98 @ ( sk_B_98 @ ( sk_A_16 @ sk_A_16 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','15'])).

thf('17',plain,(
    ~ ( zip_tseitin_97 @ ( sk_A_16 @ sk_A_16 ) ) ),
    inference(clc,[status(thm)],['5','16'])).

thf('18',plain,(
    sk_A_16 = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['2','17'])).

thf('19',plain,(
    m1_subset_1 @ ( sk_B_98 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_A_16 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t22_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( B @ A ) ) ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ ( D @ B ) )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ ( D @ E ) @ C ) ) )
      <=> ( ( k1_relset_1 @ ( B @ ( A @ C ) ) )
          = B ) ) ) )).

thf('20',plain,(
    ! [X3664: $i,X3665: $i,X3666: $i] :
      ( ( r2_hidden @ ( sk_D_76 @ ( X3666 @ X3664 ) @ X3664 ) )
      | ( ( k1_relset_1 @ ( X3664 @ ( X3665 @ X3666 ) ) )
        = X3664 )
      | ~ ( m1_subset_1 @ ( X3666 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X3664 @ X3665 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_relset_1])).

thf('21',plain,
    ( ( ( k1_relset_1 @ ( sk_A_16 @ ( sk_A_16 @ sk_B_98 ) ) )
      = sk_A_16 )
    | ( r2_hidden @ ( sk_D_76 @ ( sk_B_98 @ sk_A_16 ) @ sk_A_16 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ( k1_relset_1 @ ( sk_A_16 @ ( sk_A_16 @ sk_B_98 ) ) )
 != sk_A_16 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('23',plain,(
    r2_hidden @ ( sk_D_76 @ ( sk_B_98 @ sk_A_16 ) @ sk_A_16 ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ ( A @ B ) )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ ( C @ B ) )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ ( D @ B ) )
                    & ( r2_hidden @ ( D @ C ) ) ) ) ) )).

thf('24',plain,(
    ! [X1416: $i,X1417: $i] :
      ( ~ ( r2_hidden @ ( X1416 @ X1417 ) )
      | ( r2_hidden @ ( sk_C_16 @ X1417 @ X1417 ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('25',plain,(
    r2_hidden @ ( sk_C_16 @ sk_A_16 @ sk_A_16 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A @ B ) )
        = B ) ) )).

thf('26',plain,(
    ! [X1026: $i,X1027: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1027 @ X1026 ) )
        = X1026 )
      | ~ ( r2_hidden @ ( X1027 @ X1026 ) ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('27',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_C_16 @ sk_A_16 ) @ sk_A_16 ) )
    = sk_A_16 ),
    inference('sup-',[status(thm)],['25','26'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('28',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('29',plain,
    ( ( k2_xboole_0 @ ( sk_A_16 @ ( k1_tarski @ ( sk_C_16 @ sk_A_16 ) ) ) )
    = sk_A_16 ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A @ B ) )
     != k1_xboole_0 ) )).

thf('31',plain,(
    ! [X1343: $i,X1344: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1343 @ X1344 ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('32',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('33',plain,(
    ! [X1343: $i,X1344: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1343 @ X1344 ) )
     != o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( X1 @ ( k1_tarski @ X0 ) ) )
     != o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    sk_A_16 != o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['18','35'])).

%------------------------------------------------------------------------------
