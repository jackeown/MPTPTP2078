%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4XoutcU2nU

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 210 expanded)
%              Number of leaves         :   29 (  74 expanded)
%              Depth                    :   16
%              Number of atoms          :  959 (3274 expanded)
%              Number of equality atoms :   43 (  72 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(t66_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
         => ( r2_relset_1 @ A @ ( k1_tarski @ B ) @ C @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ ( k1_tarski @ B ) )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
           => ( r2_relset_1 @ A @ ( k1_tarski @ B ) @ C @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ! [E: $i] :
                ( ( r2_hidden @ E @ A )
               => ( ( k1_funct_1 @ C @ E )
                  = ( k1_funct_1 @ D @ E ) ) )
           => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) )).

thf('4',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ( r2_relset_1 @ X51 @ X52 @ X53 @ X50 )
      | ( r2_hidden @ ( sk_E @ X50 @ X53 @ X51 ) @ X51 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ~ ( v1_funct_2 @ X53 @ X51 @ X52 )
      | ~ ( v1_funct_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t18_funct_2])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( r2_hidden @ ( sk_E @ sk_D @ X0 @ sk_A ) @ sk_A )
      | ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ X0 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( r2_hidden @ ( sk_E @ sk_D @ X0 @ sk_A ) @ sk_A )
      | ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,
    ( ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 @ sk_D )
    | ( r2_hidden @ ( sk_E @ sk_D @ sk_C_1 @ sk_A ) @ sk_A )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 @ sk_D )
    | ( r2_hidden @ ( sk_E @ sk_D @ sk_C_1 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ~ ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r2_hidden @ ( sk_E @ sk_D @ sk_C_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('16',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ~ ( r2_hidden @ X54 @ X55 )
      | ( X56 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X57 )
      | ~ ( v1_funct_2 @ X57 @ X55 @ X56 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X56 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X57 @ X54 ) @ X56 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('21',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X41 != X40 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X41 ) @ ( k1_tarski @ X40 ) )
       != ( k1_tarski @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('22',plain,(
    ! [X40: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X40 ) @ ( k1_tarski @ X40 ) )
     != ( k1_tarski @ X40 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X47: $i,X49: $i] :
      ( ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X49 ) )
      | ~ ( r1_tarski @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k3_subset_1 @ X43 @ X44 )
        = ( k4_xboole_0 @ X43 @ X44 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X40: $i] :
      ( ( k3_subset_1 @ ( k1_tarski @ X40 ) @ ( k1_tarski @ X40 ) )
     != ( k1_tarski @ X40 ) ) ),
    inference(demod,[status(thm)],['22','28'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('30',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('31',plain,(
    ! [X47: $i,X49: $i] :
      ( ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X49 ) )
      | ~ ( r1_tarski @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('33',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k3_subset_1 @ X46 @ ( k3_subset_1 @ X46 @ X45 ) )
        = X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('36',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k3_subset_1 @ X43 @ X44 )
        = ( k4_xboole_0 @ X43 @ X44 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('38',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X40: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X40 ) ) ),
    inference(demod,[status(thm)],['29','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['20','41'])).

thf('43',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ ( sk_E @ sk_D @ sk_C_1 @ sk_A ) ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['14','42'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('44',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( X10 = X7 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('45',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( k1_funct_1 @ sk_D @ ( sk_E @ sk_D @ sk_C_1 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ( r2_relset_1 @ X51 @ X52 @ X53 @ X50 )
      | ( ( k1_funct_1 @ X53 @ ( sk_E @ X50 @ X53 @ X51 ) )
       != ( k1_funct_1 @ X50 @ ( sk_E @ X50 @ X53 @ X51 ) ) )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ~ ( v1_funct_2 @ X53 @ X51 @ X52 )
      | ~ ( v1_funct_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t18_funct_2])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_E @ sk_D @ sk_C_1 @ sk_A ) )
       != sk_B )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ( r2_relset_1 @ sk_A @ X0 @ sk_C_1 @ sk_D )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_E @ sk_D @ sk_C_1 @ sk_A ) )
       != sk_B )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ( r2_relset_1 @ sk_A @ X0 @ sk_C_1 @ sk_D )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    r2_hidden @ ( sk_E @ sk_D @ sk_C_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['12','13'])).

thf('53',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ~ ( r2_hidden @ X54 @ X55 )
      | ( X56 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X57 )
      | ~ ( v1_funct_2 @ X57 @ X55 @ X56 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X56 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X57 @ X54 ) @ X56 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_E @ sk_D @ sk_C_1 @ sk_A ) ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','58'])).

thf('60',plain,(
    ! [X40: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X40 ) ) ),
    inference(demod,[status(thm)],['29','40'])).

thf('61',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_E @ sk_D @ sk_C_1 @ sk_A ) ) @ ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('63',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_E @ sk_D @ sk_C_1 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( sk_B != sk_B )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ( r2_relset_1 @ sk_A @ X0 @ sk_C_1 @ sk_D )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['51','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_2 @ sk_D @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ( r2_relset_1 @ sk_A @ X0 @ sk_C_1 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
    | ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','65'])).

thf('67',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['0','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4XoutcU2nU
% 0.12/0.33  % Computer   : n024.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:33:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 134 iterations in 0.072s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.20/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.20/0.52  thf(t66_funct_2, conjecture,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ ( k1_tarski @ B ) ) & 
% 0.20/0.52         ( m1_subset_1 @
% 0.20/0.52           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.20/0.52       ( ![D:$i]:
% 0.20/0.52         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.20/0.52             ( m1_subset_1 @
% 0.20/0.52               D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.20/0.52           ( r2_relset_1 @ A @ ( k1_tarski @ B ) @ C @ D ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.52        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ ( k1_tarski @ B ) ) & 
% 0.20/0.52            ( m1_subset_1 @
% 0.20/0.52              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.20/0.52          ( ![D:$i]:
% 0.20/0.52            ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.52                ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.20/0.52                ( m1_subset_1 @
% 0.20/0.52                  D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.20/0.52              ( r2_relset_1 @ A @ ( k1_tarski @ B ) @ C @ D ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t66_funct_2])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (~ (r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1 @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D @ 
% 0.20/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D @ 
% 0.20/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t18_funct_2, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.52       ( ![D:$i]:
% 0.20/0.52         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.52             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.52           ( ( ![E:$i]:
% 0.20/0.52               ( ( r2_hidden @ E @ A ) =>
% 0.20/0.52                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 0.20/0.52             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.20/0.52         (~ (v1_funct_1 @ X50)
% 0.20/0.52          | ~ (v1_funct_2 @ X50 @ X51 @ X52)
% 0.20/0.52          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 0.20/0.52          | (r2_relset_1 @ X51 @ X52 @ X53 @ X50)
% 0.20/0.52          | (r2_hidden @ (sk_E @ X50 @ X53 @ X51) @ X51)
% 0.20/0.52          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 0.20/0.52          | ~ (v1_funct_2 @ X53 @ X51 @ X52)
% 0.20/0.52          | ~ (v1_funct_1 @ X53))),
% 0.20/0.52      inference('cnf', [status(esa)], [t18_funct_2])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_funct_1 @ X0)
% 0.20/0.52          | ~ (v1_funct_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ 
% 0.20/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 0.20/0.52          | (r2_hidden @ (sk_E @ sk_D @ X0 @ sk_A) @ sk_A)
% 0.20/0.52          | (r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ X0 @ sk_D)
% 0.20/0.52          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.52          | ~ (v1_funct_1 @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_funct_1 @ X0)
% 0.20/0.52          | ~ (v1_funct_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ 
% 0.20/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 0.20/0.52          | (r2_hidden @ (sk_E @ sk_D @ X0 @ sk_A) @ sk_A)
% 0.20/0.52          | (r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ X0 @ sk_D))),
% 0.20/0.52      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (((r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1 @ sk_D)
% 0.20/0.52        | (r2_hidden @ (sk_E @ sk_D @ sk_C_1 @ sk_A) @ sk_A)
% 0.20/0.52        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.52        | ~ (v1_funct_1 @ sk_C_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '8'])).
% 0.20/0.52  thf('10', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('11', plain, ((v1_funct_1 @ sk_C_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (((r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1 @ sk_D)
% 0.20/0.52        | (r2_hidden @ (sk_E @ sk_D @ sk_C_1 @ sk_A) @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (~ (r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1 @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('14', plain, ((r2_hidden @ (sk_E @ sk_D @ sk_C_1 @ sk_A) @ sk_A)),
% 0.20/0.52      inference('clc', [status(thm)], ['12', '13'])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D @ 
% 0.20/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t7_funct_2, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.52       ( ( r2_hidden @ C @ A ) =>
% 0.20/0.52         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.52           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X54 @ X55)
% 0.20/0.52          | ((X56) = (k1_xboole_0))
% 0.20/0.52          | ~ (v1_funct_1 @ X57)
% 0.20/0.52          | ~ (v1_funct_2 @ X57 @ X55 @ X56)
% 0.20/0.52          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X56)))
% 0.20/0.52          | (r2_hidden @ (k1_funct_1 @ X57 @ X54) @ X56))),
% 0.20/0.52      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.20/0.52          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.52          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.52          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.52          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('18', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.20/0.53          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.20/0.53  thf(t20_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.53         ( k1_tarski @ A ) ) <=>
% 0.20/0.53       ( ( A ) != ( B ) ) ))).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X40 : $i, X41 : $i]:
% 0.20/0.53         (((X41) != (X40))
% 0.20/0.53          | ((k4_xboole_0 @ (k1_tarski @ X41) @ (k1_tarski @ X40))
% 0.20/0.53              != (k1_tarski @ X41)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X40 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ (k1_tarski @ X40) @ (k1_tarski @ X40))
% 0.20/0.53           != (k1_tarski @ X40))),
% 0.20/0.53      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.53  thf(d10_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.53  thf('24', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.53      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.53  thf(t3_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X47 : $i, X49 : $i]:
% 0.20/0.53         ((m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X49)) | ~ (r1_tarski @ X47 @ X49))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.53  thf('26', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.53  thf(d5_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X43 : $i, X44 : $i]:
% 0.20/0.53         (((k3_subset_1 @ X43 @ X44) = (k4_xboole_0 @ X43 @ X44))
% 0.20/0.53          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X43)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (![X40 : $i]:
% 0.20/0.53         ((k3_subset_1 @ (k1_tarski @ X40) @ (k1_tarski @ X40))
% 0.20/0.53           != (k1_tarski @ X40))),
% 0.20/0.53      inference('demod', [status(thm)], ['22', '28'])).
% 0.20/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.53  thf('30', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.20/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (![X47 : $i, X49 : $i]:
% 0.20/0.53         ((m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X49)) | ~ (r1_tarski @ X47 @ X49))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.53  thf(involutiveness_k3_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (![X45 : $i, X46 : $i]:
% 0.20/0.53         (((k3_subset_1 @ X46 @ (k3_subset_1 @ X46 @ X45)) = (X45))
% 0.20/0.53          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46)))),
% 0.20/0.53      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (![X43 : $i, X44 : $i]:
% 0.20/0.53         (((k3_subset_1 @ X43 @ X44) = (k4_xboole_0 @ X43 @ X44))
% 0.20/0.53          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X43)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.53  thf(t3_boole, axiom,
% 0.20/0.53    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.53  thf('38', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.53  thf('39', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['37', '38'])).
% 0.20/0.53  thf('40', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['34', '39'])).
% 0.20/0.53  thf('41', plain, (![X40 : $i]: ((k1_xboole_0) != (k1_tarski @ X40))),
% 0.20/0.53      inference('demod', [status(thm)], ['29', '40'])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.53          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B)))),
% 0.20/0.53      inference('clc', [status(thm)], ['20', '41'])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      ((r2_hidden @ (k1_funct_1 @ sk_D @ (sk_E @ sk_D @ sk_C_1 @ sk_A)) @ 
% 0.20/0.53        (k1_tarski @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['14', '42'])).
% 0.20/0.53  thf(d1_tarski, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X10 @ X9)
% 0.20/0.53          | ((X10) = (X7))
% 0.20/0.53          | ((X9) != (k1_tarski @ X7)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      (![X7 : $i, X10 : $i]:
% 0.20/0.53         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['44'])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      (((k1_funct_1 @ sk_D @ (sk_E @ sk_D @ sk_C_1 @ sk_A)) = (sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['43', '45'])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.20/0.53         (~ (v1_funct_1 @ X50)
% 0.20/0.53          | ~ (v1_funct_2 @ X50 @ X51 @ X52)
% 0.20/0.53          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 0.20/0.53          | (r2_relset_1 @ X51 @ X52 @ X53 @ X50)
% 0.20/0.53          | ((k1_funct_1 @ X53 @ (sk_E @ X50 @ X53 @ X51))
% 0.20/0.53              != (k1_funct_1 @ X50 @ (sk_E @ X50 @ X53 @ X51)))
% 0.20/0.53          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 0.20/0.53          | ~ (v1_funct_2 @ X53 @ X51 @ X52)
% 0.20/0.53          | ~ (v1_funct_1 @ X53))),
% 0.20/0.53      inference('cnf', [status(esa)], [t18_funct_2])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k1_funct_1 @ sk_C_1 @ (sk_E @ sk_D @ sk_C_1 @ sk_A)) != (sk_B))
% 0.20/0.53          | ~ (v1_funct_1 @ sk_C_1)
% 0.20/0.53          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ X0)
% 0.20/0.53          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.20/0.53          | (r2_relset_1 @ sk_A @ X0 @ sk_C_1 @ sk_D)
% 0.20/0.53          | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.20/0.53          | ~ (v1_funct_2 @ sk_D @ sk_A @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ sk_D))),
% 0.20/0.53      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.53  thf('49', plain, ((v1_funct_1 @ sk_C_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('50', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k1_funct_1 @ sk_C_1 @ (sk_E @ sk_D @ sk_C_1 @ sk_A)) != (sk_B))
% 0.20/0.53          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ X0)
% 0.20/0.53          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.20/0.53          | (r2_relset_1 @ sk_A @ X0 @ sk_C_1 @ sk_D)
% 0.20/0.53          | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.20/0.53          | ~ (v1_funct_2 @ sk_D @ sk_A @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.20/0.53  thf('52', plain, ((r2_hidden @ (sk_E @ sk_D @ sk_C_1 @ sk_A) @ sk_A)),
% 0.20/0.53      inference('clc', [status(thm)], ['12', '13'])).
% 0.20/0.53  thf('53', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X54 @ X55)
% 0.20/0.53          | ((X56) = (k1_xboole_0))
% 0.20/0.53          | ~ (v1_funct_1 @ X57)
% 0.20/0.53          | ~ (v1_funct_2 @ X57 @ X55 @ X56)
% 0.20/0.53          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X56)))
% 0.20/0.53          | (r2_hidden @ (k1_funct_1 @ X57 @ X54) @ X56))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.20/0.53  thf('55', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k1_tarski @ sk_B))
% 0.20/0.53          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.53          | ~ (v1_funct_1 @ sk_C_1)
% 0.20/0.53          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.53  thf('56', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('57', plain, ((v1_funct_1 @ sk_C_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('58', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k1_tarski @ sk_B))
% 0.20/0.53          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.20/0.53  thf('59', plain,
% 0.20/0.53      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.53        | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ (sk_E @ sk_D @ sk_C_1 @ sk_A)) @ 
% 0.20/0.53           (k1_tarski @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['52', '58'])).
% 0.20/0.53  thf('60', plain, (![X40 : $i]: ((k1_xboole_0) != (k1_tarski @ X40))),
% 0.20/0.53      inference('demod', [status(thm)], ['29', '40'])).
% 0.20/0.53  thf('61', plain,
% 0.20/0.53      ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ (sk_E @ sk_D @ sk_C_1 @ sk_A)) @ 
% 0.20/0.53        (k1_tarski @ sk_B))),
% 0.20/0.53      inference('clc', [status(thm)], ['59', '60'])).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      (![X7 : $i, X10 : $i]:
% 0.20/0.53         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['44'])).
% 0.20/0.53  thf('63', plain,
% 0.20/0.53      (((k1_funct_1 @ sk_C_1 @ (sk_E @ sk_D @ sk_C_1 @ sk_A)) = (sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.53  thf('64', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((sk_B) != (sk_B))
% 0.20/0.53          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ X0)
% 0.20/0.53          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.20/0.53          | (r2_relset_1 @ sk_A @ X0 @ sk_C_1 @ sk_D)
% 0.20/0.53          | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.20/0.53          | ~ (v1_funct_2 @ sk_D @ sk_A @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['51', '63'])).
% 0.20/0.53  thf('65', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_funct_2 @ sk_D @ sk_A @ X0)
% 0.20/0.53          | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.20/0.53          | (r2_relset_1 @ sk_A @ X0 @ sk_C_1 @ sk_D)
% 0.20/0.53          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.20/0.53          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['64'])).
% 0.20/0.53  thf('66', plain,
% 0.20/0.53      ((~ (v1_funct_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.53        | ~ (m1_subset_1 @ sk_C_1 @ 
% 0.20/0.53             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 0.20/0.53        | (r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1 @ sk_D)
% 0.20/0.53        | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '65'])).
% 0.20/0.53  thf('67', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('68', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('69', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('70', plain, ((r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1 @ sk_D)),
% 0.20/0.53      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.20/0.53  thf('71', plain, ($false), inference('demod', [status(thm)], ['0', '70'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
