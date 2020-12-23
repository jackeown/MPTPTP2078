%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ymmCGS52KJ

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:53 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 526 expanded)
%              Number of leaves         :   38 ( 169 expanded)
%              Depth                    :   17
%              Number of atoms          :  902 (5301 expanded)
%              Number of equality atoms :   52 ( 164 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t4_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
         => ( ( v1_funct_1 @ B )
            & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t4_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_B )
   <= ~ ( v1_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_1 @ sk_B ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('8',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X26 ) @ X27 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X26 ) @ X28 )
      | ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['4','14','15'])).

thf('17',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','16'])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('21',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('23',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('24',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( X31
       != ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('26',plain,
    ( ( ( k1_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','16'])).

thf('29',plain,(
    ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['21','29'])).

thf('31',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','30'])).

thf('32',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('34',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','30'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('35',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_zfmisc_1 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('36',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34','36'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('38',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t43_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ C )
          <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('39',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_xboole_0 @ X18 @ X16 )
      | ( r1_tarski @ X18 @ ( k3_subset_1 @ X17 @ X16 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('41',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('44',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X13 ) @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('45',plain,(
    ! [X12: $i] :
      ( ( k2_subset_1 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('46',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t39_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
      <=> ( B
          = ( k2_subset_1 @ A ) ) ) ) )).

thf('49',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X15
       != ( k2_subset_1 @ X14 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X14 @ X15 ) @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t39_subset_1])).

thf('50',plain,(
    ! [X14: $i] :
      ( ~ ( m1_subset_1 @ ( k2_subset_1 @ X14 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X14 @ ( k2_subset_1 @ X14 ) ) @ ( k2_subset_1 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X12: $i] :
      ( ( k2_subset_1 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('52',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('53',plain,(
    ! [X12: $i] :
      ( ( k2_subset_1 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('54',plain,(
    ! [X12: $i] :
      ( ( k2_subset_1 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('55',plain,(
    ! [X14: $i] :
      ( r1_tarski @ ( k3_subset_1 @ X14 @ X14 ) @ X14 ) ),
    inference(demod,[status(thm)],['50','51','52','53','54'])).

thf('56',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      | ( X0
        = ( k3_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( k1_xboole_0
    = ( k3_subset_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','57'])).

thf('59',plain,(
    r1_tarski @ sk_B @ k1_xboole_0 ),
    inference(demod,[status(thm)],['43','58'])).

thf('60',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('61',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_B )
    | ( k1_xboole_0 = sk_B ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X14: $i] :
      ( r1_tarski @ ( k3_subset_1 @ X14 @ X14 ) @ X14 ) ),
    inference(demod,[status(thm)],['50','51','52','53','54'])).

thf('63',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('64',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('65',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_xboole_0 @ X18 @ X16 )
      | ( r1_tarski @ X18 @ ( k3_subset_1 @ X17 @ X16 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k3_subset_1 @ X0 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','70'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('72',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['62','73'])).

thf('75',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['61','74'])).

thf('76',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['61','74'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('77',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('78',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('79',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( X31
       != ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X30 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('87',plain,(
    ! [X29: $i] :
      ( zip_tseitin_0 @ X29 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('89',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('simplify_reflect+',[status(thm)],['85','91'])).

thf('93',plain,(
    $false ),
    inference(demod,[status(thm)],['32','75','76','77','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ymmCGS52KJ
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:26:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 228 iterations in 0.205s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.65  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.65  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.45/0.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.65  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.45/0.65  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.45/0.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.65  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.65  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.45/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.65  thf(t4_funct_2, conjecture,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.45/0.65       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.45/0.65         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.45/0.65           ( m1_subset_1 @
% 0.45/0.65             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.65    (~( ![A:$i,B:$i]:
% 0.45/0.65        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.45/0.65          ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.45/0.65            ( ( v1_funct_1 @ B ) & 
% 0.45/0.65              ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.45/0.65              ( m1_subset_1 @
% 0.45/0.65                B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )),
% 0.45/0.65    inference('cnf.neg', [status(esa)], [t4_funct_2])).
% 0.45/0.65  thf('0', plain,
% 0.45/0.65      ((~ (v1_funct_1 @ sk_B)
% 0.45/0.65        | ~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.45/0.65        | ~ (m1_subset_1 @ sk_B @ 
% 0.45/0.65             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('1', plain,
% 0.45/0.65      ((~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.45/0.65         <= (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.45/0.65      inference('split', [status(esa)], ['0'])).
% 0.45/0.65  thf('2', plain, ((v1_funct_1 @ sk_B)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('3', plain, ((~ (v1_funct_1 @ sk_B)) <= (~ ((v1_funct_1 @ sk_B)))),
% 0.45/0.65      inference('split', [status(esa)], ['0'])).
% 0.45/0.65  thf('4', plain, (((v1_funct_1 @ sk_B))),
% 0.45/0.65      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.65  thf('5', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(d10_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.65  thf('6', plain,
% 0.45/0.65      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.45/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.65  thf('7', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.45/0.65      inference('simplify', [status(thm)], ['6'])).
% 0.45/0.65  thf(t11_relset_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( v1_relat_1 @ C ) =>
% 0.45/0.65       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.45/0.65           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.45/0.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.45/0.65  thf('8', plain,
% 0.45/0.65      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.45/0.65         (~ (r1_tarski @ (k1_relat_1 @ X26) @ X27)
% 0.45/0.65          | ~ (r1_tarski @ (k2_relat_1 @ X26) @ X28)
% 0.45/0.65          | (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.45/0.65          | ~ (v1_relat_1 @ X26))),
% 0.45/0.65      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.45/0.65  thf('9', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X0)
% 0.45/0.65          | (m1_subset_1 @ X0 @ 
% 0.45/0.65             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.45/0.65          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.65  thf('10', plain,
% 0.45/0.65      (((m1_subset_1 @ sk_B @ 
% 0.45/0.65         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.45/0.65        | ~ (v1_relat_1 @ sk_B))),
% 0.45/0.65      inference('sup-', [status(thm)], ['5', '9'])).
% 0.45/0.65  thf('11', plain, ((v1_relat_1 @ sk_B)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('12', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_B @ 
% 0.45/0.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['10', '11'])).
% 0.45/0.65  thf('13', plain,
% 0.45/0.65      ((~ (m1_subset_1 @ sk_B @ 
% 0.45/0.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))
% 0.45/0.65         <= (~
% 0.45/0.65             ((m1_subset_1 @ sk_B @ 
% 0.45/0.65               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))))),
% 0.45/0.65      inference('split', [status(esa)], ['0'])).
% 0.45/0.65  thf('14', plain,
% 0.45/0.65      (((m1_subset_1 @ sk_B @ 
% 0.45/0.65         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['12', '13'])).
% 0.45/0.65  thf('15', plain,
% 0.45/0.65      (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.45/0.65       ~
% 0.45/0.65       ((m1_subset_1 @ sk_B @ 
% 0.45/0.65         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))) | 
% 0.45/0.65       ~ ((v1_funct_1 @ sk_B))),
% 0.45/0.65      inference('split', [status(esa)], ['0'])).
% 0.45/0.65  thf('16', plain, (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.45/0.65      inference('sat_resolution*', [status(thm)], ['4', '14', '15'])).
% 0.45/0.65  thf('17', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.45/0.65      inference('simpl_trail', [status(thm)], ['1', '16'])).
% 0.45/0.65  thf(d1_funct_2, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.65       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.65           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.45/0.65             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.45/0.65         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.65           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.45/0.65             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_1, axiom,
% 0.45/0.65    (![B:$i,A:$i]:
% 0.45/0.65     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.65       ( zip_tseitin_0 @ B @ A ) ))).
% 0.45/0.65  thf('18', plain,
% 0.45/0.65      (![X29 : $i, X30 : $i]:
% 0.45/0.65         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.65  thf('19', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_B @ 
% 0.45/0.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['10', '11'])).
% 0.45/0.65  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.45/0.65  thf(zf_stmt_3, axiom,
% 0.45/0.65    (![C:$i,B:$i,A:$i]:
% 0.45/0.65     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.45/0.65       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.45/0.65  thf(zf_stmt_5, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.65       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.45/0.65         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.65           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.45/0.65             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.45/0.65  thf('20', plain,
% 0.45/0.65      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.45/0.65         (~ (zip_tseitin_0 @ X34 @ X35)
% 0.45/0.65          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 0.45/0.65          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.65  thf('21', plain,
% 0.45/0.65      (((zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 0.45/0.65        | ~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.65  thf('22', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_B @ 
% 0.45/0.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['10', '11'])).
% 0.45/0.65  thf(redefinition_k1_relset_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.65       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.45/0.65  thf('23', plain,
% 0.45/0.65      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.45/0.65         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 0.45/0.65          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.45/0.65      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.65  thf('24', plain,
% 0.45/0.65      (((k1_relset_1 @ (k1_relat_1 @ sk_B) @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.45/0.65      inference('sup-', [status(thm)], ['22', '23'])).
% 0.45/0.65  thf('25', plain,
% 0.45/0.65      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.45/0.65         (((X31) != (k1_relset_1 @ X31 @ X32 @ X33))
% 0.45/0.65          | (v1_funct_2 @ X33 @ X31 @ X32)
% 0.45/0.65          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.65  thf('26', plain,
% 0.45/0.65      ((((k1_relat_1 @ sk_B) != (k1_relat_1 @ sk_B))
% 0.45/0.65        | ~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 0.45/0.65        | (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.65  thf('27', plain,
% 0.45/0.65      (((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.45/0.65        | ~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['26'])).
% 0.45/0.65  thf('28', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.45/0.65      inference('simpl_trail', [status(thm)], ['1', '16'])).
% 0.45/0.65  thf('29', plain, (~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.45/0.65      inference('clc', [status(thm)], ['27', '28'])).
% 0.45/0.65  thf('30', plain, (~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.45/0.65      inference('clc', [status(thm)], ['21', '29'])).
% 0.45/0.65  thf('31', plain, (((sk_A) = (k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['18', '30'])).
% 0.45/0.65  thf('32', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ k1_xboole_0)),
% 0.45/0.65      inference('demod', [status(thm)], ['17', '31'])).
% 0.45/0.65  thf('33', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_B @ 
% 0.45/0.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['10', '11'])).
% 0.45/0.65  thf('34', plain, (((sk_A) = (k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['18', '30'])).
% 0.45/0.65  thf(t113_zfmisc_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.45/0.65       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.45/0.65  thf('35', plain,
% 0.45/0.65      (![X10 : $i, X11 : $i]:
% 0.45/0.65         (((k2_zfmisc_1 @ X10 @ X11) = (k1_xboole_0))
% 0.45/0.65          | ((X11) != (k1_xboole_0)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.45/0.65  thf('36', plain,
% 0.45/0.65      (![X10 : $i]: ((k2_zfmisc_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['35'])).
% 0.45/0.65  thf('37', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['33', '34', '36'])).
% 0.45/0.65  thf(t4_subset_1, axiom,
% 0.45/0.65    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.45/0.65  thf('38', plain,
% 0.45/0.65      (![X19 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 0.45/0.65      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.45/0.65  thf(t43_subset_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.65       ( ![C:$i]:
% 0.45/0.65         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.65           ( ( r1_xboole_0 @ B @ C ) <=>
% 0.45/0.65             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.45/0.65  thf('39', plain,
% 0.45/0.65      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.45/0.65          | ~ (r1_xboole_0 @ X18 @ X16)
% 0.45/0.65          | (r1_tarski @ X18 @ (k3_subset_1 @ X17 @ X16))
% 0.45/0.65          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t43_subset_1])).
% 0.45/0.65  thf('40', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.45/0.65          | (r1_tarski @ X1 @ (k3_subset_1 @ X0 @ k1_xboole_0))
% 0.45/0.65          | ~ (r1_xboole_0 @ X1 @ k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['38', '39'])).
% 0.45/0.65  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.45/0.65  thf('41', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.45/0.65      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.45/0.65  thf('42', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.45/0.65          | (r1_tarski @ X1 @ (k3_subset_1 @ X0 @ k1_xboole_0)))),
% 0.45/0.65      inference('demod', [status(thm)], ['40', '41'])).
% 0.45/0.65  thf('43', plain,
% 0.45/0.65      ((r1_tarski @ sk_B @ (k3_subset_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['37', '42'])).
% 0.45/0.65  thf(dt_k2_subset_1, axiom,
% 0.45/0.65    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.45/0.65  thf('44', plain,
% 0.45/0.65      (![X13 : $i]: (m1_subset_1 @ (k2_subset_1 @ X13) @ (k1_zfmisc_1 @ X13))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.45/0.65  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.45/0.65  thf('45', plain, (![X12 : $i]: ((k2_subset_1 @ X12) = (X12))),
% 0.45/0.65      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.45/0.65  thf('46', plain, (![X13 : $i]: (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X13))),
% 0.45/0.65      inference('demod', [status(thm)], ['44', '45'])).
% 0.45/0.65  thf('47', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.45/0.65          | (r1_tarski @ X1 @ (k3_subset_1 @ X0 @ k1_xboole_0)))),
% 0.45/0.65      inference('demod', [status(thm)], ['40', '41'])).
% 0.45/0.65  thf('48', plain,
% 0.45/0.65      (![X0 : $i]: (r1_tarski @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['46', '47'])).
% 0.45/0.65  thf(t39_subset_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.65       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.45/0.65         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.45/0.65  thf('49', plain,
% 0.45/0.65      (![X14 : $i, X15 : $i]:
% 0.45/0.65         (((X15) != (k2_subset_1 @ X14))
% 0.45/0.65          | (r1_tarski @ (k3_subset_1 @ X14 @ X15) @ X15)
% 0.45/0.65          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t39_subset_1])).
% 0.45/0.65  thf('50', plain,
% 0.45/0.65      (![X14 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ (k2_subset_1 @ X14) @ (k1_zfmisc_1 @ X14))
% 0.45/0.65          | (r1_tarski @ (k3_subset_1 @ X14 @ (k2_subset_1 @ X14)) @ 
% 0.45/0.65             (k2_subset_1 @ X14)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['49'])).
% 0.45/0.65  thf('51', plain, (![X12 : $i]: ((k2_subset_1 @ X12) = (X12))),
% 0.45/0.65      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.45/0.65  thf('52', plain, (![X13 : $i]: (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X13))),
% 0.45/0.65      inference('demod', [status(thm)], ['44', '45'])).
% 0.45/0.65  thf('53', plain, (![X12 : $i]: ((k2_subset_1 @ X12) = (X12))),
% 0.45/0.65      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.45/0.65  thf('54', plain, (![X12 : $i]: ((k2_subset_1 @ X12) = (X12))),
% 0.45/0.65      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.45/0.65  thf('55', plain,
% 0.45/0.65      (![X14 : $i]: (r1_tarski @ (k3_subset_1 @ X14 @ X14) @ X14)),
% 0.45/0.65      inference('demod', [status(thm)], ['50', '51', '52', '53', '54'])).
% 0.45/0.66  thf('56', plain,
% 0.45/0.66      (![X2 : $i, X4 : $i]:
% 0.45/0.66         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.45/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.66  thf('57', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (r1_tarski @ X0 @ (k3_subset_1 @ X0 @ X0))
% 0.45/0.66          | ((X0) = (k3_subset_1 @ X0 @ X0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['55', '56'])).
% 0.45/0.66  thf('58', plain,
% 0.45/0.66      (((k1_xboole_0) = (k3_subset_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['48', '57'])).
% 0.45/0.66  thf('59', plain, ((r1_tarski @ sk_B @ k1_xboole_0)),
% 0.45/0.66      inference('demod', [status(thm)], ['43', '58'])).
% 0.45/0.66  thf('60', plain,
% 0.45/0.66      (![X2 : $i, X4 : $i]:
% 0.45/0.66         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.45/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.66  thf('61', plain,
% 0.45/0.66      ((~ (r1_tarski @ k1_xboole_0 @ sk_B) | ((k1_xboole_0) = (sk_B)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['59', '60'])).
% 0.45/0.66  thf('62', plain,
% 0.45/0.66      (![X14 : $i]: (r1_tarski @ (k3_subset_1 @ X14 @ X14) @ X14)),
% 0.45/0.66      inference('demod', [status(thm)], ['50', '51', '52', '53', '54'])).
% 0.45/0.66  thf('63', plain,
% 0.45/0.66      (![X19 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 0.45/0.66      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.45/0.66  thf('64', plain, (![X13 : $i]: (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X13))),
% 0.45/0.66      inference('demod', [status(thm)], ['44', '45'])).
% 0.45/0.66  thf('65', plain,
% 0.45/0.66      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.45/0.66          | ~ (r1_xboole_0 @ X18 @ X16)
% 0.45/0.66          | (r1_tarski @ X18 @ (k3_subset_1 @ X17 @ X16))
% 0.45/0.66          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t43_subset_1])).
% 0.45/0.66  thf('66', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.45/0.66          | (r1_tarski @ X1 @ (k3_subset_1 @ X0 @ X0))
% 0.45/0.66          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['64', '65'])).
% 0.45/0.66  thf('67', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.45/0.66          | (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ X0 @ X0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['63', '66'])).
% 0.45/0.66  thf('68', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.45/0.66      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.45/0.66  thf(symmetry_r1_xboole_0, axiom,
% 0.45/0.66    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.45/0.66  thf('69', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.45/0.66      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.45/0.66  thf('70', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.45/0.66      inference('sup-', [status(thm)], ['68', '69'])).
% 0.45/0.66  thf('71', plain,
% 0.45/0.66      (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ X0 @ X0))),
% 0.45/0.66      inference('demod', [status(thm)], ['67', '70'])).
% 0.45/0.66  thf(t1_xboole_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.45/0.66       ( r1_tarski @ A @ C ) ))).
% 0.45/0.66  thf('72', plain,
% 0.45/0.66      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.66         (~ (r1_tarski @ X5 @ X6)
% 0.45/0.66          | ~ (r1_tarski @ X6 @ X7)
% 0.45/0.66          | (r1_tarski @ X5 @ X7))),
% 0.45/0.66      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.45/0.66  thf('73', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((r1_tarski @ k1_xboole_0 @ X1)
% 0.45/0.66          | ~ (r1_tarski @ (k3_subset_1 @ X0 @ X0) @ X1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['71', '72'])).
% 0.45/0.66  thf('74', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.45/0.66      inference('sup-', [status(thm)], ['62', '73'])).
% 0.45/0.66  thf('75', plain, (((k1_xboole_0) = (sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['61', '74'])).
% 0.45/0.66  thf('76', plain, (((k1_xboole_0) = (sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['61', '74'])).
% 0.45/0.66  thf(t60_relat_1, axiom,
% 0.45/0.66    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.45/0.66     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.45/0.66  thf('77', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.45/0.66  thf('78', plain,
% 0.45/0.66      (![X19 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 0.45/0.66      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.45/0.66  thf('79', plain,
% 0.45/0.66      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.45/0.66         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 0.45/0.66          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.66  thf('80', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['78', '79'])).
% 0.45/0.66  thf('81', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.45/0.66  thf('82', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.66      inference('demod', [status(thm)], ['80', '81'])).
% 0.45/0.66  thf('83', plain,
% 0.45/0.66      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.45/0.66         (((X31) != (k1_relset_1 @ X31 @ X32 @ X33))
% 0.45/0.66          | (v1_funct_2 @ X33 @ X31 @ X32)
% 0.45/0.66          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.66  thf('84', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (((X1) != (k1_xboole_0))
% 0.45/0.66          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 0.45/0.66          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['82', '83'])).
% 0.45/0.66  thf('85', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.45/0.66          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['84'])).
% 0.45/0.66  thf('86', plain,
% 0.45/0.66      (![X29 : $i, X30 : $i]:
% 0.45/0.66         ((zip_tseitin_0 @ X29 @ X30) | ((X30) != (k1_xboole_0)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.66  thf('87', plain, (![X29 : $i]: (zip_tseitin_0 @ X29 @ k1_xboole_0)),
% 0.45/0.66      inference('simplify', [status(thm)], ['86'])).
% 0.45/0.66  thf('88', plain,
% 0.45/0.66      (![X19 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 0.45/0.66      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.45/0.66  thf('89', plain,
% 0.45/0.66      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.45/0.66         (~ (zip_tseitin_0 @ X34 @ X35)
% 0.45/0.66          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 0.45/0.66          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.66  thf('90', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['88', '89'])).
% 0.45/0.66  thf('91', plain,
% 0.45/0.66      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.45/0.66      inference('sup-', [status(thm)], ['87', '90'])).
% 0.45/0.66  thf('92', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.45/0.66      inference('simplify_reflect+', [status(thm)], ['85', '91'])).
% 0.45/0.66  thf('93', plain, ($false),
% 0.45/0.66      inference('demod', [status(thm)], ['32', '75', '76', '77', '92'])).
% 0.45/0.66  
% 0.45/0.66  % SZS output end Refutation
% 0.45/0.66  
% 0.45/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
