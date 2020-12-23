%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HEA7b6qaBa

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:48 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 483 expanded)
%              Number of leaves         :   41 ( 167 expanded)
%              Depth                    :   19
%              Number of atoms          :  826 (5214 expanded)
%              Number of equality atoms :   57 ( 267 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(t64_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_2 @ sk_C_2 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_2 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X61 ) ) )
      | ( ( k7_relset_1 @ X60 @ X61 @ X59 @ X62 )
        = ( k9_relat_1 @ X59 @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_2 @ sk_C_2 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_2 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t14_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf('8',plain,(
    ! [X63: $i,X64: $i,X65: $i,X66: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X63 ) @ X64 )
      | ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X65 @ X64 ) ) )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X65 @ X66 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    r1_tarski @ sk_D_2 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_D_2 ) ) @ sk_D_2 )
    | ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_D_2 ) )
      = sk_D_2 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('15',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('16',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X35 @ X36 ) @ ( k2_relat_1 @ X35 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('17',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ( v4_relat_1 @ X56 @ X57 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X58 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('19',plain,(
    v4_relat_1 @ sk_D_2 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('20',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v4_relat_1 @ X29 @ X30 )
      | ( r1_tarski @ ( k1_relat_1 @ X29 ) @ X30 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_2 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ( v1_relat_1 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('25',plain,(
    ! [X33: $i,X34: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('26',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_2 ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['21','26'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('28',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X15
        = ( k1_tarski @ X14 ) )
      | ( X15 = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('29',plain,
    ( ( ( k1_relat_1 @ sk_D_2 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D_2 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('30',plain,(
    ! [X49: $i,X50: $i] :
      ( ( ( k1_relat_1 @ X50 )
       != ( k1_tarski @ X49 ) )
      | ( ( k2_relat_1 @ X50 )
        = ( k1_tarski @ ( k1_funct_1 @ X50 @ X49 ) ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D_2 ) )
      | ( ( k1_relat_1 @ sk_D_2 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k2_relat_1 @ sk_D_2 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_2 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 )
    | ( ( k1_relat_1 @ sk_D_2 )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['31'])).

thf('33',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['24','25'])).

thf('35',plain,
    ( ( ( k2_relat_1 @ sk_D_2 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_2 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D_2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_2 @ sk_C_2 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_2 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_2 @ sk_C_2 ) @ ( k2_relat_1 @ sk_D_2 ) )
    | ( ( k1_relat_1 @ sk_D_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('39',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_2 @ sk_C_2 ) @ ( k2_relat_1 @ sk_D_2 ) )
    | ( ( k1_relat_1 @ sk_D_2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( ( k1_relat_1 @ sk_D_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['24','25'])).

thf('42',plain,
    ( ( k1_relat_1 @ sk_D_2 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['40','41'])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('43',plain,(
    ! [X42: $i,X43: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X42 @ X43 ) @ X42 )
      | ( r2_hidden @ ( sk_D @ X42 @ X43 ) @ ( k1_relat_1 @ X43 ) )
      | ( X42
        = ( k2_relat_1 @ X43 ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('44',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X51 @ X52 )
      | ~ ( r1_tarski @ X52 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( sk_D @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( sk_D @ X0 @ sk_D_2 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_D_2 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_D_2 ) )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ~ ( v1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('48',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['24','25'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_D_2 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X51 @ X52 )
      | ~ ( r1_tarski @ X52 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_D_2 ) )
      | ~ ( r1_tarski @ X0 @ ( sk_C_1 @ X0 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['15','52'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('54',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_zfmisc_1 @ X18 @ X19 )
        = k1_xboole_0 )
      | ( X19 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('55',plain,(
    ! [X18: $i] :
      ( ( k2_zfmisc_1 @ X18 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('57',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['15','52'])).

thf('58',plain,(
    ! [X18: $i] :
      ( ( k2_zfmisc_1 @ X18 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('59',plain,(
    k1_xboole_0 = sk_D_2 ),
    inference(demod,[status(thm)],['14','53','55','56','57','58'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('60',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('61',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ( v5_relat_1 @ X56 @ X58 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X58 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('63',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v5_relat_1 @ X31 @ X32 )
      | ( r1_tarski @ ( k2_relat_1 @ X31 ) @ X32 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_zfmisc_1 @ X18 @ X19 )
        = k1_xboole_0 )
      | ( X18 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('66',plain,(
    ! [X19: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X19 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X33: $i,X34: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('68',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['64','68'])).

thf('70',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('71',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X35 @ X36 ) @ ( k2_relat_1 @ X35 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['66','67'])).

thf('77',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    k1_xboole_0 = sk_D_2 ),
    inference(demod,[status(thm)],['14','53','55','56','57','58'])).

thf('81',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['4','59','79','80','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HEA7b6qaBa
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:42:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.74/0.92  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.74/0.92  % Solved by: fo/fo7.sh
% 0.74/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/0.92  % done 995 iterations in 0.475s
% 0.74/0.92  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.74/0.92  % SZS output start Refutation
% 0.74/0.92  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.74/0.92  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.74/0.92  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.74/0.92  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.74/0.92  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.74/0.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.74/0.92  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.74/0.92  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.74/0.92  thf(sk_B_type, type, sk_B: $i).
% 0.74/0.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.74/0.92  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.74/0.92  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.74/0.92  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.74/0.92  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.74/0.92  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.74/0.92  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.74/0.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.74/0.92  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.74/0.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.74/0.92  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.74/0.92  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.74/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.74/0.92  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.74/0.92  thf(t64_funct_2, conjecture,
% 0.74/0.92    (![A:$i,B:$i,C:$i,D:$i]:
% 0.74/0.92     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.74/0.92         ( m1_subset_1 @
% 0.74/0.92           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.74/0.92       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.74/0.92         ( r1_tarski @
% 0.74/0.92           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.74/0.92           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.74/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.74/0.92    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.74/0.92        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.74/0.92            ( m1_subset_1 @
% 0.74/0.92              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.74/0.92          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.74/0.92            ( r1_tarski @
% 0.74/0.92              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.74/0.92              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.74/0.92    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.74/0.92  thf('0', plain,
% 0.74/0.92      (~ (r1_tarski @ 
% 0.74/0.92          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_2 @ sk_C_2) @ 
% 0.74/0.92          (k1_tarski @ (k1_funct_1 @ sk_D_2 @ sk_A)))),
% 0.74/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.92  thf('1', plain,
% 0.74/0.92      ((m1_subset_1 @ sk_D_2 @ 
% 0.74/0.92        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.74/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.92  thf(redefinition_k7_relset_1, axiom,
% 0.74/0.92    (![A:$i,B:$i,C:$i,D:$i]:
% 0.74/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.74/0.92       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.74/0.92  thf('2', plain,
% 0.74/0.92      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 0.74/0.92         (~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X61)))
% 0.74/0.92          | ((k7_relset_1 @ X60 @ X61 @ X59 @ X62) = (k9_relat_1 @ X59 @ X62)))),
% 0.74/0.92      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.74/0.92  thf('3', plain,
% 0.74/0.92      (![X0 : $i]:
% 0.74/0.92         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_2 @ X0)
% 0.74/0.92           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.74/0.92      inference('sup-', [status(thm)], ['1', '2'])).
% 0.74/0.92  thf('4', plain,
% 0.74/0.92      (~ (r1_tarski @ (k9_relat_1 @ sk_D_2 @ sk_C_2) @ 
% 0.74/0.92          (k1_tarski @ (k1_funct_1 @ sk_D_2 @ sk_A)))),
% 0.74/0.92      inference('demod', [status(thm)], ['0', '3'])).
% 0.74/0.92  thf(d10_xboole_0, axiom,
% 0.74/0.92    (![A:$i,B:$i]:
% 0.74/0.92     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.74/0.92  thf('5', plain,
% 0.74/0.92      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.74/0.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.74/0.92  thf('6', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.74/0.92      inference('simplify', [status(thm)], ['5'])).
% 0.74/0.92  thf('7', plain,
% 0.74/0.92      ((m1_subset_1 @ sk_D_2 @ 
% 0.74/0.92        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.74/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.92  thf(t14_relset_1, axiom,
% 0.74/0.92    (![A:$i,B:$i,C:$i,D:$i]:
% 0.74/0.92     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.74/0.92       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 0.74/0.92         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 0.74/0.92  thf('8', plain,
% 0.74/0.92      (![X63 : $i, X64 : $i, X65 : $i, X66 : $i]:
% 0.74/0.92         (~ (r1_tarski @ (k2_relat_1 @ X63) @ X64)
% 0.74/0.92          | (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X65 @ X64)))
% 0.74/0.92          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X65 @ X66))))),
% 0.74/0.92      inference('cnf', [status(esa)], [t14_relset_1])).
% 0.74/0.92  thf('9', plain,
% 0.74/0.92      (![X0 : $i]:
% 0.74/0.92         ((m1_subset_1 @ sk_D_2 @ 
% 0.74/0.92           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ X0)))
% 0.74/0.92          | ~ (r1_tarski @ (k2_relat_1 @ sk_D_2) @ X0))),
% 0.74/0.92      inference('sup-', [status(thm)], ['7', '8'])).
% 0.74/0.92  thf('10', plain,
% 0.74/0.92      ((m1_subset_1 @ sk_D_2 @ 
% 0.74/0.92        (k1_zfmisc_1 @ 
% 0.74/0.92         (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_D_2))))),
% 0.74/0.92      inference('sup-', [status(thm)], ['6', '9'])).
% 0.74/0.92  thf(t3_subset, axiom,
% 0.74/0.92    (![A:$i,B:$i]:
% 0.74/0.92     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.74/0.92  thf('11', plain,
% 0.74/0.92      (![X21 : $i, X22 : $i]:
% 0.74/0.92         ((r1_tarski @ X21 @ X22) | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 0.74/0.92      inference('cnf', [status(esa)], [t3_subset])).
% 0.74/0.92  thf('12', plain,
% 0.74/0.92      ((r1_tarski @ sk_D_2 @ 
% 0.74/0.92        (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_D_2)))),
% 0.74/0.92      inference('sup-', [status(thm)], ['10', '11'])).
% 0.74/0.92  thf('13', plain,
% 0.74/0.92      (![X4 : $i, X6 : $i]:
% 0.74/0.92         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.74/0.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.74/0.92  thf('14', plain,
% 0.74/0.92      ((~ (r1_tarski @ 
% 0.74/0.92           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_D_2)) @ sk_D_2)
% 0.74/0.92        | ((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_D_2))
% 0.74/0.92            = (sk_D_2)))),
% 0.74/0.92      inference('sup-', [status(thm)], ['12', '13'])).
% 0.74/0.92  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.74/0.92  thf('15', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.74/0.92      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.74/0.92  thf(t144_relat_1, axiom,
% 0.74/0.92    (![A:$i,B:$i]:
% 0.74/0.92     ( ( v1_relat_1 @ B ) =>
% 0.74/0.92       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.74/0.92  thf('16', plain,
% 0.74/0.92      (![X35 : $i, X36 : $i]:
% 0.74/0.92         ((r1_tarski @ (k9_relat_1 @ X35 @ X36) @ (k2_relat_1 @ X35))
% 0.74/0.92          | ~ (v1_relat_1 @ X35))),
% 0.74/0.92      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.74/0.92  thf('17', plain,
% 0.74/0.92      ((m1_subset_1 @ sk_D_2 @ 
% 0.74/0.92        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.74/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.92  thf(cc2_relset_1, axiom,
% 0.74/0.92    (![A:$i,B:$i,C:$i]:
% 0.74/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.74/0.92       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.74/0.92  thf('18', plain,
% 0.74/0.92      (![X56 : $i, X57 : $i, X58 : $i]:
% 0.74/0.92         ((v4_relat_1 @ X56 @ X57)
% 0.74/0.92          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X58))))),
% 0.74/0.92      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.74/0.92  thf('19', plain, ((v4_relat_1 @ sk_D_2 @ (k1_tarski @ sk_A))),
% 0.74/0.92      inference('sup-', [status(thm)], ['17', '18'])).
% 0.74/0.92  thf(d18_relat_1, axiom,
% 0.74/0.92    (![A:$i,B:$i]:
% 0.74/0.92     ( ( v1_relat_1 @ B ) =>
% 0.74/0.92       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.74/0.92  thf('20', plain,
% 0.74/0.92      (![X29 : $i, X30 : $i]:
% 0.74/0.92         (~ (v4_relat_1 @ X29 @ X30)
% 0.74/0.92          | (r1_tarski @ (k1_relat_1 @ X29) @ X30)
% 0.74/0.92          | ~ (v1_relat_1 @ X29))),
% 0.74/0.92      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.74/0.92  thf('21', plain,
% 0.74/0.92      ((~ (v1_relat_1 @ sk_D_2)
% 0.74/0.92        | (r1_tarski @ (k1_relat_1 @ sk_D_2) @ (k1_tarski @ sk_A)))),
% 0.74/0.92      inference('sup-', [status(thm)], ['19', '20'])).
% 0.74/0.92  thf('22', plain,
% 0.74/0.92      ((m1_subset_1 @ sk_D_2 @ 
% 0.74/0.92        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.74/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.92  thf(cc2_relat_1, axiom,
% 0.74/0.92    (![A:$i]:
% 0.74/0.92     ( ( v1_relat_1 @ A ) =>
% 0.74/0.92       ( ![B:$i]:
% 0.74/0.92         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.74/0.92  thf('23', plain,
% 0.74/0.92      (![X27 : $i, X28 : $i]:
% 0.74/0.92         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 0.74/0.92          | (v1_relat_1 @ X27)
% 0.74/0.92          | ~ (v1_relat_1 @ X28))),
% 0.74/0.92      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.74/0.92  thf('24', plain,
% 0.74/0.92      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.74/0.92        | (v1_relat_1 @ sk_D_2))),
% 0.74/0.92      inference('sup-', [status(thm)], ['22', '23'])).
% 0.74/0.92  thf(fc6_relat_1, axiom,
% 0.74/0.92    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.74/0.92  thf('25', plain,
% 0.74/0.92      (![X33 : $i, X34 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X33 @ X34))),
% 0.74/0.92      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.74/0.92  thf('26', plain, ((v1_relat_1 @ sk_D_2)),
% 0.74/0.92      inference('demod', [status(thm)], ['24', '25'])).
% 0.74/0.92  thf('27', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_2) @ (k1_tarski @ sk_A))),
% 0.74/0.92      inference('demod', [status(thm)], ['21', '26'])).
% 0.74/0.92  thf(l3_zfmisc_1, axiom,
% 0.74/0.92    (![A:$i,B:$i]:
% 0.74/0.92     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.74/0.92       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.74/0.92  thf('28', plain,
% 0.74/0.92      (![X14 : $i, X15 : $i]:
% 0.74/0.92         (((X15) = (k1_tarski @ X14))
% 0.74/0.92          | ((X15) = (k1_xboole_0))
% 0.74/0.92          | ~ (r1_tarski @ X15 @ (k1_tarski @ X14)))),
% 0.74/0.92      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.74/0.92  thf('29', plain,
% 0.74/0.92      ((((k1_relat_1 @ sk_D_2) = (k1_xboole_0))
% 0.74/0.92        | ((k1_relat_1 @ sk_D_2) = (k1_tarski @ sk_A)))),
% 0.74/0.92      inference('sup-', [status(thm)], ['27', '28'])).
% 0.74/0.92  thf(t14_funct_1, axiom,
% 0.74/0.92    (![A:$i,B:$i]:
% 0.74/0.92     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.74/0.92       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.74/0.92         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.74/0.92  thf('30', plain,
% 0.74/0.92      (![X49 : $i, X50 : $i]:
% 0.74/0.92         (((k1_relat_1 @ X50) != (k1_tarski @ X49))
% 0.74/0.92          | ((k2_relat_1 @ X50) = (k1_tarski @ (k1_funct_1 @ X50 @ X49)))
% 0.74/0.92          | ~ (v1_funct_1 @ X50)
% 0.74/0.92          | ~ (v1_relat_1 @ X50))),
% 0.74/0.92      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.74/0.92  thf('31', plain,
% 0.74/0.92      (![X0 : $i]:
% 0.74/0.92         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D_2))
% 0.74/0.92          | ((k1_relat_1 @ sk_D_2) = (k1_xboole_0))
% 0.74/0.92          | ~ (v1_relat_1 @ X0)
% 0.74/0.92          | ~ (v1_funct_1 @ X0)
% 0.74/0.92          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.74/0.92      inference('sup-', [status(thm)], ['29', '30'])).
% 0.74/0.92  thf('32', plain,
% 0.74/0.92      ((((k2_relat_1 @ sk_D_2) = (k1_tarski @ (k1_funct_1 @ sk_D_2 @ sk_A)))
% 0.74/0.92        | ~ (v1_funct_1 @ sk_D_2)
% 0.74/0.92        | ~ (v1_relat_1 @ sk_D_2)
% 0.74/0.92        | ((k1_relat_1 @ sk_D_2) = (k1_xboole_0)))),
% 0.74/0.92      inference('eq_res', [status(thm)], ['31'])).
% 0.74/0.92  thf('33', plain, ((v1_funct_1 @ sk_D_2)),
% 0.74/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.92  thf('34', plain, ((v1_relat_1 @ sk_D_2)),
% 0.74/0.92      inference('demod', [status(thm)], ['24', '25'])).
% 0.74/0.92  thf('35', plain,
% 0.74/0.92      ((((k2_relat_1 @ sk_D_2) = (k1_tarski @ (k1_funct_1 @ sk_D_2 @ sk_A)))
% 0.74/0.92        | ((k1_relat_1 @ sk_D_2) = (k1_xboole_0)))),
% 0.74/0.92      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.74/0.92  thf('36', plain,
% 0.74/0.92      (~ (r1_tarski @ 
% 0.74/0.92          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_2 @ sk_C_2) @ 
% 0.74/0.92          (k1_tarski @ (k1_funct_1 @ sk_D_2 @ sk_A)))),
% 0.74/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.92  thf('37', plain,
% 0.74/0.92      ((~ (r1_tarski @ 
% 0.74/0.92           (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_2 @ sk_C_2) @ 
% 0.74/0.92           (k2_relat_1 @ sk_D_2))
% 0.74/0.92        | ((k1_relat_1 @ sk_D_2) = (k1_xboole_0)))),
% 0.74/0.92      inference('sup-', [status(thm)], ['35', '36'])).
% 0.74/0.92  thf('38', plain,
% 0.74/0.92      (![X0 : $i]:
% 0.74/0.92         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_2 @ X0)
% 0.74/0.92           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.74/0.92      inference('sup-', [status(thm)], ['1', '2'])).
% 0.74/0.92  thf('39', plain,
% 0.74/0.92      ((~ (r1_tarski @ (k9_relat_1 @ sk_D_2 @ sk_C_2) @ (k2_relat_1 @ sk_D_2))
% 0.74/0.92        | ((k1_relat_1 @ sk_D_2) = (k1_xboole_0)))),
% 0.74/0.92      inference('demod', [status(thm)], ['37', '38'])).
% 0.74/0.92  thf('40', plain,
% 0.74/0.92      ((~ (v1_relat_1 @ sk_D_2) | ((k1_relat_1 @ sk_D_2) = (k1_xboole_0)))),
% 0.74/0.92      inference('sup-', [status(thm)], ['16', '39'])).
% 0.74/0.92  thf('41', plain, ((v1_relat_1 @ sk_D_2)),
% 0.74/0.92      inference('demod', [status(thm)], ['24', '25'])).
% 0.74/0.92  thf('42', plain, (((k1_relat_1 @ sk_D_2) = (k1_xboole_0))),
% 0.74/0.92      inference('demod', [status(thm)], ['40', '41'])).
% 0.74/0.92  thf(d5_funct_1, axiom,
% 0.74/0.92    (![A:$i]:
% 0.74/0.92     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.74/0.92       ( ![B:$i]:
% 0.74/0.92         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.74/0.92           ( ![C:$i]:
% 0.74/0.92             ( ( r2_hidden @ C @ B ) <=>
% 0.74/0.92               ( ?[D:$i]:
% 0.74/0.92                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.74/0.92                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.74/0.92  thf('43', plain,
% 0.74/0.92      (![X42 : $i, X43 : $i]:
% 0.74/0.92         ((r2_hidden @ (sk_C_1 @ X42 @ X43) @ X42)
% 0.74/0.92          | (r2_hidden @ (sk_D @ X42 @ X43) @ (k1_relat_1 @ X43))
% 0.74/0.92          | ((X42) = (k2_relat_1 @ X43))
% 0.74/0.92          | ~ (v1_funct_1 @ X43)
% 0.74/0.92          | ~ (v1_relat_1 @ X43))),
% 0.74/0.92      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.74/0.92  thf(t7_ordinal1, axiom,
% 0.74/0.92    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.74/0.92  thf('44', plain,
% 0.74/0.92      (![X51 : $i, X52 : $i]:
% 0.74/0.92         (~ (r2_hidden @ X51 @ X52) | ~ (r1_tarski @ X52 @ X51))),
% 0.74/0.92      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.74/0.92  thf('45', plain,
% 0.74/0.92      (![X0 : $i, X1 : $i]:
% 0.74/0.92         (~ (v1_relat_1 @ X0)
% 0.74/0.92          | ~ (v1_funct_1 @ X0)
% 0.74/0.92          | ((X1) = (k2_relat_1 @ X0))
% 0.74/0.92          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 0.74/0.92          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (sk_D @ X1 @ X0)))),
% 0.74/0.92      inference('sup-', [status(thm)], ['43', '44'])).
% 0.74/0.92  thf('46', plain,
% 0.74/0.92      (![X0 : $i]:
% 0.74/0.92         (~ (r1_tarski @ k1_xboole_0 @ (sk_D @ X0 @ sk_D_2))
% 0.74/0.92          | (r2_hidden @ (sk_C_1 @ X0 @ sk_D_2) @ X0)
% 0.74/0.92          | ((X0) = (k2_relat_1 @ sk_D_2))
% 0.74/0.92          | ~ (v1_funct_1 @ sk_D_2)
% 0.74/0.92          | ~ (v1_relat_1 @ sk_D_2))),
% 0.74/0.92      inference('sup-', [status(thm)], ['42', '45'])).
% 0.74/0.92  thf('47', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.74/0.92      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.74/0.92  thf('48', plain, ((v1_funct_1 @ sk_D_2)),
% 0.74/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.92  thf('49', plain, ((v1_relat_1 @ sk_D_2)),
% 0.74/0.92      inference('demod', [status(thm)], ['24', '25'])).
% 0.74/0.92  thf('50', plain,
% 0.74/0.92      (![X0 : $i]:
% 0.74/0.92         ((r2_hidden @ (sk_C_1 @ X0 @ sk_D_2) @ X0)
% 0.74/0.92          | ((X0) = (k2_relat_1 @ sk_D_2)))),
% 0.74/0.92      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 0.74/0.92  thf('51', plain,
% 0.74/0.92      (![X51 : $i, X52 : $i]:
% 0.74/0.92         (~ (r2_hidden @ X51 @ X52) | ~ (r1_tarski @ X52 @ X51))),
% 0.74/0.92      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.74/0.92  thf('52', plain,
% 0.74/0.92      (![X0 : $i]:
% 0.74/0.92         (((X0) = (k2_relat_1 @ sk_D_2))
% 0.74/0.92          | ~ (r1_tarski @ X0 @ (sk_C_1 @ X0 @ sk_D_2)))),
% 0.74/0.92      inference('sup-', [status(thm)], ['50', '51'])).
% 0.74/0.92  thf('53', plain, (((k1_xboole_0) = (k2_relat_1 @ sk_D_2))),
% 0.74/0.92      inference('sup-', [status(thm)], ['15', '52'])).
% 0.74/0.92  thf(t113_zfmisc_1, axiom,
% 0.74/0.92    (![A:$i,B:$i]:
% 0.74/0.92     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.74/0.92       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.74/0.92  thf('54', plain,
% 0.74/0.92      (![X18 : $i, X19 : $i]:
% 0.74/0.92         (((k2_zfmisc_1 @ X18 @ X19) = (k1_xboole_0))
% 0.74/0.92          | ((X19) != (k1_xboole_0)))),
% 0.74/0.92      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.74/0.92  thf('55', plain,
% 0.74/0.92      (![X18 : $i]: ((k2_zfmisc_1 @ X18 @ k1_xboole_0) = (k1_xboole_0))),
% 0.74/0.92      inference('simplify', [status(thm)], ['54'])).
% 0.74/0.92  thf('56', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.74/0.92      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.74/0.92  thf('57', plain, (((k1_xboole_0) = (k2_relat_1 @ sk_D_2))),
% 0.74/0.92      inference('sup-', [status(thm)], ['15', '52'])).
% 0.74/0.92  thf('58', plain,
% 0.74/0.92      (![X18 : $i]: ((k2_zfmisc_1 @ X18 @ k1_xboole_0) = (k1_xboole_0))),
% 0.74/0.92      inference('simplify', [status(thm)], ['54'])).
% 0.74/0.92  thf('59', plain, (((k1_xboole_0) = (sk_D_2))),
% 0.74/0.92      inference('demod', [status(thm)], ['14', '53', '55', '56', '57', '58'])).
% 0.74/0.92  thf(t4_subset_1, axiom,
% 0.74/0.92    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.74/0.92  thf('60', plain,
% 0.74/0.92      (![X20 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 0.74/0.92      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.74/0.92  thf('61', plain,
% 0.74/0.92      (![X56 : $i, X57 : $i, X58 : $i]:
% 0.74/0.92         ((v5_relat_1 @ X56 @ X58)
% 0.74/0.92          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X58))))),
% 0.74/0.92      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.74/0.92  thf('62', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 0.74/0.92      inference('sup-', [status(thm)], ['60', '61'])).
% 0.74/0.92  thf(d19_relat_1, axiom,
% 0.74/0.92    (![A:$i,B:$i]:
% 0.74/0.92     ( ( v1_relat_1 @ B ) =>
% 0.74/0.92       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.74/0.92  thf('63', plain,
% 0.74/0.92      (![X31 : $i, X32 : $i]:
% 0.74/0.92         (~ (v5_relat_1 @ X31 @ X32)
% 0.74/0.92          | (r1_tarski @ (k2_relat_1 @ X31) @ X32)
% 0.74/0.92          | ~ (v1_relat_1 @ X31))),
% 0.74/0.92      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.74/0.92  thf('64', plain,
% 0.74/0.92      (![X0 : $i]:
% 0.74/0.92         (~ (v1_relat_1 @ k1_xboole_0)
% 0.74/0.92          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))),
% 0.74/0.92      inference('sup-', [status(thm)], ['62', '63'])).
% 0.74/0.92  thf('65', plain,
% 0.74/0.92      (![X18 : $i, X19 : $i]:
% 0.74/0.92         (((k2_zfmisc_1 @ X18 @ X19) = (k1_xboole_0))
% 0.74/0.92          | ((X18) != (k1_xboole_0)))),
% 0.74/0.92      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.74/0.92  thf('66', plain,
% 0.74/0.92      (![X19 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X19) = (k1_xboole_0))),
% 0.74/0.92      inference('simplify', [status(thm)], ['65'])).
% 0.74/0.92  thf('67', plain,
% 0.74/0.92      (![X33 : $i, X34 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X33 @ X34))),
% 0.74/0.92      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.74/0.92  thf('68', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.74/0.92      inference('sup+', [status(thm)], ['66', '67'])).
% 0.74/0.92  thf('69', plain, (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 0.74/0.92      inference('demod', [status(thm)], ['64', '68'])).
% 0.74/0.92  thf('70', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.74/0.92      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.74/0.92  thf('71', plain,
% 0.74/0.92      (![X4 : $i, X6 : $i]:
% 0.74/0.92         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.74/0.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.74/0.92  thf('72', plain,
% 0.74/0.92      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.74/0.92      inference('sup-', [status(thm)], ['70', '71'])).
% 0.74/0.92  thf('73', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.74/0.92      inference('sup-', [status(thm)], ['69', '72'])).
% 0.74/0.92  thf('74', plain,
% 0.74/0.92      (![X35 : $i, X36 : $i]:
% 0.74/0.92         ((r1_tarski @ (k9_relat_1 @ X35 @ X36) @ (k2_relat_1 @ X35))
% 0.74/0.92          | ~ (v1_relat_1 @ X35))),
% 0.74/0.92      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.74/0.92  thf('75', plain,
% 0.74/0.92      (![X0 : $i]:
% 0.74/0.92         ((r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.74/0.92          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.74/0.92      inference('sup+', [status(thm)], ['73', '74'])).
% 0.74/0.92  thf('76', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.74/0.92      inference('sup+', [status(thm)], ['66', '67'])).
% 0.74/0.92  thf('77', plain,
% 0.74/0.92      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)),
% 0.74/0.92      inference('demod', [status(thm)], ['75', '76'])).
% 0.74/0.92  thf('78', plain,
% 0.74/0.92      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.74/0.92      inference('sup-', [status(thm)], ['70', '71'])).
% 0.74/0.92  thf('79', plain,
% 0.74/0.92      (![X0 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.74/0.92      inference('sup-', [status(thm)], ['77', '78'])).
% 0.74/0.92  thf('80', plain, (((k1_xboole_0) = (sk_D_2))),
% 0.74/0.92      inference('demod', [status(thm)], ['14', '53', '55', '56', '57', '58'])).
% 0.74/0.92  thf('81', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.74/0.92      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.74/0.92  thf('82', plain, ($false),
% 0.74/0.92      inference('demod', [status(thm)], ['4', '59', '79', '80', '81'])).
% 0.74/0.92  
% 0.74/0.92  % SZS output end Refutation
% 0.74/0.92  
% 0.78/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
