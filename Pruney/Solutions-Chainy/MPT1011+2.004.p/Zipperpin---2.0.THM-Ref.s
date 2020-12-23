%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CU1dWrgFVv

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 542 expanded)
%              Number of leaves         :   25 ( 162 expanded)
%              Depth                    :   20
%              Number of atoms          :  952 (11687 expanded)
%              Number of equality atoms :   53 ( 206 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( r2_relset_1 @ X22 @ X23 @ X24 @ X21 )
      | ( r2_hidden @ ( sk_E @ X21 @ X24 @ X22 ) @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
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
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ( X27 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X28 @ X25 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_E @ sk_D @ sk_C_1 @ sk_A ) ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('22',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( X4 = X1 )
      | ( X3
       != ( k1_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('23',plain,(
    ! [X1: $i,X4: $i] :
      ( ( X4 = X1 )
      | ~ ( r2_hidden @ X4 @ ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_E @ sk_D @ sk_C_1 @ sk_A ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    r2_hidden @ ( sk_E @ sk_D @ sk_C_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['12','13'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ( X27 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X28 @ X25 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ ( sk_E @ sk_D @ sk_C_1 @ sk_A ) ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    ! [X1: $i,X4: $i] :
      ( ( X4 = X1 )
      | ~ ( r2_hidden @ X4 @ ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('34',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_D @ ( sk_E @ sk_D @ sk_C_1 @ sk_A ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( r2_relset_1 @ X22 @ X23 @ X24 @ X21 )
      | ( ( k1_funct_1 @ X24 @ ( sk_E @ X21 @ X24 @ X22 ) )
       != ( k1_funct_1 @ X21 @ ( sk_E @ X21 @ X24 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t18_funct_2])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_E @ sk_D @ sk_C_1 @ sk_A ) )
       != sk_B )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ( r2_relset_1 @ sk_A @ X0 @ sk_C_1 @ sk_D )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_E @ sk_D @ sk_C_1 @ sk_A ) )
       != sk_B )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ( r2_relset_1 @ sk_A @ X0 @ sk_C_1 @ sk_D )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( sk_B != sk_B )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ( r2_relset_1 @ sk_A @ X0 @ sk_C_1 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ X0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ( r2_relset_1 @ sk_A @ X0 @ sk_C_1 @ sk_D )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ X0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
    | ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','41'])).

thf('43',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,(
    ~ ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['0','48'])).

thf('50',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['46','47'])).

thf(t130_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != k1_xboole_0 )
     => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
         != k1_xboole_0 )
        & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
         != k1_xboole_0 ) ) ) )).

thf('51',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ ( k1_tarski @ X13 ) @ X12 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t130_zfmisc_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('53',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_zfmisc_1 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('54',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['52','54'])).

thf('56',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('58',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('60',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('61',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('62',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 )
      | ( X17 != X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('63',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['49','56','57','58','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CU1dWrgFVv
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:56:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 119 iterations in 0.067s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.52  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.20/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
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
% 0.20/0.52      ((m1_subset_1 @ sk_C_1 @ 
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
% 0.20/0.52      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.52         (~ (v1_funct_1 @ X21)
% 0.20/0.52          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 0.20/0.52          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.20/0.52          | (r2_relset_1 @ X22 @ X23 @ X24 @ X21)
% 0.20/0.52          | (r2_hidden @ (sk_E @ X21 @ X24 @ X22) @ X22)
% 0.20/0.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.20/0.52          | ~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.20/0.52          | ~ (v1_funct_1 @ X24))),
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
% 0.20/0.52      ((m1_subset_1 @ sk_C_1 @ 
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
% 0.20/0.52      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X25 @ X26)
% 0.20/0.52          | ((X27) = (k1_xboole_0))
% 0.20/0.52          | ~ (v1_funct_1 @ X28)
% 0.20/0.52          | ~ (v1_funct_2 @ X28 @ X26 @ X27)
% 0.20/0.52          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.20/0.52          | (r2_hidden @ (k1_funct_1 @ X28 @ X25) @ X27))),
% 0.20/0.52      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k1_tarski @ sk_B))
% 0.20/0.52          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.52          | ~ (v1_funct_1 @ sk_C_1)
% 0.20/0.52          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.52          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.52  thf('18', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('19', plain, ((v1_funct_1 @ sk_C_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k1_tarski @ sk_B))
% 0.20/0.52          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.52          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.52        | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ (sk_E @ sk_D @ sk_C_1 @ sk_A)) @ 
% 0.20/0.52           (k1_tarski @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['14', '20'])).
% 0.20/0.52  thf(d1_tarski, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X4 @ X3) | ((X4) = (X1)) | ((X3) != (k1_tarski @ X1)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X1 : $i, X4 : $i]:
% 0.20/0.52         (((X4) = (X1)) | ~ (r2_hidden @ X4 @ (k1_tarski @ X1)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.52        | ((k1_funct_1 @ sk_C_1 @ (sk_E @ sk_D @ sk_C_1 @ sk_A)) = (sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['21', '23'])).
% 0.20/0.52  thf('25', plain, ((r2_hidden @ (sk_E @ sk_D @ sk_C_1 @ sk_A) @ sk_A)),
% 0.20/0.52      inference('clc', [status(thm)], ['12', '13'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D @ 
% 0.20/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X25 @ X26)
% 0.20/0.52          | ((X27) = (k1_xboole_0))
% 0.20/0.52          | ~ (v1_funct_1 @ X28)
% 0.20/0.52          | ~ (v1_funct_2 @ X28 @ X26 @ X27)
% 0.20/0.52          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.20/0.52          | (r2_hidden @ (k1_funct_1 @ X28 @ X25) @ X27))),
% 0.20/0.52      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.20/0.52          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.52          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.52          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.52          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.52  thf('29', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('30', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.20/0.52          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.52          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.52        | (r2_hidden @ (k1_funct_1 @ sk_D @ (sk_E @ sk_D @ sk_C_1 @ sk_A)) @ 
% 0.20/0.52           (k1_tarski @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['25', '31'])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (![X1 : $i, X4 : $i]:
% 0.20/0.52         (((X4) = (X1)) | ~ (r2_hidden @ X4 @ (k1_tarski @ X1)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.52        | ((k1_funct_1 @ sk_D @ (sk_E @ sk_D @ sk_C_1 @ sk_A)) = (sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.52         (~ (v1_funct_1 @ X21)
% 0.20/0.52          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 0.20/0.52          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.20/0.52          | (r2_relset_1 @ X22 @ X23 @ X24 @ X21)
% 0.20/0.52          | ((k1_funct_1 @ X24 @ (sk_E @ X21 @ X24 @ X22))
% 0.20/0.52              != (k1_funct_1 @ X21 @ (sk_E @ X21 @ X24 @ X22)))
% 0.20/0.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.20/0.52          | ~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.20/0.52          | ~ (v1_funct_1 @ X24))),
% 0.20/0.52      inference('cnf', [status(esa)], [t18_funct_2])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k1_funct_1 @ sk_C_1 @ (sk_E @ sk_D @ sk_C_1 @ sk_A)) != (sk_B))
% 0.20/0.52          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.52          | ~ (v1_funct_1 @ sk_C_1)
% 0.20/0.52          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ X0)
% 0.20/0.52          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.20/0.52          | (r2_relset_1 @ sk_A @ X0 @ sk_C_1 @ sk_D)
% 0.20/0.52          | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.20/0.52          | ~ (v1_funct_2 @ sk_D @ sk_A @ X0)
% 0.20/0.52          | ~ (v1_funct_1 @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.52  thf('37', plain, ((v1_funct_1 @ sk_C_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('38', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k1_funct_1 @ sk_C_1 @ (sk_E @ sk_D @ sk_C_1 @ sk_A)) != (sk_B))
% 0.20/0.52          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.52          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ X0)
% 0.20/0.52          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.20/0.52          | (r2_relset_1 @ sk_A @ X0 @ sk_C_1 @ sk_D)
% 0.20/0.52          | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.20/0.52          | ~ (v1_funct_2 @ sk_D @ sk_A @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((sk_B) != (sk_B))
% 0.20/0.52          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.52          | ~ (v1_funct_2 @ sk_D @ sk_A @ X0)
% 0.20/0.52          | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.20/0.52          | (r2_relset_1 @ sk_A @ X0 @ sk_C_1 @ sk_D)
% 0.20/0.52          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.20/0.52          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ X0)
% 0.20/0.52          | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['24', '39'])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_funct_2 @ sk_C_1 @ sk_A @ X0)
% 0.20/0.52          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.20/0.52          | (r2_relset_1 @ sk_A @ X0 @ sk_C_1 @ sk_D)
% 0.20/0.52          | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.20/0.52          | ~ (v1_funct_2 @ sk_D @ sk_A @ X0)
% 0.20/0.52          | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.52        | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.52        | ~ (m1_subset_1 @ sk_D @ 
% 0.20/0.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 0.20/0.52        | (r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1 @ sk_D)
% 0.20/0.52        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '41'])).
% 0.20/0.52  thf('43', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D @ 
% 0.20/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('45', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.52        | (r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1 @ sk_D))),
% 0.20/0.52      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      (~ (r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1 @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('48', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.20/0.52      inference('clc', [status(thm)], ['46', '47'])).
% 0.20/0.52  thf('49', plain, (~ (r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_1 @ sk_D)),
% 0.20/0.52      inference('demod', [status(thm)], ['0', '48'])).
% 0.20/0.52  thf('50', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.20/0.52      inference('clc', [status(thm)], ['46', '47'])).
% 0.20/0.52  thf(t130_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.52       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.52         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         (((X12) = (k1_xboole_0))
% 0.20/0.52          | ((k2_zfmisc_1 @ (k1_tarski @ X13) @ X12) != (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t130_zfmisc_1])).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.20/0.52          | ((X0) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.52  thf(t113_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.52  thf('53', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i]:
% 0.20/0.52         (((k2_zfmisc_1 @ X10 @ X11) = (k1_xboole_0))
% 0.20/0.52          | ((X10) != (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.52  thf('54', plain,
% 0.20/0.52      (![X11 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['53'])).
% 0.20/0.52  thf('55', plain,
% 0.20/0.52      (![X0 : $i]: (((k1_xboole_0) != (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 0.20/0.52      inference('demod', [status(thm)], ['52', '54'])).
% 0.20/0.52  thf('56', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['55'])).
% 0.20/0.52  thf('57', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['55'])).
% 0.20/0.52  thf('58', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['55'])).
% 0.20/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.52  thf('59', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.52  thf(t3_subset, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.52  thf('60', plain,
% 0.20/0.52      (![X14 : $i, X16 : $i]:
% 0.20/0.52         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.52  thf('61', plain,
% 0.20/0.52      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.52  thf(redefinition_r2_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.52       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.20/0.52  thf('62', plain,
% 0.20/0.52      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.20/0.52          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.20/0.52          | (r2_relset_1 @ X18 @ X19 @ X17 @ X20)
% 0.20/0.52          | ((X17) != (X20)))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.20/0.52  thf('63', plain,
% 0.20/0.52      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.52         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 0.20/0.52          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.20/0.52      inference('simplify', [status(thm)], ['62'])).
% 0.20/0.52  thf('64', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.52      inference('sup-', [status(thm)], ['61', '63'])).
% 0.20/0.52  thf('65', plain, ($false),
% 0.20/0.52      inference('demod', [status(thm)], ['49', '56', '57', '58', '64'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
