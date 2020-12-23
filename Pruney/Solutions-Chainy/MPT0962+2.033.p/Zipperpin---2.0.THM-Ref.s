%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.U44kyY2GdW

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:53 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 622 expanded)
%              Number of leaves         :   37 ( 182 expanded)
%              Depth                    :   21
%              Number of atoms          :  950 (7301 expanded)
%              Number of equality atoms :   43 ( 148 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X23 ) @ X24 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ X25 )
      | ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('24',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X28
       != ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
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

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('33',plain,(
    ! [X34: $i] :
      ( ( v1_funct_2 @ X34 @ ( k1_relat_1 @ X34 ) @ ( k2_relat_1 @ X34 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('34',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('35',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','31'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( k2_relat_1 @ sk_B ) @ X0 ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( zip_tseitin_1 @ sk_B @ ( k2_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    zip_tseitin_1 @ sk_B @ ( k2_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('50',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X28
       != ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('60',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( sk_A
      = ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','30'])).

thf('62',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','30'])).

thf('63',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ sk_B ) )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('64',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('65',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X10 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('66',plain,(
    ! [X9: $i] :
      ( ( k2_subset_1 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('67',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf(t43_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ C )
          <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('68',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_xboole_0 @ X15 @ X13 )
      | ( r1_tarski @ X15 @ ( k3_subset_1 @ X14 @ X13 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k3_subset_1 @ X0 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('71',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('75',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('76',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','30'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ ( k3_subset_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','79'])).

thf(t39_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
      <=> ( B
          = ( k2_subset_1 @ A ) ) ) ) )).

thf('81',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X12
       != ( k2_subset_1 @ X11 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X11 @ X12 ) @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t39_subset_1])).

thf('82',plain,(
    ! [X11: $i] :
      ( ~ ( m1_subset_1 @ ( k2_subset_1 @ X11 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X11 @ ( k2_subset_1 @ X11 ) ) @ ( k2_subset_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X9: $i] :
      ( ( k2_subset_1 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('84',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('85',plain,(
    ! [X9: $i] :
      ( ( k2_subset_1 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('86',plain,(
    ! [X9: $i] :
      ( ( k2_subset_1 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('87',plain,(
    ! [X11: $i] :
      ( r1_tarski @ ( k3_subset_1 @ X11 @ X11 ) @ X11 ) ),
    inference(demod,[status(thm)],['82','83','84','85','86'])).

thf('88',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      | ( X0
        = ( k3_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k3_subset_1 @ ( k2_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['80','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('92',plain,(
    r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['63','92'])).

thf('94',plain,(
    v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['57','93'])).

thf('95',plain,(
    $false ),
    inference(demod,[status(thm)],['32','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.U44kyY2GdW
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:06:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.39/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.61  % Solved by: fo/fo7.sh
% 0.39/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.61  % done 192 iterations in 0.164s
% 0.39/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.61  % SZS output start Refutation
% 0.39/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.61  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.39/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.39/0.61  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.39/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.61  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.39/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.39/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.61  thf(t4_funct_2, conjecture,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.61       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.39/0.61         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.39/0.61           ( m1_subset_1 @
% 0.39/0.61             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.39/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.61    (~( ![A:$i,B:$i]:
% 0.39/0.61        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.61          ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.39/0.61            ( ( v1_funct_1 @ B ) & 
% 0.39/0.61              ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.39/0.61              ( m1_subset_1 @
% 0.39/0.61                B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )),
% 0.39/0.61    inference('cnf.neg', [status(esa)], [t4_funct_2])).
% 0.39/0.61  thf('0', plain,
% 0.39/0.61      ((~ (v1_funct_1 @ sk_B)
% 0.39/0.61        | ~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.39/0.61        | ~ (m1_subset_1 @ sk_B @ 
% 0.39/0.61             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('1', plain,
% 0.39/0.61      ((~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.39/0.61         <= (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.39/0.61      inference('split', [status(esa)], ['0'])).
% 0.39/0.61  thf('2', plain, ((v1_funct_1 @ sk_B)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('3', plain, ((~ (v1_funct_1 @ sk_B)) <= (~ ((v1_funct_1 @ sk_B)))),
% 0.39/0.61      inference('split', [status(esa)], ['0'])).
% 0.39/0.61  thf('4', plain, (((v1_funct_1 @ sk_B))),
% 0.39/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.61  thf('5', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf(d10_xboole_0, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.61  thf('6', plain,
% 0.39/0.61      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.39/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.61  thf('7', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.39/0.61      inference('simplify', [status(thm)], ['6'])).
% 0.39/0.61  thf(t11_relset_1, axiom,
% 0.39/0.61    (![A:$i,B:$i,C:$i]:
% 0.39/0.61     ( ( v1_relat_1 @ C ) =>
% 0.39/0.61       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.39/0.61           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.39/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.39/0.61  thf('8', plain,
% 0.39/0.61      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.39/0.61         (~ (r1_tarski @ (k1_relat_1 @ X23) @ X24)
% 0.39/0.61          | ~ (r1_tarski @ (k2_relat_1 @ X23) @ X25)
% 0.39/0.61          | (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.39/0.61          | ~ (v1_relat_1 @ X23))),
% 0.39/0.61      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.39/0.61  thf('9', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (~ (v1_relat_1 @ X0)
% 0.39/0.61          | (m1_subset_1 @ X0 @ 
% 0.39/0.61             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.39/0.61          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.39/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.39/0.61  thf('10', plain,
% 0.39/0.61      (((m1_subset_1 @ sk_B @ 
% 0.39/0.61         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.39/0.61        | ~ (v1_relat_1 @ sk_B))),
% 0.39/0.61      inference('sup-', [status(thm)], ['5', '9'])).
% 0.39/0.61  thf('11', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('12', plain,
% 0.39/0.61      ((m1_subset_1 @ sk_B @ 
% 0.39/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.39/0.61      inference('demod', [status(thm)], ['10', '11'])).
% 0.39/0.61  thf('13', plain,
% 0.39/0.61      ((~ (m1_subset_1 @ sk_B @ 
% 0.39/0.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))
% 0.39/0.61         <= (~
% 0.39/0.61             ((m1_subset_1 @ sk_B @ 
% 0.39/0.61               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))))),
% 0.39/0.61      inference('split', [status(esa)], ['0'])).
% 0.39/0.61  thf('14', plain,
% 0.39/0.61      (((m1_subset_1 @ sk_B @ 
% 0.39/0.61         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 0.39/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.39/0.61  thf('15', plain,
% 0.39/0.61      (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.39/0.61       ~
% 0.39/0.61       ((m1_subset_1 @ sk_B @ 
% 0.39/0.61         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))) | 
% 0.39/0.61       ~ ((v1_funct_1 @ sk_B))),
% 0.39/0.61      inference('split', [status(esa)], ['0'])).
% 0.39/0.61  thf('16', plain, (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.39/0.61      inference('sat_resolution*', [status(thm)], ['4', '14', '15'])).
% 0.39/0.61  thf('17', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.39/0.61      inference('simpl_trail', [status(thm)], ['1', '16'])).
% 0.39/0.61  thf(d1_funct_2, axiom,
% 0.39/0.61    (![A:$i,B:$i,C:$i]:
% 0.39/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.61       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.61           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.39/0.61             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.39/0.61         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.61           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.39/0.61             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.39/0.61  thf(zf_stmt_1, axiom,
% 0.39/0.61    (![B:$i,A:$i]:
% 0.39/0.61     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.61       ( zip_tseitin_0 @ B @ A ) ))).
% 0.39/0.61  thf('18', plain,
% 0.39/0.61      (![X26 : $i, X27 : $i]:
% 0.39/0.61         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.61  thf('19', plain,
% 0.39/0.61      ((m1_subset_1 @ sk_B @ 
% 0.39/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.39/0.61      inference('demod', [status(thm)], ['10', '11'])).
% 0.39/0.61  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.39/0.61  thf(zf_stmt_3, axiom,
% 0.39/0.61    (![C:$i,B:$i,A:$i]:
% 0.39/0.61     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.39/0.61       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.39/0.61  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.39/0.61  thf(zf_stmt_5, axiom,
% 0.39/0.61    (![A:$i,B:$i,C:$i]:
% 0.39/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.61       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.39/0.61         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.61           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.39/0.61             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.39/0.61  thf('20', plain,
% 0.39/0.61      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.39/0.61         (~ (zip_tseitin_0 @ X31 @ X32)
% 0.39/0.61          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 0.39/0.61          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.39/0.61  thf('21', plain,
% 0.39/0.61      (((zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 0.39/0.61        | ~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['19', '20'])).
% 0.39/0.61  thf('22', plain,
% 0.39/0.61      ((m1_subset_1 @ sk_B @ 
% 0.39/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.39/0.61      inference('demod', [status(thm)], ['10', '11'])).
% 0.39/0.61  thf(redefinition_k1_relset_1, axiom,
% 0.39/0.61    (![A:$i,B:$i,C:$i]:
% 0.39/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.39/0.61  thf('23', plain,
% 0.39/0.61      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.39/0.61         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.39/0.61          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.39/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.39/0.61  thf('24', plain,
% 0.39/0.61      (((k1_relset_1 @ (k1_relat_1 @ sk_B) @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.39/0.61      inference('sup-', [status(thm)], ['22', '23'])).
% 0.39/0.61  thf('25', plain,
% 0.39/0.61      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.39/0.61         (((X28) != (k1_relset_1 @ X28 @ X29 @ X30))
% 0.39/0.61          | (v1_funct_2 @ X30 @ X28 @ X29)
% 0.39/0.61          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.61  thf('26', plain,
% 0.39/0.61      ((((k1_relat_1 @ sk_B) != (k1_relat_1 @ sk_B))
% 0.39/0.61        | ~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 0.39/0.61        | (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.39/0.61      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.61  thf('27', plain,
% 0.39/0.61      (((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.39/0.61        | ~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.39/0.61      inference('simplify', [status(thm)], ['26'])).
% 0.39/0.61  thf('28', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.39/0.61      inference('simpl_trail', [status(thm)], ['1', '16'])).
% 0.39/0.61  thf('29', plain, (~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.39/0.61      inference('clc', [status(thm)], ['27', '28'])).
% 0.39/0.61  thf('30', plain, (~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.39/0.61      inference('clc', [status(thm)], ['21', '29'])).
% 0.39/0.61  thf('31', plain, (((sk_A) = (k1_xboole_0))),
% 0.39/0.61      inference('sup-', [status(thm)], ['18', '30'])).
% 0.39/0.61  thf('32', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ k1_xboole_0)),
% 0.39/0.61      inference('demod', [status(thm)], ['17', '31'])).
% 0.39/0.61  thf(t3_funct_2, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.61       ( ( v1_funct_1 @ A ) & 
% 0.39/0.61         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.39/0.61         ( m1_subset_1 @
% 0.39/0.61           A @ 
% 0.39/0.61           ( k1_zfmisc_1 @
% 0.39/0.61             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.39/0.61  thf('33', plain,
% 0.39/0.61      (![X34 : $i]:
% 0.39/0.61         ((v1_funct_2 @ X34 @ (k1_relat_1 @ X34) @ (k2_relat_1 @ X34))
% 0.39/0.61          | ~ (v1_funct_1 @ X34)
% 0.39/0.61          | ~ (v1_relat_1 @ X34))),
% 0.39/0.61      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.39/0.61  thf('34', plain,
% 0.39/0.61      (![X26 : $i, X27 : $i]:
% 0.39/0.61         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.62  thf('35', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ k1_xboole_0)),
% 0.39/0.62      inference('demod', [status(thm)], ['17', '31'])).
% 0.39/0.62  thf('36', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ X0)
% 0.39/0.62          | (zip_tseitin_0 @ X0 @ X1))),
% 0.39/0.62      inference('sup-', [status(thm)], ['34', '35'])).
% 0.39/0.62  thf('37', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ sk_B)
% 0.39/0.62          | ~ (v1_funct_1 @ sk_B)
% 0.39/0.62          | (zip_tseitin_0 @ (k2_relat_1 @ sk_B) @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['33', '36'])).
% 0.39/0.62  thf('38', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('39', plain, ((v1_funct_1 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('40', plain, (![X0 : $i]: (zip_tseitin_0 @ (k2_relat_1 @ sk_B) @ X0)),
% 0.39/0.62      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.39/0.62  thf('41', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.39/0.62      inference('simplify', [status(thm)], ['6'])).
% 0.39/0.62  thf('42', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ X0)
% 0.39/0.62          | (m1_subset_1 @ X0 @ 
% 0.39/0.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.39/0.62          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.39/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.39/0.62  thf('43', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((m1_subset_1 @ X0 @ 
% 0.39/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.39/0.62          | ~ (v1_relat_1 @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['41', '42'])).
% 0.39/0.62  thf('44', plain,
% 0.39/0.62      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.39/0.62         (~ (zip_tseitin_0 @ X31 @ X32)
% 0.39/0.62          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 0.39/0.62          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.39/0.62  thf('45', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ X0)
% 0.39/0.62          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.39/0.62          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['43', '44'])).
% 0.39/0.62  thf('46', plain,
% 0.39/0.62      (((zip_tseitin_1 @ sk_B @ (k2_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.39/0.62        | ~ (v1_relat_1 @ sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['40', '45'])).
% 0.39/0.62  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('48', plain,
% 0.39/0.62      ((zip_tseitin_1 @ sk_B @ (k2_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['46', '47'])).
% 0.39/0.62  thf('49', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((m1_subset_1 @ X0 @ 
% 0.39/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.39/0.62          | ~ (v1_relat_1 @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['41', '42'])).
% 0.39/0.62  thf('50', plain,
% 0.39/0.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.39/0.62         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.39/0.62          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.39/0.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.39/0.62  thf('51', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ X0)
% 0.39/0.62          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.39/0.62              = (k1_relat_1 @ X0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['49', '50'])).
% 0.39/0.62  thf('52', plain,
% 0.39/0.62      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.39/0.62         (((X28) != (k1_relset_1 @ X28 @ X29 @ X30))
% 0.39/0.62          | (v1_funct_2 @ X30 @ X28 @ X29)
% 0.39/0.62          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.62  thf('53', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.39/0.62          | ~ (v1_relat_1 @ X0)
% 0.39/0.62          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.39/0.62          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['51', '52'])).
% 0.39/0.62  thf('54', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.39/0.62          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.39/0.62          | ~ (v1_relat_1 @ X0))),
% 0.39/0.62      inference('simplify', [status(thm)], ['53'])).
% 0.39/0.62  thf('55', plain,
% 0.39/0.62      ((~ (v1_relat_1 @ sk_B)
% 0.39/0.62        | (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ (k2_relat_1 @ sk_B)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['48', '54'])).
% 0.39/0.62  thf('56', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('57', plain,
% 0.39/0.62      ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ (k2_relat_1 @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['55', '56'])).
% 0.39/0.62  thf('58', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('59', plain,
% 0.39/0.62      (![X2 : $i, X4 : $i]:
% 0.39/0.62         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.39/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.62  thf('60', plain,
% 0.39/0.62      ((~ (r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))
% 0.39/0.62        | ((sk_A) = (k2_relat_1 @ sk_B)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['58', '59'])).
% 0.39/0.62  thf('61', plain, (((sk_A) = (k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['18', '30'])).
% 0.39/0.62  thf('62', plain, (((sk_A) = (k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['18', '30'])).
% 0.39/0.62  thf('63', plain,
% 0.39/0.62      ((~ (r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ sk_B))
% 0.39/0.62        | ((k1_xboole_0) = (k2_relat_1 @ sk_B)))),
% 0.39/0.62      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.39/0.62  thf(t4_subset_1, axiom,
% 0.39/0.62    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.39/0.62  thf('64', plain,
% 0.39/0.62      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.39/0.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.39/0.62  thf(dt_k2_subset_1, axiom,
% 0.39/0.62    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.39/0.62  thf('65', plain,
% 0.39/0.62      (![X10 : $i]: (m1_subset_1 @ (k2_subset_1 @ X10) @ (k1_zfmisc_1 @ X10))),
% 0.39/0.62      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.39/0.62  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.39/0.62  thf('66', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 0.39/0.62      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.39/0.62  thf('67', plain, (![X10 : $i]: (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X10))),
% 0.39/0.62      inference('demod', [status(thm)], ['65', '66'])).
% 0.39/0.62  thf(t43_subset_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.62       ( ![C:$i]:
% 0.39/0.62         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.62           ( ( r1_xboole_0 @ B @ C ) <=>
% 0.39/0.62             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.39/0.62  thf('68', plain,
% 0.39/0.62      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.39/0.62         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.39/0.62          | ~ (r1_xboole_0 @ X15 @ X13)
% 0.39/0.62          | (r1_tarski @ X15 @ (k3_subset_1 @ X14 @ X13))
% 0.39/0.62          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t43_subset_1])).
% 0.39/0.62  thf('69', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.39/0.62          | (r1_tarski @ X1 @ (k3_subset_1 @ X0 @ X0))
% 0.39/0.62          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['67', '68'])).
% 0.39/0.62  thf('70', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.39/0.62          | (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ X0 @ X0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['64', '69'])).
% 0.39/0.62  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.39/0.62  thf('71', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.39/0.62      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.39/0.62  thf(symmetry_r1_xboole_0, axiom,
% 0.39/0.62    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.39/0.62  thf('72', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.39/0.62      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.39/0.62  thf('73', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.39/0.62      inference('sup-', [status(thm)], ['71', '72'])).
% 0.39/0.62  thf('74', plain,
% 0.39/0.62      (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ X0 @ X0))),
% 0.39/0.62      inference('demod', [status(thm)], ['70', '73'])).
% 0.39/0.62  thf('75', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(t1_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.39/0.62       ( r1_tarski @ A @ C ) ))).
% 0.39/0.62  thf('76', plain,
% 0.39/0.62      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.39/0.62         (~ (r1_tarski @ X5 @ X6)
% 0.39/0.62          | ~ (r1_tarski @ X6 @ X7)
% 0.39/0.62          | (r1_tarski @ X5 @ X7))),
% 0.39/0.62      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.39/0.62  thf('77', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((r1_tarski @ (k2_relat_1 @ sk_B) @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['75', '76'])).
% 0.39/0.62  thf('78', plain, (((sk_A) = (k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['18', '30'])).
% 0.39/0.62  thf('79', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((r1_tarski @ (k2_relat_1 @ sk_B) @ X0)
% 0.39/0.62          | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.39/0.62      inference('demod', [status(thm)], ['77', '78'])).
% 0.39/0.62  thf('80', plain,
% 0.39/0.62      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ sk_B) @ (k3_subset_1 @ X0 @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['74', '79'])).
% 0.39/0.62  thf(t39_subset_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.62       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.39/0.62         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.39/0.62  thf('81', plain,
% 0.39/0.62      (![X11 : $i, X12 : $i]:
% 0.39/0.62         (((X12) != (k2_subset_1 @ X11))
% 0.39/0.62          | (r1_tarski @ (k3_subset_1 @ X11 @ X12) @ X12)
% 0.39/0.62          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t39_subset_1])).
% 0.39/0.62  thf('82', plain,
% 0.39/0.62      (![X11 : $i]:
% 0.39/0.62         (~ (m1_subset_1 @ (k2_subset_1 @ X11) @ (k1_zfmisc_1 @ X11))
% 0.39/0.62          | (r1_tarski @ (k3_subset_1 @ X11 @ (k2_subset_1 @ X11)) @ 
% 0.39/0.62             (k2_subset_1 @ X11)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['81'])).
% 0.39/0.62  thf('83', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 0.39/0.62      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.39/0.62  thf('84', plain, (![X10 : $i]: (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X10))),
% 0.39/0.62      inference('demod', [status(thm)], ['65', '66'])).
% 0.39/0.62  thf('85', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 0.39/0.62      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.39/0.62  thf('86', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 0.39/0.62      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.39/0.62  thf('87', plain,
% 0.39/0.62      (![X11 : $i]: (r1_tarski @ (k3_subset_1 @ X11 @ X11) @ X11)),
% 0.39/0.62      inference('demod', [status(thm)], ['82', '83', '84', '85', '86'])).
% 0.39/0.62  thf('88', plain,
% 0.39/0.62      (![X2 : $i, X4 : $i]:
% 0.39/0.62         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.39/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.62  thf('89', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (r1_tarski @ X0 @ (k3_subset_1 @ X0 @ X0))
% 0.39/0.62          | ((X0) = (k3_subset_1 @ X0 @ X0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['87', '88'])).
% 0.39/0.62  thf('90', plain,
% 0.39/0.62      (((k2_relat_1 @ sk_B)
% 0.39/0.62         = (k3_subset_1 @ (k2_relat_1 @ sk_B) @ (k2_relat_1 @ sk_B)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['80', '89'])).
% 0.39/0.62  thf('91', plain,
% 0.39/0.62      (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ X0 @ X0))),
% 0.39/0.62      inference('demod', [status(thm)], ['70', '73'])).
% 0.39/0.62  thf('92', plain, ((r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ sk_B))),
% 0.39/0.62      inference('sup+', [status(thm)], ['90', '91'])).
% 0.39/0.62  thf('93', plain, (((k1_xboole_0) = (k2_relat_1 @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['63', '92'])).
% 0.39/0.62  thf('94', plain, ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ k1_xboole_0)),
% 0.39/0.62      inference('demod', [status(thm)], ['57', '93'])).
% 0.39/0.62  thf('95', plain, ($false), inference('demod', [status(thm)], ['32', '94'])).
% 0.39/0.62  
% 0.39/0.62  % SZS output end Refutation
% 0.39/0.62  
% 0.39/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
