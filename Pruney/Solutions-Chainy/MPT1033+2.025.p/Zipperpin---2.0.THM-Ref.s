%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z2DaJEiJ7g

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:07 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 168 expanded)
%              Number of leaves         :   27 (  63 expanded)
%              Depth                    :   13
%              Number of atoms          :  751 (2153 expanded)
%              Number of equality atoms :   20 (  85 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t142_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( r1_partfun1 @ C @ D )
           => ( ( ( B = k1_xboole_0 )
                & ( A != k1_xboole_0 ) )
              | ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ( r1_partfun1 @ C @ D )
             => ( ( ( B = k1_xboole_0 )
                  & ( A != k1_xboole_0 ) )
                | ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t142_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( v1_partfun1 @ X19 @ X20 )
      | ~ ( v1_funct_2 @ X19 @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X19 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('4',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B_1 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t148_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( ( v1_partfun1 @ C @ A )
              & ( v1_partfun1 @ D @ A )
              & ( r1_partfun1 @ C @ D ) )
           => ( C = D ) ) ) ) )).

thf('9',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( X25 = X22 )
      | ~ ( r1_partfun1 @ X25 @ X22 )
      | ~ ( v1_partfun1 @ X22 @ X23 )
      | ~ ( v1_partfun1 @ X25 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t148_partfun1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( X0 = sk_D )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ~ ( r1_partfun1 @ sk_C_1 @ sk_D )
    | ( sk_C_1 = sk_D )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ( sk_C_1 = sk_D )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( v1_partfun1 @ X19 @ X20 )
      | ~ ( v1_funct_2 @ X19 @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X19 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C_1 = sk_D ) ),
    inference(clc,[status(thm)],['17','23'])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X10 @ X11 ) )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('26',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('35',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['35'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('37',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('39',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_relset_1 @ X15 @ X16 @ X17 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X3 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference('sup+',[status(thm)],['33','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r2_relset_1 @ X2 @ X1 @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X10 @ X11 ) )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf('48',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('51',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( r2_hidden @ ( sk_B @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('56',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['47','56'])).

thf('58',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['46','57'])).

thf('59',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X10 @ X11 ) )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf('60',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('61',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('63',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('68',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['59','68'])).

thf('70',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['58','69'])).

thf('71',plain,(
    sk_C_1 = sk_D ),
    inference(clc,[status(thm)],['24','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['39'])).

thf('74',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    $false ),
    inference(demod,[status(thm)],['0','71','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z2DaJEiJ7g
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:14:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.50/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.50/0.73  % Solved by: fo/fo7.sh
% 0.50/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.73  % done 536 iterations in 0.274s
% 0.50/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.50/0.73  % SZS output start Refutation
% 0.50/0.73  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.50/0.73  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.50/0.73  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.50/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.50/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.50/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.50/0.73  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.50/0.73  thf(sk_B_type, type, sk_B: $i > $i).
% 0.50/0.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.50/0.73  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.50/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.73  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.50/0.73  thf(sk_D_type, type, sk_D: $i).
% 0.50/0.73  thf(t142_funct_2, conjecture,
% 0.50/0.73    (![A:$i,B:$i,C:$i]:
% 0.50/0.73     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.50/0.73         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.73       ( ![D:$i]:
% 0.50/0.73         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.50/0.73             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.73           ( ( r1_partfun1 @ C @ D ) =>
% 0.50/0.73             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.50/0.73               ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.50/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.73    (~( ![A:$i,B:$i,C:$i]:
% 0.50/0.73        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.50/0.73            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.73          ( ![D:$i]:
% 0.50/0.73            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.50/0.73                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.73              ( ( r1_partfun1 @ C @ D ) =>
% 0.50/0.73                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.50/0.73                  ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ) )),
% 0.50/0.73    inference('cnf.neg', [status(esa)], [t142_funct_2])).
% 0.50/0.73  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('1', plain,
% 0.50/0.73      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('2', plain,
% 0.50/0.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf(cc5_funct_2, axiom,
% 0.50/0.73    (![A:$i,B:$i]:
% 0.50/0.73     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.50/0.73       ( ![C:$i]:
% 0.50/0.73         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.73           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.50/0.73             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.50/0.73  thf('3', plain,
% 0.50/0.73      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.50/0.73         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.50/0.73          | (v1_partfun1 @ X19 @ X20)
% 0.50/0.73          | ~ (v1_funct_2 @ X19 @ X20 @ X21)
% 0.50/0.73          | ~ (v1_funct_1 @ X19)
% 0.50/0.73          | (v1_xboole_0 @ X21))),
% 0.50/0.73      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.50/0.73  thf('4', plain,
% 0.50/0.73      (((v1_xboole_0 @ sk_B_1)
% 0.50/0.73        | ~ (v1_funct_1 @ sk_D)
% 0.50/0.73        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B_1)
% 0.50/0.73        | (v1_partfun1 @ sk_D @ sk_A))),
% 0.50/0.73      inference('sup-', [status(thm)], ['2', '3'])).
% 0.50/0.73  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('7', plain, (((v1_xboole_0 @ sk_B_1) | (v1_partfun1 @ sk_D @ sk_A))),
% 0.50/0.73      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.50/0.73  thf('8', plain,
% 0.50/0.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf(t148_partfun1, axiom,
% 0.50/0.73    (![A:$i,B:$i,C:$i]:
% 0.50/0.73     ( ( ( v1_funct_1 @ C ) & 
% 0.50/0.73         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.73       ( ![D:$i]:
% 0.50/0.73         ( ( ( v1_funct_1 @ D ) & 
% 0.50/0.73             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.73           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 0.50/0.73               ( r1_partfun1 @ C @ D ) ) =>
% 0.50/0.73             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.50/0.73  thf('9', plain,
% 0.50/0.73      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.50/0.73         (~ (v1_funct_1 @ X22)
% 0.50/0.73          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.50/0.73          | ((X25) = (X22))
% 0.50/0.73          | ~ (r1_partfun1 @ X25 @ X22)
% 0.50/0.73          | ~ (v1_partfun1 @ X22 @ X23)
% 0.50/0.73          | ~ (v1_partfun1 @ X25 @ X23)
% 0.50/0.73          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.50/0.73          | ~ (v1_funct_1 @ X25))),
% 0.50/0.73      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.50/0.73  thf('10', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (v1_funct_1 @ X0)
% 0.50/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.50/0.73          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.50/0.73          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.50/0.73          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.50/0.73          | ((X0) = (sk_D))
% 0.50/0.73          | ~ (v1_funct_1 @ sk_D))),
% 0.50/0.73      inference('sup-', [status(thm)], ['8', '9'])).
% 0.50/0.73  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('12', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (v1_funct_1 @ X0)
% 0.50/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.50/0.73          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.50/0.73          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.50/0.73          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.50/0.73          | ((X0) = (sk_D)))),
% 0.50/0.73      inference('demod', [status(thm)], ['10', '11'])).
% 0.50/0.73  thf('13', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         ((v1_xboole_0 @ sk_B_1)
% 0.50/0.73          | ((X0) = (sk_D))
% 0.50/0.73          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.50/0.73          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.50/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.50/0.73          | ~ (v1_funct_1 @ X0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['7', '12'])).
% 0.50/0.73  thf('14', plain,
% 0.50/0.73      ((~ (v1_funct_1 @ sk_C_1)
% 0.50/0.73        | ~ (v1_partfun1 @ sk_C_1 @ sk_A)
% 0.50/0.73        | ~ (r1_partfun1 @ sk_C_1 @ sk_D)
% 0.50/0.73        | ((sk_C_1) = (sk_D))
% 0.50/0.73        | (v1_xboole_0 @ sk_B_1))),
% 0.50/0.73      inference('sup-', [status(thm)], ['1', '13'])).
% 0.50/0.73  thf('15', plain, ((v1_funct_1 @ sk_C_1)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('16', plain, ((r1_partfun1 @ sk_C_1 @ sk_D)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('17', plain,
% 0.50/0.73      ((~ (v1_partfun1 @ sk_C_1 @ sk_A)
% 0.50/0.73        | ((sk_C_1) = (sk_D))
% 0.50/0.73        | (v1_xboole_0 @ sk_B_1))),
% 0.50/0.73      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.50/0.73  thf('18', plain,
% 0.50/0.73      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('19', plain,
% 0.50/0.73      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.50/0.73         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.50/0.73          | (v1_partfun1 @ X19 @ X20)
% 0.50/0.73          | ~ (v1_funct_2 @ X19 @ X20 @ X21)
% 0.50/0.73          | ~ (v1_funct_1 @ X19)
% 0.50/0.73          | (v1_xboole_0 @ X21))),
% 0.50/0.73      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.50/0.73  thf('20', plain,
% 0.50/0.73      (((v1_xboole_0 @ sk_B_1)
% 0.50/0.73        | ~ (v1_funct_1 @ sk_C_1)
% 0.50/0.73        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 0.50/0.73        | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.50/0.73      inference('sup-', [status(thm)], ['18', '19'])).
% 0.50/0.73  thf('21', plain, ((v1_funct_1 @ sk_C_1)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('22', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('23', plain, (((v1_xboole_0 @ sk_B_1) | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.50/0.73      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.50/0.73  thf('24', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_C_1) = (sk_D)))),
% 0.50/0.73      inference('clc', [status(thm)], ['17', '23'])).
% 0.50/0.73  thf(fc3_zfmisc_1, axiom,
% 0.50/0.73    (![A:$i,B:$i]:
% 0.50/0.73     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.50/0.73  thf('25', plain,
% 0.50/0.73      (![X10 : $i, X11 : $i]:
% 0.50/0.73         ((v1_xboole_0 @ (k2_zfmisc_1 @ X10 @ X11)) | ~ (v1_xboole_0 @ X11))),
% 0.50/0.73      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.50/0.73  thf(d3_tarski, axiom,
% 0.50/0.73    (![A:$i,B:$i]:
% 0.50/0.73     ( ( r1_tarski @ A @ B ) <=>
% 0.50/0.73       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.50/0.73  thf('26', plain,
% 0.50/0.73      (![X4 : $i, X6 : $i]:
% 0.50/0.73         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.50/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.73  thf(d1_xboole_0, axiom,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.50/0.73  thf('27', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.50/0.73      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.50/0.73  thf('28', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['26', '27'])).
% 0.50/0.73  thf('29', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['26', '27'])).
% 0.50/0.73  thf(d10_xboole_0, axiom,
% 0.50/0.73    (![A:$i,B:$i]:
% 0.50/0.73     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.50/0.73  thf('30', plain,
% 0.50/0.73      (![X7 : $i, X9 : $i]:
% 0.50/0.73         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.50/0.73      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.50/0.73  thf('31', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['29', '30'])).
% 0.50/0.73  thf('32', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['28', '31'])).
% 0.50/0.73  thf('33', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.73         (~ (v1_xboole_0 @ X0)
% 0.50/0.73          | ~ (v1_xboole_0 @ X2)
% 0.50/0.73          | ((k2_zfmisc_1 @ X1 @ X0) = (X2)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['25', '32'])).
% 0.50/0.73  thf('34', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.73         (~ (v1_xboole_0 @ X0)
% 0.50/0.73          | ~ (v1_xboole_0 @ X2)
% 0.50/0.73          | ((k2_zfmisc_1 @ X1 @ X0) = (X2)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['25', '32'])).
% 0.50/0.73  thf('35', plain,
% 0.50/0.73      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 0.50/0.73      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.50/0.73  thf('36', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.50/0.73      inference('simplify', [status(thm)], ['35'])).
% 0.50/0.73  thf(t3_subset, axiom,
% 0.50/0.73    (![A:$i,B:$i]:
% 0.50/0.73     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.50/0.73  thf('37', plain,
% 0.50/0.73      (![X12 : $i, X14 : $i]:
% 0.50/0.73         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.50/0.73      inference('cnf', [status(esa)], [t3_subset])).
% 0.50/0.73  thf('38', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['36', '37'])).
% 0.50/0.73  thf(reflexivity_r2_relset_1, axiom,
% 0.50/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.73     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.50/0.73         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.73       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.50/0.73  thf('39', plain,
% 0.50/0.73      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.50/0.73         ((r2_relset_1 @ X15 @ X16 @ X17 @ X17)
% 0.50/0.73          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.50/0.73          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.50/0.73      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.50/0.73  thf('40', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.73         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.50/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.50/0.73      inference('condensation', [status(thm)], ['39'])).
% 0.50/0.73  thf('41', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         (r2_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 0.50/0.73          (k2_zfmisc_1 @ X1 @ X0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['38', '40'])).
% 0.50/0.73  thf('42', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.73         ((r2_relset_1 @ X2 @ X1 @ X0 @ (k2_zfmisc_1 @ X2 @ X1))
% 0.50/0.73          | ~ (v1_xboole_0 @ X0)
% 0.50/0.73          | ~ (v1_xboole_0 @ X1))),
% 0.50/0.73      inference('sup+', [status(thm)], ['34', '41'])).
% 0.50/0.73  thf('43', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.50/0.73         ((r2_relset_1 @ X2 @ X1 @ X3 @ X0)
% 0.50/0.73          | ~ (v1_xboole_0 @ X0)
% 0.50/0.73          | ~ (v1_xboole_0 @ X1)
% 0.50/0.73          | ~ (v1_xboole_0 @ X1)
% 0.50/0.73          | ~ (v1_xboole_0 @ X3))),
% 0.50/0.73      inference('sup+', [status(thm)], ['33', '42'])).
% 0.50/0.73  thf('44', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.50/0.73         (~ (v1_xboole_0 @ X3)
% 0.50/0.73          | ~ (v1_xboole_0 @ X1)
% 0.50/0.73          | ~ (v1_xboole_0 @ X0)
% 0.50/0.73          | (r2_relset_1 @ X2 @ X1 @ X3 @ X0))),
% 0.50/0.73      inference('simplify', [status(thm)], ['43'])).
% 0.50/0.73  thf('45', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('46', plain,
% 0.50/0.73      ((~ (v1_xboole_0 @ sk_D)
% 0.50/0.73        | ~ (v1_xboole_0 @ sk_B_1)
% 0.50/0.73        | ~ (v1_xboole_0 @ sk_C_1))),
% 0.50/0.73      inference('sup-', [status(thm)], ['44', '45'])).
% 0.50/0.73  thf('47', plain,
% 0.50/0.73      (![X10 : $i, X11 : $i]:
% 0.50/0.73         ((v1_xboole_0 @ (k2_zfmisc_1 @ X10 @ X11)) | ~ (v1_xboole_0 @ X11))),
% 0.50/0.73      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.50/0.73  thf('48', plain,
% 0.50/0.73      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.50/0.73      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.50/0.73  thf('49', plain,
% 0.50/0.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('50', plain,
% 0.50/0.73      (![X12 : $i, X13 : $i]:
% 0.50/0.73         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.50/0.73      inference('cnf', [status(esa)], [t3_subset])).
% 0.50/0.73  thf('51', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.50/0.73      inference('sup-', [status(thm)], ['49', '50'])).
% 0.50/0.73  thf('52', plain,
% 0.50/0.73      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.50/0.73         (~ (r2_hidden @ X3 @ X4)
% 0.50/0.73          | (r2_hidden @ X3 @ X5)
% 0.50/0.73          | ~ (r1_tarski @ X4 @ X5))),
% 0.50/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.73  thf('53', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.50/0.73          | ~ (r2_hidden @ X0 @ sk_D))),
% 0.50/0.73      inference('sup-', [status(thm)], ['51', '52'])).
% 0.50/0.73  thf('54', plain,
% 0.50/0.73      (((v1_xboole_0 @ sk_D)
% 0.50/0.73        | (r2_hidden @ (sk_B @ sk_D) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['48', '53'])).
% 0.50/0.73  thf('55', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.50/0.73      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.50/0.73  thf('56', plain,
% 0.50/0.73      (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['54', '55'])).
% 0.50/0.73  thf('57', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_D))),
% 0.50/0.73      inference('sup-', [status(thm)], ['47', '56'])).
% 0.50/0.73  thf('58', plain, ((~ (v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.50/0.73      inference('clc', [status(thm)], ['46', '57'])).
% 0.50/0.73  thf('59', plain,
% 0.50/0.73      (![X10 : $i, X11 : $i]:
% 0.50/0.73         ((v1_xboole_0 @ (k2_zfmisc_1 @ X10 @ X11)) | ~ (v1_xboole_0 @ X11))),
% 0.50/0.73      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.50/0.73  thf('60', plain,
% 0.50/0.73      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.50/0.73      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.50/0.73  thf('61', plain,
% 0.50/0.73      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('62', plain,
% 0.50/0.73      (![X12 : $i, X13 : $i]:
% 0.50/0.73         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.50/0.73      inference('cnf', [status(esa)], [t3_subset])).
% 0.50/0.73  thf('63', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.50/0.73      inference('sup-', [status(thm)], ['61', '62'])).
% 0.50/0.73  thf('64', plain,
% 0.50/0.73      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.50/0.73         (~ (r2_hidden @ X3 @ X4)
% 0.50/0.73          | (r2_hidden @ X3 @ X5)
% 0.50/0.73          | ~ (r1_tarski @ X4 @ X5))),
% 0.50/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.73  thf('65', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.50/0.73          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.50/0.73      inference('sup-', [status(thm)], ['63', '64'])).
% 0.50/0.73  thf('66', plain,
% 0.50/0.73      (((v1_xboole_0 @ sk_C_1)
% 0.50/0.73        | (r2_hidden @ (sk_B @ sk_C_1) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['60', '65'])).
% 0.50/0.73  thf('67', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.50/0.73      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.50/0.73  thf('68', plain,
% 0.50/0.73      (((v1_xboole_0 @ sk_C_1)
% 0.50/0.73        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['66', '67'])).
% 0.50/0.73  thf('69', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_C_1))),
% 0.50/0.73      inference('sup-', [status(thm)], ['59', '68'])).
% 0.50/0.73  thf('70', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.50/0.73      inference('clc', [status(thm)], ['58', '69'])).
% 0.50/0.73  thf('71', plain, (((sk_C_1) = (sk_D))),
% 0.50/0.73      inference('clc', [status(thm)], ['24', '70'])).
% 0.50/0.73  thf('72', plain,
% 0.50/0.73      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('73', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.73         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.50/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.50/0.73      inference('condensation', [status(thm)], ['39'])).
% 0.50/0.73  thf('74', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_C_1)),
% 0.50/0.73      inference('sup-', [status(thm)], ['72', '73'])).
% 0.50/0.73  thf('75', plain, ($false),
% 0.50/0.73      inference('demod', [status(thm)], ['0', '71', '74'])).
% 0.50/0.73  
% 0.50/0.73  % SZS output end Refutation
% 0.50/0.73  
% 0.50/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
