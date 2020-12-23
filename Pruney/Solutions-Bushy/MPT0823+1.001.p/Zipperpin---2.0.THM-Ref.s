%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0823+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l5bpRtBaYa

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:32 EST 2020

% Result     : Theorem 0.92s
% Output     : Refutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 676 expanded)
%              Number of leaves         :   30 ( 204 expanded)
%              Depth                    :   23
%              Number of atoms          : 1342 (10425 expanded)
%              Number of equality atoms :   80 ( 596 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t24_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
            = ( k2_relset_1 @ A @ B @ C ) )
          & ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
            = ( k1_relset_1 @ A @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_relset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k3_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X22 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_relset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C_3 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('4',plain,(
    v1_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ C )
        = ( k4_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k3_relset_1 @ X32 @ X33 @ X31 )
        = ( k4_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('7',plain,
    ( ( k3_relset_1 @ sk_A @ sk_B @ sk_C_3 )
    = ( k4_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X15: $i] :
      ( ( X15
        = ( k2_relat_1 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X15 @ X12 ) @ ( sk_C_1 @ X15 @ X12 ) ) @ X12 )
      | ( r2_hidden @ ( sk_C_1 @ X15 @ X12 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf(d7_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( B
              = ( k4_relat_1 @ A ) )
          <=> ! [C: $i,D: $i] :
                ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i,X19: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( X17
       != ( k4_relat_1 @ X18 ) )
      | ( r2_hidden @ ( k4_tarski @ X21 @ X19 ) @ X18 )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_1])).

thf('11',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ ( k4_relat_1 @ X18 ) )
      | ( r2_hidden @ ( k4_tarski @ X21 @ X19 ) @ X18 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ ( k4_relat_1 @ X0 ) ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X1 @ ( k4_relat_1 @ X0 ) ) @ ( sk_D_2 @ X1 @ ( k4_relat_1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ ( k4_relat_1 @ sk_C_3 ) ) @ ( sk_D_2 @ X0 @ ( k4_relat_1 @ sk_C_3 ) ) ) @ sk_C_3 )
      | ( X0
        = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_3 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( k4_relat_1 @ sk_C_3 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('16',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ ( k4_relat_1 @ sk_C_3 ) ) @ ( sk_D_2 @ X0 @ ( k4_relat_1 @ sk_C_3 ) ) ) @ sk_C_3 )
      | ( X0
        = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_3 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( k4_relat_1 @ sk_C_3 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X5 )
      | ( r2_hidden @ X3 @ X6 )
      | ( X6
       != ( k1_relat_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X3 @ ( k1_relat_1 @ X5 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X5 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ ( k4_relat_1 @ sk_C_3 ) ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_3 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( k4_relat_1 @ sk_C_3 ) ) @ ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ( r2_hidden @ ( sk_C_1 @ ( k1_relat_1 @ sk_C_3 ) @ ( k4_relat_1 @ sk_C_3 ) ) @ ( k1_relat_1 @ sk_C_3 ) )
    | ( ( k1_relat_1 @ sk_C_3 )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_3 ) ) ) ),
    inference(eq_fact,[status(thm)],['20'])).

thf('22',plain,
    ( ( r2_hidden @ ( sk_C_1 @ ( k1_relat_1 @ sk_C_3 ) @ ( k4_relat_1 @ sk_C_3 ) ) @ ( k1_relat_1 @ sk_C_3 ) )
    | ( ( k1_relat_1 @ sk_C_3 )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_3 ) ) ) ),
    inference(eq_fact,[status(thm)],['20'])).

thf('23',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ ( k4_tarski @ X7 @ ( sk_D_1 @ X7 @ X5 ) ) @ X5 )
      | ( X6
       != ( k1_relat_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('24',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X7 @ ( sk_D_1 @ X7 @ X5 ) ) @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k1_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( ( k1_relat_1 @ sk_C_3 )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_3 ) ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( k1_relat_1 @ sk_C_3 ) @ ( k4_relat_1 @ sk_C_3 ) ) @ ( sk_D_1 @ ( sk_C_1 @ ( k1_relat_1 @ sk_C_3 ) @ ( k4_relat_1 @ sk_C_3 ) ) @ sk_C_3 ) ) @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('27',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( X17
       != ( k4_relat_1 @ X18 ) )
      | ( r2_hidden @ ( k4_tarski @ X19 @ X20 ) @ X17 )
      | ~ ( r2_hidden @ ( k4_tarski @ X20 @ X19 ) @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_1])).

thf('28',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( r2_hidden @ ( k4_tarski @ X20 @ X19 ) @ X18 )
      | ( r2_hidden @ ( k4_tarski @ X19 @ X20 ) @ ( k4_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k4_relat_1 @ sk_C_3 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ sk_C_3 )
      | ~ ( v1_relat_1 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k4_relat_1 @ sk_C_3 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k1_relat_1 @ sk_C_3 )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_3 ) ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_C_1 @ ( k1_relat_1 @ sk_C_3 ) @ ( k4_relat_1 @ sk_C_3 ) ) @ sk_C_3 ) @ ( sk_C_1 @ ( k1_relat_1 @ sk_C_3 ) @ ( k4_relat_1 @ sk_C_3 ) ) ) @ ( k4_relat_1 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,
    ( ( ( k1_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C_3 ) )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C_3 ) )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C_3 ) )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C_3 ) )
   <= ( ( k2_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C_3 ) )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C_3 ) ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,
    ( ( k3_relset_1 @ sk_A @ sk_B @ sk_C_3 )
    = ( k4_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('36',plain,(
    m1_subset_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C_3 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('37',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('38',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C_3 ) )
    = ( k2_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k3_relset_1 @ sk_A @ sk_B @ sk_C_3 )
    = ( k4_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('40',plain,
    ( ( k3_relset_1 @ sk_A @ sk_B @ sk_C_3 )
    = ( k4_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('41',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ ( k4_relat_1 @ sk_C_3 ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('43',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('44',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_3 )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C_3 ) )
     != ( k1_relat_1 @ sk_C_3 ) )
   <= ( ( k2_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C_3 ) )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['34','35','41','44'])).

thf('46',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('47',plain,(
    ! [X5: $i,X8: $i] :
      ( ( X8
        = ( k1_relat_1 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X8 @ X5 ) @ ( sk_D @ X8 @ X5 ) ) @ X5 )
      | ( r2_hidden @ ( sk_C @ X8 @ X5 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('48',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ ( k4_relat_1 @ X18 ) )
      | ( r2_hidden @ ( k4_tarski @ X21 @ X19 ) @ X18 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k4_relat_1 @ X0 ) ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ ( k4_relat_1 @ X0 ) ) @ ( sk_C @ X1 @ ( k4_relat_1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k4_relat_1 @ sk_C_3 ) ) @ ( sk_C @ X0 @ ( k4_relat_1 @ sk_C_3 ) ) ) @ sk_C_3 )
      | ( X0
        = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_3 ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k4_relat_1 @ sk_C_3 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k4_relat_1 @ sk_C_3 ) ) @ ( sk_C @ X0 @ ( k4_relat_1 @ sk_C_3 ) ) ) @ sk_C_3 )
      | ( X0
        = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_3 ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k4_relat_1 @ sk_C_3 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 )
      | ( r2_hidden @ X11 @ X13 )
      | ( X13
       != ( k2_relat_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('54',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ ( k2_relat_1 @ X12 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k4_relat_1 @ sk_C_3 ) ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_3 ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k4_relat_1 @ sk_C_3 ) ) @ ( k2_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,
    ( ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_C_3 ) @ ( k4_relat_1 @ sk_C_3 ) ) @ ( k2_relat_1 @ sk_C_3 ) )
    | ( ( k2_relat_1 @ sk_C_3 )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_3 ) ) ) ),
    inference(eq_fact,[status(thm)],['55'])).

thf('57',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X14 @ X12 ) @ X14 ) @ X12 )
      | ( X13
       != ( k2_relat_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('58',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X14 @ X12 ) @ X14 ) @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k2_relat_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( ( k2_relat_1 @ sk_C_3 )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_3 ) ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ ( sk_C @ ( k2_relat_1 @ sk_C_3 ) @ ( k4_relat_1 @ sk_C_3 ) ) @ sk_C_3 ) @ ( sk_C @ ( k2_relat_1 @ sk_C_3 ) @ ( k4_relat_1 @ sk_C_3 ) ) ) @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k4_relat_1 @ sk_C_3 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('61',plain,
    ( ( ( k2_relat_1 @ sk_C_3 )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_3 ) ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k2_relat_1 @ sk_C_3 ) @ ( k4_relat_1 @ sk_C_3 ) ) @ ( sk_D_3 @ ( sk_C @ ( k2_relat_1 @ sk_C_3 ) @ ( k4_relat_1 @ sk_C_3 ) ) @ sk_C_3 ) ) @ ( k4_relat_1 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X5: $i,X8: $i,X9: $i] :
      ( ( X8
        = ( k1_relat_1 @ X5 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X8 @ X5 ) @ X9 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X8 @ X5 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('63',plain,
    ( ( ( k2_relat_1 @ sk_C_3 )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_3 ) ) )
    | ~ ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_C_3 ) @ ( k4_relat_1 @ sk_C_3 ) ) @ ( k2_relat_1 @ sk_C_3 ) )
    | ( ( k2_relat_1 @ sk_C_3 )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_C_3 ) @ ( k4_relat_1 @ sk_C_3 ) ) @ ( k2_relat_1 @ sk_C_3 ) )
    | ( ( k2_relat_1 @ sk_C_3 )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_3 ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_C_3 ) @ ( k4_relat_1 @ sk_C_3 ) ) @ ( k2_relat_1 @ sk_C_3 ) )
    | ( ( k2_relat_1 @ sk_C_3 )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_3 ) ) ) ),
    inference(eq_fact,[status(thm)],['55'])).

thf('66',plain,
    ( ( k2_relat_1 @ sk_C_3 )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_3 ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k3_relset_1 @ sk_A @ sk_B @ sk_C_3 )
    = ( k4_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('68',plain,(
    m1_subset_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C_3 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('69',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('70',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C_3 ) )
    = ( k1_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( k1_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C_3 ) )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 ) )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C_3 ) )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 ) ) ),
    inference(split,[status(esa)],['33'])).

thf('72',plain,
    ( ( ( k1_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C_3 ) )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 ) )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C_3 ) )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('75',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
    = ( k2_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( k1_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C_3 ) )
     != ( k2_relat_1 @ sk_C_3 ) )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C_3 ) )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['72','75'])).

thf('77',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C_3 ) )
     != ( k2_relat_1 @ sk_C_3 ) )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C_3 ) )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['67','76'])).

thf('78',plain,
    ( ( ( k2_relat_1 @ sk_C_3 )
     != ( k2_relat_1 @ sk_C_3 ) )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C_3 ) )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['66','77'])).

thf('79',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C_3 ) )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C_3 ) )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C_3 ) )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C_3 ) )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 ) ) ),
    inference(split,[status(esa)],['33'])).

thf('81',plain,(
    ( k2_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C_3 ) )
 != ( k1_relset_1 @ sk_A @ sk_B @ sk_C_3 ) ),
    inference('sat_resolution*',[status(thm)],['79','80'])).

thf('82',plain,(
    ( k2_relat_1 @ ( k4_relat_1 @ sk_C_3 ) )
 != ( k1_relat_1 @ sk_C_3 ) ),
    inference(simpl_trail,[status(thm)],['45','81'])).

thf('83',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_C_1 @ ( k1_relat_1 @ sk_C_3 ) @ ( k4_relat_1 @ sk_C_3 ) ) @ sk_C_3 ) @ ( sk_C_1 @ ( k1_relat_1 @ sk_C_3 ) @ ( k4_relat_1 @ sk_C_3 ) ) ) @ ( k4_relat_1 @ sk_C_3 ) ),
    inference('simplify_reflect-',[status(thm)],['32','82'])).

thf('84',plain,(
    ! [X12: $i,X15: $i,X16: $i] :
      ( ( X15
        = ( k2_relat_1 @ X12 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ ( sk_C_1 @ X15 @ X12 ) ) @ X12 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X15 @ X12 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('85',plain,
    ( ~ ( r2_hidden @ ( sk_C_1 @ ( k1_relat_1 @ sk_C_3 ) @ ( k4_relat_1 @ sk_C_3 ) ) @ ( k1_relat_1 @ sk_C_3 ) )
    | ( ( k1_relat_1 @ sk_C_3 )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ( k2_relat_1 @ ( k4_relat_1 @ sk_C_3 ) )
 != ( k1_relat_1 @ sk_C_3 ) ),
    inference(simpl_trail,[status(thm)],['45','81'])).

thf('87',plain,(
    ~ ( r2_hidden @ ( sk_C_1 @ ( k1_relat_1 @ sk_C_3 ) @ ( k4_relat_1 @ sk_C_3 ) ) @ ( k1_relat_1 @ sk_C_3 ) ) ),
    inference('simplify_reflect-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['21','87'])).

thf('89',plain,(
    ( k2_relat_1 @ ( k4_relat_1 @ sk_C_3 ) )
 != ( k1_relat_1 @ sk_C_3 ) ),
    inference(simpl_trail,[status(thm)],['45','81'])).

thf('90',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['88','89'])).


%------------------------------------------------------------------------------
