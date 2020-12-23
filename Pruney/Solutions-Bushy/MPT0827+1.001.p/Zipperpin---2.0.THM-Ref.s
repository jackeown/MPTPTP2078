%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0827+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7LIikInmF0

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:32 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 107 expanded)
%              Number of leaves         :   25 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :  485 (1045 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t30_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D )
       => ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) )
          & ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D )
         => ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) )
            & ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t30_relset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_C_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) )
    | ~ ( r1_tarski @ sk_C_2 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_C_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) )
   <= ~ ( r1_tarski @ sk_C_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('4',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( r1_tarski @ sk_C_2 @ ( k1_relat_1 @ sk_D_1 ) )
   <= ~ ( r1_tarski @ sk_C_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d10_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ! [C: $i,D: $i] :
            ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
          <=> ( ( r2_hidden @ C @ A )
              & ( C = D ) ) ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i,X7: $i] :
      ( ( X3
       != ( k6_relat_1 @ X4 ) )
      | ( r2_hidden @ ( k4_tarski @ X5 @ X7 ) @ X3 )
      | ( X5 != X7 )
      | ~ ( r2_hidden @ X5 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_relat_1])).

thf('8',plain,(
    ! [X4: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X4 ) )
      | ~ ( r2_hidden @ X7 @ X4 )
      | ( r2_hidden @ ( k4_tarski @ X7 @ X7 ) @ ( k6_relat_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('9',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('10',plain,(
    ! [X4: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X4 )
      | ( r2_hidden @ ( k4_tarski @ X7 @ X7 ) @ ( k6_relat_1 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X1 @ X0 ) @ ( sk_C_1 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_C_2 ) @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ ( k6_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( sk_C_1 @ X0 @ sk_C_2 ) ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X19 @ X20 ) @ X21 )
      | ( r2_hidden @ X20 @ ( k2_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('20',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X11 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X11 @ X9 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,
    ( ( r1_tarski @ sk_C_2 @ ( k2_relat_1 @ sk_D_1 ) )
    | ( r1_tarski @ sk_C_2 @ ( k2_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ sk_C_2 @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('26',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('27',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( r1_tarski @ sk_C_2 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_1 ) )
   <= ~ ( r1_tarski @ sk_C_2 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,
    ( ~ ( r1_tarski @ sk_C_2 @ ( k2_relat_1 @ sk_D_1 ) )
   <= ~ ( r1_tarski @ sk_C_2 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r1_tarski @ sk_C_2 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,
    ( ~ ( r1_tarski @ sk_C_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) )
    | ~ ( r1_tarski @ sk_C_2 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,(
    ~ ( r1_tarski @ sk_C_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( r1_tarski @ sk_C_2 @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(simpl_trail,[status(thm)],['5','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( sk_C_1 @ X0 @ sk_C_2 ) ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('35',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X19 @ X20 ) @ X21 )
      | ( r2_hidden @ X19 @ ( k1_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X11 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X11 @ X9 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('40',plain,
    ( ( r1_tarski @ sk_C_2 @ ( k1_relat_1 @ sk_D_1 ) )
    | ( r1_tarski @ sk_C_2 @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r1_tarski @ sk_C_2 @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['33','41'])).


%------------------------------------------------------------------------------
