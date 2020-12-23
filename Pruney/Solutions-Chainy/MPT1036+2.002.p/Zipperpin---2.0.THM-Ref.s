%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ESioYETo4M

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 527 expanded)
%              Number of leaves         :   26 ( 167 expanded)
%              Depth                    :   18
%              Number of atoms          :  922 (9662 expanded)
%              Number of equality atoms :   42 ( 309 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t146_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( r1_partfun1 @ B @ C )
          <=> ! [D: $i] :
                ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ A @ B ) )
               => ( ( k1_funct_1 @ B @ D )
                  = ( k1_funct_1 @ C @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( r1_partfun1 @ B @ C )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ A @ B ) )
                 => ( ( k1_funct_1 @ B @ D )
                    = ( k1_funct_1 @ C @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t146_funct_2])).

thf('0',plain,
    ( ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
    | ~ ( r1_partfun1 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('4',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_D @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X16: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
      | ( ( k1_funct_1 @ sk_B @ X16 )
        = ( k1_funct_1 @ sk_C_1 @ X16 ) )
      | ( r1_partfun1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_partfun1 @ sk_B @ sk_C_1 )
    | ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X16 )
          = ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('10',plain,(
    v4_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('15',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X14 @ X15 )
        = X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X14 @ X14 )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('24',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['19','20','21','24'])).

thf(t132_partfun1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( r1_partfun1 @ A @ B )
            <=> ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X12 ) @ ( k1_relat_1 @ X12 ) )
      | ( r1_partfun1 @ X12 @ X11 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_partfun1 @ X0 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('31',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_partfun1 @ X0 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28','31'])).

thf('33',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ( r1_partfun1 @ sk_B @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['13','14'])).

thf('36',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ( r1_partfun1 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('38',plain,
    ( ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X16 )
          = ( k1_funct_1 @ sk_C_1 @ X16 ) ) )
   <= ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X16 )
          = ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X0 )
          = ( k1_funct_1 @ sk_C_1 @ X0 ) ) )
   <= ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X16 )
          = ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( r1_partfun1 @ sk_B @ sk_C_1 )
      | ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_C_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_C_1 @ sk_B ) ) ) )
   <= ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X16 )
          = ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( ( k1_funct_1 @ X12 @ ( sk_C @ X11 @ X12 ) )
       != ( k1_funct_1 @ X11 @ ( sk_C @ X11 @ X12 ) ) )
      | ( r1_partfun1 @ X12 @ X11 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('42',plain,
    ( ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
       != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_C_1 @ sk_B ) ) )
      | ( r1_partfun1 @ sk_B @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( r1_partfun1 @ sk_B @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X16 )
          = ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['13','14'])).

thf('44',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['19','20','21','24'])).

thf('46',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['12','15'])).

thf('47',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('49',plain,
    ( ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
       != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_C_1 @ sk_B ) ) )
      | ( r1_partfun1 @ sk_B @ sk_C_1 )
      | ( r1_partfun1 @ sk_B @ sk_C_1 ) )
   <= ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X16 )
          = ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['42','43','44','45','46','47','48'])).

thf('50',plain,
    ( ( r1_partfun1 @ sk_B @ sk_C_1 )
   <= ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X16 )
          = ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_D )
     != ( k1_funct_1 @ sk_C_1 @ sk_D ) )
    | ~ ( r1_partfun1 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ~ ( r1_partfun1 @ sk_B @ sk_C_1 )
   <= ~ ( r1_partfun1 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['51'])).

thf('53',plain,
    ( ~ ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
          | ( ( k1_funct_1 @ sk_B @ X16 )
            = ( k1_funct_1 @ sk_C_1 @ X16 ) ) )
    | ( r1_partfun1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,
    ( ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
    | ~ ( r1_partfun1 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,(
    r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['7','53','54'])).

thf('56',plain,(
    r2_hidden @ sk_D @ ( k1_relat_1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['5','55'])).

thf('57',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['12','15'])).

thf('58',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['19','20','21','24'])).

thf('59',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( r1_partfun1 @ X12 @ X11 )
      | ( ( k1_funct_1 @ X12 @ X13 )
        = ( k1_funct_1 @ X11 @ X13 ) )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X12 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = ( k1_funct_1 @ sk_C_1 @ X1 ) )
      | ~ ( r1_partfun1 @ X0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = ( k1_funct_1 @ sk_C_1 @ X1 ) )
      | ~ ( r1_partfun1 @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r1_partfun1 @ sk_B @ sk_C_1 )
      | ( ( k1_funct_1 @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','63'])).

thf('65',plain,
    ( ( r1_partfun1 @ sk_B @ sk_C_1 )
   <= ( r1_partfun1 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('66',plain,(
    r1_partfun1 @ sk_B @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['7','53'])).

thf('67',plain,(
    r1_partfun1 @ sk_B @ sk_C_1 ),
    inference(simpl_trail,[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['13','14'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','67','68','69'])).

thf('71',plain,
    ( ( k1_funct_1 @ sk_B @ sk_D )
    = ( k1_funct_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['56','70'])).

thf('72',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_D )
     != ( k1_funct_1 @ sk_C_1 @ sk_D ) )
   <= ( ( k1_funct_1 @ sk_B @ sk_D )
     != ( k1_funct_1 @ sk_C_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['51'])).

thf('73',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_D )
     != ( k1_funct_1 @ sk_C_1 @ sk_D ) )
    | ~ ( r1_partfun1 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['51'])).

thf('74',plain,(
    ( k1_funct_1 @ sk_B @ sk_D )
 != ( k1_funct_1 @ sk_C_1 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['7','53','73'])).

thf('75',plain,(
    ( k1_funct_1 @ sk_B @ sk_D )
 != ( k1_funct_1 @ sk_C_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['72','74'])).

thf('76',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['71','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ESioYETo4M
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:52:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 63 iterations in 0.028s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.49  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.49  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(t146_funct_2, conjecture,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_funct_1 @ B ) & 
% 0.20/0.49         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.20/0.49             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.49           ( ( r1_partfun1 @ B @ C ) <=>
% 0.20/0.49             ( ![D:$i]:
% 0.20/0.49               ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ A @ B ) ) =>
% 0.20/0.49                 ( ( k1_funct_1 @ B @ D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i]:
% 0.20/0.49        ( ( ( v1_funct_1 @ B ) & 
% 0.20/0.49            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.49          ( ![C:$i]:
% 0.20/0.49            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.20/0.49                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.49              ( ( r1_partfun1 @ B @ C ) <=>
% 0.20/0.49                ( ![D:$i]:
% 0.20/0.49                  ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ A @ B ) ) =>
% 0.20/0.49                    ( ( k1_funct_1 @ B @ D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t146_funct_2])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.20/0.49        | ~ (r1_partfun1 @ sk_B @ sk_C_1))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B)))
% 0.20/0.49         <= (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.49         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.20/0.49          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.49  thf('4', plain, (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (((r2_hidden @ sk_D @ (k1_relat_1 @ sk_B)))
% 0.20/0.49         <= (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.20/0.49      inference('demod', [status(thm)], ['1', '4'])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X16 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X16 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.20/0.49          | ((k1_funct_1 @ sk_B @ X16) = (k1_funct_1 @ sk_C_1 @ X16))
% 0.20/0.49          | (r1_partfun1 @ sk_B @ sk_C_1))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (((r1_partfun1 @ sk_B @ sk_C_1)) | 
% 0.20/0.49       (![X16 : $i]:
% 0.20/0.49          (~ (r2_hidden @ X16 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.20/0.49           | ((k1_funct_1 @ sk_B @ X16) = (k1_funct_1 @ sk_C_1 @ X16))))),
% 0.20/0.49      inference('split', [status(esa)], ['6'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(cc2_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.49         ((v4_relat_1 @ X5 @ X6)
% 0.20/0.49          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.49  thf('10', plain, ((v4_relat_1 @ sk_B @ sk_A)),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf(d18_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v4_relat_1 @ X0 @ X1)
% 0.20/0.49          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.20/0.49          | ~ (v1_relat_1 @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ sk_B) | (r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(cc1_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( v1_relat_1 @ C ) ))).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.49         ((v1_relat_1 @ X2)
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.49  thf('15', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('16', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.20/0.49      inference('demod', [status(thm)], ['12', '15'])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t67_funct_2, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.49         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.49       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i]:
% 0.20/0.49         (((k1_relset_1 @ X14 @ X14 @ X15) = (X14))
% 0.20/0.49          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X14)))
% 0.20/0.49          | ~ (v1_funct_2 @ X15 @ X14 @ X14)
% 0.20/0.49          | ~ (v1_funct_1 @ X15))),
% 0.20/0.49      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      ((~ (v1_funct_1 @ sk_C_1)
% 0.20/0.49        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_A)
% 0.20/0.49        | ((k1_relset_1 @ sk_A @ sk_A @ sk_C_1) = (sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.49  thf('20', plain, ((v1_funct_1 @ sk_C_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('21', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.49         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.20/0.49          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (((k1_relset_1 @ sk_A @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.49  thf('25', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['19', '20', '21', '24'])).
% 0.20/0.49  thf(t132_partfun1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.49           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.49             ( ( r1_partfun1 @ A @ B ) <=>
% 0.20/0.49               ( ![C:$i]:
% 0.20/0.49                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 0.20/0.49                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X11 : $i, X12 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X11)
% 0.20/0.49          | ~ (v1_funct_1 @ X11)
% 0.20/0.49          | (r2_hidden @ (sk_C @ X11 @ X12) @ (k1_relat_1 @ X12))
% 0.20/0.49          | (r1_partfun1 @ X12 @ X11)
% 0.20/0.49          | ~ (r1_tarski @ (k1_relat_1 @ X12) @ (k1_relat_1 @ X11))
% 0.20/0.49          | ~ (v1_funct_1 @ X12)
% 0.20/0.49          | ~ (v1_relat_1 @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [t132_partfun1])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 0.20/0.49          | ~ (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | (r1_partfun1 @ X0 @ sk_C_1)
% 0.20/0.49          | (r2_hidden @ (sk_C @ sk_C_1 @ X0) @ (k1_relat_1 @ X0))
% 0.20/0.49          | ~ (v1_funct_1 @ sk_C_1)
% 0.20/0.49          | ~ (v1_relat_1 @ sk_C_1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.49  thf('28', plain, ((v1_funct_1 @ sk_C_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.49         ((v1_relat_1 @ X2)
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.49  thf('31', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 0.20/0.49          | ~ (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | (r1_partfun1 @ X0 @ sk_C_1)
% 0.20/0.49          | (r2_hidden @ (sk_C @ sk_C_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['27', '28', '31'])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (((r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.20/0.49        | (r1_partfun1 @ sk_B @ sk_C_1)
% 0.20/0.49        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.49        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['16', '32'])).
% 0.20/0.49  thf('34', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (((r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.20/0.49        | (r1_partfun1 @ sk_B @ sk_C_1))),
% 0.20/0.49      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      ((![X16 : $i]:
% 0.20/0.49          (~ (r2_hidden @ X16 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.20/0.49           | ((k1_funct_1 @ sk_B @ X16) = (k1_funct_1 @ sk_C_1 @ X16))))
% 0.20/0.49         <= ((![X16 : $i]:
% 0.20/0.49                (~ (r2_hidden @ X16 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.20/0.49                 | ((k1_funct_1 @ sk_B @ X16) = (k1_funct_1 @ sk_C_1 @ X16)))))),
% 0.20/0.49      inference('split', [status(esa)], ['6'])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.20/0.49           | ((k1_funct_1 @ sk_B @ X0) = (k1_funct_1 @ sk_C_1 @ X0))))
% 0.20/0.49         <= ((![X16 : $i]:
% 0.20/0.49                (~ (r2_hidden @ X16 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.20/0.49                 | ((k1_funct_1 @ sk_B @ X16) = (k1_funct_1 @ sk_C_1 @ X16)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      ((((r1_partfun1 @ sk_B @ sk_C_1)
% 0.20/0.49         | ((k1_funct_1 @ sk_B @ (sk_C @ sk_C_1 @ sk_B))
% 0.20/0.49             = (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_C_1 @ sk_B)))))
% 0.20/0.49         <= ((![X16 : $i]:
% 0.20/0.49                (~ (r2_hidden @ X16 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.20/0.49                 | ((k1_funct_1 @ sk_B @ X16) = (k1_funct_1 @ sk_C_1 @ X16)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['36', '39'])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      (![X11 : $i, X12 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X11)
% 0.20/0.49          | ~ (v1_funct_1 @ X11)
% 0.20/0.49          | ((k1_funct_1 @ X12 @ (sk_C @ X11 @ X12))
% 0.20/0.49              != (k1_funct_1 @ X11 @ (sk_C @ X11 @ X12)))
% 0.20/0.49          | (r1_partfun1 @ X12 @ X11)
% 0.20/0.49          | ~ (r1_tarski @ (k1_relat_1 @ X12) @ (k1_relat_1 @ X11))
% 0.20/0.49          | ~ (v1_funct_1 @ X12)
% 0.20/0.49          | ~ (v1_relat_1 @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [t132_partfun1])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_C_1 @ sk_B))
% 0.20/0.49           != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_C_1 @ sk_B)))
% 0.20/0.49         | (r1_partfun1 @ sk_B @ sk_C_1)
% 0.20/0.49         | ~ (v1_relat_1 @ sk_B)
% 0.20/0.49         | ~ (v1_funct_1 @ sk_B)
% 0.20/0.49         | ~ (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_C_1))
% 0.20/0.49         | (r1_partfun1 @ sk_B @ sk_C_1)
% 0.20/0.49         | ~ (v1_funct_1 @ sk_C_1)
% 0.20/0.49         | ~ (v1_relat_1 @ sk_C_1)))
% 0.20/0.49         <= ((![X16 : $i]:
% 0.20/0.49                (~ (r2_hidden @ X16 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.20/0.49                 | ((k1_funct_1 @ sk_B @ X16) = (k1_funct_1 @ sk_C_1 @ X16)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.49  thf('43', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('44', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('45', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['19', '20', '21', '24'])).
% 0.20/0.49  thf('46', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.20/0.49      inference('demod', [status(thm)], ['12', '15'])).
% 0.20/0.49  thf('47', plain, ((v1_funct_1 @ sk_C_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('48', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.49  thf('49', plain,
% 0.20/0.49      (((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_C_1 @ sk_B))
% 0.20/0.49           != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_C_1 @ sk_B)))
% 0.20/0.49         | (r1_partfun1 @ sk_B @ sk_C_1)
% 0.20/0.49         | (r1_partfun1 @ sk_B @ sk_C_1)))
% 0.20/0.49         <= ((![X16 : $i]:
% 0.20/0.49                (~ (r2_hidden @ X16 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.20/0.49                 | ((k1_funct_1 @ sk_B @ X16) = (k1_funct_1 @ sk_C_1 @ X16)))))),
% 0.20/0.49      inference('demod', [status(thm)],
% 0.20/0.49                ['42', '43', '44', '45', '46', '47', '48'])).
% 0.20/0.49  thf('50', plain,
% 0.20/0.49      (((r1_partfun1 @ sk_B @ sk_C_1))
% 0.20/0.49         <= ((![X16 : $i]:
% 0.20/0.49                (~ (r2_hidden @ X16 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.20/0.49                 | ((k1_funct_1 @ sk_B @ X16) = (k1_funct_1 @ sk_C_1 @ X16)))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['49'])).
% 0.20/0.49  thf('51', plain,
% 0.20/0.49      ((((k1_funct_1 @ sk_B @ sk_D) != (k1_funct_1 @ sk_C_1 @ sk_D))
% 0.20/0.49        | ~ (r1_partfun1 @ sk_B @ sk_C_1))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('52', plain,
% 0.20/0.49      ((~ (r1_partfun1 @ sk_B @ sk_C_1)) <= (~ ((r1_partfun1 @ sk_B @ sk_C_1)))),
% 0.20/0.49      inference('split', [status(esa)], ['51'])).
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      (~
% 0.20/0.49       (![X16 : $i]:
% 0.20/0.49          (~ (r2_hidden @ X16 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.20/0.49           | ((k1_funct_1 @ sk_B @ X16) = (k1_funct_1 @ sk_C_1 @ X16)))) | 
% 0.20/0.49       ((r1_partfun1 @ sk_B @ sk_C_1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['50', '52'])).
% 0.20/0.49  thf('54', plain,
% 0.20/0.49      (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))) | 
% 0.20/0.49       ~ ((r1_partfun1 @ sk_B @ sk_C_1))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('55', plain, (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['7', '53', '54'])).
% 0.20/0.49  thf('56', plain, ((r2_hidden @ sk_D @ (k1_relat_1 @ sk_B))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['5', '55'])).
% 0.20/0.49  thf('57', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.20/0.49      inference('demod', [status(thm)], ['12', '15'])).
% 0.20/0.49  thf('58', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['19', '20', '21', '24'])).
% 0.20/0.49  thf('59', plain,
% 0.20/0.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X11)
% 0.20/0.49          | ~ (v1_funct_1 @ X11)
% 0.20/0.49          | ~ (r1_partfun1 @ X12 @ X11)
% 0.20/0.49          | ((k1_funct_1 @ X12 @ X13) = (k1_funct_1 @ X11 @ X13))
% 0.20/0.49          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X12))
% 0.20/0.49          | ~ (r1_tarski @ (k1_relat_1 @ X12) @ (k1_relat_1 @ X11))
% 0.20/0.49          | ~ (v1_funct_1 @ X12)
% 0.20/0.49          | ~ (v1_relat_1 @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [t132_partfun1])).
% 0.20/0.49  thf('60', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 0.20/0.49          | ~ (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.20/0.49          | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_C_1 @ X1))
% 0.20/0.49          | ~ (r1_partfun1 @ X0 @ sk_C_1)
% 0.20/0.49          | ~ (v1_funct_1 @ sk_C_1)
% 0.20/0.49          | ~ (v1_relat_1 @ sk_C_1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.49  thf('61', plain, ((v1_funct_1 @ sk_C_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('62', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.49  thf('63', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 0.20/0.49          | ~ (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.20/0.49          | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_C_1 @ X1))
% 0.20/0.49          | ~ (r1_partfun1 @ X0 @ sk_C_1))),
% 0.20/0.49      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.20/0.49  thf('64', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r1_partfun1 @ sk_B @ sk_C_1)
% 0.20/0.49          | ((k1_funct_1 @ sk_B @ X0) = (k1_funct_1 @ sk_C_1 @ X0))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.20/0.49          | ~ (v1_funct_1 @ sk_B)
% 0.20/0.49          | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['57', '63'])).
% 0.20/0.49  thf('65', plain,
% 0.20/0.49      (((r1_partfun1 @ sk_B @ sk_C_1)) <= (((r1_partfun1 @ sk_B @ sk_C_1)))),
% 0.20/0.49      inference('split', [status(esa)], ['6'])).
% 0.20/0.49  thf('66', plain, (((r1_partfun1 @ sk_B @ sk_C_1))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['7', '53'])).
% 0.20/0.49  thf('67', plain, ((r1_partfun1 @ sk_B @ sk_C_1)),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['65', '66'])).
% 0.20/0.49  thf('68', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('69', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('70', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_funct_1 @ sk_B @ X0) = (k1_funct_1 @ sk_C_1 @ X0))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)))),
% 0.20/0.49      inference('demod', [status(thm)], ['64', '67', '68', '69'])).
% 0.20/0.49  thf('71', plain,
% 0.20/0.49      (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C_1 @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['56', '70'])).
% 0.20/0.49  thf('72', plain,
% 0.20/0.49      ((((k1_funct_1 @ sk_B @ sk_D) != (k1_funct_1 @ sk_C_1 @ sk_D)))
% 0.20/0.49         <= (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C_1 @ sk_D))))),
% 0.20/0.49      inference('split', [status(esa)], ['51'])).
% 0.20/0.49  thf('73', plain,
% 0.20/0.49      (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C_1 @ sk_D))) | 
% 0.20/0.49       ~ ((r1_partfun1 @ sk_B @ sk_C_1))),
% 0.20/0.49      inference('split', [status(esa)], ['51'])).
% 0.20/0.49  thf('74', plain,
% 0.20/0.49      (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C_1 @ sk_D)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['7', '53', '73'])).
% 0.20/0.49  thf('75', plain,
% 0.20/0.49      (((k1_funct_1 @ sk_B @ sk_D) != (k1_funct_1 @ sk_C_1 @ sk_D))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['72', '74'])).
% 0.20/0.49  thf('76', plain, ($false),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['71', '75'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
