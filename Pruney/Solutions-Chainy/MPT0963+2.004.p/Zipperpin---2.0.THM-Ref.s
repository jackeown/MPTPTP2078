%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rLxgCjcdQG

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 211 expanded)
%              Number of leaves         :   22 (  70 expanded)
%              Depth                    :   17
%              Number of atoms          :  665 (3500 expanded)
%              Number of equality atoms :   34 ( 150 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t5_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( ( k1_relat_1 @ C )
            = A )
          & ! [D: $i] :
              ( ( r2_hidden @ D @ A )
             => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( ( k1_relat_1 @ C )
              = A )
            & ! [D: $i] :
                ( ( r2_hidden @ D @ A )
               => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) )
         => ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ B )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t5_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d13_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k10_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
                & ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X2 @ X3 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X2 @ X3 ) @ ( k1_relat_1 @ X3 ) )
      | ( X1
        = ( k10_relat_1 @ X3 @ X2 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ X0 ) @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_A @ X0 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
      | ( ( k1_relat_1 @ sk_C )
        = ( k10_relat_1 @ sk_C @ X0 ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_A @ X0 @ sk_C ) @ sk_A )
      | ( sk_A
        = ( k10_relat_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6','7','8','9'])).

thf('11',plain,(
    ! [X11: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X11 ) @ sk_B )
      | ~ ( r2_hidden @ X11 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k10_relat_1 @ sk_C @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_D @ sk_A @ X0 @ sk_C ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ X0 ) @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['3'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ X0 ) @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['3'])).

thf('16',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X1 @ X2 @ X3 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X2 @ X3 ) @ ( k1_relat_1 @ X3 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X3 @ ( sk_D @ X1 @ X2 @ X3 ) ) @ X2 )
      | ( X1
        = ( k10_relat_1 @ X3 @ X2 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D @ ( k1_relat_1 @ X0 ) @ X1 @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ X0 ) @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ X0 ) @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D @ ( k1_relat_1 @ X0 ) @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D @ ( k1_relat_1 @ X0 ) @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D @ ( k1_relat_1 @ X0 ) @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_D @ sk_A @ X0 @ sk_C ) ) @ X0 )
      | ( ( k1_relat_1 @ sk_C )
        = ( k10_relat_1 @ sk_C @ X0 ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf('22',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_D @ sk_A @ X0 @ sk_C ) ) @ X0 )
      | ( sk_A
        = ( k10_relat_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23','24'])).

thf('26',plain,
    ( ( sk_A
      = ( k10_relat_1 @ sk_C @ sk_B ) )
    | ( sk_A
      = ( k10_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','25'])).

thf('27',plain,
    ( sk_A
    = ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X7 @ ( k10_relat_1 @ X7 @ X8 ) ) @ X8 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('29',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('32',plain,
    ( ( ( k9_relat_1 @ sk_C @ sk_A )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['29','34','35','36'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('38',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X9 ) @ X10 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,
    ( $false
   <= ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['1','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( v1_funct_1 @ sk_C )
   <= ~ ( v1_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['29','34','35','36'])).

thf('49',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ( v1_funct_2 @ X9 @ ( k1_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('50',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,
    ( ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
   <= ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,(
    ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['47','56','57'])).

thf('59',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['44','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rLxgCjcdQG
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:00:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 63 iterations in 0.052s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.51  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(t5_funct_2, conjecture,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.51       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.20/0.51           ( ![D:$i]:
% 0.20/0.51             ( ( r2_hidden @ D @ A ) =>
% 0.20/0.51               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) ) =>
% 0.20/0.51         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.51           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.51        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.51          ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.20/0.51              ( ![D:$i]:
% 0.20/0.51                ( ( r2_hidden @ D @ A ) =>
% 0.20/0.51                  ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) ) =>
% 0.20/0.51            ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.51              ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t5_funct_2])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      ((~ (v1_funct_1 @ sk_C)
% 0.20/0.51        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.20/0.51        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      ((~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))
% 0.20/0.51         <= (~
% 0.20/0.51             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('2', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(d13_funct_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.51       ( ![B:$i,C:$i]:
% 0.20/0.51         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 0.20/0.51           ( ![D:$i]:
% 0.20/0.51             ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.51               ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.51                 ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ B ) ) ) ) ) ) ))).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         ((r2_hidden @ (sk_D @ X1 @ X2 @ X3) @ X1)
% 0.20/0.51          | (r2_hidden @ (sk_D @ X1 @ X2 @ X3) @ (k1_relat_1 @ X3))
% 0.20/0.51          | ((X1) = (k10_relat_1 @ X3 @ X2))
% 0.20/0.51          | ~ (v1_funct_1 @ X3)
% 0.20/0.51          | ~ (v1_relat_1 @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [d13_funct_1])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X0)
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1))
% 0.20/0.51          | (r2_hidden @ (sk_D @ (k1_relat_1 @ X0) @ X1 @ X0) @ 
% 0.20/0.51             (k1_relat_1 @ X0)))),
% 0.20/0.51      inference('eq_fact', [status(thm)], ['3'])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ (sk_D @ sk_A @ X0 @ sk_C) @ (k1_relat_1 @ sk_C))
% 0.20/0.51          | ((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ X0))
% 0.20/0.51          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.51          | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.51      inference('sup+', [status(thm)], ['2', '4'])).
% 0.20/0.51  thf('6', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('7', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('9', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ (sk_D @ sk_A @ X0 @ sk_C) @ sk_A)
% 0.20/0.51          | ((sk_A) = (k10_relat_1 @ sk_C @ X0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['5', '6', '7', '8', '9'])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X11 : $i]:
% 0.20/0.51         ((r2_hidden @ (k1_funct_1 @ sk_C @ X11) @ sk_B)
% 0.20/0.51          | ~ (r2_hidden @ X11 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((sk_A) = (k10_relat_1 @ sk_C @ X0))
% 0.20/0.51          | (r2_hidden @ (k1_funct_1 @ sk_C @ (sk_D @ sk_A @ X0 @ sk_C)) @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf('13', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X0)
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1))
% 0.20/0.51          | (r2_hidden @ (sk_D @ (k1_relat_1 @ X0) @ X1 @ X0) @ 
% 0.20/0.51             (k1_relat_1 @ X0)))),
% 0.20/0.51      inference('eq_fact', [status(thm)], ['3'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X0)
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1))
% 0.20/0.51          | (r2_hidden @ (sk_D @ (k1_relat_1 @ X0) @ X1 @ X0) @ 
% 0.20/0.51             (k1_relat_1 @ X0)))),
% 0.20/0.51      inference('eq_fact', [status(thm)], ['3'])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         (~ (r2_hidden @ (sk_D @ X1 @ X2 @ X3) @ X1)
% 0.20/0.51          | ~ (r2_hidden @ (sk_D @ X1 @ X2 @ X3) @ (k1_relat_1 @ X3))
% 0.20/0.51          | ~ (r2_hidden @ (k1_funct_1 @ X3 @ (sk_D @ X1 @ X2 @ X3)) @ X2)
% 0.20/0.51          | ((X1) = (k10_relat_1 @ X3 @ X2))
% 0.20/0.51          | ~ (v1_funct_1 @ X3)
% 0.20/0.51          | ~ (v1_relat_1 @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [d13_funct_1])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1))
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | ~ (v1_relat_1 @ X0)
% 0.20/0.51          | ~ (v1_relat_1 @ X0)
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1))
% 0.20/0.51          | ~ (r2_hidden @ 
% 0.20/0.51               (k1_funct_1 @ X0 @ (sk_D @ (k1_relat_1 @ X0) @ X1 @ X0)) @ X1)
% 0.20/0.51          | ~ (r2_hidden @ (sk_D @ (k1_relat_1 @ X0) @ X1 @ X0) @ 
% 0.20/0.51               (k1_relat_1 @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r2_hidden @ (sk_D @ (k1_relat_1 @ X0) @ X1 @ X0) @ 
% 0.20/0.51             (k1_relat_1 @ X0))
% 0.20/0.51          | ~ (r2_hidden @ 
% 0.20/0.51               (k1_funct_1 @ X0 @ (sk_D @ (k1_relat_1 @ X0) @ X1 @ X0)) @ X1)
% 0.20/0.51          | ~ (v1_relat_1 @ X0)
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1))
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | ~ (v1_relat_1 @ X0)
% 0.20/0.51          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1))
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | ~ (v1_relat_1 @ X0)
% 0.20/0.51          | ~ (r2_hidden @ 
% 0.20/0.51               (k1_funct_1 @ X0 @ (sk_D @ (k1_relat_1 @ X0) @ X1 @ X0)) @ X1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['14', '18'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r2_hidden @ 
% 0.20/0.51             (k1_funct_1 @ X0 @ (sk_D @ (k1_relat_1 @ X0) @ X1 @ X0)) @ X1)
% 0.20/0.51          | ~ (v1_relat_1 @ X0)
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r2_hidden @ (k1_funct_1 @ sk_C @ (sk_D @ sk_A @ X0 @ sk_C)) @ X0)
% 0.20/0.51          | ((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ X0))
% 0.20/0.51          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.51          | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['13', '20'])).
% 0.20/0.51  thf('22', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('23', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r2_hidden @ (k1_funct_1 @ sk_C @ (sk_D @ sk_A @ X0 @ sk_C)) @ X0)
% 0.20/0.51          | ((sk_A) = (k10_relat_1 @ sk_C @ X0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['21', '22', '23', '24'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      ((((sk_A) = (k10_relat_1 @ sk_C @ sk_B))
% 0.20/0.51        | ((sk_A) = (k10_relat_1 @ sk_C @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '25'])).
% 0.20/0.51  thf('27', plain, (((sk_A) = (k10_relat_1 @ sk_C @ sk_B))),
% 0.20/0.51      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.51  thf(t145_funct_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.51       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (![X7 : $i, X8 : $i]:
% 0.20/0.51         ((r1_tarski @ (k9_relat_1 @ X7 @ (k10_relat_1 @ X7 @ X8)) @ X8)
% 0.20/0.51          | ~ (v1_funct_1 @ X7)
% 0.20/0.51          | ~ (v1_relat_1 @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.20/0.51        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.51        | ~ (v1_funct_1 @ sk_C))),
% 0.20/0.51      inference('sup+', [status(thm)], ['27', '28'])).
% 0.20/0.51  thf('30', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t146_relat_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 0.20/0.51          | ~ (v1_relat_1 @ X0))),
% 0.20/0.51      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      ((((k9_relat_1 @ sk_C @ sk_A) = (k2_relat_1 @ sk_C))
% 0.20/0.51        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.51      inference('sup+', [status(thm)], ['30', '31'])).
% 0.20/0.51  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('34', plain, (((k9_relat_1 @ sk_C @ sk_A) = (k2_relat_1 @ sk_C))),
% 0.20/0.51      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.51  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('36', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('37', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.20/0.51      inference('demod', [status(thm)], ['29', '34', '35', '36'])).
% 0.20/0.51  thf(t4_funct_2, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.51       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.20/0.51         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.20/0.51           ( m1_subset_1 @
% 0.20/0.51             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i]:
% 0.20/0.51         (~ (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 0.20/0.51          | (m1_subset_1 @ X9 @ 
% 0.20/0.51             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X9) @ X10)))
% 0.20/0.51          | ~ (v1_funct_1 @ X9)
% 0.20/0.51          | ~ (v1_relat_1 @ X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.51        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.51        | (m1_subset_1 @ sk_C @ 
% 0.20/0.51           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.51  thf('40', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('42', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      (($false)
% 0.20/0.51         <= (~
% 0.20/0.51             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))))),
% 0.20/0.51      inference('demod', [status(thm)], ['1', '43'])).
% 0.20/0.51  thf('45', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('46', plain, ((~ (v1_funct_1 @ sk_C)) <= (~ ((v1_funct_1 @ sk_C)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('47', plain, (((v1_funct_1 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.51  thf('48', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.20/0.51      inference('demod', [status(thm)], ['29', '34', '35', '36'])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i]:
% 0.20/0.51         (~ (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 0.20/0.51          | (v1_funct_2 @ X9 @ (k1_relat_1 @ X9) @ X10)
% 0.20/0.51          | ~ (v1_funct_1 @ X9)
% 0.20/0.51          | ~ (v1_relat_1 @ X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.51        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.51        | (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.51  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('53', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('54', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.51      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.20/0.51  thf('55', plain,
% 0.20/0.51      ((~ (v1_funct_2 @ sk_C @ sk_A @ sk_B))
% 0.20/0.51         <= (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('56', plain, (((v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.51  thf('57', plain,
% 0.20/0.51      (~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))) | 
% 0.20/0.51       ~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B)) | ~ ((v1_funct_1 @ sk_C))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('58', plain,
% 0.20/0.51      (~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['47', '56', '57'])).
% 0.20/0.51  thf('59', plain, ($false),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['44', '58'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
