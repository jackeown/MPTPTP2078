%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RuJafv16Q6

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:34 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  253 (2688 expanded)
%              Number of leaves         :   58 ( 862 expanded)
%              Depth                    :   29
%              Number of atoms          : 1593 (35360 expanded)
%              Number of equality atoms :  103 (1574 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X5 ) @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('2',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('3',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t31_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v2_funct_1 @ C )
            & ( ( k2_relset_1 @ A @ B @ C )
              = B ) )
         => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
            & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
            & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_funct_2])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('10',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( v1_relat_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('11',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k2_funct_1 @ X26 )
        = ( k4_relat_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k2_funct_1 @ sk_C_1 )
      = ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ~ ( v1_xboole_0 @ ( k4_relat_1 @ sk_C_1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('22',plain,(
    ! [X27: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('23',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['17'])).

thf('24',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('30',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( v4_relat_1 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('31',plain,(
    v4_relat_1 @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('32',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v4_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('35',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('37',plain,(
    ! [X38: $i] :
      ( ~ ( v2_funct_1 @ X38 )
      | ( ( k2_relat_1 @ X38 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('38',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('40',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('44',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( ( k2_relset_1 @ X48 @ X49 @ X47 )
        = ( k2_relat_1 @ X47 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('45',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['42','47'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('49',plain,(
    ! [X56: $i] :
      ( ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) ) ) )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('50',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('52',plain,(
    ! [X38: $i] :
      ( ~ ( v2_funct_1 @ X38 )
      | ( ( k1_relat_1 @ X38 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('53',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('55',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('59',plain,(
    ! [X27: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('60',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('62',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('65',plain,(
    ! [X27: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('66',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('68',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['50','57','63','69'])).

thf(t9_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ D @ A @ B )
        & ( v1_funct_1 @ D ) )
     => ( ( r1_tarski @ B @ C )
       => ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
            & ( v1_funct_2 @ D @ A @ C )
            & ( v1_funct_1 @ D ) )
          | ( ( A != k1_xboole_0 )
            & ( B = k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_1 @ B @ A )
     => ( ( B = k1_xboole_0 )
        & ( A != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ A )
     => ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ C )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ B @ C )
       => ( ( zip_tseitin_1 @ B @ A )
          | ( zip_tseitin_0 @ D @ C @ A ) ) ) ) )).

thf('71',plain,(
    ! [X62: $i,X63: $i,X64: $i,X65: $i] :
      ( ~ ( r1_tarski @ X62 @ X63 )
      | ( zip_tseitin_1 @ X62 @ X64 )
      | ~ ( v1_funct_1 @ X65 )
      | ~ ( v1_funct_2 @ X65 @ X64 @ X62 )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X64 @ X62 ) ) )
      | ( zip_tseitin_0 @ X65 @ X63 @ X64 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k4_relat_1 @ sk_C_1 ) @ X0 @ sk_B )
      | ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ sk_B @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['42','47'])).

thf('74',plain,(
    ! [X56: $i] :
      ( ( v1_funct_2 @ X56 @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('75',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ sk_B @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('77',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('78',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('79',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('80',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k4_relat_1 @ sk_C_1 ) @ X0 @ sk_B )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['72','79','80'])).

thf('82',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
    | ( zip_tseitin_0 @ ( k4_relat_1 @ sk_C_1 ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['35','81'])).

thf('83',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( v1_funct_2 @ X57 @ X59 @ X58 )
      | ~ ( zip_tseitin_0 @ X57 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('84',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
    | ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('86',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf('87',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X60: $i,X61: $i] :
      ( ( X60 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('90',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('91',plain,(
    ! [X20: $i] :
      ( ( ( k1_relat_1 @ X20 )
       != k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('92',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('94',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['94'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('96',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('97',plain,(
    ! [X55: $i] :
      ( ( k6_partfun1 @ X55 )
      = ( k6_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('98',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['96','97'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('99',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('100',plain,(
    ! [X55: $i] :
      ( ( k6_partfun1 @ X55 )
      = ( k6_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('101',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X28 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k2_funct_1 @ X26 )
        = ( k4_relat_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('104',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( ( k2_funct_1 @ k1_xboole_0 )
      = ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v2_funct_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['96','97'])).

thf('106',plain,(
    ! [X29: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('107',plain,(
    ! [X55: $i] :
      ( ( k6_partfun1 @ X55 )
      = ( k6_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('108',plain,(
    ! [X29: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X29 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['105','108'])).

thf('110',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['96','97'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('111',plain,(
    ! [X31: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('112',plain,(
    ! [X55: $i] :
      ( ( k6_partfun1 @ X55 )
      = ( k6_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('113',plain,(
    ! [X31: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X31 ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['110','113'])).

thf('115',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','109','114'])).

thf('116',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','109','114'])).

thf('117',plain,(
    ! [X38: $i] :
      ( ~ ( v2_funct_1 @ X38 )
      | ( ( k1_relat_1 @ X38 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('118',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = ( k2_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v2_funct_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['96','97'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('120',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('121',plain,(
    ! [X55: $i] :
      ( ( k6_partfun1 @ X55 )
      = ( k6_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('122',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X22 ) )
      = X22 ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['119','122'])).

thf('124',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['98','101'])).

thf('125',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['105','108'])).

thf('126',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['110','113'])).

thf('127',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['118','123','124','125','126'])).

thf('128',plain,(
    ! [X20: $i] :
      ( ( ( k2_relat_1 @ X20 )
       != k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('129',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ( ( k4_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','109','114'])).

thf('131',plain,(
    ! [X27: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('132',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['98','101'])).

thf('134',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['105','108'])).

thf('135',plain,(
    v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['132','133','134'])).

thf('136',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k4_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['129','135'])).

thf('137',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['115','137'])).

thf('139',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['28','95','138'])).

thf('140',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('141',plain,(
    ! [X21: $i] :
      ( ( ( k1_relat_1 @ X21 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X21 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('142',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( ( k2_relat_1 @ sk_C_1 )
        = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('144',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['45','46'])).

thf('145',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['96','97'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('148',plain,(
    ! [X53: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X53 ) @ X53 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('149',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('151',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['119','122'])).

thf('152',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( v4_relat_1 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v4_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['98','101'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( v4_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v4_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['150','155'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('157',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('158',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v4_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['98','101'])).

thf('162',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['119','122'])).

thf('163',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['160','161','162'])).

thf('164',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('165',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('166',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_partfun1 @ X50 @ X51 )
      | ( v1_funct_2 @ X50 @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_partfun1 @ k1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['105','108'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_partfun1 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['149','169'])).

thf('171',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['139','146','170'])).

thf('172',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['17'])).

thf('173',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['27','171','172'])).

thf('174',plain,(
    ~ ( v1_xboole_0 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['20','173'])).

thf('175',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
    | ( zip_tseitin_0 @ ( k4_relat_1 @ sk_C_1 ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['35','81'])).

thf('176',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X58 ) ) )
      | ~ ( zip_tseitin_0 @ X57 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('177',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
    | ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['17'])).

thf('179',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('180',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['27','171','172'])).

thf('182',plain,(
    ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['180','181'])).

thf('183',plain,(
    zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(clc,[status(thm)],['177','182'])).

thf('184',plain,(
    ! [X60: $i,X61: $i] :
      ( ( X60 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('185',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X20: $i] :
      ( ( ( k1_relat_1 @ X20 )
       != k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('187',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('189',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['189'])).

thf('191',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['136'])).

thf('192',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('193',plain,(
    $false ),
    inference(demod,[status(thm)],['174','190','191','192'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RuJafv16Q6
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:21:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.47/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.70  % Solved by: fo/fo7.sh
% 0.47/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.70  % done 780 iterations in 0.249s
% 0.47/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.70  % SZS output start Refutation
% 0.47/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.70  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.47/0.70  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.47/0.70  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.47/0.70  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.47/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.70  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.47/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.70  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.47/0.70  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.47/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.70  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.47/0.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.70  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.47/0.70  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.47/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.70  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.47/0.70  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.47/0.70  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.47/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.70  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.47/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.70  thf(d3_tarski, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( r1_tarski @ A @ B ) <=>
% 0.47/0.70       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.47/0.70  thf('0', plain,
% 0.47/0.70      (![X1 : $i, X3 : $i]:
% 0.47/0.70         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.47/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.70  thf(dt_k2_subset_1, axiom,
% 0.47/0.70    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.47/0.70  thf('1', plain,
% 0.47/0.70      (![X5 : $i]: (m1_subset_1 @ (k2_subset_1 @ X5) @ (k1_zfmisc_1 @ X5))),
% 0.47/0.70      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.47/0.70  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.47/0.70  thf('2', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 0.47/0.70      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.47/0.70  thf('3', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.47/0.70      inference('demod', [status(thm)], ['1', '2'])).
% 0.47/0.70  thf(t5_subset, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i]:
% 0.47/0.70     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.47/0.70          ( v1_xboole_0 @ C ) ) ))).
% 0.47/0.70  thf('4', plain,
% 0.47/0.70      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.47/0.70         (~ (r2_hidden @ X9 @ X10)
% 0.47/0.70          | ~ (v1_xboole_0 @ X11)
% 0.47/0.70          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.47/0.70      inference('cnf', [status(esa)], [t5_subset])).
% 0.47/0.70  thf('5', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['3', '4'])).
% 0.47/0.70  thf('6', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['0', '5'])).
% 0.47/0.70  thf(t3_subset, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.47/0.70  thf('7', plain,
% 0.47/0.70      (![X6 : $i, X8 : $i]:
% 0.47/0.70         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.47/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.70  thf('8', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['6', '7'])).
% 0.47/0.70  thf(t31_funct_2, conjecture,
% 0.47/0.70    (![A:$i,B:$i,C:$i]:
% 0.47/0.70     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.47/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.70       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.47/0.70         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.47/0.70           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.47/0.70           ( m1_subset_1 @
% 0.47/0.70             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.47/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.70    (~( ![A:$i,B:$i,C:$i]:
% 0.47/0.70        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.47/0.70            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.70          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.47/0.70            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.47/0.70              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.47/0.70              ( m1_subset_1 @
% 0.47/0.70                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.47/0.70    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.47/0.70  thf('9', plain,
% 0.47/0.70      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf(cc1_relset_1, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i]:
% 0.47/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.70       ( v1_relat_1 @ C ) ))).
% 0.47/0.70  thf('10', plain,
% 0.47/0.70      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.47/0.70         ((v1_relat_1 @ X41)
% 0.47/0.70          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43))))),
% 0.47/0.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.47/0.70  thf('11', plain, ((v1_relat_1 @ sk_C_1)),
% 0.47/0.70      inference('sup-', [status(thm)], ['9', '10'])).
% 0.47/0.70  thf(d9_funct_1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.70       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.47/0.70  thf('12', plain,
% 0.47/0.70      (![X26 : $i]:
% 0.47/0.70         (~ (v2_funct_1 @ X26)
% 0.47/0.70          | ((k2_funct_1 @ X26) = (k4_relat_1 @ X26))
% 0.47/0.70          | ~ (v1_funct_1 @ X26)
% 0.47/0.70          | ~ (v1_relat_1 @ X26))),
% 0.47/0.70      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.47/0.70  thf('13', plain,
% 0.47/0.70      ((~ (v1_funct_1 @ sk_C_1)
% 0.47/0.70        | ((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))
% 0.47/0.70        | ~ (v2_funct_1 @ sk_C_1))),
% 0.47/0.70      inference('sup-', [status(thm)], ['11', '12'])).
% 0.47/0.70  thf('14', plain, ((v1_funct_1 @ sk_C_1)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('15', plain, ((v2_funct_1 @ sk_C_1)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('16', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.47/0.70      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.47/0.70  thf('17', plain,
% 0.47/0.70      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.47/0.70        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)
% 0.47/0.70        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.47/0.70             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('18', plain,
% 0.47/0.70      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.47/0.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.47/0.70         <= (~
% 0.47/0.70             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.47/0.70               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.47/0.70      inference('split', [status(esa)], ['17'])).
% 0.47/0.70  thf('19', plain,
% 0.47/0.70      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 0.47/0.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.47/0.70         <= (~
% 0.47/0.70             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.47/0.70               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.47/0.70      inference('sup-', [status(thm)], ['16', '18'])).
% 0.47/0.70  thf('20', plain,
% 0.47/0.70      ((~ (v1_xboole_0 @ (k4_relat_1 @ sk_C_1)))
% 0.47/0.70         <= (~
% 0.47/0.70             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.47/0.70               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.47/0.70      inference('sup-', [status(thm)], ['8', '19'])).
% 0.47/0.70  thf('21', plain, ((v1_relat_1 @ sk_C_1)),
% 0.47/0.70      inference('sup-', [status(thm)], ['9', '10'])).
% 0.47/0.70  thf(dt_k2_funct_1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.70       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.47/0.70         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.47/0.70  thf('22', plain,
% 0.47/0.70      (![X27 : $i]:
% 0.47/0.70         ((v1_funct_1 @ (k2_funct_1 @ X27))
% 0.47/0.70          | ~ (v1_funct_1 @ X27)
% 0.47/0.70          | ~ (v1_relat_1 @ X27))),
% 0.47/0.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.47/0.70  thf('23', plain,
% 0.47/0.70      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 0.47/0.70         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.47/0.70      inference('split', [status(esa)], ['17'])).
% 0.47/0.70  thf('24', plain,
% 0.47/0.70      (((~ (v1_relat_1 @ sk_C_1) | ~ (v1_funct_1 @ sk_C_1)))
% 0.47/0.70         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.47/0.70      inference('sup-', [status(thm)], ['22', '23'])).
% 0.47/0.70  thf('25', plain, ((v1_funct_1 @ sk_C_1)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('26', plain,
% 0.47/0.70      ((~ (v1_relat_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.47/0.70      inference('demod', [status(thm)], ['24', '25'])).
% 0.47/0.70  thf('27', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['21', '26'])).
% 0.47/0.70  thf('28', plain,
% 0.47/0.70      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))
% 0.47/0.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.47/0.70      inference('split', [status(esa)], ['17'])).
% 0.47/0.70  thf('29', plain,
% 0.47/0.70      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf(cc2_relset_1, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i]:
% 0.47/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.70       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.47/0.70  thf('30', plain,
% 0.47/0.70      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.47/0.70         ((v4_relat_1 @ X44 @ X45)
% 0.47/0.70          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46))))),
% 0.47/0.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.70  thf('31', plain, ((v4_relat_1 @ sk_C_1 @ sk_A)),
% 0.47/0.70      inference('sup-', [status(thm)], ['29', '30'])).
% 0.47/0.70  thf(d18_relat_1, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( v1_relat_1 @ B ) =>
% 0.47/0.70       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.47/0.70  thf('32', plain,
% 0.47/0.70      (![X12 : $i, X13 : $i]:
% 0.47/0.70         (~ (v4_relat_1 @ X12 @ X13)
% 0.47/0.70          | (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.47/0.70          | ~ (v1_relat_1 @ X12))),
% 0.47/0.70      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.47/0.70  thf('33', plain,
% 0.47/0.70      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A))),
% 0.47/0.70      inference('sup-', [status(thm)], ['31', '32'])).
% 0.47/0.70  thf('34', plain, ((v1_relat_1 @ sk_C_1)),
% 0.47/0.70      inference('sup-', [status(thm)], ['9', '10'])).
% 0.47/0.70  thf('35', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 0.47/0.70      inference('demod', [status(thm)], ['33', '34'])).
% 0.47/0.70  thf('36', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.47/0.70      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.47/0.70  thf(t55_funct_1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.70       ( ( v2_funct_1 @ A ) =>
% 0.47/0.70         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.47/0.70           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.47/0.70  thf('37', plain,
% 0.47/0.70      (![X38 : $i]:
% 0.47/0.70         (~ (v2_funct_1 @ X38)
% 0.47/0.70          | ((k2_relat_1 @ X38) = (k1_relat_1 @ (k2_funct_1 @ X38)))
% 0.47/0.70          | ~ (v1_funct_1 @ X38)
% 0.47/0.70          | ~ (v1_relat_1 @ X38))),
% 0.47/0.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.47/0.70  thf('38', plain,
% 0.47/0.70      ((((k2_relat_1 @ sk_C_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 0.47/0.70        | ~ (v1_relat_1 @ sk_C_1)
% 0.47/0.70        | ~ (v1_funct_1 @ sk_C_1)
% 0.47/0.70        | ~ (v2_funct_1 @ sk_C_1))),
% 0.47/0.70      inference('sup+', [status(thm)], ['36', '37'])).
% 0.47/0.70  thf('39', plain, ((v1_relat_1 @ sk_C_1)),
% 0.47/0.70      inference('sup-', [status(thm)], ['9', '10'])).
% 0.47/0.70  thf('40', plain, ((v1_funct_1 @ sk_C_1)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('41', plain, ((v2_funct_1 @ sk_C_1)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('42', plain,
% 0.47/0.70      (((k2_relat_1 @ sk_C_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.47/0.70      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 0.47/0.70  thf('43', plain,
% 0.47/0.70      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf(redefinition_k2_relset_1, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i]:
% 0.47/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.70       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.47/0.70  thf('44', plain,
% 0.47/0.70      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.47/0.70         (((k2_relset_1 @ X48 @ X49 @ X47) = (k2_relat_1 @ X47))
% 0.47/0.70          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49))))),
% 0.47/0.70      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.47/0.70  thf('45', plain,
% 0.47/0.70      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.47/0.70      inference('sup-', [status(thm)], ['43', '44'])).
% 0.47/0.70  thf('46', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('47', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 0.47/0.70      inference('sup+', [status(thm)], ['45', '46'])).
% 0.47/0.70  thf('48', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.47/0.70      inference('demod', [status(thm)], ['42', '47'])).
% 0.47/0.70  thf(t3_funct_2, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.70       ( ( v1_funct_1 @ A ) & 
% 0.47/0.70         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.47/0.70         ( m1_subset_1 @
% 0.47/0.70           A @ 
% 0.47/0.70           ( k1_zfmisc_1 @
% 0.47/0.70             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.47/0.70  thf('49', plain,
% 0.47/0.70      (![X56 : $i]:
% 0.47/0.70         ((m1_subset_1 @ X56 @ 
% 0.47/0.70           (k1_zfmisc_1 @ 
% 0.47/0.70            (k2_zfmisc_1 @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56))))
% 0.47/0.70          | ~ (v1_funct_1 @ X56)
% 0.47/0.70          | ~ (v1_relat_1 @ X56))),
% 0.47/0.70      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.47/0.70  thf('50', plain,
% 0.47/0.70      (((m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 0.47/0.70         (k1_zfmisc_1 @ 
% 0.47/0.70          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))))
% 0.47/0.70        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 0.47/0.70        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.47/0.70      inference('sup+', [status(thm)], ['48', '49'])).
% 0.47/0.70  thf('51', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.47/0.70      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.47/0.70  thf('52', plain,
% 0.47/0.70      (![X38 : $i]:
% 0.47/0.70         (~ (v2_funct_1 @ X38)
% 0.47/0.70          | ((k1_relat_1 @ X38) = (k2_relat_1 @ (k2_funct_1 @ X38)))
% 0.47/0.70          | ~ (v1_funct_1 @ X38)
% 0.47/0.70          | ~ (v1_relat_1 @ X38))),
% 0.47/0.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.47/0.70  thf('53', plain,
% 0.47/0.70      ((((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 0.47/0.70        | ~ (v1_relat_1 @ sk_C_1)
% 0.47/0.70        | ~ (v1_funct_1 @ sk_C_1)
% 0.47/0.70        | ~ (v2_funct_1 @ sk_C_1))),
% 0.47/0.70      inference('sup+', [status(thm)], ['51', '52'])).
% 0.47/0.70  thf('54', plain, ((v1_relat_1 @ sk_C_1)),
% 0.47/0.70      inference('sup-', [status(thm)], ['9', '10'])).
% 0.47/0.70  thf('55', plain, ((v1_funct_1 @ sk_C_1)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('56', plain, ((v2_funct_1 @ sk_C_1)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('57', plain,
% 0.47/0.70      (((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.47/0.70      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 0.47/0.70  thf('58', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.47/0.70      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.47/0.70  thf('59', plain,
% 0.47/0.70      (![X27 : $i]:
% 0.47/0.70         ((v1_relat_1 @ (k2_funct_1 @ X27))
% 0.47/0.70          | ~ (v1_funct_1 @ X27)
% 0.47/0.70          | ~ (v1_relat_1 @ X27))),
% 0.47/0.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.47/0.70  thf('60', plain,
% 0.47/0.70      (((v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 0.47/0.70        | ~ (v1_relat_1 @ sk_C_1)
% 0.47/0.70        | ~ (v1_funct_1 @ sk_C_1))),
% 0.47/0.70      inference('sup+', [status(thm)], ['58', '59'])).
% 0.47/0.70  thf('61', plain, ((v1_relat_1 @ sk_C_1)),
% 0.47/0.70      inference('sup-', [status(thm)], ['9', '10'])).
% 0.47/0.70  thf('62', plain, ((v1_funct_1 @ sk_C_1)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('63', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 0.47/0.70      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.47/0.70  thf('64', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.47/0.70      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.47/0.70  thf('65', plain,
% 0.47/0.70      (![X27 : $i]:
% 0.47/0.70         ((v1_funct_1 @ (k2_funct_1 @ X27))
% 0.47/0.70          | ~ (v1_funct_1 @ X27)
% 0.47/0.70          | ~ (v1_relat_1 @ X27))),
% 0.47/0.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.47/0.70  thf('66', plain,
% 0.47/0.70      (((v1_funct_1 @ (k4_relat_1 @ sk_C_1))
% 0.47/0.70        | ~ (v1_relat_1 @ sk_C_1)
% 0.47/0.70        | ~ (v1_funct_1 @ sk_C_1))),
% 0.47/0.70      inference('sup+', [status(thm)], ['64', '65'])).
% 0.47/0.70  thf('67', plain, ((v1_relat_1 @ sk_C_1)),
% 0.47/0.70      inference('sup-', [status(thm)], ['9', '10'])).
% 0.47/0.70  thf('68', plain, ((v1_funct_1 @ sk_C_1)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('69', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C_1))),
% 0.47/0.70      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.47/0.70  thf('70', plain,
% 0.47/0.70      ((m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 0.47/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C_1))))),
% 0.47/0.70      inference('demod', [status(thm)], ['50', '57', '63', '69'])).
% 0.47/0.70  thf(t9_funct_2, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.70     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.47/0.70         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.47/0.70       ( ( r1_tarski @ B @ C ) =>
% 0.47/0.70         ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.47/0.70             ( v1_funct_2 @ D @ A @ C ) & ( v1_funct_1 @ D ) ) | 
% 0.47/0.70           ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.47/0.70  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.47/0.70  thf(zf_stmt_2, axiom,
% 0.47/0.70    (![B:$i,A:$i]:
% 0.47/0.70     ( ( zip_tseitin_1 @ B @ A ) =>
% 0.47/0.70       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) ))).
% 0.47/0.70  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.47/0.70  thf(zf_stmt_4, axiom,
% 0.47/0.70    (![D:$i,C:$i,A:$i]:
% 0.47/0.70     ( ( zip_tseitin_0 @ D @ C @ A ) =>
% 0.47/0.70       ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.47/0.70         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ))).
% 0.47/0.70  thf(zf_stmt_5, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.70     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.47/0.70         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.70       ( ( r1_tarski @ B @ C ) =>
% 0.47/0.70         ( ( zip_tseitin_1 @ B @ A ) | ( zip_tseitin_0 @ D @ C @ A ) ) ) ))).
% 0.47/0.70  thf('71', plain,
% 0.47/0.70      (![X62 : $i, X63 : $i, X64 : $i, X65 : $i]:
% 0.47/0.70         (~ (r1_tarski @ X62 @ X63)
% 0.47/0.70          | (zip_tseitin_1 @ X62 @ X64)
% 0.47/0.70          | ~ (v1_funct_1 @ X65)
% 0.47/0.70          | ~ (v1_funct_2 @ X65 @ X64 @ X62)
% 0.47/0.70          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X64 @ X62)))
% 0.47/0.70          | (zip_tseitin_0 @ X65 @ X63 @ X64))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.47/0.70  thf('72', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((zip_tseitin_0 @ (k4_relat_1 @ sk_C_1) @ X0 @ sk_B)
% 0.47/0.70          | ~ (v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ sk_B @ 
% 0.47/0.70               (k1_relat_1 @ sk_C_1))
% 0.47/0.70          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C_1))
% 0.47/0.70          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)
% 0.47/0.70          | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['70', '71'])).
% 0.47/0.70  thf('73', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.47/0.70      inference('demod', [status(thm)], ['42', '47'])).
% 0.47/0.70  thf('74', plain,
% 0.47/0.70      (![X56 : $i]:
% 0.47/0.70         ((v1_funct_2 @ X56 @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56))
% 0.47/0.70          | ~ (v1_funct_1 @ X56)
% 0.47/0.70          | ~ (v1_relat_1 @ X56))),
% 0.47/0.70      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.47/0.70  thf('75', plain,
% 0.47/0.70      (((v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ sk_B @ 
% 0.47/0.70         (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 0.47/0.70        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 0.47/0.70        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.47/0.70      inference('sup+', [status(thm)], ['73', '74'])).
% 0.47/0.70  thf('76', plain,
% 0.47/0.70      (((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.47/0.70      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 0.47/0.70  thf('77', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 0.47/0.70      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.47/0.70  thf('78', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C_1))),
% 0.47/0.70      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.47/0.70  thf('79', plain,
% 0.47/0.70      ((v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ sk_B @ (k1_relat_1 @ sk_C_1))),
% 0.47/0.70      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 0.47/0.70  thf('80', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C_1))),
% 0.47/0.70      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.47/0.70  thf('81', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((zip_tseitin_0 @ (k4_relat_1 @ sk_C_1) @ X0 @ sk_B)
% 0.47/0.70          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)
% 0.47/0.70          | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0))),
% 0.47/0.70      inference('demod', [status(thm)], ['72', '79', '80'])).
% 0.47/0.70  thf('82', plain,
% 0.47/0.70      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)
% 0.47/0.70        | (zip_tseitin_0 @ (k4_relat_1 @ sk_C_1) @ sk_A @ sk_B))),
% 0.47/0.70      inference('sup-', [status(thm)], ['35', '81'])).
% 0.47/0.70  thf('83', plain,
% 0.47/0.70      (![X57 : $i, X58 : $i, X59 : $i]:
% 0.47/0.70         ((v1_funct_2 @ X57 @ X59 @ X58) | ~ (zip_tseitin_0 @ X57 @ X58 @ X59))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.47/0.70  thf('84', plain,
% 0.47/0.70      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)
% 0.47/0.70        | (v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ sk_B @ sk_A))),
% 0.47/0.70      inference('sup-', [status(thm)], ['82', '83'])).
% 0.47/0.70  thf('85', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.47/0.70      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.47/0.70  thf('86', plain,
% 0.47/0.70      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))
% 0.47/0.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.47/0.70      inference('split', [status(esa)], ['17'])).
% 0.47/0.70  thf('87', plain,
% 0.47/0.70      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ sk_B @ sk_A))
% 0.47/0.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['85', '86'])).
% 0.47/0.70  thf('88', plain,
% 0.47/0.70      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B))
% 0.47/0.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['84', '87'])).
% 0.47/0.70  thf('89', plain,
% 0.47/0.70      (![X60 : $i, X61 : $i]:
% 0.47/0.70         (((X60) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X60 @ X61))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.47/0.70  thf('90', plain,
% 0.47/0.70      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))
% 0.47/0.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['88', '89'])).
% 0.47/0.70  thf(t64_relat_1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( v1_relat_1 @ A ) =>
% 0.47/0.70       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.47/0.70           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.70         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.47/0.70  thf('91', plain,
% 0.47/0.70      (![X20 : $i]:
% 0.47/0.70         (((k1_relat_1 @ X20) != (k1_xboole_0))
% 0.47/0.70          | ((X20) = (k1_xboole_0))
% 0.47/0.70          | ~ (v1_relat_1 @ X20))),
% 0.47/0.70      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.47/0.70  thf('92', plain,
% 0.47/0.70      (((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.70         | ~ (v1_relat_1 @ sk_C_1)
% 0.47/0.70         | ((sk_C_1) = (k1_xboole_0))))
% 0.47/0.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['90', '91'])).
% 0.47/0.70  thf('93', plain, ((v1_relat_1 @ sk_C_1)),
% 0.47/0.70      inference('sup-', [status(thm)], ['9', '10'])).
% 0.47/0.70  thf('94', plain,
% 0.47/0.70      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0))))
% 0.47/0.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.47/0.70      inference('demod', [status(thm)], ['92', '93'])).
% 0.47/0.70  thf('95', plain,
% 0.47/0.70      ((((sk_C_1) = (k1_xboole_0)))
% 0.47/0.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.47/0.70      inference('simplify', [status(thm)], ['94'])).
% 0.47/0.70  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.47/0.70  thf('96', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.70      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.47/0.70  thf(redefinition_k6_partfun1, axiom,
% 0.47/0.70    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.47/0.70  thf('97', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 0.47/0.70      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.70  thf('98', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.70      inference('demod', [status(thm)], ['96', '97'])).
% 0.47/0.70  thf(fc3_funct_1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.47/0.70       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.47/0.70  thf('99', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.47/0.70      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.47/0.70  thf('100', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 0.47/0.70      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.70  thf('101', plain, (![X28 : $i]: (v1_relat_1 @ (k6_partfun1 @ X28))),
% 0.47/0.70      inference('demod', [status(thm)], ['99', '100'])).
% 0.47/0.70  thf('102', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.70      inference('sup+', [status(thm)], ['98', '101'])).
% 0.47/0.70  thf('103', plain,
% 0.47/0.70      (![X26 : $i]:
% 0.47/0.70         (~ (v2_funct_1 @ X26)
% 0.47/0.70          | ((k2_funct_1 @ X26) = (k4_relat_1 @ X26))
% 0.47/0.70          | ~ (v1_funct_1 @ X26)
% 0.47/0.70          | ~ (v1_relat_1 @ X26))),
% 0.47/0.70      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.47/0.70  thf('104', plain,
% 0.47/0.70      ((~ (v1_funct_1 @ k1_xboole_0)
% 0.47/0.70        | ((k2_funct_1 @ k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))
% 0.47/0.70        | ~ (v2_funct_1 @ k1_xboole_0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['102', '103'])).
% 0.47/0.70  thf('105', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.70      inference('demod', [status(thm)], ['96', '97'])).
% 0.47/0.70  thf('106', plain, (![X29 : $i]: (v1_funct_1 @ (k6_relat_1 @ X29))),
% 0.47/0.70      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.47/0.70  thf('107', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 0.47/0.70      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.70  thf('108', plain, (![X29 : $i]: (v1_funct_1 @ (k6_partfun1 @ X29))),
% 0.47/0.70      inference('demod', [status(thm)], ['106', '107'])).
% 0.47/0.70  thf('109', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.47/0.70      inference('sup+', [status(thm)], ['105', '108'])).
% 0.47/0.70  thf('110', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.70      inference('demod', [status(thm)], ['96', '97'])).
% 0.47/0.70  thf(fc4_funct_1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.47/0.70       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.47/0.70  thf('111', plain, (![X31 : $i]: (v2_funct_1 @ (k6_relat_1 @ X31))),
% 0.47/0.70      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.47/0.70  thf('112', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 0.47/0.70      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.70  thf('113', plain, (![X31 : $i]: (v2_funct_1 @ (k6_partfun1 @ X31))),
% 0.47/0.70      inference('demod', [status(thm)], ['111', '112'])).
% 0.47/0.70  thf('114', plain, ((v2_funct_1 @ k1_xboole_0)),
% 0.47/0.70      inference('sup+', [status(thm)], ['110', '113'])).
% 0.47/0.70  thf('115', plain,
% 0.47/0.70      (((k2_funct_1 @ k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 0.47/0.70      inference('demod', [status(thm)], ['104', '109', '114'])).
% 0.47/0.70  thf('116', plain,
% 0.47/0.70      (((k2_funct_1 @ k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 0.47/0.70      inference('demod', [status(thm)], ['104', '109', '114'])).
% 0.47/0.70  thf('117', plain,
% 0.47/0.70      (![X38 : $i]:
% 0.47/0.70         (~ (v2_funct_1 @ X38)
% 0.47/0.70          | ((k1_relat_1 @ X38) = (k2_relat_1 @ (k2_funct_1 @ X38)))
% 0.47/0.70          | ~ (v1_funct_1 @ X38)
% 0.47/0.70          | ~ (v1_relat_1 @ X38))),
% 0.47/0.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.47/0.70  thf('118', plain,
% 0.47/0.70      ((((k1_relat_1 @ k1_xboole_0) = (k2_relat_1 @ (k4_relat_1 @ k1_xboole_0)))
% 0.47/0.70        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.70        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.47/0.70        | ~ (v2_funct_1 @ k1_xboole_0))),
% 0.47/0.70      inference('sup+', [status(thm)], ['116', '117'])).
% 0.47/0.70  thf('119', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.70      inference('demod', [status(thm)], ['96', '97'])).
% 0.47/0.70  thf(t71_relat_1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.47/0.70       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.47/0.70  thf('120', plain, (![X22 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 0.47/0.70      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.47/0.70  thf('121', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 0.47/0.70      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.70  thf('122', plain,
% 0.47/0.70      (![X22 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X22)) = (X22))),
% 0.47/0.70      inference('demod', [status(thm)], ['120', '121'])).
% 0.47/0.70  thf('123', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.70      inference('sup+', [status(thm)], ['119', '122'])).
% 0.47/0.70  thf('124', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.70      inference('sup+', [status(thm)], ['98', '101'])).
% 0.47/0.70  thf('125', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.47/0.70      inference('sup+', [status(thm)], ['105', '108'])).
% 0.47/0.70  thf('126', plain, ((v2_funct_1 @ k1_xboole_0)),
% 0.47/0.70      inference('sup+', [status(thm)], ['110', '113'])).
% 0.47/0.70  thf('127', plain,
% 0.47/0.70      (((k1_xboole_0) = (k2_relat_1 @ (k4_relat_1 @ k1_xboole_0)))),
% 0.47/0.70      inference('demod', [status(thm)], ['118', '123', '124', '125', '126'])).
% 0.47/0.70  thf('128', plain,
% 0.47/0.70      (![X20 : $i]:
% 0.47/0.70         (((k2_relat_1 @ X20) != (k1_xboole_0))
% 0.47/0.70          | ((X20) = (k1_xboole_0))
% 0.47/0.70          | ~ (v1_relat_1 @ X20))),
% 0.47/0.70      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.47/0.70  thf('129', plain,
% 0.47/0.70      ((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.70        | ~ (v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))
% 0.47/0.70        | ((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['127', '128'])).
% 0.47/0.70  thf('130', plain,
% 0.47/0.70      (((k2_funct_1 @ k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 0.47/0.70      inference('demod', [status(thm)], ['104', '109', '114'])).
% 0.47/0.70  thf('131', plain,
% 0.47/0.70      (![X27 : $i]:
% 0.47/0.70         ((v1_relat_1 @ (k2_funct_1 @ X27))
% 0.47/0.70          | ~ (v1_funct_1 @ X27)
% 0.47/0.70          | ~ (v1_relat_1 @ X27))),
% 0.47/0.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.47/0.70  thf('132', plain,
% 0.47/0.70      (((v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))
% 0.47/0.70        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.70        | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.47/0.70      inference('sup+', [status(thm)], ['130', '131'])).
% 0.47/0.70  thf('133', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.70      inference('sup+', [status(thm)], ['98', '101'])).
% 0.47/0.70  thf('134', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.47/0.70      inference('sup+', [status(thm)], ['105', '108'])).
% 0.47/0.70  thf('135', plain, ((v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))),
% 0.47/0.70      inference('demod', [status(thm)], ['132', '133', '134'])).
% 0.47/0.70  thf('136', plain,
% 0.47/0.70      ((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.70        | ((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.47/0.70      inference('demod', [status(thm)], ['129', '135'])).
% 0.47/0.70  thf('137', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['136'])).
% 0.47/0.70  thf('138', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.70      inference('demod', [status(thm)], ['115', '137'])).
% 0.47/0.70  thf('139', plain,
% 0.47/0.70      ((~ (v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A))
% 0.47/0.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.47/0.70      inference('demod', [status(thm)], ['28', '95', '138'])).
% 0.47/0.70  thf('140', plain,
% 0.47/0.70      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))
% 0.47/0.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['88', '89'])).
% 0.47/0.70  thf(t65_relat_1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( v1_relat_1 @ A ) =>
% 0.47/0.70       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.47/0.70         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.47/0.70  thf('141', plain,
% 0.47/0.70      (![X21 : $i]:
% 0.47/0.70         (((k1_relat_1 @ X21) != (k1_xboole_0))
% 0.47/0.70          | ((k2_relat_1 @ X21) = (k1_xboole_0))
% 0.47/0.70          | ~ (v1_relat_1 @ X21))),
% 0.47/0.70      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.47/0.70  thf('142', plain,
% 0.47/0.70      (((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.70         | ~ (v1_relat_1 @ sk_C_1)
% 0.47/0.70         | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0))))
% 0.47/0.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['140', '141'])).
% 0.47/0.70  thf('143', plain, ((v1_relat_1 @ sk_C_1)),
% 0.47/0.70      inference('sup-', [status(thm)], ['9', '10'])).
% 0.47/0.70  thf('144', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 0.47/0.70      inference('sup+', [status(thm)], ['45', '46'])).
% 0.47/0.70  thf('145', plain,
% 0.47/0.70      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 0.47/0.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.47/0.70      inference('demod', [status(thm)], ['142', '143', '144'])).
% 0.47/0.70  thf('146', plain,
% 0.47/0.70      ((((sk_B) = (k1_xboole_0)))
% 0.47/0.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.47/0.70      inference('simplify', [status(thm)], ['145'])).
% 0.47/0.70  thf('147', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.70      inference('demod', [status(thm)], ['96', '97'])).
% 0.47/0.70  thf(dt_k6_partfun1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( m1_subset_1 @
% 0.47/0.70         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.47/0.70       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.47/0.70  thf('148', plain, (![X53 : $i]: (v1_partfun1 @ (k6_partfun1 @ X53) @ X53)),
% 0.47/0.70      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.47/0.70  thf('149', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.47/0.70      inference('sup+', [status(thm)], ['147', '148'])).
% 0.47/0.70  thf('150', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['0', '5'])).
% 0.47/0.70  thf('151', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.70      inference('sup+', [status(thm)], ['119', '122'])).
% 0.47/0.70  thf('152', plain,
% 0.47/0.70      (![X12 : $i, X13 : $i]:
% 0.47/0.70         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.47/0.70          | (v4_relat_1 @ X12 @ X13)
% 0.47/0.70          | ~ (v1_relat_1 @ X12))),
% 0.47/0.70      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.47/0.70  thf('153', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.47/0.70          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.70          | (v4_relat_1 @ k1_xboole_0 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['151', '152'])).
% 0.47/0.70  thf('154', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.70      inference('sup+', [status(thm)], ['98', '101'])).
% 0.47/0.70  thf('155', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (r1_tarski @ k1_xboole_0 @ X0) | (v4_relat_1 @ k1_xboole_0 @ X0))),
% 0.47/0.70      inference('demod', [status(thm)], ['153', '154'])).
% 0.47/0.70  thf('156', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (v1_xboole_0 @ k1_xboole_0) | (v4_relat_1 @ k1_xboole_0 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['150', '155'])).
% 0.47/0.70  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.47/0.70  thf('157', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.70  thf('158', plain, (![X0 : $i]: (v4_relat_1 @ k1_xboole_0 @ X0)),
% 0.47/0.70      inference('demod', [status(thm)], ['156', '157'])).
% 0.47/0.70  thf('159', plain,
% 0.47/0.70      (![X12 : $i, X13 : $i]:
% 0.47/0.70         (~ (v4_relat_1 @ X12 @ X13)
% 0.47/0.70          | (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.47/0.70          | ~ (v1_relat_1 @ X12))),
% 0.47/0.70      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.47/0.70  thf('160', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.70          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['158', '159'])).
% 0.47/0.70  thf('161', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.70      inference('sup+', [status(thm)], ['98', '101'])).
% 0.47/0.70  thf('162', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.70      inference('sup+', [status(thm)], ['119', '122'])).
% 0.47/0.70  thf('163', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.47/0.70      inference('demod', [status(thm)], ['160', '161', '162'])).
% 0.47/0.70  thf('164', plain,
% 0.47/0.70      (![X6 : $i, X8 : $i]:
% 0.47/0.70         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.47/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.70  thf('165', plain,
% 0.47/0.70      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['163', '164'])).
% 0.47/0.70  thf(cc1_funct_2, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i]:
% 0.47/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.70       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.47/0.70         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.47/0.70  thf('166', plain,
% 0.47/0.70      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.47/0.70         (~ (v1_funct_1 @ X50)
% 0.47/0.70          | ~ (v1_partfun1 @ X50 @ X51)
% 0.47/0.70          | (v1_funct_2 @ X50 @ X51 @ X52)
% 0.47/0.70          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52))))),
% 0.47/0.70      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.47/0.70  thf('167', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         ((v1_funct_2 @ k1_xboole_0 @ X1 @ X0)
% 0.47/0.70          | ~ (v1_partfun1 @ k1_xboole_0 @ X1)
% 0.47/0.70          | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['165', '166'])).
% 0.47/0.70  thf('168', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.47/0.70      inference('sup+', [status(thm)], ['105', '108'])).
% 0.47/0.70  thf('169', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         ((v1_funct_2 @ k1_xboole_0 @ X1 @ X0)
% 0.47/0.70          | ~ (v1_partfun1 @ k1_xboole_0 @ X1))),
% 0.47/0.70      inference('demod', [status(thm)], ['167', '168'])).
% 0.47/0.70  thf('170', plain,
% 0.47/0.70      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.47/0.70      inference('sup-', [status(thm)], ['149', '169'])).
% 0.47/0.70  thf('171', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))),
% 0.47/0.70      inference('demod', [status(thm)], ['139', '146', '170'])).
% 0.47/0.70  thf('172', plain,
% 0.47/0.70      (~
% 0.47/0.70       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.47/0.70         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 0.47/0.70       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)) | 
% 0.47/0.70       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.47/0.70      inference('split', [status(esa)], ['17'])).
% 0.47/0.70  thf('173', plain,
% 0.47/0.70      (~
% 0.47/0.70       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.47/0.70         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.47/0.70      inference('sat_resolution*', [status(thm)], ['27', '171', '172'])).
% 0.47/0.70  thf('174', plain, (~ (v1_xboole_0 @ (k4_relat_1 @ sk_C_1))),
% 0.47/0.70      inference('simpl_trail', [status(thm)], ['20', '173'])).
% 0.47/0.70  thf('175', plain,
% 0.47/0.70      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)
% 0.47/0.70        | (zip_tseitin_0 @ (k4_relat_1 @ sk_C_1) @ sk_A @ sk_B))),
% 0.47/0.70      inference('sup-', [status(thm)], ['35', '81'])).
% 0.47/0.70  thf('176', plain,
% 0.47/0.70      (![X57 : $i, X58 : $i, X59 : $i]:
% 0.47/0.70         ((m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X58)))
% 0.47/0.70          | ~ (zip_tseitin_0 @ X57 @ X58 @ X59))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.47/0.70  thf('177', plain,
% 0.47/0.70      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)
% 0.47/0.70        | (m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 0.47/0.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.47/0.70      inference('sup-', [status(thm)], ['175', '176'])).
% 0.47/0.70  thf('178', plain,
% 0.47/0.70      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.47/0.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.47/0.70         <= (~
% 0.47/0.70             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.47/0.70               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.47/0.70      inference('split', [status(esa)], ['17'])).
% 0.47/0.70  thf('179', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.47/0.70      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.47/0.70  thf('180', plain,
% 0.47/0.70      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 0.47/0.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.47/0.70         <= (~
% 0.47/0.70             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.47/0.70               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.47/0.70      inference('demod', [status(thm)], ['178', '179'])).
% 0.47/0.70  thf('181', plain,
% 0.47/0.70      (~
% 0.47/0.70       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.47/0.70         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.47/0.70      inference('sat_resolution*', [status(thm)], ['27', '171', '172'])).
% 0.47/0.70  thf('182', plain,
% 0.47/0.70      (~ (m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 0.47/0.70          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.47/0.70      inference('simpl_trail', [status(thm)], ['180', '181'])).
% 0.47/0.70  thf('183', plain, ((zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)),
% 0.47/0.70      inference('clc', [status(thm)], ['177', '182'])).
% 0.47/0.70  thf('184', plain,
% 0.47/0.70      (![X60 : $i, X61 : $i]:
% 0.47/0.70         (((X60) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X60 @ X61))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.47/0.70  thf('185', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['183', '184'])).
% 0.47/0.70  thf('186', plain,
% 0.47/0.70      (![X20 : $i]:
% 0.47/0.70         (((k1_relat_1 @ X20) != (k1_xboole_0))
% 0.47/0.70          | ((X20) = (k1_xboole_0))
% 0.47/0.70          | ~ (v1_relat_1 @ X20))),
% 0.47/0.70      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.47/0.70  thf('187', plain,
% 0.47/0.70      ((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.70        | ~ (v1_relat_1 @ sk_C_1)
% 0.47/0.70        | ((sk_C_1) = (k1_xboole_0)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['185', '186'])).
% 0.47/0.70  thf('188', plain, ((v1_relat_1 @ sk_C_1)),
% 0.47/0.70      inference('sup-', [status(thm)], ['9', '10'])).
% 0.47/0.70  thf('189', plain,
% 0.47/0.70      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0)))),
% 0.47/0.70      inference('demod', [status(thm)], ['187', '188'])).
% 0.47/0.70  thf('190', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['189'])).
% 0.47/0.70  thf('191', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['136'])).
% 0.47/0.70  thf('192', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.70  thf('193', plain, ($false),
% 0.47/0.70      inference('demod', [status(thm)], ['174', '190', '191', '192'])).
% 0.47/0.70  
% 0.47/0.70  % SZS output end Refutation
% 0.47/0.70  
% 0.47/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
