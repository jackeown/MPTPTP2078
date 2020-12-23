%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0428+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.adBizmHAYx

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:55 EST 2020

% Result     : Theorem 8.71s
% Output     : Refutation 8.71s
% Verified   : 
% Statistics : Number of formulae       :   51 (  76 expanded)
%              Number of leaves         :   15 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :  319 ( 602 expanded)
%              Number of equality atoms :   30 (  53 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(sk_B_11_type,type,(
    sk_B_11: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t60_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
     => ( ( m1_setfam_1 @ ( B @ A ) )
      <=> ( ( k5_setfam_1 @ ( A @ B ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
       => ( ( m1_setfam_1 @ ( B @ A ) )
        <=> ( ( k5_setfam_1 @ ( A @ B ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t60_setfam_1])).

thf('0',plain,
    ( ( ( k5_setfam_1 @ ( sk_A_2 @ sk_B_11 ) )
     != sk_A_2 )
    | ~ ( m1_setfam_1 @ ( sk_B_11 @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k5_setfam_1 @ ( sk_A_2 @ sk_B_11 ) )
     != sk_A_2 )
    | ~ ( m1_setfam_1 @ ( sk_B_11 @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ ( sk_B_11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( A @ ( k1_zfmisc_1 @ B ) ) )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('3',plain,(
    ! [X1955: $i,X1956: $i] :
      ( ( r1_tarski @ ( X1955 @ X1956 ) )
      | ~ ( m1_subset_1 @ ( X1955 @ ( k1_zfmisc_1 @ X1956 ) ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    r1_tarski @ ( sk_B_11 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A @ ( k3_tarski @ B ) ) ) ) )).

thf('5',plain,(
    ! [X1439: $i,X1440: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X1439 @ ( k3_tarski @ X1440 ) ) )
      | ~ ( r1_tarski @ ( X1439 @ X1440 ) ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('6',plain,(
    r1_tarski @ ( k3_tarski @ sk_B_11 @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A_2 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('7',plain,(
    ! [X1447: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X1447 ) )
      = X1447 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('8',plain,(
    r1_tarski @ ( k3_tarski @ sk_B_11 @ sk_A_2 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k5_setfam_1 @ ( sk_A_2 @ sk_B_11 ) )
      = sk_A_2 )
    | ( m1_setfam_1 @ ( sk_B_11 @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( m1_setfam_1 @ ( sk_B_11 @ sk_A_2 ) )
   <= ( m1_setfam_1 @ ( sk_B_11 @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['9'])).

thf(d12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_setfam_1 @ ( B @ A ) )
    <=> ( r1_tarski @ ( A @ ( k3_tarski @ B ) ) ) ) )).

thf('11',plain,(
    ! [X1815: $i,X1816: $i] :
      ( ( r1_tarski @ ( X1815 @ ( k3_tarski @ X1816 ) ) )
      | ~ ( m1_setfam_1 @ ( X1816 @ X1815 ) ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('12',plain,
    ( ( r1_tarski @ ( sk_A_2 @ ( k3_tarski @ sk_B_11 ) ) )
   <= ( m1_setfam_1 @ ( sk_B_11 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('13',plain,(
    ! [X78: $i,X80: $i] :
      ( ( X78 = X80 )
      | ~ ( r1_tarski @ ( X80 @ X78 ) )
      | ~ ( r1_tarski @ ( X78 @ X80 ) ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,
    ( ( ~ ( r1_tarski @ ( k3_tarski @ sk_B_11 @ sk_A_2 ) )
      | ( ( k3_tarski @ sk_B_11 )
        = sk_A_2 ) )
   <= ( m1_setfam_1 @ ( sk_B_11 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k3_tarski @ sk_B_11 )
      = sk_A_2 )
   <= ( m1_setfam_1 @ ( sk_B_11 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    m1_subset_1 @ ( sk_B_11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
     => ( ( k5_setfam_1 @ ( A @ B ) )
        = ( k3_tarski @ B ) ) ) )).

thf('17',plain,(
    ! [X1906: $i,X1907: $i] :
      ( ( ( k5_setfam_1 @ ( X1907 @ X1906 ) )
        = ( k3_tarski @ X1906 ) )
      | ~ ( m1_subset_1 @ ( X1906 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1907 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('18',plain,
    ( ( k5_setfam_1 @ ( sk_A_2 @ sk_B_11 ) )
    = ( k3_tarski @ sk_B_11 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k5_setfam_1 @ ( sk_A_2 @ sk_B_11 ) )
     != sk_A_2 )
   <= ( ( k5_setfam_1 @ ( sk_A_2 @ sk_B_11 ) )
     != sk_A_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ( ( k3_tarski @ sk_B_11 )
     != sk_A_2 )
   <= ( ( k5_setfam_1 @ ( sk_A_2 @ sk_B_11 ) )
     != sk_A_2 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_A_2 != sk_A_2 )
   <= ( ( ( k5_setfam_1 @ ( sk_A_2 @ sk_B_11 ) )
       != sk_A_2 )
      & ( m1_setfam_1 @ ( sk_B_11 @ sk_A_2 ) ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,
    ( ( ( k5_setfam_1 @ ( sk_A_2 @ sk_B_11 ) )
      = sk_A_2 )
    | ~ ( m1_setfam_1 @ ( sk_B_11 @ sk_A_2 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( ( k5_setfam_1 @ ( sk_A_2 @ sk_B_11 ) )
      = sk_A_2 )
    | ( m1_setfam_1 @ ( sk_B_11 @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['9'])).

thf('24',plain,
    ( ( k5_setfam_1 @ ( sk_A_2 @ sk_B_11 ) )
    = ( k3_tarski @ sk_B_11 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('25',plain,
    ( ( ( k5_setfam_1 @ ( sk_A_2 @ sk_B_11 ) )
      = sk_A_2 )
   <= ( ( k5_setfam_1 @ ( sk_A_2 @ sk_B_11 ) )
      = sk_A_2 ) ),
    inference(split,[status(esa)],['9'])).

thf('26',plain,
    ( ( ( k3_tarski @ sk_B_11 )
      = sk_A_2 )
   <= ( ( k5_setfam_1 @ ( sk_A_2 @ sk_B_11 ) )
      = sk_A_2 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X78: $i,X79: $i] :
      ( ( r1_tarski @ ( X78 @ X79 ) )
      | ( X78 != X79 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X79: $i] :
      ( r1_tarski @ ( X79 @ X79 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X1815: $i,X1817: $i] :
      ( ( m1_setfam_1 @ ( X1817 @ X1815 ) )
      | ~ ( r1_tarski @ ( X1815 @ ( k3_tarski @ X1817 ) ) ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( m1_setfam_1 @ ( X0 @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( m1_setfam_1 @ ( sk_B_11 @ sk_A_2 ) )
   <= ( ( k5_setfam_1 @ ( sk_A_2 @ sk_B_11 ) )
      = sk_A_2 ) ),
    inference('sup+',[status(thm)],['26','30'])).

thf('32',plain,
    ( ~ ( m1_setfam_1 @ ( sk_B_11 @ sk_A_2 ) )
   <= ~ ( m1_setfam_1 @ ( sk_B_11 @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,
    ( ( ( k5_setfam_1 @ ( sk_A_2 @ sk_B_11 ) )
     != sk_A_2 )
    | ( m1_setfam_1 @ ( sk_B_11 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','22','23','33'])).

%------------------------------------------------------------------------------
