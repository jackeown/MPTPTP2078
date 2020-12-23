%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0401+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uL5mVziZDN

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:55 EST 2020

% Result     : Theorem 7.80s
% Output     : Refutation 7.80s
% Verified   : 
% Statistics : Number of formulae       :   42 (  48 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :   11
%              Number of atoms          :  192 ( 248 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_10_type,type,(
    sk_B_10: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_C_24_type,type,(
    sk_C_24: $i )).

thf(t24_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ ( B @ ( k1_tarski @ A ) ) )
     => ! [C: $i] :
          ( ( r2_hidden @ ( C @ B ) )
         => ( r1_tarski @ ( C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_setfam_1 @ ( B @ ( k1_tarski @ A ) ) )
       => ! [C: $i] :
            ( ( r2_hidden @ ( C @ B ) )
           => ( r1_tarski @ ( C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( sk_C_24 @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_setfam_1 @ ( sk_B_10 @ ( k1_tarski @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ ( A @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A @ ( k3_tarski @ B ) ) ) ) )).

thf('2',plain,(
    ! [X1838: $i,X1839: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X1838 @ ( k3_tarski @ X1839 ) ) )
      | ~ ( r1_setfam_1 @ ( X1838 @ X1839 ) ) ) ),
    inference(cnf,[status(esa)],[t18_setfam_1])).

thf('3',plain,(
    r1_tarski @ ( k3_tarski @ sk_B_10 @ ( k3_tarski @ ( k1_tarski @ sk_A_2 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('4',plain,(
    ! [X1281: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X1281 ) )
      = X1281 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('5',plain,(
    r1_tarski @ ( k3_tarski @ sk_B_10 @ sk_A_2 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) ) )).

thf('6',plain,(
    ! [X1072: $i] :
      ( r1_tarski @ ( X1072 @ ( k1_zfmisc_1 @ ( k3_tarski @ X1072 ) ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf('7',plain,(
    r2_hidden @ ( sk_C_24 @ sk_B_10 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A @ B ) )
    <=> ( r2_hidden @ ( A @ B ) ) ) )).

thf('8',plain,(
    ! [X1021: $i,X1023: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1021 @ X1023 ) )
      | ~ ( r2_hidden @ ( X1021 @ X1023 ) ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('9',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_24 @ sk_B_10 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( B @ C ) ) )
     => ( r1_tarski @ ( A @ C ) ) ) )).

thf('10',plain,(
    ! [X184: $i,X185: $i,X186: $i] :
      ( ~ ( r1_tarski @ ( X184 @ X185 ) )
      | ~ ( r1_tarski @ ( X185 @ X186 ) )
      | ( r1_tarski @ ( X184 @ X186 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_C_24 @ X0 ) )
      | ~ ( r1_tarski @ ( sk_B_10 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_24 @ ( k1_zfmisc_1 @ ( k3_tarski @ sk_B_10 ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X1021: $i,X1022: $i] :
      ( ( r2_hidden @ ( X1021 @ X1022 ) )
      | ~ ( r1_tarski @ ( k1_tarski @ X1021 @ X1022 ) ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('14',plain,(
    r2_hidden @ ( sk_C_24 @ ( k1_zfmisc_1 @ ( k3_tarski @ sk_B_10 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ ( A @ B ) )
     => ( m1_subset_1 @ ( A @ B ) ) ) )).

thf('15',plain,(
    ! [X1842: $i,X1843: $i] :
      ( ( m1_subset_1 @ ( X1842 @ X1843 ) )
      | ~ ( r2_hidden @ ( X1842 @ X1843 ) ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('16',plain,(
    m1_subset_1 @ ( sk_C_24 @ ( k1_zfmisc_1 @ ( k3_tarski @ sk_B_10 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( A @ ( k1_zfmisc_1 @ B ) ) )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('17',plain,(
    ! [X1852: $i,X1853: $i] :
      ( ( r1_tarski @ ( X1852 @ X1853 ) )
      | ~ ( m1_subset_1 @ ( X1852 @ ( k1_zfmisc_1 @ X1853 ) ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    r1_tarski @ ( sk_C_24 @ ( k3_tarski @ sk_B_10 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X184: $i,X185: $i,X186: $i] :
      ( ~ ( r1_tarski @ ( X184 @ X185 ) )
      | ~ ( r1_tarski @ ( X185 @ X186 ) )
      | ( r1_tarski @ ( X184 @ X186 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_C_24 @ X0 ) )
      | ~ ( r1_tarski @ ( k3_tarski @ sk_B_10 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ ( sk_C_24 @ sk_A_2 ) ),
    inference('sup-',[status(thm)],['5','20'])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['0','21'])).

%------------------------------------------------------------------------------
