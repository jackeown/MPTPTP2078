%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lQT8rXwJGd

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 579 expanded)
%              Number of leaves         :   39 ( 178 expanded)
%              Depth                    :   24
%              Number of atoms          :  762 (4920 expanded)
%              Number of equality atoms :   69 ( 283 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(t6_tex_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
              & ( v1_zfmisc_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ A )
           => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
                & ( v1_zfmisc_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r2_hidden @ X30 @ X31 )
      | ( v1_xboole_0 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('2',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r2_hidden @ sk_B_3 @ sk_A ),
    inference(clc,[status(thm)],['2','3'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X39: $i] :
      ( ~ ( v1_zfmisc_1 @ X39 )
      | ( X39
        = ( k6_domain_1 @ X39 @ ( sk_B_2 @ X39 ) ) )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('6',plain,(
    ! [X39: $i] :
      ( ~ ( v1_zfmisc_1 @ X39 )
      | ( m1_subset_1 @ ( sk_B_2 @ X39 ) @ X39 )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('7',plain,(
    ! [X37: $i,X38: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ X37 )
      | ( ( k6_domain_1 @ X37 @ X38 )
        = ( k1_tarski @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B_2 @ X0 ) )
        = ( k1_tarski @ ( sk_B_2 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_2 @ X0 ) )
        = ( k1_tarski @ ( sk_B_2 @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B_2 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B_2 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('12',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ( X13 = X10 )
      | ( X12
       != ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('13',plain,(
    ! [X10: $i,X13: $i] :
      ( ( X13 = X10 )
      | ~ ( r2_hidden @ X13 @ ( k1_tarski @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( X1
        = ( sk_B_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,
    ( ( sk_B_3
      = ( sk_B_2 @ sk_A ) )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','14'])).

thf('16',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( sk_B_3
      = ( sk_B_2 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( sk_B_3
    = ( sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X39: $i] :
      ( ~ ( v1_zfmisc_1 @ X39 )
      | ( X39
        = ( k6_domain_1 @ X39 @ ( sk_B_2 @ X39 ) ) )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('21',plain,
    ( ( sk_A
      = ( k6_domain_1 @ sk_A @ sk_B_3 ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X37: $i,X38: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ X37 )
      | ( ( k6_domain_1 @ X37 @ X38 )
        = ( k1_tarski @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('24',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B_3 )
      = ( k1_tarski @ sk_B_3 ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_3 )
    = ( k1_tarski @ sk_B_3 ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_3 ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['21','26','27'])).

thf('29',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( sk_A
    = ( k1_tarski @ sk_B_3 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf(rc3_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ~ ( v1_subset_1 @ B @ A )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('31',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X29 ) @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('32',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_B_1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( sk_B_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t43_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( ( C = k1_xboole_0 )
            & ( B
              = ( k1_tarski @ A ) ) )
        & ~ ( ( C
              = ( k1_tarski @ A ) )
            & ( B = k1_xboole_0 ) )
        & ~ ( ( C
              = ( k1_tarski @ A ) )
            & ( B
              = ( k1_tarski @ A ) ) )
        & ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( B
          = ( k1_tarski @ A ) )
        & ( C
          = ( k1_tarski @ A ) ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( B = k1_xboole_0 )
        & ( C
          = ( k1_tarski @ A ) ) ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
     => ( ( B
          = ( k1_tarski @ A ) )
        & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_7,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( zip_tseitin_2 @ C @ B @ A )
        & ~ ( zip_tseitin_1 @ C @ B @ A )
        & ~ ( zip_tseitin_0 @ C @ B @ A ) ) )).

thf('36',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_tarski @ X26 )
       != ( k2_xboole_0 @ X24 @ X25 ) )
      | ( zip_tseitin_2 @ X25 @ X24 @ X26 )
      | ( zip_tseitin_1 @ X25 @ X24 @ X26 )
      | ( zip_tseitin_0 @ X25 @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
       != X0 )
      | ( zip_tseitin_0 @ X0 @ ( sk_B_1 @ X0 ) @ X1 )
      | ( zip_tseitin_1 @ X0 @ ( sk_B_1 @ X0 ) @ X1 )
      | ( zip_tseitin_2 @ X0 @ ( sk_B_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X1: $i] :
      ( ( zip_tseitin_2 @ ( k1_tarski @ X1 ) @ ( sk_B_1 @ ( k1_tarski @ X1 ) ) @ X1 )
      | ( zip_tseitin_1 @ ( k1_tarski @ X1 ) @ ( sk_B_1 @ ( k1_tarski @ X1 ) ) @ X1 )
      | ( zip_tseitin_0 @ ( k1_tarski @ X1 ) @ ( sk_B_1 @ ( k1_tarski @ X1 ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( zip_tseitin_2 @ ( k1_tarski @ sk_B_3 ) @ ( sk_B_1 @ sk_A ) @ sk_B_3 )
    | ( zip_tseitin_0 @ ( k1_tarski @ sk_B_3 ) @ ( sk_B_1 @ ( k1_tarski @ sk_B_3 ) ) @ sk_B_3 )
    | ( zip_tseitin_1 @ ( k1_tarski @ sk_B_3 ) @ ( sk_B_1 @ ( k1_tarski @ sk_B_3 ) ) @ sk_B_3 ) ),
    inference('sup+',[status(thm)],['30','38'])).

thf('40',plain,
    ( sk_A
    = ( k1_tarski @ sk_B_3 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('41',plain,
    ( sk_A
    = ( k1_tarski @ sk_B_3 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('42',plain,
    ( sk_A
    = ( k1_tarski @ sk_B_3 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('43',plain,
    ( sk_A
    = ( k1_tarski @ sk_B_3 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('44',plain,
    ( sk_A
    = ( k1_tarski @ sk_B_3 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('45',plain,
    ( ( zip_tseitin_2 @ sk_A @ ( sk_B_1 @ sk_A ) @ sk_B_3 )
    | ( zip_tseitin_0 @ sk_A @ ( sk_B_1 @ sk_A ) @ sk_B_3 )
    | ( zip_tseitin_1 @ sk_A @ ( sk_B_1 @ sk_A ) @ sk_B_3 ) ),
    inference(demod,[status(thm)],['39','40','41','42','43','44'])).

thf('46',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( X22
        = ( k1_tarski @ X21 ) )
      | ~ ( zip_tseitin_2 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('47',plain,
    ( ( zip_tseitin_1 @ sk_A @ ( sk_B_1 @ sk_A ) @ sk_B_3 )
    | ( zip_tseitin_0 @ sk_A @ ( sk_B_1 @ sk_A ) @ sk_B_3 )
    | ( ( sk_B_1 @ sk_A )
      = ( k1_tarski @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( sk_A
    = ( k1_tarski @ sk_B_3 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('49',plain,
    ( ( zip_tseitin_1 @ sk_A @ ( sk_B_1 @ sk_A ) @ sk_B_3 )
    | ( zip_tseitin_0 @ sk_A @ ( sk_B_1 @ sk_A ) @ sk_B_3 )
    | ( ( sk_B_1 @ sk_A )
      = sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X18 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X19 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('51',plain,
    ( ( ( sk_B_1 @ sk_A )
      = sk_A )
    | ( zip_tseitin_0 @ sk_A @ ( sk_B_1 @ sk_A ) @ sk_B_3 )
    | ( ( sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X16
        = ( k1_tarski @ X15 ) )
      | ~ ( zip_tseitin_0 @ X17 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('53',plain,
    ( ( ( sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ( ( sk_B_1 @ sk_A )
      = sk_A )
    | ( ( sk_B_1 @ sk_A )
      = ( k1_tarski @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( sk_A
    = ( k1_tarski @ sk_B_3 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('55',plain,
    ( ( ( sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ( ( sk_B_1 @ sk_A )
      = sk_A )
    | ( ( sk_B_1 @ sk_A )
      = sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( sk_B_1 @ sk_A )
      = sk_A )
    | ( ( sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X29: $i] :
      ~ ( v1_subset_1 @ ( sk_B_1 @ X29 ) @ X29 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('58',plain,
    ( ~ ( v1_subset_1 @ sk_A @ sk_A )
    | ( ( sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_3 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_3 )
    = ( k1_tarski @ sk_B_3 ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('61',plain,(
    v1_subset_1 @ ( k1_tarski @ sk_B_3 ) @ sk_A ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( sk_A
    = ( k1_tarski @ sk_B_3 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('63',plain,(
    v1_subset_1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['58','63'])).

thf('65',plain,(
    ! [X29: $i] :
      ~ ( v1_subset_1 @ ( sk_B_1 @ X29 ) @ X29 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('66',plain,(
    ~ ( v1_subset_1 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('67',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('68',plain,(
    ! [X32: $i,X34: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( r1_tarski @ X32 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('69',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(cc2_subset_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( ~ ( v1_subset_1 @ B @ A )
           => ~ ( v1_xboole_0 @ B ) ) ) ) )).

thf('70',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( v1_xboole_0 @ X27 )
      | ( v1_subset_1 @ X27 @ X28 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[cc2_subset_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_subset_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('73',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('74',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ~ ( r1_tarski @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_subset_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['71','76'])).

thf('78',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['66','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lQT8rXwJGd
% 0.15/0.34  % Computer   : n019.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:04:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.21/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.59  % Solved by: fo/fo7.sh
% 0.21/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.59  % done 276 iterations in 0.132s
% 0.21/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.59  % SZS output start Refutation
% 0.21/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.59  thf(sk_B_2_type, type, sk_B_2: $i > $i).
% 0.21/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.59  thf(sk_B_3_type, type, sk_B_3: $i).
% 0.21/0.59  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.59  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.59  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.21/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.21/0.59  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.21/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.59  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.21/0.59  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.59  thf(t6_tex_2, conjecture,
% 0.21/0.59    (![A:$i]:
% 0.21/0.59     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.59       ( ![B:$i]:
% 0.21/0.59         ( ( m1_subset_1 @ B @ A ) =>
% 0.21/0.59           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.21/0.59                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.21/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.59    (~( ![A:$i]:
% 0.21/0.59        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.59          ( ![B:$i]:
% 0.21/0.59            ( ( m1_subset_1 @ B @ A ) =>
% 0.21/0.59              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.21/0.59                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.21/0.59    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.21/0.59  thf('0', plain, ((m1_subset_1 @ sk_B_3 @ sk_A)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf(t2_subset, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.59       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.59  thf('1', plain,
% 0.21/0.59      (![X30 : $i, X31 : $i]:
% 0.21/0.59         ((r2_hidden @ X30 @ X31)
% 0.21/0.59          | (v1_xboole_0 @ X31)
% 0.21/0.59          | ~ (m1_subset_1 @ X30 @ X31))),
% 0.21/0.59      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.59  thf('2', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_B_3 @ sk_A))),
% 0.21/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.59  thf('3', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('4', plain, ((r2_hidden @ sk_B_3 @ sk_A)),
% 0.21/0.59      inference('clc', [status(thm)], ['2', '3'])).
% 0.21/0.59  thf(d1_tex_2, axiom,
% 0.21/0.59    (![A:$i]:
% 0.21/0.59     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.59       ( ( v1_zfmisc_1 @ A ) <=>
% 0.21/0.59         ( ?[B:$i]:
% 0.21/0.59           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.21/0.59  thf('5', plain,
% 0.21/0.59      (![X39 : $i]:
% 0.21/0.59         (~ (v1_zfmisc_1 @ X39)
% 0.21/0.59          | ((X39) = (k6_domain_1 @ X39 @ (sk_B_2 @ X39)))
% 0.21/0.59          | (v1_xboole_0 @ X39))),
% 0.21/0.59      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.21/0.59  thf('6', plain,
% 0.21/0.59      (![X39 : $i]:
% 0.21/0.59         (~ (v1_zfmisc_1 @ X39)
% 0.21/0.59          | (m1_subset_1 @ (sk_B_2 @ X39) @ X39)
% 0.21/0.59          | (v1_xboole_0 @ X39))),
% 0.21/0.59      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.21/0.59  thf(redefinition_k6_domain_1, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.59       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.21/0.59  thf('7', plain,
% 0.21/0.59      (![X37 : $i, X38 : $i]:
% 0.21/0.59         ((v1_xboole_0 @ X37)
% 0.21/0.59          | ~ (m1_subset_1 @ X38 @ X37)
% 0.21/0.59          | ((k6_domain_1 @ X37 @ X38) = (k1_tarski @ X38)))),
% 0.21/0.59      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.21/0.59  thf('8', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         ((v1_xboole_0 @ X0)
% 0.21/0.59          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.59          | ((k6_domain_1 @ X0 @ (sk_B_2 @ X0)) = (k1_tarski @ (sk_B_2 @ X0)))
% 0.21/0.59          | (v1_xboole_0 @ X0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.59  thf('9', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (((k6_domain_1 @ X0 @ (sk_B_2 @ X0)) = (k1_tarski @ (sk_B_2 @ X0)))
% 0.21/0.59          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.59          | (v1_xboole_0 @ X0))),
% 0.21/0.59      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.59  thf('10', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (((X0) = (k1_tarski @ (sk_B_2 @ X0)))
% 0.21/0.59          | (v1_xboole_0 @ X0)
% 0.21/0.59          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.59          | (v1_xboole_0 @ X0)
% 0.21/0.59          | ~ (v1_zfmisc_1 @ X0))),
% 0.21/0.59      inference('sup+', [status(thm)], ['5', '9'])).
% 0.21/0.59  thf('11', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (~ (v1_zfmisc_1 @ X0)
% 0.21/0.59          | (v1_xboole_0 @ X0)
% 0.21/0.59          | ((X0) = (k1_tarski @ (sk_B_2 @ X0))))),
% 0.21/0.59      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.59  thf(d1_tarski, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.59  thf('12', plain,
% 0.21/0.59      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.21/0.59         (~ (r2_hidden @ X13 @ X12)
% 0.21/0.59          | ((X13) = (X10))
% 0.21/0.59          | ((X12) != (k1_tarski @ X10)))),
% 0.21/0.59      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.59  thf('13', plain,
% 0.21/0.59      (![X10 : $i, X13 : $i]:
% 0.21/0.59         (((X13) = (X10)) | ~ (r2_hidden @ X13 @ (k1_tarski @ X10)))),
% 0.21/0.59      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.59  thf('14', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         (~ (r2_hidden @ X1 @ X0)
% 0.21/0.59          | (v1_xboole_0 @ X0)
% 0.21/0.59          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.59          | ((X1) = (sk_B_2 @ X0)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['11', '13'])).
% 0.21/0.59  thf('15', plain,
% 0.21/0.59      ((((sk_B_3) = (sk_B_2 @ sk_A))
% 0.21/0.59        | ~ (v1_zfmisc_1 @ sk_A)
% 0.21/0.59        | (v1_xboole_0 @ sk_A))),
% 0.21/0.59      inference('sup-', [status(thm)], ['4', '14'])).
% 0.21/0.59  thf('16', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('17', plain, ((((sk_B_3) = (sk_B_2 @ sk_A)) | (v1_xboole_0 @ sk_A))),
% 0.21/0.59      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.59  thf('18', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('19', plain, (((sk_B_3) = (sk_B_2 @ sk_A))),
% 0.21/0.59      inference('clc', [status(thm)], ['17', '18'])).
% 0.21/0.59  thf('20', plain,
% 0.21/0.59      (![X39 : $i]:
% 0.21/0.59         (~ (v1_zfmisc_1 @ X39)
% 0.21/0.59          | ((X39) = (k6_domain_1 @ X39 @ (sk_B_2 @ X39)))
% 0.21/0.59          | (v1_xboole_0 @ X39))),
% 0.21/0.59      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.21/0.59  thf('21', plain,
% 0.21/0.59      ((((sk_A) = (k6_domain_1 @ sk_A @ sk_B_3))
% 0.21/0.59        | (v1_xboole_0 @ sk_A)
% 0.21/0.59        | ~ (v1_zfmisc_1 @ sk_A))),
% 0.21/0.59      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.59  thf('22', plain, ((m1_subset_1 @ sk_B_3 @ sk_A)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('23', plain,
% 0.21/0.59      (![X37 : $i, X38 : $i]:
% 0.21/0.59         ((v1_xboole_0 @ X37)
% 0.21/0.59          | ~ (m1_subset_1 @ X38 @ X37)
% 0.21/0.59          | ((k6_domain_1 @ X37 @ X38) = (k1_tarski @ X38)))),
% 0.21/0.59      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.21/0.59  thf('24', plain,
% 0.21/0.59      ((((k6_domain_1 @ sk_A @ sk_B_3) = (k1_tarski @ sk_B_3))
% 0.21/0.59        | (v1_xboole_0 @ sk_A))),
% 0.21/0.59      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.59  thf('25', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('26', plain, (((k6_domain_1 @ sk_A @ sk_B_3) = (k1_tarski @ sk_B_3))),
% 0.21/0.59      inference('clc', [status(thm)], ['24', '25'])).
% 0.21/0.59  thf('27', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('28', plain, ((((sk_A) = (k1_tarski @ sk_B_3)) | (v1_xboole_0 @ sk_A))),
% 0.21/0.59      inference('demod', [status(thm)], ['21', '26', '27'])).
% 0.21/0.59  thf('29', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('30', plain, (((sk_A) = (k1_tarski @ sk_B_3))),
% 0.21/0.59      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.59  thf(rc3_subset_1, axiom,
% 0.21/0.59    (![A:$i]:
% 0.21/0.59     ( ?[B:$i]:
% 0.21/0.59       ( ( ~( v1_subset_1 @ B @ A ) ) & 
% 0.21/0.59         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.21/0.59  thf('31', plain,
% 0.21/0.59      (![X29 : $i]: (m1_subset_1 @ (sk_B_1 @ X29) @ (k1_zfmisc_1 @ X29))),
% 0.21/0.59      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.21/0.59  thf(t3_subset, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.59  thf('32', plain,
% 0.21/0.59      (![X32 : $i, X33 : $i]:
% 0.21/0.59         ((r1_tarski @ X32 @ X33) | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33)))),
% 0.21/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.59  thf('33', plain, (![X0 : $i]: (r1_tarski @ (sk_B_1 @ X0) @ X0)),
% 0.21/0.59      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.59  thf(t12_xboole_1, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.59  thf('34', plain,
% 0.21/0.59      (![X5 : $i, X6 : $i]:
% 0.21/0.59         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.21/0.59      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.59  thf('35', plain, (![X0 : $i]: ((k2_xboole_0 @ (sk_B_1 @ X0) @ X0) = (X0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.59  thf(t43_zfmisc_1, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i]:
% 0.21/0.59     ( ~( ( ~( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.59          ( ~( ( ( C ) = ( k1_tarski @ A ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.59          ( ~( ( ( C ) = ( k1_tarski @ A ) ) & ( ( B ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.59          ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) ) ))).
% 0.21/0.59  thf(zf_stmt_1, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.21/0.59  thf(zf_stmt_2, axiom,
% 0.21/0.59    (![C:$i,B:$i,A:$i]:
% 0.21/0.59     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.21/0.59       ( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ))).
% 0.21/0.59  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.59  thf(zf_stmt_4, axiom,
% 0.21/0.59    (![C:$i,B:$i,A:$i]:
% 0.21/0.59     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.59       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ))).
% 0.21/0.59  thf(zf_stmt_5, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.21/0.59  thf(zf_stmt_6, axiom,
% 0.21/0.59    (![C:$i,B:$i,A:$i]:
% 0.21/0.59     ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.21/0.59       ( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.59  thf(zf_stmt_7, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i]:
% 0.21/0.59     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.21/0.59          ( ~( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.21/0.59          ( ~( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.21/0.59          ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ))).
% 0.21/0.59  thf('36', plain,
% 0.21/0.59      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.59         (((k1_tarski @ X26) != (k2_xboole_0 @ X24 @ X25))
% 0.21/0.59          | (zip_tseitin_2 @ X25 @ X24 @ X26)
% 0.21/0.59          | (zip_tseitin_1 @ X25 @ X24 @ X26)
% 0.21/0.59          | (zip_tseitin_0 @ X25 @ X24 @ X26))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.21/0.59  thf('37', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         (((k1_tarski @ X1) != (X0))
% 0.21/0.59          | (zip_tseitin_0 @ X0 @ (sk_B_1 @ X0) @ X1)
% 0.21/0.59          | (zip_tseitin_1 @ X0 @ (sk_B_1 @ X0) @ X1)
% 0.21/0.59          | (zip_tseitin_2 @ X0 @ (sk_B_1 @ X0) @ X1))),
% 0.21/0.59      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.59  thf('38', plain,
% 0.21/0.59      (![X1 : $i]:
% 0.21/0.59         ((zip_tseitin_2 @ (k1_tarski @ X1) @ (sk_B_1 @ (k1_tarski @ X1)) @ X1)
% 0.21/0.59          | (zip_tseitin_1 @ (k1_tarski @ X1) @ (sk_B_1 @ (k1_tarski @ X1)) @ 
% 0.21/0.59             X1)
% 0.21/0.59          | (zip_tseitin_0 @ (k1_tarski @ X1) @ (sk_B_1 @ (k1_tarski @ X1)) @ 
% 0.21/0.59             X1))),
% 0.21/0.59      inference('simplify', [status(thm)], ['37'])).
% 0.21/0.59  thf('39', plain,
% 0.21/0.59      (((zip_tseitin_2 @ (k1_tarski @ sk_B_3) @ (sk_B_1 @ sk_A) @ sk_B_3)
% 0.21/0.59        | (zip_tseitin_0 @ (k1_tarski @ sk_B_3) @ 
% 0.21/0.59           (sk_B_1 @ (k1_tarski @ sk_B_3)) @ sk_B_3)
% 0.21/0.59        | (zip_tseitin_1 @ (k1_tarski @ sk_B_3) @ 
% 0.21/0.59           (sk_B_1 @ (k1_tarski @ sk_B_3)) @ sk_B_3))),
% 0.21/0.59      inference('sup+', [status(thm)], ['30', '38'])).
% 0.21/0.59  thf('40', plain, (((sk_A) = (k1_tarski @ sk_B_3))),
% 0.21/0.59      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.59  thf('41', plain, (((sk_A) = (k1_tarski @ sk_B_3))),
% 0.21/0.59      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.59  thf('42', plain, (((sk_A) = (k1_tarski @ sk_B_3))),
% 0.21/0.59      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.59  thf('43', plain, (((sk_A) = (k1_tarski @ sk_B_3))),
% 0.21/0.59      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.59  thf('44', plain, (((sk_A) = (k1_tarski @ sk_B_3))),
% 0.21/0.59      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.59  thf('45', plain,
% 0.21/0.59      (((zip_tseitin_2 @ sk_A @ (sk_B_1 @ sk_A) @ sk_B_3)
% 0.21/0.59        | (zip_tseitin_0 @ sk_A @ (sk_B_1 @ sk_A) @ sk_B_3)
% 0.21/0.59        | (zip_tseitin_1 @ sk_A @ (sk_B_1 @ sk_A) @ sk_B_3))),
% 0.21/0.59      inference('demod', [status(thm)], ['39', '40', '41', '42', '43', '44'])).
% 0.21/0.59  thf('46', plain,
% 0.21/0.59      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.59         (((X22) = (k1_tarski @ X21)) | ~ (zip_tseitin_2 @ X23 @ X22 @ X21))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.59  thf('47', plain,
% 0.21/0.59      (((zip_tseitin_1 @ sk_A @ (sk_B_1 @ sk_A) @ sk_B_3)
% 0.21/0.59        | (zip_tseitin_0 @ sk_A @ (sk_B_1 @ sk_A) @ sk_B_3)
% 0.21/0.59        | ((sk_B_1 @ sk_A) = (k1_tarski @ sk_B_3)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.59  thf('48', plain, (((sk_A) = (k1_tarski @ sk_B_3))),
% 0.21/0.59      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.59  thf('49', plain,
% 0.21/0.59      (((zip_tseitin_1 @ sk_A @ (sk_B_1 @ sk_A) @ sk_B_3)
% 0.21/0.59        | (zip_tseitin_0 @ sk_A @ (sk_B_1 @ sk_A) @ sk_B_3)
% 0.21/0.59        | ((sk_B_1 @ sk_A) = (sk_A)))),
% 0.21/0.59      inference('demod', [status(thm)], ['47', '48'])).
% 0.21/0.59  thf('50', plain,
% 0.21/0.59      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.59         (((X18) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X19 @ X18 @ X20))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.59  thf('51', plain,
% 0.21/0.59      ((((sk_B_1 @ sk_A) = (sk_A))
% 0.21/0.59        | (zip_tseitin_0 @ sk_A @ (sk_B_1 @ sk_A) @ sk_B_3)
% 0.21/0.59        | ((sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.59  thf('52', plain,
% 0.21/0.59      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.59         (((X16) = (k1_tarski @ X15)) | ~ (zip_tseitin_0 @ X17 @ X16 @ X15))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.21/0.59  thf('53', plain,
% 0.21/0.59      ((((sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.21/0.59        | ((sk_B_1 @ sk_A) = (sk_A))
% 0.21/0.59        | ((sk_B_1 @ sk_A) = (k1_tarski @ sk_B_3)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.59  thf('54', plain, (((sk_A) = (k1_tarski @ sk_B_3))),
% 0.21/0.59      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.59  thf('55', plain,
% 0.21/0.59      ((((sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.21/0.59        | ((sk_B_1 @ sk_A) = (sk_A))
% 0.21/0.59        | ((sk_B_1 @ sk_A) = (sk_A)))),
% 0.21/0.59      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.59  thf('56', plain,
% 0.21/0.59      ((((sk_B_1 @ sk_A) = (sk_A)) | ((sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.59      inference('simplify', [status(thm)], ['55'])).
% 0.21/0.59  thf('57', plain, (![X29 : $i]: ~ (v1_subset_1 @ (sk_B_1 @ X29) @ X29)),
% 0.21/0.59      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.21/0.59  thf('58', plain,
% 0.21/0.59      ((~ (v1_subset_1 @ sk_A @ sk_A) | ((sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.59  thf('59', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_3) @ sk_A)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('60', plain, (((k6_domain_1 @ sk_A @ sk_B_3) = (k1_tarski @ sk_B_3))),
% 0.21/0.59      inference('clc', [status(thm)], ['24', '25'])).
% 0.21/0.59  thf('61', plain, ((v1_subset_1 @ (k1_tarski @ sk_B_3) @ sk_A)),
% 0.21/0.59      inference('demod', [status(thm)], ['59', '60'])).
% 0.21/0.59  thf('62', plain, (((sk_A) = (k1_tarski @ sk_B_3))),
% 0.21/0.59      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.59  thf('63', plain, ((v1_subset_1 @ sk_A @ sk_A)),
% 0.21/0.59      inference('demod', [status(thm)], ['61', '62'])).
% 0.21/0.59  thf('64', plain, (((sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.21/0.59      inference('demod', [status(thm)], ['58', '63'])).
% 0.21/0.59  thf('65', plain, (![X29 : $i]: ~ (v1_subset_1 @ (sk_B_1 @ X29) @ X29)),
% 0.21/0.59      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.21/0.59  thf('66', plain, (~ (v1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.21/0.59      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.59  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.59  thf('67', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.21/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.59  thf('68', plain,
% 0.21/0.59      (![X32 : $i, X34 : $i]:
% 0.21/0.59         ((m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X34)) | ~ (r1_tarski @ X32 @ X34))),
% 0.21/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.59  thf('69', plain,
% 0.21/0.59      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.59  thf(cc2_subset_1, axiom,
% 0.21/0.59    (![A:$i]:
% 0.21/0.59     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.59       ( ![B:$i]:
% 0.21/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.59           ( ( ~( v1_subset_1 @ B @ A ) ) => ( ~( v1_xboole_0 @ B ) ) ) ) ) ))).
% 0.21/0.59  thf('70', plain,
% 0.21/0.59      (![X27 : $i, X28 : $i]:
% 0.21/0.59         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 0.21/0.59          | ~ (v1_xboole_0 @ X27)
% 0.21/0.59          | (v1_subset_1 @ X27 @ X28)
% 0.21/0.59          | (v1_xboole_0 @ X28))),
% 0.21/0.59      inference('cnf', [status(esa)], [cc2_subset_1])).
% 0.21/0.59  thf('71', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         ((v1_xboole_0 @ X0)
% 0.21/0.59          | (v1_subset_1 @ k1_xboole_0 @ X0)
% 0.21/0.59          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['69', '70'])).
% 0.21/0.59  thf('72', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.21/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.59  thf(d1_xboole_0, axiom,
% 0.21/0.59    (![A:$i]:
% 0.21/0.59     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.59  thf('73', plain,
% 0.21/0.59      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.59  thf(t7_ordinal1, axiom,
% 0.21/0.59    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.59  thf('74', plain,
% 0.21/0.59      (![X35 : $i, X36 : $i]:
% 0.21/0.59         (~ (r2_hidden @ X35 @ X36) | ~ (r1_tarski @ X36 @ X35))),
% 0.21/0.59      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.59  thf('75', plain,
% 0.21/0.59      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['73', '74'])).
% 0.21/0.59  thf('76', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.59      inference('sup-', [status(thm)], ['72', '75'])).
% 0.21/0.59  thf('77', plain,
% 0.21/0.59      (![X0 : $i]: ((v1_xboole_0 @ X0) | (v1_subset_1 @ k1_xboole_0 @ X0))),
% 0.21/0.59      inference('demod', [status(thm)], ['71', '76'])).
% 0.21/0.59  thf('78', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('79', plain, ((v1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.21/0.59      inference('sup-', [status(thm)], ['77', '78'])).
% 0.21/0.59  thf('80', plain, ($false), inference('demod', [status(thm)], ['66', '79'])).
% 0.21/0.59  
% 0.21/0.59  % SZS output end Refutation
% 0.21/0.59  
% 0.43/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
