%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eevqqcu6sU

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:29 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 111 expanded)
%              Number of leaves         :   27 (  46 expanded)
%              Depth                    :   18
%              Number of atoms          :  536 ( 913 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t31_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_pre_topc @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
               => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_tops_2])).

thf('1',plain,(
    ~ ( m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ~ ( m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('4',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('5',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    r1_tarski @ sk_C_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_tarski @ X7 @ X5 )
      | ( X6
       != ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('17',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ( r1_tarski @ ( sk_C @ X0 @ sk_C_3 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_C @ X0 @ sk_C_3 ) @ ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B )
      | ( r1_tarski @ sk_C_3 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','18'])).

thf('20',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('21',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( l1_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('26',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_C @ X0 @ sk_C_3 ) @ ( k2_struct_0 @ sk_B ) )
      | ( r1_tarski @ sk_C_3 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ( r2_hidden @ X1 @ ( k2_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X1 @ ( sk_C @ X0 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_C @ X0 @ sk_C_3 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( sk_C @ X0 @ sk_C_3 ) ) @ ( k2_struct_0 @ sk_B ) )
      | ( r1_tarski @ sk_C_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','29'])).

thf('31',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ B @ A )
          <=> ( ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) )
                  <=> ? [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                        & ( r2_hidden @ D @ ( u1_pre_topc @ A ) )
                        & ( C
                          = ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) )
              & ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B @ A )
    <=> ( ( C
          = ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) )
        & ( r2_hidden @ D @ ( u1_pre_topc @ A ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ B @ A )
          <=> ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) )
                  <=> ? [D: $i] :
                        ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ( r1_tarski @ ( k2_struct_0 @ X18 ) @ ( k2_struct_0 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['22','23'])).

thf('36',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ( r1_tarski @ ( sk_C @ X0 @ sk_C_3 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( sk_C @ X0 @ sk_C_3 ) ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('40',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_C @ X0 @ sk_C_3 ) @ ( k2_struct_0 @ sk_A ) )
      | ( r1_tarski @ sk_C_3 @ X0 )
      | ( r1_tarski @ ( sk_C @ X0 @ sk_C_3 ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ( r1_tarski @ ( sk_C @ X0 @ sk_C_3 ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( X6
       != ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('44',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_3 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('47',plain,
    ( ( r1_tarski @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( r1_tarski @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r1_tarski @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('50',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['6','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eevqqcu6sU
% 0.16/0.37  % Computer   : n010.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 20:50:59 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.24/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.55  % Solved by: fo/fo7.sh
% 0.24/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.55  % done 164 iterations in 0.099s
% 0.24/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.55  % SZS output start Refutation
% 0.24/0.55  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.24/0.55  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.24/0.55  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.24/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.24/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.24/0.55  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.24/0.55  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.24/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.24/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.24/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.24/0.55  thf(d3_struct_0, axiom,
% 0.24/0.55    (![A:$i]:
% 0.24/0.55     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.24/0.55  thf('0', plain,
% 0.24/0.55      (![X12 : $i]:
% 0.24/0.55         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.24/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.24/0.55  thf(t31_tops_2, conjecture,
% 0.24/0.55    (![A:$i]:
% 0.24/0.55     ( ( l1_pre_topc @ A ) =>
% 0.24/0.55       ( ![B:$i]:
% 0.24/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.24/0.55           ( ![C:$i]:
% 0.24/0.55             ( ( m1_subset_1 @
% 0.24/0.55                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.24/0.55               ( m1_subset_1 @
% 0.24/0.55                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.24/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.55    (~( ![A:$i]:
% 0.24/0.55        ( ( l1_pre_topc @ A ) =>
% 0.24/0.55          ( ![B:$i]:
% 0.24/0.55            ( ( m1_pre_topc @ B @ A ) =>
% 0.24/0.55              ( ![C:$i]:
% 0.24/0.55                ( ( m1_subset_1 @
% 0.24/0.55                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.24/0.55                  ( m1_subset_1 @
% 0.24/0.55                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.24/0.55    inference('cnf.neg', [status(esa)], [t31_tops_2])).
% 0.24/0.55  thf('1', plain,
% 0.24/0.55      (~ (m1_subset_1 @ sk_C_3 @ 
% 0.24/0.55          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf('2', plain,
% 0.24/0.55      ((~ (m1_subset_1 @ sk_C_3 @ 
% 0.24/0.55           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.55        | ~ (l1_struct_0 @ sk_A))),
% 0.24/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.24/0.55  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf(dt_l1_pre_topc, axiom,
% 0.24/0.55    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.24/0.55  thf('4', plain, (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.24/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.24/0.55  thf('5', plain, ((l1_struct_0 @ sk_A)),
% 0.24/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.24/0.55  thf('6', plain,
% 0.24/0.55      (~ (m1_subset_1 @ sk_C_3 @ 
% 0.24/0.55          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))),
% 0.24/0.55      inference('demod', [status(thm)], ['2', '5'])).
% 0.24/0.55  thf(d3_tarski, axiom,
% 0.24/0.55    (![A:$i,B:$i]:
% 0.24/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.24/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.24/0.55  thf('7', plain,
% 0.24/0.55      (![X1 : $i, X3 : $i]:
% 0.24/0.55         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.24/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.24/0.55  thf('8', plain,
% 0.24/0.55      (![X12 : $i]:
% 0.24/0.55         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.24/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.24/0.55  thf('9', plain,
% 0.24/0.55      (![X1 : $i, X3 : $i]:
% 0.24/0.55         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.24/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.24/0.55  thf('10', plain,
% 0.24/0.55      ((m1_subset_1 @ sk_C_3 @ 
% 0.24/0.55        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf(t3_subset, axiom,
% 0.24/0.55    (![A:$i,B:$i]:
% 0.24/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.24/0.55  thf('11', plain,
% 0.24/0.55      (![X9 : $i, X10 : $i]:
% 0.24/0.55         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.24/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.24/0.55  thf('12', plain,
% 0.24/0.55      ((r1_tarski @ sk_C_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.24/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.24/0.55  thf('13', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.24/0.55          | (r2_hidden @ X0 @ X2)
% 0.24/0.55          | ~ (r1_tarski @ X1 @ X2))),
% 0.24/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.24/0.55  thf('14', plain,
% 0.24/0.55      (![X0 : $i]:
% 0.24/0.55         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.24/0.55          | ~ (r2_hidden @ X0 @ sk_C_3))),
% 0.24/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.24/0.55  thf('15', plain,
% 0.24/0.55      (![X0 : $i]:
% 0.24/0.55         ((r1_tarski @ sk_C_3 @ X0)
% 0.24/0.55          | (r2_hidden @ (sk_C @ X0 @ sk_C_3) @ 
% 0.24/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.24/0.55      inference('sup-', [status(thm)], ['9', '14'])).
% 0.24/0.55  thf(d1_zfmisc_1, axiom,
% 0.24/0.55    (![A:$i,B:$i]:
% 0.24/0.55     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.24/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.24/0.55  thf('16', plain,
% 0.24/0.55      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.24/0.55         (~ (r2_hidden @ X7 @ X6)
% 0.24/0.55          | (r1_tarski @ X7 @ X5)
% 0.24/0.55          | ((X6) != (k1_zfmisc_1 @ X5)))),
% 0.24/0.55      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.24/0.55  thf('17', plain,
% 0.24/0.55      (![X5 : $i, X7 : $i]:
% 0.24/0.55         ((r1_tarski @ X7 @ X5) | ~ (r2_hidden @ X7 @ (k1_zfmisc_1 @ X5)))),
% 0.24/0.55      inference('simplify', [status(thm)], ['16'])).
% 0.24/0.55  thf('18', plain,
% 0.24/0.55      (![X0 : $i]:
% 0.24/0.55         ((r1_tarski @ sk_C_3 @ X0)
% 0.24/0.55          | (r1_tarski @ (sk_C @ X0 @ sk_C_3) @ (u1_struct_0 @ sk_B)))),
% 0.24/0.55      inference('sup-', [status(thm)], ['15', '17'])).
% 0.24/0.55  thf('19', plain,
% 0.24/0.55      (![X0 : $i]:
% 0.24/0.55         ((r1_tarski @ (sk_C @ X0 @ sk_C_3) @ (k2_struct_0 @ sk_B))
% 0.24/0.55          | ~ (l1_struct_0 @ sk_B)
% 0.24/0.55          | (r1_tarski @ sk_C_3 @ X0))),
% 0.24/0.55      inference('sup+', [status(thm)], ['8', '18'])).
% 0.24/0.55  thf('20', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf(dt_m1_pre_topc, axiom,
% 0.24/0.55    (![A:$i]:
% 0.24/0.55     ( ( l1_pre_topc @ A ) =>
% 0.24/0.55       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.24/0.55  thf('21', plain,
% 0.24/0.55      (![X24 : $i, X25 : $i]:
% 0.24/0.55         (~ (m1_pre_topc @ X24 @ X25)
% 0.24/0.55          | (l1_pre_topc @ X24)
% 0.24/0.55          | ~ (l1_pre_topc @ X25))),
% 0.24/0.55      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.24/0.55  thf('22', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.24/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.24/0.55  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf('24', plain, ((l1_pre_topc @ sk_B)),
% 0.24/0.55      inference('demod', [status(thm)], ['22', '23'])).
% 0.24/0.55  thf('25', plain,
% 0.24/0.55      (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.24/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.24/0.55  thf('26', plain, ((l1_struct_0 @ sk_B)),
% 0.24/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.24/0.55  thf('27', plain,
% 0.24/0.55      (![X0 : $i]:
% 0.24/0.55         ((r1_tarski @ (sk_C @ X0 @ sk_C_3) @ (k2_struct_0 @ sk_B))
% 0.24/0.55          | (r1_tarski @ sk_C_3 @ X0))),
% 0.24/0.55      inference('demod', [status(thm)], ['19', '26'])).
% 0.24/0.55  thf('28', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.24/0.55          | (r2_hidden @ X0 @ X2)
% 0.24/0.55          | ~ (r1_tarski @ X1 @ X2))),
% 0.24/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.24/0.55  thf('29', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i]:
% 0.24/0.55         ((r1_tarski @ sk_C_3 @ X0)
% 0.24/0.55          | (r2_hidden @ X1 @ (k2_struct_0 @ sk_B))
% 0.24/0.55          | ~ (r2_hidden @ X1 @ (sk_C @ X0 @ sk_C_3)))),
% 0.24/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.24/0.55  thf('30', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i]:
% 0.24/0.55         ((r1_tarski @ (sk_C @ X0 @ sk_C_3) @ X1)
% 0.24/0.55          | (r2_hidden @ (sk_C @ X1 @ (sk_C @ X0 @ sk_C_3)) @ 
% 0.24/0.55             (k2_struct_0 @ sk_B))
% 0.24/0.55          | (r1_tarski @ sk_C_3 @ X0))),
% 0.24/0.55      inference('sup-', [status(thm)], ['7', '29'])).
% 0.24/0.55  thf('31', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf(d9_pre_topc, axiom,
% 0.24/0.55    (![A:$i]:
% 0.24/0.55     ( ( l1_pre_topc @ A ) =>
% 0.24/0.55       ( ![B:$i]:
% 0.24/0.55         ( ( l1_pre_topc @ B ) =>
% 0.24/0.55           ( ( m1_pre_topc @ B @ A ) <=>
% 0.24/0.55             ( ( ![C:$i]:
% 0.24/0.55                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.24/0.55                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.24/0.55                     ( ?[D:$i]:
% 0.24/0.55                       ( ( m1_subset_1 @
% 0.24/0.55                           D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.24/0.55                         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.24/0.55                         ( ( C ) =
% 0.24/0.55                           ( k9_subset_1 @
% 0.24/0.55                             ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) ) ) ) & 
% 0.24/0.55               ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) ))).
% 0.24/0.55  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.24/0.55  thf(zf_stmt_2, axiom,
% 0.24/0.55    (![D:$i,C:$i,B:$i,A:$i]:
% 0.24/0.55     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.24/0.55       ( ( ( C ) =
% 0.24/0.55           ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) & 
% 0.24/0.55         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.24/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.24/0.55  thf(zf_stmt_3, axiom,
% 0.24/0.55    (![A:$i]:
% 0.24/0.55     ( ( l1_pre_topc @ A ) =>
% 0.24/0.55       ( ![B:$i]:
% 0.24/0.55         ( ( l1_pre_topc @ B ) =>
% 0.24/0.55           ( ( m1_pre_topc @ B @ A ) <=>
% 0.24/0.55             ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) & 
% 0.24/0.55               ( ![C:$i]:
% 0.24/0.55                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.24/0.55                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.24/0.55                     ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.24/0.55  thf('32', plain,
% 0.24/0.55      (![X18 : $i, X19 : $i]:
% 0.24/0.55         (~ (l1_pre_topc @ X18)
% 0.24/0.55          | ~ (m1_pre_topc @ X18 @ X19)
% 0.24/0.55          | (r1_tarski @ (k2_struct_0 @ X18) @ (k2_struct_0 @ X19))
% 0.24/0.55          | ~ (l1_pre_topc @ X19))),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.24/0.55  thf('33', plain,
% 0.24/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.24/0.55        | (r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 0.24/0.55        | ~ (l1_pre_topc @ sk_B))),
% 0.24/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.24/0.55  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf('35', plain, ((l1_pre_topc @ sk_B)),
% 0.24/0.55      inference('demod', [status(thm)], ['22', '23'])).
% 0.24/0.55  thf('36', plain, ((r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))),
% 0.24/0.55      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.24/0.55  thf('37', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.24/0.55          | (r2_hidden @ X0 @ X2)
% 0.24/0.55          | ~ (r1_tarski @ X1 @ X2))),
% 0.24/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.24/0.55  thf('38', plain,
% 0.24/0.55      (![X0 : $i]:
% 0.24/0.55         ((r2_hidden @ X0 @ (k2_struct_0 @ sk_A))
% 0.24/0.55          | ~ (r2_hidden @ X0 @ (k2_struct_0 @ sk_B)))),
% 0.24/0.55      inference('sup-', [status(thm)], ['36', '37'])).
% 0.24/0.55  thf('39', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i]:
% 0.24/0.55         ((r1_tarski @ sk_C_3 @ X0)
% 0.24/0.55          | (r1_tarski @ (sk_C @ X0 @ sk_C_3) @ X1)
% 0.24/0.55          | (r2_hidden @ (sk_C @ X1 @ (sk_C @ X0 @ sk_C_3)) @ 
% 0.24/0.55             (k2_struct_0 @ sk_A)))),
% 0.24/0.55      inference('sup-', [status(thm)], ['30', '38'])).
% 0.24/0.55  thf('40', plain,
% 0.24/0.55      (![X1 : $i, X3 : $i]:
% 0.24/0.55         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.24/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.24/0.55  thf('41', plain,
% 0.24/0.55      (![X0 : $i]:
% 0.24/0.55         ((r1_tarski @ (sk_C @ X0 @ sk_C_3) @ (k2_struct_0 @ sk_A))
% 0.24/0.55          | (r1_tarski @ sk_C_3 @ X0)
% 0.24/0.55          | (r1_tarski @ (sk_C @ X0 @ sk_C_3) @ (k2_struct_0 @ sk_A)))),
% 0.24/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.24/0.55  thf('42', plain,
% 0.24/0.55      (![X0 : $i]:
% 0.24/0.55         ((r1_tarski @ sk_C_3 @ X0)
% 0.24/0.55          | (r1_tarski @ (sk_C @ X0 @ sk_C_3) @ (k2_struct_0 @ sk_A)))),
% 0.24/0.55      inference('simplify', [status(thm)], ['41'])).
% 0.24/0.55  thf('43', plain,
% 0.24/0.55      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.24/0.55         (~ (r1_tarski @ X4 @ X5)
% 0.24/0.55          | (r2_hidden @ X4 @ X6)
% 0.24/0.55          | ((X6) != (k1_zfmisc_1 @ X5)))),
% 0.24/0.55      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.24/0.55  thf('44', plain,
% 0.24/0.55      (![X4 : $i, X5 : $i]:
% 0.24/0.55         ((r2_hidden @ X4 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X4 @ X5))),
% 0.24/0.55      inference('simplify', [status(thm)], ['43'])).
% 0.24/0.55  thf('45', plain,
% 0.24/0.55      (![X0 : $i]:
% 0.24/0.55         ((r1_tarski @ sk_C_3 @ X0)
% 0.24/0.55          | (r2_hidden @ (sk_C @ X0 @ sk_C_3) @ 
% 0.24/0.55             (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))),
% 0.24/0.55      inference('sup-', [status(thm)], ['42', '44'])).
% 0.24/0.55  thf('46', plain,
% 0.24/0.55      (![X1 : $i, X3 : $i]:
% 0.24/0.55         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.24/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.24/0.55  thf('47', plain,
% 0.24/0.55      (((r1_tarski @ sk_C_3 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.55        | (r1_tarski @ sk_C_3 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))),
% 0.24/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.24/0.55  thf('48', plain,
% 0.24/0.55      ((r1_tarski @ sk_C_3 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.24/0.55      inference('simplify', [status(thm)], ['47'])).
% 0.24/0.55  thf('49', plain,
% 0.24/0.55      (![X9 : $i, X11 : $i]:
% 0.24/0.55         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.24/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.24/0.55  thf('50', plain,
% 0.24/0.55      ((m1_subset_1 @ sk_C_3 @ 
% 0.24/0.55        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))),
% 0.24/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.24/0.55  thf('51', plain, ($false), inference('demod', [status(thm)], ['6', '50'])).
% 0.24/0.55  
% 0.24/0.55  % SZS output end Refutation
% 0.24/0.55  
% 0.24/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
