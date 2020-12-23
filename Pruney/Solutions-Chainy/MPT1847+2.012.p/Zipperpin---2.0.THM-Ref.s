%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WFNbtsaC94

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 193 expanded)
%              Number of leaves         :   18 (  62 expanded)
%              Depth                    :   16
%              Number of atoms          :  527 (2523 expanded)
%              Number of equality atoms :   29 ( 136 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t14_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) )
                    = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) )
                  & ( v1_tex_2 @ B @ A ) )
               => ( v1_tex_2 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_pre_topc @ B @ A )
           => ! [C: $i] :
                ( ( m1_pre_topc @ C @ A )
               => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) )
                      = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) )
                    & ( v1_tex_2 @ B @ A ) )
                 => ( v1_tex_2 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_tex_2])).

thf('0',plain,(
    ~ ( v1_tex_2 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X2: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X2 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( g1_pre_topc @ X5 @ X6 )
       != ( g1_pre_topc @ X3 @ X4 ) )
      | ( X6 = X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_C )
        = X0 )
      | ~ ( l1_pre_topc @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_C )
        = X0 ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,
    ( ( u1_pre_topc @ sk_C )
    = ( u1_pre_topc @ sk_B ) ),
    inference(eq_res,[status(thm)],['16'])).

thf('18',plain,(
    ! [X2: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X2 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('19',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('21',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( g1_pre_topc @ X5 @ X6 )
       != ( g1_pre_topc @ X3 @ X4 ) )
      | ( X5 = X3 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_C )
        = X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_B ) )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( u1_pre_topc @ sk_C )
    = ( u1_pre_topc @ sk_B ) ),
    inference(eq_res,[status(thm)],['16'])).

thf('26',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_C )
        = X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(eq_res,[status(thm)],['27'])).

thf(t13_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                <=> ( v1_tex_2 @ B @ A ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( X11
       != ( u1_struct_0 @ X9 ) )
      | ~ ( v1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( v1_tex_2 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t13_tex_2])).

thf('30',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v1_tex_2 @ X9 @ X10 )
      | ~ ( v1_subset_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_pre_topc @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ( v1_tex_2 @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(eq_res,[status(thm)],['27'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ( v1_tex_2 @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ sk_C @ sk_A )
    | ~ ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('37',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( X11
       != ( u1_struct_0 @ X9 ) )
      | ~ ( v1_tex_2 @ X9 @ X10 )
      | ( v1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t13_tex_2])).

thf('38',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( v1_tex_2 @ X9 @ X10 )
      | ~ ( m1_pre_topc @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tex_2 @ sk_B @ sk_A )
    | ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_tex_2 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['34','35','43','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['0','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WFNbtsaC94
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:28:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 47 iterations in 0.026s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.46  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.46  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.21/0.46  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.46  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.46  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.21/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.46  thf(t14_tex_2, conjecture,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( l1_pre_topc @ A ) =>
% 0.21/0.46       ( ![B:$i]:
% 0.21/0.46         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.46           ( ![C:$i]:
% 0.21/0.46             ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.46               ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 0.21/0.46                     ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) & 
% 0.21/0.46                   ( v1_tex_2 @ B @ A ) ) =>
% 0.21/0.46                 ( v1_tex_2 @ C @ A ) ) ) ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i]:
% 0.21/0.46        ( ( l1_pre_topc @ A ) =>
% 0.21/0.46          ( ![B:$i]:
% 0.21/0.46            ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.46              ( ![C:$i]:
% 0.21/0.46                ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.46                  ( ( ( ( g1_pre_topc @
% 0.21/0.46                          ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 0.21/0.46                        ( g1_pre_topc @
% 0.21/0.46                          ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) & 
% 0.21/0.46                      ( v1_tex_2 @ B @ A ) ) =>
% 0.21/0.46                    ( v1_tex_2 @ C @ A ) ) ) ) ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t14_tex_2])).
% 0.21/0.46  thf('0', plain, (~ (v1_tex_2 @ sk_C @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t1_tsep_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( l1_pre_topc @ A ) =>
% 0.21/0.46       ( ![B:$i]:
% 0.21/0.46         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.46           ( m1_subset_1 @
% 0.21/0.46             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X7 : $i, X8 : $i]:
% 0.21/0.46         (~ (m1_pre_topc @ X7 @ X8)
% 0.21/0.46          | (m1_subset_1 @ (u1_struct_0 @ X7) @ 
% 0.21/0.46             (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.46          | ~ (l1_pre_topc @ X8))),
% 0.21/0.46      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.46        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.46           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.46  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.46        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.46      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.21/0.46         = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(dt_u1_pre_topc, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( l1_pre_topc @ A ) =>
% 0.21/0.46       ( m1_subset_1 @
% 0.21/0.46         ( u1_pre_topc @ A ) @ 
% 0.21/0.46         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X2 : $i]:
% 0.21/0.46         ((m1_subset_1 @ (u1_pre_topc @ X2) @ 
% 0.21/0.46           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2))))
% 0.21/0.46          | ~ (l1_pre_topc @ X2))),
% 0.21/0.46      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.21/0.46  thf(free_g1_pre_topc, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.46       ( ![C:$i,D:$i]:
% 0.21/0.46         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.21/0.46           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.21/0.46  thf('8', plain,
% 0.21/0.46      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.46         (((g1_pre_topc @ X5 @ X6) != (g1_pre_topc @ X3 @ X4))
% 0.21/0.46          | ((X6) = (X4))
% 0.21/0.46          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.21/0.46      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (~ (l1_pre_topc @ X0)
% 0.21/0.46          | ((u1_pre_topc @ X0) = (X1))
% 0.21/0.46          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.21/0.46              != (g1_pre_topc @ X2 @ X1)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.21/0.46            != (g1_pre_topc @ X1 @ X0))
% 0.21/0.46          | ((u1_pre_topc @ sk_C) = (X0))
% 0.21/0.46          | ~ (l1_pre_topc @ sk_C))),
% 0.21/0.46      inference('sup-', [status(thm)], ['6', '9'])).
% 0.21/0.46  thf('11', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(dt_m1_pre_topc, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( l1_pre_topc @ A ) =>
% 0.21/0.46       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.46  thf('12', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (~ (m1_pre_topc @ X0 @ X1) | (l1_pre_topc @ X0) | ~ (l1_pre_topc @ X1))),
% 0.21/0.46      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.46  thf('13', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.21/0.46      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.46  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('15', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.46      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.46  thf('16', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.21/0.46            != (g1_pre_topc @ X1 @ X0))
% 0.21/0.46          | ((u1_pre_topc @ sk_C) = (X0)))),
% 0.21/0.46      inference('demod', [status(thm)], ['10', '15'])).
% 0.21/0.46  thf('17', plain, (((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_B))),
% 0.21/0.46      inference('eq_res', [status(thm)], ['16'])).
% 0.21/0.46  thf('18', plain,
% 0.21/0.46      (![X2 : $i]:
% 0.21/0.46         ((m1_subset_1 @ (u1_pre_topc @ X2) @ 
% 0.21/0.46           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2))))
% 0.21/0.46          | ~ (l1_pre_topc @ X2))),
% 0.21/0.46      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.21/0.46  thf('19', plain,
% 0.21/0.46      (((m1_subset_1 @ (u1_pre_topc @ sk_B) @ 
% 0.21/0.46         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))
% 0.21/0.46        | ~ (l1_pre_topc @ sk_C))),
% 0.21/0.46      inference('sup+', [status(thm)], ['17', '18'])).
% 0.21/0.46  thf('20', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.46      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.46  thf('21', plain,
% 0.21/0.46      ((m1_subset_1 @ (u1_pre_topc @ sk_B) @ 
% 0.21/0.46        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 0.21/0.46      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.46  thf('22', plain,
% 0.21/0.46      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.46         (((g1_pre_topc @ X5 @ X6) != (g1_pre_topc @ X3 @ X4))
% 0.21/0.46          | ((X5) = (X3))
% 0.21/0.46          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.21/0.46      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.21/0.46  thf('23', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (((u1_struct_0 @ sk_C) = (X0))
% 0.21/0.46          | ((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_B))
% 0.21/0.46              != (g1_pre_topc @ X0 @ X1)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.46  thf('24', plain,
% 0.21/0.46      (((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.21/0.46         = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('25', plain, (((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_B))),
% 0.21/0.46      inference('eq_res', [status(thm)], ['16'])).
% 0.21/0.46  thf('26', plain,
% 0.21/0.46      (((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.21/0.46         = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_B)))),
% 0.21/0.46      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.46  thf('27', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (((u1_struct_0 @ sk_C) = (X0))
% 0.21/0.46          | ((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.21/0.46              != (g1_pre_topc @ X0 @ X1)))),
% 0.21/0.46      inference('demod', [status(thm)], ['23', '26'])).
% 0.21/0.46  thf('28', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B))),
% 0.21/0.46      inference('eq_res', [status(thm)], ['27'])).
% 0.21/0.46  thf(t13_tex_2, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( l1_pre_topc @ A ) =>
% 0.21/0.46       ( ![B:$i]:
% 0.21/0.46         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.46           ( ![C:$i]:
% 0.21/0.46             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.46               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.46                 ( ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) <=>
% 0.21/0.46                   ( v1_tex_2 @ B @ A ) ) ) ) ) ) ) ))).
% 0.21/0.46  thf('29', plain,
% 0.21/0.46      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.46         (~ (m1_pre_topc @ X9 @ X10)
% 0.21/0.46          | ((X11) != (u1_struct_0 @ X9))
% 0.21/0.46          | ~ (v1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.21/0.46          | (v1_tex_2 @ X9 @ X10)
% 0.21/0.46          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.46          | ~ (l1_pre_topc @ X10))),
% 0.21/0.46      inference('cnf', [status(esa)], [t13_tex_2])).
% 0.21/0.46  thf('30', plain,
% 0.21/0.46      (![X9 : $i, X10 : $i]:
% 0.21/0.46         (~ (l1_pre_topc @ X10)
% 0.21/0.46          | ~ (m1_subset_1 @ (u1_struct_0 @ X9) @ 
% 0.21/0.46               (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.46          | (v1_tex_2 @ X9 @ X10)
% 0.21/0.46          | ~ (v1_subset_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X10))
% 0.21/0.46          | ~ (m1_pre_topc @ X9 @ X10))),
% 0.21/0.46      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.46  thf('31', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.46             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.46          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.21/0.46          | ~ (v1_subset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.21/0.46          | (v1_tex_2 @ sk_C @ X0)
% 0.21/0.46          | ~ (l1_pre_topc @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['28', '30'])).
% 0.21/0.46  thf('32', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B))),
% 0.21/0.46      inference('eq_res', [status(thm)], ['27'])).
% 0.21/0.46  thf('33', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.46             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.46          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.21/0.46          | ~ (v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.21/0.46          | (v1_tex_2 @ sk_C @ X0)
% 0.21/0.46          | ~ (l1_pre_topc @ X0))),
% 0.21/0.46      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.46  thf('34', plain,
% 0.21/0.46      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.46        | (v1_tex_2 @ sk_C @ sk_A)
% 0.21/0.46        | ~ (v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.46        | ~ (m1_pre_topc @ sk_C @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['5', '33'])).
% 0.21/0.46  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('36', plain,
% 0.21/0.46      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.46        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.46      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.46  thf('37', plain,
% 0.21/0.46      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.46         (~ (m1_pre_topc @ X9 @ X10)
% 0.21/0.46          | ((X11) != (u1_struct_0 @ X9))
% 0.21/0.46          | ~ (v1_tex_2 @ X9 @ X10)
% 0.21/0.46          | (v1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.21/0.46          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.46          | ~ (l1_pre_topc @ X10))),
% 0.21/0.46      inference('cnf', [status(esa)], [t13_tex_2])).
% 0.21/0.46  thf('38', plain,
% 0.21/0.46      (![X9 : $i, X10 : $i]:
% 0.21/0.46         (~ (l1_pre_topc @ X10)
% 0.21/0.46          | ~ (m1_subset_1 @ (u1_struct_0 @ X9) @ 
% 0.21/0.46               (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.46          | (v1_subset_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X10))
% 0.21/0.46          | ~ (v1_tex_2 @ X9 @ X10)
% 0.21/0.46          | ~ (m1_pre_topc @ X9 @ X10))),
% 0.21/0.46      inference('simplify', [status(thm)], ['37'])).
% 0.21/0.46  thf('39', plain,
% 0.21/0.46      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.21/0.46        | ~ (v1_tex_2 @ sk_B @ sk_A)
% 0.21/0.46        | (v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.46        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['36', '38'])).
% 0.21/0.46  thf('40', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('41', plain, ((v1_tex_2 @ sk_B @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('43', plain,
% 0.21/0.46      ((v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.46      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.21/0.46  thf('44', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('45', plain, ((v1_tex_2 @ sk_C @ sk_A)),
% 0.21/0.46      inference('demod', [status(thm)], ['34', '35', '43', '44'])).
% 0.21/0.46  thf('46', plain, ($false), inference('demod', [status(thm)], ['0', '45'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
