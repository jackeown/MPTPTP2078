%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1677+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:14 EST 2020

% Result     : Theorem 20.02s
% Output     : CNFRefutation 20.17s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 258 expanded)
%              Number of leaves         :   41 ( 108 expanded)
%              Depth                    :   30
%              Number of atoms          :  386 (1595 expanded)
%              Number of equality atoms :   21 ( 154 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r2_hidden > r1_tarski > m1_subset_1 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_finset_1 > l1_orders_2 > k2_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k2_yellow_0,type,(
    k2_yellow_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_200,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( ! [D] :
                        ( ( v1_finset_1(D)
                          & m1_subset_1(D,k1_zfmisc_1(B)) )
                       => ( D != k1_xboole_0
                         => r2_yellow_0(A,D) ) )
                    & ! [D] :
                        ( m1_subset_1(D,u1_struct_0(A))
                       => ~ ( r2_hidden(D,C)
                            & ! [E] :
                                ( ( v1_finset_1(E)
                                  & m1_subset_1(E,k1_zfmisc_1(B)) )
                               => ~ ( r2_yellow_0(A,E)
                                    & D = k2_yellow_0(A,E) ) ) ) )
                    & ! [D] :
                        ( ( v1_finset_1(D)
                          & m1_subset_1(D,k1_zfmisc_1(B)) )
                       => ( D != k1_xboole_0
                         => r2_hidden(k2_yellow_0(A,D),C) ) ) )
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r1_lattice3(A,B,D)
                      <=> r1_lattice3(A,C,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_waybel_0)).

tff(f_90,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_63,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_86,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_62,axiom,(
    ! [A] : v1_finset_1(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).

tff(f_141,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => ! [D] :
              ( m1_subset_1(D,u1_struct_0(A))
             => ( ( r1_lattice3(A,C,D)
                 => r1_lattice3(A,B,D) )
                & ( r2_lattice3(A,C,D)
                 => r2_lattice3(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).

tff(f_125,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( r1_lattice3(A,k1_tarski(C),B)
                 => r1_orders_2(A,B,C) )
                & ( r1_orders_2(A,B,C)
                 => r1_lattice3(A,k1_tarski(C),B) )
                & ( r2_lattice3(A,k1_tarski(C),B)
                 => r1_orders_2(A,C,B) )
                & ( r1_orders_2(A,C,B)
                 => r2_lattice3(A,k1_tarski(C),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k2_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_0)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_yellow_0(A,B)
           => ( C = k2_yellow_0(A,B)
            <=> ( r1_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r1_lattice3(A,B,D)
                     => r1_orders_2(A,D,C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_yellow_0)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( r1_orders_2(A,B,C)
                      & r1_orders_2(A,C,D) )
                   => r1_orders_2(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_orders_2)).

tff(f_101,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(c_70,plain,
    ( ~ r1_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ r1_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_108,plain,(
    ~ r1_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_62,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_52,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_87,plain,(
    ! [A_121,B_122] :
      ( r1_tarski(A_121,B_122)
      | ~ m1_subset_1(A_121,k1_zfmisc_1(B_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_94,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_60,c_87])).

tff(c_24,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    ! [A_13,B_20,C_21] :
      ( r2_hidden('#skF_2'(A_13,B_20,C_21),B_20)
      | r1_lattice3(A_13,B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_110,plain,(
    ! [A_131,C_132,B_133] :
      ( m1_subset_1(A_131,C_132)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(C_132))
      | ~ r2_hidden(A_131,B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_118,plain,(
    ! [A_131] :
      ( m1_subset_1(A_131,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_131,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_110])).

tff(c_30,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(k1_tarski(A_43),B_44)
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_22,plain,(
    ! [A_27] : v1_finset_1(k1_tarski(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_34,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1(A_45,k1_zfmisc_1(B_46))
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_146,plain,(
    ! [D_142] :
      ( r2_yellow_0('#skF_3',D_142)
      | k1_xboole_0 = D_142
      | ~ m1_subset_1(D_142,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_151,plain,(
    ! [A_45] :
      ( r2_yellow_0('#skF_3',A_45)
      | k1_xboole_0 = A_45
      | ~ v1_finset_1(A_45)
      | ~ r1_tarski(A_45,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_146])).

tff(c_54,plain,(
    ! [D_117] :
      ( r2_hidden(k2_yellow_0('#skF_3',D_117),'#skF_5')
      | k1_xboole_0 = D_117
      | ~ m1_subset_1(D_117,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_119,plain,(
    ! [A_131] :
      ( m1_subset_1(A_131,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_131,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_110])).

tff(c_64,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_76,plain,
    ( r1_lattice3('#skF_3','#skF_4','#skF_7')
    | r1_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_109,plain,(
    r1_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_76])).

tff(c_322,plain,(
    ! [A_178,B_179,D_180,C_181] :
      ( r1_lattice3(A_178,B_179,D_180)
      | ~ r1_lattice3(A_178,C_181,D_180)
      | ~ m1_subset_1(D_180,u1_struct_0(A_178))
      | ~ r1_tarski(B_179,C_181)
      | ~ l1_orders_2(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_334,plain,(
    ! [B_179] :
      ( r1_lattice3('#skF_3',B_179,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_179,'#skF_5')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_109,c_322])).

tff(c_348,plain,(
    ! [B_179] :
      ( r1_lattice3('#skF_3',B_179,'#skF_7')
      | ~ r1_tarski(B_179,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_334])).

tff(c_540,plain,(
    ! [A_216,B_217,C_218] :
      ( r1_orders_2(A_216,B_217,C_218)
      | ~ r1_lattice3(A_216,k1_tarski(C_218),B_217)
      | ~ m1_subset_1(C_218,u1_struct_0(A_216))
      | ~ m1_subset_1(B_217,u1_struct_0(A_216))
      | ~ l1_orders_2(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_559,plain,(
    ! [C_218] :
      ( r1_orders_2('#skF_3','#skF_7',C_218)
      | ~ m1_subset_1(C_218,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r1_tarski(k1_tarski(C_218),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_348,c_540])).

tff(c_660,plain,(
    ! [C_229] :
      ( r1_orders_2('#skF_3','#skF_7',C_229)
      | ~ m1_subset_1(C_229,u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tarski(C_229),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_559])).

tff(c_666,plain,(
    ! [A_230] :
      ( r1_orders_2('#skF_3','#skF_7',A_230)
      | ~ m1_subset_1(A_230,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_230,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_660])).

tff(c_694,plain,(
    ! [A_131] :
      ( r1_orders_2('#skF_3','#skF_7',A_131)
      | ~ r2_hidden(A_131,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_119,c_666])).

tff(c_20,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(k2_yellow_0(A_25,B_26),u1_struct_0(A_25))
      | ~ l1_orders_2(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_290,plain,(
    ! [A_174,B_175] :
      ( r1_lattice3(A_174,B_175,k2_yellow_0(A_174,B_175))
      | ~ r2_yellow_0(A_174,B_175)
      | ~ m1_subset_1(k2_yellow_0(A_174,B_175),u1_struct_0(A_174))
      | ~ l1_orders_2(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_315,plain,(
    ! [A_25,B_26] :
      ( r1_lattice3(A_25,B_26,k2_yellow_0(A_25,B_26))
      | ~ r2_yellow_0(A_25,B_26)
      | ~ l1_orders_2(A_25) ) ),
    inference(resolution,[status(thm)],[c_20,c_290])).

tff(c_2520,plain,(
    ! [A_459,C_460] :
      ( r1_orders_2(A_459,k2_yellow_0(A_459,k1_tarski(C_460)),C_460)
      | ~ m1_subset_1(C_460,u1_struct_0(A_459))
      | ~ m1_subset_1(k2_yellow_0(A_459,k1_tarski(C_460)),u1_struct_0(A_459))
      | ~ r2_yellow_0(A_459,k1_tarski(C_460))
      | ~ l1_orders_2(A_459) ) ),
    inference(resolution,[status(thm)],[c_315,c_540])).

tff(c_2543,plain,(
    ! [A_461,C_462] :
      ( r1_orders_2(A_461,k2_yellow_0(A_461,k1_tarski(C_462)),C_462)
      | ~ m1_subset_1(C_462,u1_struct_0(A_461))
      | ~ r2_yellow_0(A_461,k1_tarski(C_462))
      | ~ l1_orders_2(A_461) ) ),
    inference(resolution,[status(thm)],[c_20,c_2520])).

tff(c_26,plain,(
    ! [A_28,B_36,D_42,C_40] :
      ( r1_orders_2(A_28,B_36,D_42)
      | ~ r1_orders_2(A_28,C_40,D_42)
      | ~ r1_orders_2(A_28,B_36,C_40)
      | ~ m1_subset_1(D_42,u1_struct_0(A_28))
      | ~ m1_subset_1(C_40,u1_struct_0(A_28))
      | ~ m1_subset_1(B_36,u1_struct_0(A_28))
      | ~ l1_orders_2(A_28)
      | ~ v4_orders_2(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_27748,plain,(
    ! [A_2308,B_2309,C_2310] :
      ( r1_orders_2(A_2308,B_2309,C_2310)
      | ~ r1_orders_2(A_2308,B_2309,k2_yellow_0(A_2308,k1_tarski(C_2310)))
      | ~ m1_subset_1(k2_yellow_0(A_2308,k1_tarski(C_2310)),u1_struct_0(A_2308))
      | ~ m1_subset_1(B_2309,u1_struct_0(A_2308))
      | ~ v4_orders_2(A_2308)
      | ~ m1_subset_1(C_2310,u1_struct_0(A_2308))
      | ~ r2_yellow_0(A_2308,k1_tarski(C_2310))
      | ~ l1_orders_2(A_2308) ) ),
    inference(resolution,[status(thm)],[c_2543,c_26])).

tff(c_27929,plain,(
    ! [C_2310] :
      ( r1_orders_2('#skF_3','#skF_7',C_2310)
      | ~ m1_subset_1(k2_yellow_0('#skF_3',k1_tarski(C_2310)),u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ v4_orders_2('#skF_3')
      | ~ m1_subset_1(C_2310,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3',k1_tarski(C_2310))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden(k2_yellow_0('#skF_3',k1_tarski(C_2310)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_694,c_27748])).

tff(c_28084,plain,(
    ! [C_2311] :
      ( r1_orders_2('#skF_3','#skF_7',C_2311)
      | ~ m1_subset_1(k2_yellow_0('#skF_3',k1_tarski(C_2311)),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_2311,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3',k1_tarski(C_2311))
      | ~ r2_hidden(k2_yellow_0('#skF_3',k1_tarski(C_2311)),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_64,c_52,c_27929])).

tff(c_28108,plain,(
    ! [C_2312] :
      ( r1_orders_2('#skF_3','#skF_7',C_2312)
      | ~ m1_subset_1(C_2312,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3',k1_tarski(C_2312))
      | ~ r2_hidden(k2_yellow_0('#skF_3',k1_tarski(C_2312)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_119,c_28084])).

tff(c_28114,plain,(
    ! [C_2312] :
      ( r1_orders_2('#skF_3','#skF_7',C_2312)
      | ~ m1_subset_1(C_2312,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3',k1_tarski(C_2312))
      | k1_tarski(C_2312) = k1_xboole_0
      | ~ m1_subset_1(k1_tarski(C_2312),k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(k1_tarski(C_2312)) ) ),
    inference(resolution,[status(thm)],[c_54,c_28108])).

tff(c_28118,plain,(
    ! [C_2313] :
      ( r1_orders_2('#skF_3','#skF_7',C_2313)
      | ~ m1_subset_1(C_2313,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3',k1_tarski(C_2313))
      | k1_tarski(C_2313) = k1_xboole_0
      | ~ m1_subset_1(k1_tarski(C_2313),k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_28114])).

tff(c_28123,plain,(
    ! [C_2314] :
      ( r1_orders_2('#skF_3','#skF_7',C_2314)
      | ~ m1_subset_1(C_2314,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3',k1_tarski(C_2314))
      | k1_tarski(C_2314) = k1_xboole_0
      | ~ r1_tarski(k1_tarski(C_2314),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_28118])).

tff(c_28126,plain,(
    ! [C_2314] :
      ( r1_orders_2('#skF_3','#skF_7',C_2314)
      | ~ m1_subset_1(C_2314,u1_struct_0('#skF_3'))
      | k1_tarski(C_2314) = k1_xboole_0
      | ~ v1_finset_1(k1_tarski(C_2314))
      | ~ r1_tarski(k1_tarski(C_2314),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_151,c_28123])).

tff(c_28130,plain,(
    ! [C_2315] :
      ( r1_orders_2('#skF_3','#skF_7',C_2315)
      | ~ m1_subset_1(C_2315,u1_struct_0('#skF_3'))
      | k1_tarski(C_2315) = k1_xboole_0
      | ~ r1_tarski(k1_tarski(C_2315),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_28126])).

tff(c_28136,plain,(
    ! [A_2316] :
      ( r1_orders_2('#skF_3','#skF_7',A_2316)
      | ~ m1_subset_1(A_2316,u1_struct_0('#skF_3'))
      | k1_tarski(A_2316) = k1_xboole_0
      | ~ r2_hidden(A_2316,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_28130])).

tff(c_28187,plain,(
    ! [A_2317] :
      ( r1_orders_2('#skF_3','#skF_7',A_2317)
      | k1_tarski(A_2317) = k1_xboole_0
      | ~ r2_hidden(A_2317,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_118,c_28136])).

tff(c_14,plain,(
    ! [A_13,C_21,B_20] :
      ( ~ r1_orders_2(A_13,C_21,'#skF_2'(A_13,B_20,C_21))
      | r1_lattice3(A_13,B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_28260,plain,(
    ! [B_20] :
      ( r1_lattice3('#skF_3',B_20,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | k1_tarski('#skF_2'('#skF_3',B_20,'#skF_7')) = k1_xboole_0
      | ~ r2_hidden('#skF_2'('#skF_3',B_20,'#skF_7'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28187,c_14])).

tff(c_28334,plain,(
    ! [B_2318] :
      ( r1_lattice3('#skF_3',B_2318,'#skF_7')
      | k1_tarski('#skF_2'('#skF_3',B_2318,'#skF_7')) = k1_xboole_0
      | ~ r2_hidden('#skF_2'('#skF_3',B_2318,'#skF_7'),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_28260])).

tff(c_28338,plain,
    ( k1_tarski('#skF_2'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0
    | r1_lattice3('#skF_3','#skF_4','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_28334])).

tff(c_28341,plain,
    ( k1_tarski('#skF_2'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0
    | r1_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_28338])).

tff(c_28342,plain,(
    k1_tarski('#skF_2'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_28341])).

tff(c_213,plain,(
    ! [A_151,B_152,C_153] :
      ( r2_hidden('#skF_2'(A_151,B_152,C_153),B_152)
      | r1_lattice3(A_151,B_152,C_153)
      | ~ m1_subset_1(C_153,u1_struct_0(A_151))
      | ~ l1_orders_2(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_117,plain,(
    ! [A_131,B_46,A_45] :
      ( m1_subset_1(A_131,B_46)
      | ~ r2_hidden(A_131,A_45)
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_34,c_110])).

tff(c_981,plain,(
    ! [A_276,B_277,C_278,B_279] :
      ( m1_subset_1('#skF_2'(A_276,B_277,C_278),B_279)
      | ~ r1_tarski(B_277,B_279)
      | r1_lattice3(A_276,B_277,C_278)
      | ~ m1_subset_1(C_278,u1_struct_0(A_276))
      | ~ l1_orders_2(A_276) ) ),
    inference(resolution,[status(thm)],[c_213,c_117])).

tff(c_38,plain,(
    ! [B_51,A_50] :
      ( ~ v1_xboole_0(B_51)
      | ~ r2_hidden(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_226,plain,(
    ! [B_154,A_155,C_156] :
      ( ~ v1_xboole_0(B_154)
      | r1_lattice3(A_155,B_154,C_156)
      | ~ m1_subset_1(C_156,u1_struct_0(A_155))
      | ~ l1_orders_2(A_155) ) ),
    inference(resolution,[status(thm)],[c_213,c_38])).

tff(c_234,plain,(
    ! [B_154] :
      ( ~ v1_xboole_0(B_154)
      | r1_lattice3('#skF_3',B_154,'#skF_7')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_226])).

tff(c_244,plain,(
    ! [B_154] :
      ( ~ v1_xboole_0(B_154)
      | r1_lattice3('#skF_3',B_154,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_234])).

tff(c_579,plain,(
    ! [C_218] :
      ( r1_orders_2('#skF_3','#skF_7',C_218)
      | ~ m1_subset_1(C_218,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_xboole_0(k1_tarski(C_218)) ) ),
    inference(resolution,[status(thm)],[c_244,c_540])).

tff(c_603,plain,(
    ! [C_218] :
      ( r1_orders_2('#skF_3','#skF_7',C_218)
      | ~ m1_subset_1(C_218,u1_struct_0('#skF_3'))
      | ~ v1_xboole_0(k1_tarski(C_218)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_579])).

tff(c_1008,plain,(
    ! [A_276,B_277,C_278] :
      ( r1_orders_2('#skF_3','#skF_7','#skF_2'(A_276,B_277,C_278))
      | ~ v1_xboole_0(k1_tarski('#skF_2'(A_276,B_277,C_278)))
      | ~ r1_tarski(B_277,u1_struct_0('#skF_3'))
      | r1_lattice3(A_276,B_277,C_278)
      | ~ m1_subset_1(C_278,u1_struct_0(A_276))
      | ~ l1_orders_2(A_276) ) ),
    inference(resolution,[status(thm)],[c_981,c_603])).

tff(c_28621,plain,
    ( r1_orders_2('#skF_3','#skF_7','#skF_2'('#skF_3','#skF_4','#skF_7'))
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ r1_tarski('#skF_4',u1_struct_0('#skF_3'))
    | r1_lattice3('#skF_3','#skF_4','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28342,c_1008])).

tff(c_28927,plain,
    ( r1_orders_2('#skF_3','#skF_7','#skF_2'('#skF_3','#skF_4','#skF_7'))
    | r1_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_94,c_24,c_28621])).

tff(c_28928,plain,(
    r1_orders_2('#skF_3','#skF_7','#skF_2'('#skF_3','#skF_4','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_28927])).

tff(c_29016,plain,
    ( r1_lattice3('#skF_3','#skF_4','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_28928,c_14])).

tff(c_29064,plain,(
    r1_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_29016])).

tff(c_29066,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_29064])).

tff(c_29067,plain,(
    ~ r1_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_29084,plain,(
    ! [A_2320,C_2321,B_2322] :
      ( m1_subset_1(A_2320,C_2321)
      | ~ m1_subset_1(B_2322,k1_zfmisc_1(C_2321))
      | ~ r2_hidden(A_2320,B_2322) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_29093,plain,(
    ! [A_2320] :
      ( m1_subset_1(A_2320,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_2320,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_29084])).

tff(c_29148,plain,(
    ! [D_2334] :
      ( m1_subset_1('#skF_6'(D_2334),k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(D_2334,'#skF_5')
      | ~ m1_subset_1(D_2334,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_32,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,B_46)
      | ~ m1_subset_1(A_45,k1_zfmisc_1(B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_29159,plain,(
    ! [D_2334] :
      ( r1_tarski('#skF_6'(D_2334),'#skF_4')
      | ~ r2_hidden(D_2334,'#skF_5')
      | ~ m1_subset_1(D_2334,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_29148,c_32])).

tff(c_80,plain,(
    ! [D_115] :
      ( r2_yellow_0('#skF_3','#skF_6'(D_115))
      | ~ r2_hidden(D_115,'#skF_5')
      | ~ m1_subset_1(D_115,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_29068,plain,(
    r1_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_29297,plain,(
    ! [A_2372,B_2373,D_2374,C_2375] :
      ( r1_lattice3(A_2372,B_2373,D_2374)
      | ~ r1_lattice3(A_2372,C_2375,D_2374)
      | ~ m1_subset_1(D_2374,u1_struct_0(A_2372))
      | ~ r1_tarski(B_2373,C_2375)
      | ~ l1_orders_2(A_2372) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_29315,plain,(
    ! [B_2373] :
      ( r1_lattice3('#skF_3',B_2373,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_2373,'#skF_4')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_29068,c_29297])).

tff(c_29338,plain,(
    ! [B_2373] :
      ( r1_lattice3('#skF_3',B_2373,'#skF_7')
      | ~ r1_tarski(B_2373,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_29315])).

tff(c_29113,plain,(
    ! [D_2331] :
      ( k2_yellow_0('#skF_3','#skF_6'(D_2331)) = D_2331
      | ~ r2_hidden(D_2331,'#skF_5')
      | ~ m1_subset_1(D_2331,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_29127,plain,(
    ! [A_2320] :
      ( k2_yellow_0('#skF_3','#skF_6'(A_2320)) = A_2320
      | ~ r2_hidden(A_2320,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_29093,c_29113])).

tff(c_30191,plain,(
    ! [A_2508,D_2509,B_2510] :
      ( r1_orders_2(A_2508,D_2509,k2_yellow_0(A_2508,B_2510))
      | ~ r1_lattice3(A_2508,B_2510,D_2509)
      | ~ m1_subset_1(D_2509,u1_struct_0(A_2508))
      | ~ r2_yellow_0(A_2508,B_2510)
      | ~ m1_subset_1(k2_yellow_0(A_2508,B_2510),u1_struct_0(A_2508))
      | ~ l1_orders_2(A_2508) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_30217,plain,(
    ! [A_2511,D_2512,B_2513] :
      ( r1_orders_2(A_2511,D_2512,k2_yellow_0(A_2511,B_2513))
      | ~ r1_lattice3(A_2511,B_2513,D_2512)
      | ~ m1_subset_1(D_2512,u1_struct_0(A_2511))
      | ~ r2_yellow_0(A_2511,B_2513)
      | ~ l1_orders_2(A_2511) ) ),
    inference(resolution,[status(thm)],[c_20,c_30191])).

tff(c_30224,plain,(
    ! [D_2512,A_2320] :
      ( r1_orders_2('#skF_3',D_2512,A_2320)
      | ~ r1_lattice3('#skF_3','#skF_6'(A_2320),D_2512)
      | ~ m1_subset_1(D_2512,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3','#skF_6'(A_2320))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden(A_2320,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29127,c_30217])).

tff(c_30254,plain,(
    ! [D_2518,A_2519] :
      ( r1_orders_2('#skF_3',D_2518,A_2519)
      | ~ r1_lattice3('#skF_3','#skF_6'(A_2519),D_2518)
      | ~ m1_subset_1(D_2518,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3','#skF_6'(A_2519))
      | ~ r2_hidden(A_2519,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_30224])).

tff(c_30289,plain,(
    ! [A_2519] :
      ( r1_orders_2('#skF_3','#skF_7',A_2519)
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3','#skF_6'(A_2519))
      | ~ r2_hidden(A_2519,'#skF_5')
      | ~ r1_tarski('#skF_6'(A_2519),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_29338,c_30254])).

tff(c_30495,plain,(
    ! [A_2532] :
      ( r1_orders_2('#skF_3','#skF_7',A_2532)
      | ~ r2_yellow_0('#skF_3','#skF_6'(A_2532))
      | ~ r2_hidden(A_2532,'#skF_5')
      | ~ r1_tarski('#skF_6'(A_2532),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_30289])).

tff(c_30504,plain,(
    ! [D_2533] :
      ( r1_orders_2('#skF_3','#skF_7',D_2533)
      | ~ r1_tarski('#skF_6'(D_2533),'#skF_4')
      | ~ r2_hidden(D_2533,'#skF_5')
      | ~ m1_subset_1(D_2533,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_80,c_30495])).

tff(c_30509,plain,(
    ! [D_2534] :
      ( r1_orders_2('#skF_3','#skF_7',D_2534)
      | ~ r2_hidden(D_2534,'#skF_5')
      | ~ m1_subset_1(D_2534,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_29159,c_30504])).

tff(c_30555,plain,(
    ! [A_2535] :
      ( r1_orders_2('#skF_3','#skF_7',A_2535)
      | ~ r2_hidden(A_2535,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_29093,c_30509])).

tff(c_30561,plain,(
    ! [B_20] :
      ( r1_lattice3('#skF_3',B_20,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_3',B_20,'#skF_7'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30555,c_14])).

tff(c_30568,plain,(
    ! [B_2536] :
      ( r1_lattice3('#skF_3',B_2536,'#skF_7')
      | ~ r2_hidden('#skF_2'('#skF_3',B_2536,'#skF_7'),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_30561])).

tff(c_30572,plain,
    ( r1_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_30568])).

tff(c_30575,plain,(
    r1_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_30572])).

tff(c_30577,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29067,c_30575])).

%------------------------------------------------------------------------------
