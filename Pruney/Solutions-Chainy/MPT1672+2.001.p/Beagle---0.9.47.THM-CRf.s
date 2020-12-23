%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:01 EST 2020

% Result     : Theorem 8.15s
% Output     : CNFRefutation 8.15s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 219 expanded)
%              Number of leaves         :   43 (  95 expanded)
%              Depth                    :   27
%              Number of atoms          :  356 (1314 expanded)
%              Number of equality atoms :   24 ( 135 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_finset_1 > l1_orders_2 > k2_tarski > k1_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

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

tff(f_214,negated_conjecture,(
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
                         => r1_yellow_0(A,D) ) )
                    & ! [D] :
                        ( m1_subset_1(D,u1_struct_0(A))
                       => ~ ( r2_hidden(D,C)
                            & ! [E] :
                                ( ( v1_finset_1(E)
                                  & m1_subset_1(E,k1_zfmisc_1(B)) )
                               => ~ ( r1_yellow_0(A,E)
                                    & D = k1_yellow_0(A,E) ) ) ) )
                    & ! [D] :
                        ( ( v1_finset_1(D)
                          & m1_subset_1(D,k1_zfmisc_1(B)) )
                       => ( D != k1_xboole_0
                         => r2_hidden(k1_yellow_0(A,D),C) ) ) )
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_lattice3(A,B,D)
                      <=> r2_lattice3(A,C,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_waybel_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] : v1_finset_1(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_finset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_28,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_155,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_0)).

tff(f_139,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( r1_lattice3(A,k2_tarski(C,D),B)
                     => ( r1_orders_2(A,B,C)
                        & r1_orders_2(A,B,D) ) )
                    & ( ( r1_orders_2(A,B,C)
                        & r1_orders_2(A,B,D) )
                     => r1_lattice3(A,k2_tarski(C,D),B) )
                    & ( r2_lattice3(A,k2_tarski(C,D),B)
                     => ( r1_orders_2(A,C,B)
                        & r1_orders_2(A,D,B) ) )
                    & ( ( r1_orders_2(A,C,B)
                        & r1_orders_2(A,D,B) )
                     => r2_lattice3(A,k2_tarski(C,D),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_yellow_0)).

tff(f_83,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_yellow_0(A,B)
           => ( C = k1_yellow_0(A,B)
            <=> ( r2_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r2_lattice3(A,B,D)
                     => r1_orders_2(A,C,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).

tff(f_104,axiom,(
    ! [A] :
      ( ( v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
               => ! [D] :
                    ( ( r1_lattice3(A,D,C)
                     => r1_lattice3(A,D,B) )
                    & ( r2_lattice3(A,D,B)
                     => r2_lattice3(A,D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_0)).

tff(f_31,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(c_84,plain,
    ( r2_lattice3('#skF_3','#skF_4','#skF_7')
    | r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_125,plain,(
    r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_78,plain,
    ( ~ r2_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_126,plain,(
    ~ r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_70,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_60,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_24,plain,(
    ! [A_11,B_18,C_19] :
      ( r2_hidden('#skF_1'(A_11,B_18,C_19),B_18)
      | r2_lattice3(A_11,B_18,C_19)
      | ~ m1_subset_1(C_19,u1_struct_0(A_11))
      | ~ l1_orders_2(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_140,plain,(
    ! [A_140,C_141,B_142] :
      ( m1_subset_1(A_140,C_141)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(C_141))
      | ~ r2_hidden(A_140,B_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_148,plain,(
    ! [A_140] :
      ( m1_subset_1(A_140,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_140,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_140])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(k1_tarski(A_3),B_4)
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [A_10] : v1_finset_1(k1_tarski(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_163,plain,(
    ! [D_150] :
      ( r1_yellow_0('#skF_3',D_150)
      | k1_xboole_0 = D_150
      | ~ m1_subset_1(D_150,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_168,plain,(
    ! [A_5] :
      ( r1_yellow_0('#skF_3',A_5)
      | k1_xboole_0 = A_5
      | ~ v1_finset_1(A_5)
      | ~ r1_tarski(A_5,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_14,c_163])).

tff(c_62,plain,(
    ! [D_125] :
      ( r2_hidden(k1_yellow_0('#skF_3',D_125),'#skF_5')
      | k1_xboole_0 = D_125
      | ~ m1_subset_1(D_125,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_66,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_149,plain,(
    ! [A_140] :
      ( m1_subset_1(A_140,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_140,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_66,c_140])).

tff(c_72,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_4,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_252,plain,(
    ! [A_164,B_165,D_166,C_167] :
      ( r2_lattice3(A_164,B_165,D_166)
      | ~ r2_lattice3(A_164,C_167,D_166)
      | ~ m1_subset_1(D_166,u1_struct_0(A_164))
      | ~ r1_tarski(B_165,C_167)
      | ~ l1_orders_2(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_254,plain,(
    ! [B_165] :
      ( r2_lattice3('#skF_3',B_165,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_165,'#skF_5')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_125,c_252])).

tff(c_257,plain,(
    ! [B_165] :
      ( r2_lattice3('#skF_3',B_165,'#skF_7')
      | ~ r1_tarski(B_165,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_60,c_254])).

tff(c_690,plain,(
    ! [A_237,D_238,B_239,C_240] :
      ( r1_orders_2(A_237,D_238,B_239)
      | ~ r2_lattice3(A_237,k2_tarski(C_240,D_238),B_239)
      | ~ m1_subset_1(D_238,u1_struct_0(A_237))
      | ~ m1_subset_1(C_240,u1_struct_0(A_237))
      | ~ m1_subset_1(B_239,u1_struct_0(A_237))
      | ~ l1_orders_2(A_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_726,plain,(
    ! [D_238,C_240] :
      ( r1_orders_2('#skF_3',D_238,'#skF_7')
      | ~ m1_subset_1(D_238,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_240,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r1_tarski(k2_tarski(C_240,D_238),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_257,c_690])).

tff(c_774,plain,(
    ! [D_243,C_244] :
      ( r1_orders_2('#skF_3',D_243,'#skF_7')
      | ~ m1_subset_1(D_243,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_244,u1_struct_0('#skF_3'))
      | ~ r1_tarski(k2_tarski(C_244,D_243),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_60,c_726])).

tff(c_778,plain,(
    ! [A_245] :
      ( r1_orders_2('#skF_3',A_245,'#skF_7')
      | ~ m1_subset_1(A_245,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_245,u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tarski(A_245),'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_774])).

tff(c_787,plain,(
    ! [A_248] :
      ( r1_orders_2('#skF_3',A_248,'#skF_7')
      | ~ m1_subset_1(A_248,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_248,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_10,c_778])).

tff(c_820,plain,(
    ! [A_140] :
      ( r1_orders_2('#skF_3',A_140,'#skF_7')
      | ~ r2_hidden(A_140,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_149,c_787])).

tff(c_38,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(k1_yellow_0(A_35,B_36),u1_struct_0(A_35))
      | ~ l1_orders_2(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_293,plain,(
    ! [A_177,B_178] :
      ( r2_lattice3(A_177,B_178,k1_yellow_0(A_177,B_178))
      | ~ r1_yellow_0(A_177,B_178)
      | ~ m1_subset_1(k1_yellow_0(A_177,B_178),u1_struct_0(A_177))
      | ~ l1_orders_2(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_318,plain,(
    ! [A_35,B_36] :
      ( r2_lattice3(A_35,B_36,k1_yellow_0(A_35,B_36))
      | ~ r1_yellow_0(A_35,B_36)
      | ~ l1_orders_2(A_35) ) ),
    inference(resolution,[status(thm)],[c_38,c_293])).

tff(c_495,plain,(
    ! [A_219,D_220,C_221,B_222] :
      ( r2_lattice3(A_219,D_220,C_221)
      | ~ r2_lattice3(A_219,D_220,B_222)
      | ~ r1_orders_2(A_219,B_222,C_221)
      | ~ m1_subset_1(C_221,u1_struct_0(A_219))
      | ~ m1_subset_1(B_222,u1_struct_0(A_219))
      | ~ l1_orders_2(A_219)
      | ~ v4_orders_2(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_4869,plain,(
    ! [A_682,B_683,C_684] :
      ( r2_lattice3(A_682,B_683,C_684)
      | ~ r1_orders_2(A_682,k1_yellow_0(A_682,B_683),C_684)
      | ~ m1_subset_1(C_684,u1_struct_0(A_682))
      | ~ m1_subset_1(k1_yellow_0(A_682,B_683),u1_struct_0(A_682))
      | ~ v4_orders_2(A_682)
      | ~ r1_yellow_0(A_682,B_683)
      | ~ l1_orders_2(A_682) ) ),
    inference(resolution,[status(thm)],[c_318,c_495])).

tff(c_4915,plain,(
    ! [B_683] :
      ( r2_lattice3('#skF_3',B_683,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(k1_yellow_0('#skF_3',B_683),u1_struct_0('#skF_3'))
      | ~ v4_orders_2('#skF_3')
      | ~ r1_yellow_0('#skF_3',B_683)
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden(k1_yellow_0('#skF_3',B_683),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_820,c_4869])).

tff(c_4965,plain,(
    ! [B_685] :
      ( r2_lattice3('#skF_3',B_685,'#skF_7')
      | ~ m1_subset_1(k1_yellow_0('#skF_3',B_685),u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3',B_685)
      | ~ r2_hidden(k1_yellow_0('#skF_3',B_685),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_72,c_60,c_4915])).

tff(c_4991,plain,(
    ! [B_686] :
      ( r2_lattice3('#skF_3',B_686,'#skF_7')
      | ~ r1_yellow_0('#skF_3',B_686)
      | ~ r2_hidden(k1_yellow_0('#skF_3',B_686),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_149,c_4965])).

tff(c_4999,plain,(
    ! [D_687] :
      ( r2_lattice3('#skF_3',D_687,'#skF_7')
      | ~ r1_yellow_0('#skF_3',D_687)
      | k1_xboole_0 = D_687
      | ~ m1_subset_1(D_687,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_687) ) ),
    inference(resolution,[status(thm)],[c_62,c_4991])).

tff(c_5019,plain,(
    ! [A_688] :
      ( r2_lattice3('#skF_3',A_688,'#skF_7')
      | ~ r1_yellow_0('#skF_3',A_688)
      | k1_xboole_0 = A_688
      | ~ v1_finset_1(A_688)
      | ~ r1_tarski(A_688,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_14,c_4999])).

tff(c_911,plain,(
    ! [A_265,C_266,B_267,D_268] :
      ( r1_orders_2(A_265,C_266,B_267)
      | ~ r2_lattice3(A_265,k2_tarski(C_266,D_268),B_267)
      | ~ m1_subset_1(D_268,u1_struct_0(A_265))
      | ~ m1_subset_1(C_266,u1_struct_0(A_265))
      | ~ m1_subset_1(B_267,u1_struct_0(A_265))
      | ~ l1_orders_2(A_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_966,plain,(
    ! [A_265,A_1,B_267] :
      ( r1_orders_2(A_265,A_1,B_267)
      | ~ r2_lattice3(A_265,k1_tarski(A_1),B_267)
      | ~ m1_subset_1(A_1,u1_struct_0(A_265))
      | ~ m1_subset_1(A_1,u1_struct_0(A_265))
      | ~ m1_subset_1(B_267,u1_struct_0(A_265))
      | ~ l1_orders_2(A_265) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_911])).

tff(c_5033,plain,(
    ! [A_1] :
      ( r1_orders_2('#skF_3',A_1,'#skF_7')
      | ~ m1_subset_1(A_1,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r1_yellow_0('#skF_3',k1_tarski(A_1))
      | k1_tarski(A_1) = k1_xboole_0
      | ~ v1_finset_1(k1_tarski(A_1))
      | ~ r1_tarski(k1_tarski(A_1),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5019,c_966])).

tff(c_5174,plain,(
    ! [A_702] :
      ( r1_orders_2('#skF_3',A_702,'#skF_7')
      | ~ m1_subset_1(A_702,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3',k1_tarski(A_702))
      | k1_tarski(A_702) = k1_xboole_0
      | ~ r1_tarski(k1_tarski(A_702),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_70,c_60,c_5033])).

tff(c_5177,plain,(
    ! [A_702] :
      ( r1_orders_2('#skF_3',A_702,'#skF_7')
      | ~ m1_subset_1(A_702,u1_struct_0('#skF_3'))
      | k1_tarski(A_702) = k1_xboole_0
      | ~ v1_finset_1(k1_tarski(A_702))
      | ~ r1_tarski(k1_tarski(A_702),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_168,c_5174])).

tff(c_5198,plain,(
    ! [A_704] :
      ( r1_orders_2('#skF_3',A_704,'#skF_7')
      | ~ m1_subset_1(A_704,u1_struct_0('#skF_3'))
      | k1_tarski(A_704) = k1_xboole_0
      | ~ r1_tarski(k1_tarski(A_704),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_5177])).

tff(c_5204,plain,(
    ! [A_705] :
      ( r1_orders_2('#skF_3',A_705,'#skF_7')
      | ~ m1_subset_1(A_705,u1_struct_0('#skF_3'))
      | k1_tarski(A_705) = k1_xboole_0
      | ~ r2_hidden(A_705,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10,c_5198])).

tff(c_5250,plain,(
    ! [A_706] :
      ( r1_orders_2('#skF_3',A_706,'#skF_7')
      | k1_tarski(A_706) = k1_xboole_0
      | ~ r2_hidden(A_706,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_148,c_5204])).

tff(c_22,plain,(
    ! [A_11,B_18,C_19] :
      ( ~ r1_orders_2(A_11,'#skF_1'(A_11,B_18,C_19),C_19)
      | r2_lattice3(A_11,B_18,C_19)
      | ~ m1_subset_1(C_19,u1_struct_0(A_11))
      | ~ l1_orders_2(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_5299,plain,(
    ! [B_18] :
      ( r2_lattice3('#skF_3',B_18,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | k1_tarski('#skF_1'('#skF_3',B_18,'#skF_7')) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_18,'#skF_7'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5250,c_22])).

tff(c_5345,plain,(
    ! [B_707] :
      ( r2_lattice3('#skF_3',B_707,'#skF_7')
      | k1_tarski('#skF_1'('#skF_3',B_707,'#skF_7')) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_707,'#skF_7'),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_60,c_5299])).

tff(c_5349,plain,
    ( k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0
    | r2_lattice3('#skF_3','#skF_4','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_5345])).

tff(c_5352,plain,
    ( k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0
    | r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_60,c_5349])).

tff(c_5353,plain,(
    k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_5352])).

tff(c_6,plain,(
    ! [A_2] : ~ v1_xboole_0(k1_tarski(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5540,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5353,c_6])).

tff(c_5561,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_5540])).

tff(c_5562,plain,(
    ~ r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_5565,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_5562])).

tff(c_5567,plain,(
    ~ r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_5588,plain,(
    ! [A_714,C_715,B_716] :
      ( m1_subset_1(A_714,C_715)
      | ~ m1_subset_1(B_716,k1_zfmisc_1(C_715))
      | ~ r2_hidden(A_714,B_716) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5597,plain,(
    ! [A_714] :
      ( m1_subset_1(A_714,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_714,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_66,c_5588])).

tff(c_5616,plain,(
    ! [D_724] :
      ( m1_subset_1('#skF_6'(D_724),k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(D_724,'#skF_5')
      | ~ m1_subset_1(D_724,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5627,plain,(
    ! [D_724] :
      ( r1_tarski('#skF_6'(D_724),'#skF_4')
      | ~ r2_hidden(D_724,'#skF_5')
      | ~ m1_subset_1(D_724,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_5616,c_12])).

tff(c_88,plain,(
    ! [D_123] :
      ( r1_yellow_0('#skF_3','#skF_6'(D_123))
      | ~ r2_hidden(D_123,'#skF_5')
      | ~ m1_subset_1(D_123,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_5566,plain,(
    r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_5742,plain,(
    ! [A_751,B_752,D_753,C_754] :
      ( r2_lattice3(A_751,B_752,D_753)
      | ~ r2_lattice3(A_751,C_754,D_753)
      | ~ m1_subset_1(D_753,u1_struct_0(A_751))
      | ~ r1_tarski(B_752,C_754)
      | ~ l1_orders_2(A_751) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_5752,plain,(
    ! [B_752] :
      ( r2_lattice3('#skF_3',B_752,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_752,'#skF_4')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_5566,c_5742])).

tff(c_5765,plain,(
    ! [B_752] :
      ( r2_lattice3('#skF_3',B_752,'#skF_7')
      | ~ r1_tarski(B_752,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_60,c_5752])).

tff(c_5630,plain,(
    ! [D_727] :
      ( k1_yellow_0('#skF_3','#skF_6'(D_727)) = D_727
      | ~ r2_hidden(D_727,'#skF_5')
      | ~ m1_subset_1(D_727,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_5644,plain,(
    ! [A_714] :
      ( k1_yellow_0('#skF_3','#skF_6'(A_714)) = A_714
      | ~ r2_hidden(A_714,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5597,c_5630])).

tff(c_7067,plain,(
    ! [A_956,B_957,D_958] :
      ( r1_orders_2(A_956,k1_yellow_0(A_956,B_957),D_958)
      | ~ r2_lattice3(A_956,B_957,D_958)
      | ~ m1_subset_1(D_958,u1_struct_0(A_956))
      | ~ r1_yellow_0(A_956,B_957)
      | ~ m1_subset_1(k1_yellow_0(A_956,B_957),u1_struct_0(A_956))
      | ~ l1_orders_2(A_956) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_7093,plain,(
    ! [A_959,B_960,D_961] :
      ( r1_orders_2(A_959,k1_yellow_0(A_959,B_960),D_961)
      | ~ r2_lattice3(A_959,B_960,D_961)
      | ~ m1_subset_1(D_961,u1_struct_0(A_959))
      | ~ r1_yellow_0(A_959,B_960)
      | ~ l1_orders_2(A_959) ) ),
    inference(resolution,[status(thm)],[c_38,c_7067])).

tff(c_7106,plain,(
    ! [A_714,D_961] :
      ( r1_orders_2('#skF_3',A_714,D_961)
      | ~ r2_lattice3('#skF_3','#skF_6'(A_714),D_961)
      | ~ m1_subset_1(D_961,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3','#skF_6'(A_714))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden(A_714,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5644,c_7093])).

tff(c_7116,plain,(
    ! [A_962,D_963] :
      ( r1_orders_2('#skF_3',A_962,D_963)
      | ~ r2_lattice3('#skF_3','#skF_6'(A_962),D_963)
      | ~ m1_subset_1(D_963,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3','#skF_6'(A_962))
      | ~ r2_hidden(A_962,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_7106])).

tff(c_7167,plain,(
    ! [A_962] :
      ( r1_orders_2('#skF_3',A_962,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3','#skF_6'(A_962))
      | ~ r2_hidden(A_962,'#skF_5')
      | ~ r1_tarski('#skF_6'(A_962),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5765,c_7116])).

tff(c_7210,plain,(
    ! [A_964] :
      ( r1_orders_2('#skF_3',A_964,'#skF_7')
      | ~ r1_yellow_0('#skF_3','#skF_6'(A_964))
      | ~ r2_hidden(A_964,'#skF_5')
      | ~ r1_tarski('#skF_6'(A_964),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_7167])).

tff(c_7219,plain,(
    ! [D_965] :
      ( r1_orders_2('#skF_3',D_965,'#skF_7')
      | ~ r1_tarski('#skF_6'(D_965),'#skF_4')
      | ~ r2_hidden(D_965,'#skF_5')
      | ~ m1_subset_1(D_965,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_88,c_7210])).

tff(c_7224,plain,(
    ! [D_966] :
      ( r1_orders_2('#skF_3',D_966,'#skF_7')
      | ~ r2_hidden(D_966,'#skF_5')
      | ~ m1_subset_1(D_966,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_5627,c_7219])).

tff(c_7270,plain,(
    ! [A_967] :
      ( r1_orders_2('#skF_3',A_967,'#skF_7')
      | ~ r2_hidden(A_967,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5597,c_7224])).

tff(c_7278,plain,(
    ! [B_18] :
      ( r2_lattice3('#skF_3',B_18,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden('#skF_1'('#skF_3',B_18,'#skF_7'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_7270,c_22])).

tff(c_7288,plain,(
    ! [B_968] :
      ( r2_lattice3('#skF_3',B_968,'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_3',B_968,'#skF_7'),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_60,c_7278])).

tff(c_7292,plain,
    ( r2_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_7288])).

tff(c_7295,plain,(
    r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_60,c_7292])).

tff(c_7297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5567,c_7295])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.07  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.06/0.25  % Computer   : n008.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % DateTime   : Tue Dec  1 14:28:14 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.06/0.26  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.15/2.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.15/2.69  
% 8.15/2.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.15/2.69  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_finset_1 > l1_orders_2 > k2_tarski > k1_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_6
% 8.15/2.69  
% 8.15/2.69  %Foreground sorts:
% 8.15/2.69  
% 8.15/2.69  
% 8.15/2.69  %Background operators:
% 8.15/2.69  
% 8.15/2.69  
% 8.15/2.69  %Foreground operators:
% 8.15/2.69  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.15/2.69  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 8.15/2.69  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.15/2.69  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 8.15/2.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.15/2.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.15/2.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.15/2.69  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 8.15/2.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.15/2.69  tff('#skF_7', type, '#skF_7': $i).
% 8.15/2.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.15/2.69  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 8.15/2.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.15/2.69  tff('#skF_5', type, '#skF_5': $i).
% 8.15/2.69  tff('#skF_3', type, '#skF_3': $i).
% 8.15/2.69  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.15/2.69  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 8.15/2.69  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 8.15/2.69  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 8.15/2.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.15/2.69  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 8.15/2.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.15/2.69  tff('#skF_4', type, '#skF_4': $i).
% 8.15/2.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.15/2.69  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.15/2.69  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.15/2.69  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 8.15/2.69  tff('#skF_6', type, '#skF_6': $i > $i).
% 8.15/2.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.15/2.69  
% 8.15/2.72  tff(f_214, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((((![D]: ((v1_finset_1(D) & m1_subset_1(D, k1_zfmisc_1(B))) => (~(D = k1_xboole_0) => r1_yellow_0(A, D)))) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => ~(r2_hidden(D, C) & (![E]: ((v1_finset_1(E) & m1_subset_1(E, k1_zfmisc_1(B))) => ~(r1_yellow_0(A, E) & (D = k1_yellow_0(A, E))))))))) & (![D]: ((v1_finset_1(D) & m1_subset_1(D, k1_zfmisc_1(B))) => (~(D = k1_xboole_0) => r2_hidden(k1_yellow_0(A, D), C))))) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) <=> r2_lattice3(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_waybel_0)).
% 8.15/2.72  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.15/2.72  tff(f_61, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 8.15/2.72  tff(f_45, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 8.15/2.72  tff(f_35, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 8.15/2.72  tff(f_47, axiom, (![A]: v1_finset_1(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_finset_1)).
% 8.15/2.72  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.15/2.72  tff(f_28, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 8.15/2.72  tff(f_155, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (r1_tarski(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_lattice3(A, C, D) => r1_lattice3(A, B, D)) & (r2_lattice3(A, C, D) => r2_lattice3(A, B, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_yellow_0)).
% 8.15/2.72  tff(f_139, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((((r1_lattice3(A, k2_tarski(C, D), B) => (r1_orders_2(A, B, C) & r1_orders_2(A, B, D))) & ((r1_orders_2(A, B, C) & r1_orders_2(A, B, D)) => r1_lattice3(A, k2_tarski(C, D), B))) & (r2_lattice3(A, k2_tarski(C, D), B) => (r1_orders_2(A, C, B) & r1_orders_2(A, D, B)))) & ((r1_orders_2(A, C, B) & r1_orders_2(A, D, B)) => r2_lattice3(A, k2_tarski(C, D), B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_yellow_0)).
% 8.15/2.72  tff(f_83, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k1_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 8.15/2.72  tff(f_79, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_yellow_0(A, B) => ((C = k1_yellow_0(A, B)) <=> (r2_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) => r1_orders_2(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_yellow_0)).
% 8.15/2.72  tff(f_104, axiom, (![A]: ((v4_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) => (![D]: ((r1_lattice3(A, D, C) => r1_lattice3(A, D, B)) & (r2_lattice3(A, D, B) => r2_lattice3(A, D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_0)).
% 8.15/2.72  tff(f_31, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 8.15/2.72  tff(c_84, plain, (r2_lattice3('#skF_3', '#skF_4', '#skF_7') | r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_214])).
% 8.15/2.72  tff(c_125, plain, (r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_84])).
% 8.15/2.72  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 8.15/2.72  tff(c_78, plain, (~r2_lattice3('#skF_3', '#skF_5', '#skF_7') | ~r2_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_214])).
% 8.15/2.72  tff(c_126, plain, (~r2_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_78])).
% 8.15/2.72  tff(c_70, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_214])).
% 8.15/2.72  tff(c_60, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_214])).
% 8.15/2.72  tff(c_24, plain, (![A_11, B_18, C_19]: (r2_hidden('#skF_1'(A_11, B_18, C_19), B_18) | r2_lattice3(A_11, B_18, C_19) | ~m1_subset_1(C_19, u1_struct_0(A_11)) | ~l1_orders_2(A_11))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.15/2.72  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_214])).
% 8.15/2.72  tff(c_140, plain, (![A_140, C_141, B_142]: (m1_subset_1(A_140, C_141) | ~m1_subset_1(B_142, k1_zfmisc_1(C_141)) | ~r2_hidden(A_140, B_142))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.15/2.72  tff(c_148, plain, (![A_140]: (m1_subset_1(A_140, u1_struct_0('#skF_3')) | ~r2_hidden(A_140, '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_140])).
% 8.15/2.72  tff(c_10, plain, (![A_3, B_4]: (r1_tarski(k1_tarski(A_3), B_4) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.15/2.72  tff(c_18, plain, (![A_10]: (v1_finset_1(k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.15/2.72  tff(c_14, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.15/2.72  tff(c_163, plain, (![D_150]: (r1_yellow_0('#skF_3', D_150) | k1_xboole_0=D_150 | ~m1_subset_1(D_150, k1_zfmisc_1('#skF_4')) | ~v1_finset_1(D_150))), inference(cnfTransformation, [status(thm)], [f_214])).
% 8.15/2.72  tff(c_168, plain, (![A_5]: (r1_yellow_0('#skF_3', A_5) | k1_xboole_0=A_5 | ~v1_finset_1(A_5) | ~r1_tarski(A_5, '#skF_4'))), inference(resolution, [status(thm)], [c_14, c_163])).
% 8.15/2.72  tff(c_62, plain, (![D_125]: (r2_hidden(k1_yellow_0('#skF_3', D_125), '#skF_5') | k1_xboole_0=D_125 | ~m1_subset_1(D_125, k1_zfmisc_1('#skF_4')) | ~v1_finset_1(D_125))), inference(cnfTransformation, [status(thm)], [f_214])).
% 8.15/2.72  tff(c_66, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_214])).
% 8.15/2.72  tff(c_149, plain, (![A_140]: (m1_subset_1(A_140, u1_struct_0('#skF_3')) | ~r2_hidden(A_140, '#skF_5'))), inference(resolution, [status(thm)], [c_66, c_140])).
% 8.15/2.72  tff(c_72, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_214])).
% 8.15/2.72  tff(c_4, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 8.15/2.72  tff(c_252, plain, (![A_164, B_165, D_166, C_167]: (r2_lattice3(A_164, B_165, D_166) | ~r2_lattice3(A_164, C_167, D_166) | ~m1_subset_1(D_166, u1_struct_0(A_164)) | ~r1_tarski(B_165, C_167) | ~l1_orders_2(A_164))), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.15/2.72  tff(c_254, plain, (![B_165]: (r2_lattice3('#skF_3', B_165, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_tarski(B_165, '#skF_5') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_125, c_252])).
% 8.15/2.72  tff(c_257, plain, (![B_165]: (r2_lattice3('#skF_3', B_165, '#skF_7') | ~r1_tarski(B_165, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_60, c_254])).
% 8.15/2.72  tff(c_690, plain, (![A_237, D_238, B_239, C_240]: (r1_orders_2(A_237, D_238, B_239) | ~r2_lattice3(A_237, k2_tarski(C_240, D_238), B_239) | ~m1_subset_1(D_238, u1_struct_0(A_237)) | ~m1_subset_1(C_240, u1_struct_0(A_237)) | ~m1_subset_1(B_239, u1_struct_0(A_237)) | ~l1_orders_2(A_237))), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.15/2.72  tff(c_726, plain, (![D_238, C_240]: (r1_orders_2('#skF_3', D_238, '#skF_7') | ~m1_subset_1(D_238, u1_struct_0('#skF_3')) | ~m1_subset_1(C_240, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r1_tarski(k2_tarski(C_240, D_238), '#skF_5'))), inference(resolution, [status(thm)], [c_257, c_690])).
% 8.15/2.72  tff(c_774, plain, (![D_243, C_244]: (r1_orders_2('#skF_3', D_243, '#skF_7') | ~m1_subset_1(D_243, u1_struct_0('#skF_3')) | ~m1_subset_1(C_244, u1_struct_0('#skF_3')) | ~r1_tarski(k2_tarski(C_244, D_243), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_60, c_726])).
% 8.15/2.72  tff(c_778, plain, (![A_245]: (r1_orders_2('#skF_3', A_245, '#skF_7') | ~m1_subset_1(A_245, u1_struct_0('#skF_3')) | ~m1_subset_1(A_245, u1_struct_0('#skF_3')) | ~r1_tarski(k1_tarski(A_245), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_774])).
% 8.15/2.72  tff(c_787, plain, (![A_248]: (r1_orders_2('#skF_3', A_248, '#skF_7') | ~m1_subset_1(A_248, u1_struct_0('#skF_3')) | ~r2_hidden(A_248, '#skF_5'))), inference(resolution, [status(thm)], [c_10, c_778])).
% 8.15/2.72  tff(c_820, plain, (![A_140]: (r1_orders_2('#skF_3', A_140, '#skF_7') | ~r2_hidden(A_140, '#skF_5'))), inference(resolution, [status(thm)], [c_149, c_787])).
% 8.15/2.72  tff(c_38, plain, (![A_35, B_36]: (m1_subset_1(k1_yellow_0(A_35, B_36), u1_struct_0(A_35)) | ~l1_orders_2(A_35))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.15/2.72  tff(c_293, plain, (![A_177, B_178]: (r2_lattice3(A_177, B_178, k1_yellow_0(A_177, B_178)) | ~r1_yellow_0(A_177, B_178) | ~m1_subset_1(k1_yellow_0(A_177, B_178), u1_struct_0(A_177)) | ~l1_orders_2(A_177))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.15/2.72  tff(c_318, plain, (![A_35, B_36]: (r2_lattice3(A_35, B_36, k1_yellow_0(A_35, B_36)) | ~r1_yellow_0(A_35, B_36) | ~l1_orders_2(A_35))), inference(resolution, [status(thm)], [c_38, c_293])).
% 8.15/2.72  tff(c_495, plain, (![A_219, D_220, C_221, B_222]: (r2_lattice3(A_219, D_220, C_221) | ~r2_lattice3(A_219, D_220, B_222) | ~r1_orders_2(A_219, B_222, C_221) | ~m1_subset_1(C_221, u1_struct_0(A_219)) | ~m1_subset_1(B_222, u1_struct_0(A_219)) | ~l1_orders_2(A_219) | ~v4_orders_2(A_219))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.15/2.72  tff(c_4869, plain, (![A_682, B_683, C_684]: (r2_lattice3(A_682, B_683, C_684) | ~r1_orders_2(A_682, k1_yellow_0(A_682, B_683), C_684) | ~m1_subset_1(C_684, u1_struct_0(A_682)) | ~m1_subset_1(k1_yellow_0(A_682, B_683), u1_struct_0(A_682)) | ~v4_orders_2(A_682) | ~r1_yellow_0(A_682, B_683) | ~l1_orders_2(A_682))), inference(resolution, [status(thm)], [c_318, c_495])).
% 8.15/2.72  tff(c_4915, plain, (![B_683]: (r2_lattice3('#skF_3', B_683, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~m1_subset_1(k1_yellow_0('#skF_3', B_683), u1_struct_0('#skF_3')) | ~v4_orders_2('#skF_3') | ~r1_yellow_0('#skF_3', B_683) | ~l1_orders_2('#skF_3') | ~r2_hidden(k1_yellow_0('#skF_3', B_683), '#skF_5'))), inference(resolution, [status(thm)], [c_820, c_4869])).
% 8.15/2.72  tff(c_4965, plain, (![B_685]: (r2_lattice3('#skF_3', B_685, '#skF_7') | ~m1_subset_1(k1_yellow_0('#skF_3', B_685), u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', B_685) | ~r2_hidden(k1_yellow_0('#skF_3', B_685), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_72, c_60, c_4915])).
% 8.15/2.72  tff(c_4991, plain, (![B_686]: (r2_lattice3('#skF_3', B_686, '#skF_7') | ~r1_yellow_0('#skF_3', B_686) | ~r2_hidden(k1_yellow_0('#skF_3', B_686), '#skF_5'))), inference(resolution, [status(thm)], [c_149, c_4965])).
% 8.15/2.72  tff(c_4999, plain, (![D_687]: (r2_lattice3('#skF_3', D_687, '#skF_7') | ~r1_yellow_0('#skF_3', D_687) | k1_xboole_0=D_687 | ~m1_subset_1(D_687, k1_zfmisc_1('#skF_4')) | ~v1_finset_1(D_687))), inference(resolution, [status(thm)], [c_62, c_4991])).
% 8.15/2.72  tff(c_5019, plain, (![A_688]: (r2_lattice3('#skF_3', A_688, '#skF_7') | ~r1_yellow_0('#skF_3', A_688) | k1_xboole_0=A_688 | ~v1_finset_1(A_688) | ~r1_tarski(A_688, '#skF_4'))), inference(resolution, [status(thm)], [c_14, c_4999])).
% 8.15/2.72  tff(c_911, plain, (![A_265, C_266, B_267, D_268]: (r1_orders_2(A_265, C_266, B_267) | ~r2_lattice3(A_265, k2_tarski(C_266, D_268), B_267) | ~m1_subset_1(D_268, u1_struct_0(A_265)) | ~m1_subset_1(C_266, u1_struct_0(A_265)) | ~m1_subset_1(B_267, u1_struct_0(A_265)) | ~l1_orders_2(A_265))), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.15/2.72  tff(c_966, plain, (![A_265, A_1, B_267]: (r1_orders_2(A_265, A_1, B_267) | ~r2_lattice3(A_265, k1_tarski(A_1), B_267) | ~m1_subset_1(A_1, u1_struct_0(A_265)) | ~m1_subset_1(A_1, u1_struct_0(A_265)) | ~m1_subset_1(B_267, u1_struct_0(A_265)) | ~l1_orders_2(A_265))), inference(superposition, [status(thm), theory('equality')], [c_4, c_911])).
% 8.15/2.72  tff(c_5033, plain, (![A_1]: (r1_orders_2('#skF_3', A_1, '#skF_7') | ~m1_subset_1(A_1, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r1_yellow_0('#skF_3', k1_tarski(A_1)) | k1_tarski(A_1)=k1_xboole_0 | ~v1_finset_1(k1_tarski(A_1)) | ~r1_tarski(k1_tarski(A_1), '#skF_4'))), inference(resolution, [status(thm)], [c_5019, c_966])).
% 8.15/2.72  tff(c_5174, plain, (![A_702]: (r1_orders_2('#skF_3', A_702, '#skF_7') | ~m1_subset_1(A_702, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', k1_tarski(A_702)) | k1_tarski(A_702)=k1_xboole_0 | ~r1_tarski(k1_tarski(A_702), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_70, c_60, c_5033])).
% 8.15/2.72  tff(c_5177, plain, (![A_702]: (r1_orders_2('#skF_3', A_702, '#skF_7') | ~m1_subset_1(A_702, u1_struct_0('#skF_3')) | k1_tarski(A_702)=k1_xboole_0 | ~v1_finset_1(k1_tarski(A_702)) | ~r1_tarski(k1_tarski(A_702), '#skF_4'))), inference(resolution, [status(thm)], [c_168, c_5174])).
% 8.15/2.72  tff(c_5198, plain, (![A_704]: (r1_orders_2('#skF_3', A_704, '#skF_7') | ~m1_subset_1(A_704, u1_struct_0('#skF_3')) | k1_tarski(A_704)=k1_xboole_0 | ~r1_tarski(k1_tarski(A_704), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_5177])).
% 8.15/2.72  tff(c_5204, plain, (![A_705]: (r1_orders_2('#skF_3', A_705, '#skF_7') | ~m1_subset_1(A_705, u1_struct_0('#skF_3')) | k1_tarski(A_705)=k1_xboole_0 | ~r2_hidden(A_705, '#skF_4'))), inference(resolution, [status(thm)], [c_10, c_5198])).
% 8.15/2.72  tff(c_5250, plain, (![A_706]: (r1_orders_2('#skF_3', A_706, '#skF_7') | k1_tarski(A_706)=k1_xboole_0 | ~r2_hidden(A_706, '#skF_4'))), inference(resolution, [status(thm)], [c_148, c_5204])).
% 8.15/2.72  tff(c_22, plain, (![A_11, B_18, C_19]: (~r1_orders_2(A_11, '#skF_1'(A_11, B_18, C_19), C_19) | r2_lattice3(A_11, B_18, C_19) | ~m1_subset_1(C_19, u1_struct_0(A_11)) | ~l1_orders_2(A_11))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.15/2.72  tff(c_5299, plain, (![B_18]: (r2_lattice3('#skF_3', B_18, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | k1_tarski('#skF_1'('#skF_3', B_18, '#skF_7'))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_18, '#skF_7'), '#skF_4'))), inference(resolution, [status(thm)], [c_5250, c_22])).
% 8.15/2.72  tff(c_5345, plain, (![B_707]: (r2_lattice3('#skF_3', B_707, '#skF_7') | k1_tarski('#skF_1'('#skF_3', B_707, '#skF_7'))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_707, '#skF_7'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_60, c_5299])).
% 8.15/2.72  tff(c_5349, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0 | r2_lattice3('#skF_3', '#skF_4', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_24, c_5345])).
% 8.15/2.72  tff(c_5352, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0 | r2_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_60, c_5349])).
% 8.15/2.72  tff(c_5353, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_126, c_5352])).
% 8.15/2.72  tff(c_6, plain, (![A_2]: (~v1_xboole_0(k1_tarski(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.15/2.72  tff(c_5540, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5353, c_6])).
% 8.15/2.72  tff(c_5561, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_5540])).
% 8.15/2.72  tff(c_5562, plain, (~r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_78])).
% 8.15/2.72  tff(c_5565, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_5562])).
% 8.15/2.72  tff(c_5567, plain, (~r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_84])).
% 8.15/2.72  tff(c_5588, plain, (![A_714, C_715, B_716]: (m1_subset_1(A_714, C_715) | ~m1_subset_1(B_716, k1_zfmisc_1(C_715)) | ~r2_hidden(A_714, B_716))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.15/2.72  tff(c_5597, plain, (![A_714]: (m1_subset_1(A_714, u1_struct_0('#skF_3')) | ~r2_hidden(A_714, '#skF_5'))), inference(resolution, [status(thm)], [c_66, c_5588])).
% 8.15/2.72  tff(c_5616, plain, (![D_724]: (m1_subset_1('#skF_6'(D_724), k1_zfmisc_1('#skF_4')) | ~r2_hidden(D_724, '#skF_5') | ~m1_subset_1(D_724, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_214])).
% 8.15/2.72  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.15/2.72  tff(c_5627, plain, (![D_724]: (r1_tarski('#skF_6'(D_724), '#skF_4') | ~r2_hidden(D_724, '#skF_5') | ~m1_subset_1(D_724, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_5616, c_12])).
% 8.15/2.72  tff(c_88, plain, (![D_123]: (r1_yellow_0('#skF_3', '#skF_6'(D_123)) | ~r2_hidden(D_123, '#skF_5') | ~m1_subset_1(D_123, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_214])).
% 8.15/2.72  tff(c_5566, plain, (r2_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(splitRight, [status(thm)], [c_84])).
% 8.15/2.72  tff(c_5742, plain, (![A_751, B_752, D_753, C_754]: (r2_lattice3(A_751, B_752, D_753) | ~r2_lattice3(A_751, C_754, D_753) | ~m1_subset_1(D_753, u1_struct_0(A_751)) | ~r1_tarski(B_752, C_754) | ~l1_orders_2(A_751))), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.15/2.72  tff(c_5752, plain, (![B_752]: (r2_lattice3('#skF_3', B_752, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_tarski(B_752, '#skF_4') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_5566, c_5742])).
% 8.15/2.72  tff(c_5765, plain, (![B_752]: (r2_lattice3('#skF_3', B_752, '#skF_7') | ~r1_tarski(B_752, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_60, c_5752])).
% 8.15/2.72  tff(c_5630, plain, (![D_727]: (k1_yellow_0('#skF_3', '#skF_6'(D_727))=D_727 | ~r2_hidden(D_727, '#skF_5') | ~m1_subset_1(D_727, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_214])).
% 8.15/2.72  tff(c_5644, plain, (![A_714]: (k1_yellow_0('#skF_3', '#skF_6'(A_714))=A_714 | ~r2_hidden(A_714, '#skF_5'))), inference(resolution, [status(thm)], [c_5597, c_5630])).
% 8.15/2.72  tff(c_7067, plain, (![A_956, B_957, D_958]: (r1_orders_2(A_956, k1_yellow_0(A_956, B_957), D_958) | ~r2_lattice3(A_956, B_957, D_958) | ~m1_subset_1(D_958, u1_struct_0(A_956)) | ~r1_yellow_0(A_956, B_957) | ~m1_subset_1(k1_yellow_0(A_956, B_957), u1_struct_0(A_956)) | ~l1_orders_2(A_956))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.15/2.72  tff(c_7093, plain, (![A_959, B_960, D_961]: (r1_orders_2(A_959, k1_yellow_0(A_959, B_960), D_961) | ~r2_lattice3(A_959, B_960, D_961) | ~m1_subset_1(D_961, u1_struct_0(A_959)) | ~r1_yellow_0(A_959, B_960) | ~l1_orders_2(A_959))), inference(resolution, [status(thm)], [c_38, c_7067])).
% 8.15/2.72  tff(c_7106, plain, (![A_714, D_961]: (r1_orders_2('#skF_3', A_714, D_961) | ~r2_lattice3('#skF_3', '#skF_6'(A_714), D_961) | ~m1_subset_1(D_961, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', '#skF_6'(A_714)) | ~l1_orders_2('#skF_3') | ~r2_hidden(A_714, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5644, c_7093])).
% 8.15/2.72  tff(c_7116, plain, (![A_962, D_963]: (r1_orders_2('#skF_3', A_962, D_963) | ~r2_lattice3('#skF_3', '#skF_6'(A_962), D_963) | ~m1_subset_1(D_963, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', '#skF_6'(A_962)) | ~r2_hidden(A_962, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_7106])).
% 8.15/2.72  tff(c_7167, plain, (![A_962]: (r1_orders_2('#skF_3', A_962, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', '#skF_6'(A_962)) | ~r2_hidden(A_962, '#skF_5') | ~r1_tarski('#skF_6'(A_962), '#skF_4'))), inference(resolution, [status(thm)], [c_5765, c_7116])).
% 8.15/2.72  tff(c_7210, plain, (![A_964]: (r1_orders_2('#skF_3', A_964, '#skF_7') | ~r1_yellow_0('#skF_3', '#skF_6'(A_964)) | ~r2_hidden(A_964, '#skF_5') | ~r1_tarski('#skF_6'(A_964), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_7167])).
% 8.15/2.72  tff(c_7219, plain, (![D_965]: (r1_orders_2('#skF_3', D_965, '#skF_7') | ~r1_tarski('#skF_6'(D_965), '#skF_4') | ~r2_hidden(D_965, '#skF_5') | ~m1_subset_1(D_965, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_88, c_7210])).
% 8.15/2.72  tff(c_7224, plain, (![D_966]: (r1_orders_2('#skF_3', D_966, '#skF_7') | ~r2_hidden(D_966, '#skF_5') | ~m1_subset_1(D_966, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_5627, c_7219])).
% 8.15/2.72  tff(c_7270, plain, (![A_967]: (r1_orders_2('#skF_3', A_967, '#skF_7') | ~r2_hidden(A_967, '#skF_5'))), inference(resolution, [status(thm)], [c_5597, c_7224])).
% 8.15/2.72  tff(c_7278, plain, (![B_18]: (r2_lattice3('#skF_3', B_18, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r2_hidden('#skF_1'('#skF_3', B_18, '#skF_7'), '#skF_5'))), inference(resolution, [status(thm)], [c_7270, c_22])).
% 8.15/2.72  tff(c_7288, plain, (![B_968]: (r2_lattice3('#skF_3', B_968, '#skF_7') | ~r2_hidden('#skF_1'('#skF_3', B_968, '#skF_7'), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_60, c_7278])).
% 8.15/2.72  tff(c_7292, plain, (r2_lattice3('#skF_3', '#skF_5', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_24, c_7288])).
% 8.15/2.72  tff(c_7295, plain, (r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_60, c_7292])).
% 8.15/2.72  tff(c_7297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5567, c_7295])).
% 8.15/2.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.15/2.72  
% 8.15/2.72  Inference rules
% 8.15/2.72  ----------------------
% 8.15/2.72  #Ref     : 0
% 8.15/2.72  #Sup     : 1514
% 8.15/2.72  #Fact    : 0
% 8.15/2.72  #Define  : 0
% 8.15/2.72  #Split   : 25
% 8.15/2.72  #Chain   : 0
% 8.15/2.72  #Close   : 0
% 8.15/2.72  
% 8.15/2.72  Ordering : KBO
% 8.15/2.72  
% 8.15/2.72  Simplification rules
% 8.15/2.72  ----------------------
% 8.15/2.72  #Subsume      : 331
% 8.15/2.72  #Demod        : 914
% 8.15/2.72  #Tautology    : 50
% 8.15/2.72  #SimpNegUnit  : 8
% 8.15/2.72  #BackRed      : 0
% 8.15/2.72  
% 8.15/2.72  #Partial instantiations: 0
% 8.15/2.72  #Strategies tried      : 1
% 8.15/2.72  
% 8.15/2.72  Timing (in seconds)
% 8.15/2.72  ----------------------
% 8.15/2.72  Preprocessing        : 0.38
% 8.15/2.72  Parsing              : 0.20
% 8.15/2.72  CNF conversion       : 0.03
% 8.15/2.72  Main loop            : 1.69
% 8.15/2.72  Inferencing          : 0.57
% 8.15/2.72  Reduction            : 0.47
% 8.15/2.72  Demodulation         : 0.30
% 8.15/2.72  BG Simplification    : 0.06
% 8.15/2.72  Subsumption          : 0.46
% 8.15/2.72  Abstraction          : 0.07
% 8.15/2.72  MUC search           : 0.00
% 8.15/2.72  Cooper               : 0.00
% 8.15/2.72  Total                : 2.12
% 8.15/2.72  Index Insertion      : 0.00
% 8.15/2.72  Index Deletion       : 0.00
% 8.15/2.72  Index Matching       : 0.00
% 8.15/2.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
