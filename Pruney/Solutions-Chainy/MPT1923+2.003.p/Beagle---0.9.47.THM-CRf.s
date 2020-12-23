%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:46 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 285 expanded)
%              Number of leaves         :   33 ( 118 expanded)
%              Depth                    :   13
%              Number of atoms          :  172 (1181 expanded)
%              Number of equality atoms :   11 ( 148 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_yellow_6 > r1_orders_2 > m1_yellow_6 > v4_yellow_0 > r2_hidden > m1_yellow_0 > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(v4_yellow_0,type,(
    v4_yellow_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(m1_yellow_0,type,(
    m1_yellow_0: ( $i * $i ) > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(m1_yellow_6,type,(
    m1_yellow_6: ( $i * $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_yellow_6,type,(
    v2_yellow_6: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_waybel_0(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & v2_yellow_6(C,A,B)
                  & m1_yellow_6(C,A,B) )
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(B))
                   => ! [E] :
                        ( m1_subset_1(E,u1_struct_0(B))
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(C))
                           => ! [G] :
                                ( m1_subset_1(G,u1_struct_0(C))
                               => ( ( D = F
                                    & E = G
                                    & r1_orders_2(B,D,E) )
                                 => r1_orders_2(C,F,G) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_yellow_6)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => ! [C] :
          ( m1_yellow_6(C,A,B)
         => l1_waybel_0(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_6)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => ! [C] :
              ( m1_yellow_6(C,A,B)
             => ( v2_yellow_6(C,A,B)
              <=> ( v4_yellow_0(C,B)
                  & m1_yellow_0(C,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_6)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( ( v4_yellow_0(B,A)
            & m1_yellow_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(B))
                         => ( ( E = C
                              & F = D
                              & r1_orders_2(A,C,D)
                              & r2_hidden(E,u1_struct_0(B)) )
                           => r1_orders_2(B,E,F) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_yellow_0)).

tff(f_43,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_48,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_44,plain,(
    l1_waybel_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_38,plain,(
    m1_yellow_6('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_94,plain,(
    ! [C_211,A_212,B_213] :
      ( l1_waybel_0(C_211,A_212)
      | ~ m1_yellow_6(C_211,A_212,B_213)
      | ~ l1_waybel_0(B_213,A_212)
      | ~ l1_struct_0(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_97,plain,
    ( l1_waybel_0('#skF_3','#skF_1')
    | ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_94])).

tff(c_100,plain,(
    l1_waybel_0('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_97])).

tff(c_12,plain,(
    ! [B_71,A_69] :
      ( l1_orders_2(B_71)
      | ~ l1_waybel_0(B_71,A_69)
      | ~ l1_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_103,plain,
    ( l1_orders_2('#skF_3')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_100,c_12])).

tff(c_106,plain,(
    l1_orders_2('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_103])).

tff(c_8,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_26,plain,(
    '#skF_7' = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_28,plain,(
    '#skF_6' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_22,plain,(
    ~ r1_orders_2('#skF_3','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_51,plain,(
    ~ r1_orders_2('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_22])).

tff(c_61,plain,(
    ! [A_204] :
      ( u1_struct_0(A_204) = k2_struct_0(A_204)
      | ~ l1_struct_0(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_68,plain,(
    ! [A_5] :
      ( u1_struct_0(A_5) = k2_struct_0(A_5)
      | ~ l1_orders_2(A_5) ) ),
    inference(resolution,[status(thm)],[c_8,c_61])).

tff(c_110,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_68])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_49,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32])).

tff(c_112,plain,(
    m1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_49])).

tff(c_40,plain,(
    v2_yellow_6('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_117,plain,(
    ! [C_214,B_215,A_216] :
      ( v4_yellow_0(C_214,B_215)
      | ~ v2_yellow_6(C_214,A_216,B_215)
      | ~ m1_yellow_6(C_214,A_216,B_215)
      | ~ l1_waybel_0(B_215,A_216)
      | ~ l1_struct_0(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_120,plain,
    ( v4_yellow_0('#skF_3','#skF_2')
    | ~ m1_yellow_6('#skF_3','#skF_1','#skF_2')
    | ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_117])).

tff(c_123,plain,(
    v4_yellow_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_38,c_120])).

tff(c_124,plain,(
    ! [C_217,B_218,A_219] :
      ( m1_yellow_0(C_217,B_218)
      | ~ v2_yellow_6(C_217,A_219,B_218)
      | ~ m1_yellow_6(C_217,A_219,B_218)
      | ~ l1_waybel_0(B_218,A_219)
      | ~ l1_struct_0(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_127,plain,
    ( m1_yellow_0('#skF_3','#skF_2')
    | ~ m1_yellow_6('#skF_3','#skF_1','#skF_2')
    | ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_124])).

tff(c_130,plain,(
    m1_yellow_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_38,c_127])).

tff(c_30,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_30])).

tff(c_111,plain,(
    m1_subset_1('#skF_5',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_50])).

tff(c_75,plain,(
    ! [B_206,A_207] :
      ( l1_orders_2(B_206)
      | ~ l1_waybel_0(B_206,A_207)
      | ~ l1_struct_0(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_78,plain,
    ( l1_orders_2('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_75])).

tff(c_81,plain,(
    l1_orders_2('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_78])).

tff(c_85,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_81,c_68])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_87,plain,(
    m1_subset_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_36])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_86,plain,(
    m1_subset_1('#skF_5',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_34])).

tff(c_24,plain,(
    r1_orders_2('#skF_2','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_140,plain,(
    ! [B_223,E_224,F_225,A_226] :
      ( r1_orders_2(B_223,E_224,F_225)
      | ~ r2_hidden(E_224,u1_struct_0(B_223))
      | ~ r1_orders_2(A_226,E_224,F_225)
      | ~ m1_subset_1(F_225,u1_struct_0(B_223))
      | ~ m1_subset_1(E_224,u1_struct_0(B_223))
      | ~ m1_subset_1(F_225,u1_struct_0(A_226))
      | ~ m1_subset_1(E_224,u1_struct_0(A_226))
      | ~ m1_yellow_0(B_223,A_226)
      | ~ v4_yellow_0(B_223,A_226)
      | ~ l1_orders_2(A_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_154,plain,(
    ! [B_227,A_228,F_229,A_230] :
      ( r1_orders_2(B_227,A_228,F_229)
      | ~ r1_orders_2(A_230,A_228,F_229)
      | ~ m1_subset_1(F_229,u1_struct_0(B_227))
      | ~ m1_subset_1(F_229,u1_struct_0(A_230))
      | ~ m1_subset_1(A_228,u1_struct_0(A_230))
      | ~ m1_yellow_0(B_227,A_230)
      | ~ v4_yellow_0(B_227,A_230)
      | ~ l1_orders_2(A_230)
      | v1_xboole_0(u1_struct_0(B_227))
      | ~ m1_subset_1(A_228,u1_struct_0(B_227)) ) ),
    inference(resolution,[status(thm)],[c_2,c_140])).

tff(c_156,plain,(
    ! [B_227] :
      ( r1_orders_2(B_227,'#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0(B_227))
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ m1_yellow_0(B_227,'#skF_2')
      | ~ v4_yellow_0(B_227,'#skF_2')
      | ~ l1_orders_2('#skF_2')
      | v1_xboole_0(u1_struct_0(B_227))
      | ~ m1_subset_1('#skF_4',u1_struct_0(B_227)) ) ),
    inference(resolution,[status(thm)],[c_24,c_154])).

tff(c_160,plain,(
    ! [B_231] :
      ( r1_orders_2(B_231,'#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0(B_231))
      | ~ m1_yellow_0(B_231,'#skF_2')
      | ~ v4_yellow_0(B_231,'#skF_2')
      | v1_xboole_0(u1_struct_0(B_231))
      | ~ m1_subset_1('#skF_4',u1_struct_0(B_231)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_87,c_85,c_86,c_85,c_156])).

tff(c_163,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k2_struct_0('#skF_3'))
    | ~ m1_yellow_0('#skF_3','#skF_2')
    | ~ v4_yellow_0('#skF_3','#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_160])).

tff(c_171,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_5')
    | v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_110,c_110,c_123,c_130,c_111,c_163])).

tff(c_172,plain,(
    v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_171])).

tff(c_6,plain,(
    ! [A_4] :
      ( ~ v1_xboole_0(k2_struct_0(A_4))
      | ~ l1_struct_0(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_178,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_172,c_6])).

tff(c_181,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_178])).

tff(c_184,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_181])).

tff(c_188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_184])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:50:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.25  
% 2.30/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.25  %$ v2_yellow_6 > r1_orders_2 > m1_yellow_6 > v4_yellow_0 > r2_hidden > m1_yellow_0 > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.30/1.25  
% 2.30/1.25  %Foreground sorts:
% 2.30/1.25  
% 2.30/1.25  
% 2.30/1.25  %Background operators:
% 2.30/1.25  
% 2.30/1.25  
% 2.30/1.25  %Foreground operators:
% 2.30/1.25  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.30/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.30/1.25  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.30/1.25  tff(v4_yellow_0, type, v4_yellow_0: ($i * $i) > $o).
% 2.30/1.25  tff('#skF_7', type, '#skF_7': $i).
% 2.30/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.30/1.25  tff('#skF_6', type, '#skF_6': $i).
% 2.30/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.30/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.30/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.30/1.25  tff(m1_yellow_0, type, m1_yellow_0: ($i * $i) > $o).
% 2.30/1.25  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.30/1.25  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.30/1.25  tff(m1_yellow_6, type, m1_yellow_6: ($i * $i * $i) > $o).
% 2.30/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.25  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.30/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.30/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.25  tff(v2_yellow_6, type, v2_yellow_6: ($i * $i * $i) > $o).
% 2.30/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.30/1.25  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.30/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.30/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.30/1.25  
% 2.30/1.27  tff(f_143, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (((~v2_struct_0(C) & v2_yellow_6(C, A, B)) & m1_yellow_6(C, A, B)) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((((D = F) & (E = G)) & r1_orders_2(B, D, E)) => r1_orders_2(C, F, G)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_yellow_6)).
% 2.30/1.27  tff(f_106, axiom, (![A, B]: ((l1_struct_0(A) & l1_waybel_0(B, A)) => (![C]: (m1_yellow_6(C, A, B) => l1_waybel_0(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_yellow_6)).
% 2.30/1.27  tff(f_83, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 2.30/1.27  tff(f_47, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.30/1.27  tff(f_35, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.30/1.27  tff(f_97, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => (![C]: (m1_yellow_6(C, A, B) => (v2_yellow_6(C, A, B) <=> (v4_yellow_0(C, B) & m1_yellow_0(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_yellow_6)).
% 2.30/1.27  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.30/1.27  tff(f_76, axiom, (![A]: (l1_orders_2(A) => (![B]: ((v4_yellow_0(B, A) & m1_yellow_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (((((E = C) & (F = D)) & r1_orders_2(A, C, D)) & r2_hidden(E, u1_struct_0(B))) => r1_orders_2(B, E, F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_yellow_0)).
% 2.30/1.27  tff(f_43, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 2.30/1.27  tff(c_48, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.30/1.27  tff(c_44, plain, (l1_waybel_0('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.30/1.27  tff(c_38, plain, (m1_yellow_6('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.30/1.27  tff(c_94, plain, (![C_211, A_212, B_213]: (l1_waybel_0(C_211, A_212) | ~m1_yellow_6(C_211, A_212, B_213) | ~l1_waybel_0(B_213, A_212) | ~l1_struct_0(A_212))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.30/1.27  tff(c_97, plain, (l1_waybel_0('#skF_3', '#skF_1') | ~l1_waybel_0('#skF_2', '#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_94])).
% 2.30/1.27  tff(c_100, plain, (l1_waybel_0('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_97])).
% 2.30/1.27  tff(c_12, plain, (![B_71, A_69]: (l1_orders_2(B_71) | ~l1_waybel_0(B_71, A_69) | ~l1_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.30/1.27  tff(c_103, plain, (l1_orders_2('#skF_3') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_100, c_12])).
% 2.30/1.27  tff(c_106, plain, (l1_orders_2('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_103])).
% 2.30/1.27  tff(c_8, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_orders_2(A_5))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.30/1.27  tff(c_42, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.30/1.27  tff(c_26, plain, ('#skF_7'='#skF_5'), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.30/1.27  tff(c_28, plain, ('#skF_6'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.30/1.27  tff(c_22, plain, (~r1_orders_2('#skF_3', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.30/1.27  tff(c_51, plain, (~r1_orders_2('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_22])).
% 2.30/1.27  tff(c_61, plain, (![A_204]: (u1_struct_0(A_204)=k2_struct_0(A_204) | ~l1_struct_0(A_204))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.30/1.27  tff(c_68, plain, (![A_5]: (u1_struct_0(A_5)=k2_struct_0(A_5) | ~l1_orders_2(A_5))), inference(resolution, [status(thm)], [c_8, c_61])).
% 2.30/1.27  tff(c_110, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_106, c_68])).
% 2.30/1.27  tff(c_32, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.30/1.27  tff(c_49, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32])).
% 2.30/1.27  tff(c_112, plain, (m1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_49])).
% 2.30/1.27  tff(c_40, plain, (v2_yellow_6('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.30/1.27  tff(c_117, plain, (![C_214, B_215, A_216]: (v4_yellow_0(C_214, B_215) | ~v2_yellow_6(C_214, A_216, B_215) | ~m1_yellow_6(C_214, A_216, B_215) | ~l1_waybel_0(B_215, A_216) | ~l1_struct_0(A_216))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.30/1.27  tff(c_120, plain, (v4_yellow_0('#skF_3', '#skF_2') | ~m1_yellow_6('#skF_3', '#skF_1', '#skF_2') | ~l1_waybel_0('#skF_2', '#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_117])).
% 2.30/1.27  tff(c_123, plain, (v4_yellow_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_38, c_120])).
% 2.30/1.27  tff(c_124, plain, (![C_217, B_218, A_219]: (m1_yellow_0(C_217, B_218) | ~v2_yellow_6(C_217, A_219, B_218) | ~m1_yellow_6(C_217, A_219, B_218) | ~l1_waybel_0(B_218, A_219) | ~l1_struct_0(A_219))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.30/1.27  tff(c_127, plain, (m1_yellow_0('#skF_3', '#skF_2') | ~m1_yellow_6('#skF_3', '#skF_1', '#skF_2') | ~l1_waybel_0('#skF_2', '#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_124])).
% 2.30/1.27  tff(c_130, plain, (m1_yellow_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_38, c_127])).
% 2.30/1.27  tff(c_30, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.30/1.27  tff(c_50, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_30])).
% 2.30/1.27  tff(c_111, plain, (m1_subset_1('#skF_5', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_50])).
% 2.30/1.27  tff(c_75, plain, (![B_206, A_207]: (l1_orders_2(B_206) | ~l1_waybel_0(B_206, A_207) | ~l1_struct_0(A_207))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.30/1.27  tff(c_78, plain, (l1_orders_2('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_75])).
% 2.30/1.27  tff(c_81, plain, (l1_orders_2('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_78])).
% 2.30/1.27  tff(c_85, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_81, c_68])).
% 2.30/1.27  tff(c_36, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.30/1.27  tff(c_87, plain, (m1_subset_1('#skF_4', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_36])).
% 2.30/1.27  tff(c_34, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.30/1.27  tff(c_86, plain, (m1_subset_1('#skF_5', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_34])).
% 2.30/1.27  tff(c_24, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.30/1.27  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.30/1.27  tff(c_140, plain, (![B_223, E_224, F_225, A_226]: (r1_orders_2(B_223, E_224, F_225) | ~r2_hidden(E_224, u1_struct_0(B_223)) | ~r1_orders_2(A_226, E_224, F_225) | ~m1_subset_1(F_225, u1_struct_0(B_223)) | ~m1_subset_1(E_224, u1_struct_0(B_223)) | ~m1_subset_1(F_225, u1_struct_0(A_226)) | ~m1_subset_1(E_224, u1_struct_0(A_226)) | ~m1_yellow_0(B_223, A_226) | ~v4_yellow_0(B_223, A_226) | ~l1_orders_2(A_226))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.30/1.27  tff(c_154, plain, (![B_227, A_228, F_229, A_230]: (r1_orders_2(B_227, A_228, F_229) | ~r1_orders_2(A_230, A_228, F_229) | ~m1_subset_1(F_229, u1_struct_0(B_227)) | ~m1_subset_1(F_229, u1_struct_0(A_230)) | ~m1_subset_1(A_228, u1_struct_0(A_230)) | ~m1_yellow_0(B_227, A_230) | ~v4_yellow_0(B_227, A_230) | ~l1_orders_2(A_230) | v1_xboole_0(u1_struct_0(B_227)) | ~m1_subset_1(A_228, u1_struct_0(B_227)))), inference(resolution, [status(thm)], [c_2, c_140])).
% 2.30/1.27  tff(c_156, plain, (![B_227]: (r1_orders_2(B_227, '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0(B_227)) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_yellow_0(B_227, '#skF_2') | ~v4_yellow_0(B_227, '#skF_2') | ~l1_orders_2('#skF_2') | v1_xboole_0(u1_struct_0(B_227)) | ~m1_subset_1('#skF_4', u1_struct_0(B_227)))), inference(resolution, [status(thm)], [c_24, c_154])).
% 2.30/1.27  tff(c_160, plain, (![B_231]: (r1_orders_2(B_231, '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0(B_231)) | ~m1_yellow_0(B_231, '#skF_2') | ~v4_yellow_0(B_231, '#skF_2') | v1_xboole_0(u1_struct_0(B_231)) | ~m1_subset_1('#skF_4', u1_struct_0(B_231)))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_87, c_85, c_86, c_85, c_156])).
% 2.30/1.27  tff(c_163, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k2_struct_0('#skF_3')) | ~m1_yellow_0('#skF_3', '#skF_2') | ~v4_yellow_0('#skF_3', '#skF_2') | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_160])).
% 2.30/1.27  tff(c_171, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_5') | v1_xboole_0(k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_110, c_110, c_123, c_130, c_111, c_163])).
% 2.30/1.27  tff(c_172, plain, (v1_xboole_0(k2_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_51, c_171])).
% 2.30/1.27  tff(c_6, plain, (![A_4]: (~v1_xboole_0(k2_struct_0(A_4)) | ~l1_struct_0(A_4) | v2_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.30/1.27  tff(c_178, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_172, c_6])).
% 2.30/1.27  tff(c_181, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_42, c_178])).
% 2.30/1.27  tff(c_184, plain, (~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_8, c_181])).
% 2.30/1.27  tff(c_188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_184])).
% 2.30/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.27  
% 2.30/1.27  Inference rules
% 2.30/1.27  ----------------------
% 2.30/1.27  #Ref     : 0
% 2.30/1.27  #Sup     : 31
% 2.30/1.27  #Fact    : 0
% 2.30/1.27  #Define  : 0
% 2.30/1.27  #Split   : 0
% 2.30/1.27  #Chain   : 0
% 2.30/1.27  #Close   : 0
% 2.30/1.27  
% 2.30/1.27  Ordering : KBO
% 2.30/1.27  
% 2.30/1.27  Simplification rules
% 2.30/1.27  ----------------------
% 2.30/1.27  #Subsume      : 0
% 2.30/1.27  #Demod        : 43
% 2.30/1.27  #Tautology    : 13
% 2.30/1.27  #SimpNegUnit  : 2
% 2.30/1.27  #BackRed      : 4
% 2.30/1.27  
% 2.30/1.27  #Partial instantiations: 0
% 2.30/1.27  #Strategies tried      : 1
% 2.30/1.27  
% 2.30/1.27  Timing (in seconds)
% 2.30/1.27  ----------------------
% 2.30/1.27  Preprocessing        : 0.33
% 2.30/1.27  Parsing              : 0.18
% 2.30/1.27  CNF conversion       : 0.03
% 2.30/1.27  Main loop            : 0.18
% 2.30/1.27  Inferencing          : 0.07
% 2.30/1.27  Reduction            : 0.06
% 2.30/1.27  Demodulation         : 0.04
% 2.30/1.27  BG Simplification    : 0.02
% 2.30/1.27  Subsumption          : 0.02
% 2.30/1.27  Abstraction          : 0.01
% 2.30/1.27  MUC search           : 0.00
% 2.30/1.27  Cooper               : 0.00
% 2.30/1.27  Total                : 0.55
% 2.30/1.27  Index Insertion      : 0.00
% 2.30/1.27  Index Deletion       : 0.00
% 2.30/1.27  Index Matching       : 0.00
% 2.30/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
