%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:46 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 132 expanded)
%              Number of leaves         :   31 (  63 expanded)
%              Depth                    :    8
%              Number of atoms          :  169 ( 605 expanded)
%              Number of equality atoms :    6 (  66 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_yellow_6 > r1_orders_2 > m1_yellow_6 > v4_yellow_0 > r2_hidden > m1_yellow_0 > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > #nlpp > u1_struct_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_50,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_146,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_yellow_6)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => ! [C] :
              ( m1_yellow_6(C,A,B)
             => ( v2_yellow_6(C,A,B)
              <=> ( v4_yellow_0(C,B)
                  & m1_yellow_0(C,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_6)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_79,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_yellow_0)).

tff(f_46,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => ! [C] :
          ( m1_yellow_6(C,A,B)
         => l1_waybel_0(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow_6)).

tff(c_12,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_30,plain,(
    '#skF_7' = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_34,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34])).

tff(c_73,plain,(
    ! [B_207,A_208] :
      ( v1_xboole_0(B_207)
      | ~ m1_subset_1(B_207,A_208)
      | ~ v1_xboole_0(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_90,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_73])).

tff(c_95,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_32,plain,(
    '#skF_6' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_26,plain,(
    ~ r1_orders_2('#skF_3','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_55,plain,(
    ~ r1_orders_2('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_26])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_53,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36])).

tff(c_52,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_48,plain,(
    l1_waybel_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_42,plain,(
    m1_yellow_6('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_44,plain,(
    v2_yellow_6('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_116,plain,(
    ! [C_217,B_218,A_219] :
      ( v4_yellow_0(C_217,B_218)
      | ~ v2_yellow_6(C_217,A_219,B_218)
      | ~ m1_yellow_6(C_217,A_219,B_218)
      | ~ l1_waybel_0(B_218,A_219)
      | ~ l1_struct_0(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_119,plain,
    ( v4_yellow_0('#skF_3','#skF_2')
    | ~ m1_yellow_6('#skF_3','#skF_1','#skF_2')
    | ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_116])).

tff(c_122,plain,(
    v4_yellow_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_42,c_119])).

tff(c_123,plain,(
    ! [C_220,B_221,A_222] :
      ( m1_yellow_0(C_220,B_221)
      | ~ v2_yellow_6(C_220,A_222,B_221)
      | ~ m1_yellow_6(C_220,A_222,B_221)
      | ~ l1_waybel_0(B_221,A_222)
      | ~ l1_struct_0(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_126,plain,
    ( m1_yellow_0('#skF_3','#skF_2')
    | ~ m1_yellow_6('#skF_3','#skF_1','#skF_2')
    | ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_123])).

tff(c_129,plain,(
    m1_yellow_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_42,c_126])).

tff(c_66,plain,(
    ! [B_205,A_206] :
      ( l1_orders_2(B_205)
      | ~ l1_waybel_0(B_205,A_206)
      | ~ l1_struct_0(A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_69,plain,
    ( l1_orders_2('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_66])).

tff(c_72,plain,(
    l1_orders_2('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_69])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_28,plain,(
    r1_orders_2('#skF_2','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_139,plain,(
    ! [B_226,E_227,F_228,A_229] :
      ( r1_orders_2(B_226,E_227,F_228)
      | ~ r2_hidden(E_227,u1_struct_0(B_226))
      | ~ r1_orders_2(A_229,E_227,F_228)
      | ~ m1_subset_1(F_228,u1_struct_0(B_226))
      | ~ m1_subset_1(E_227,u1_struct_0(B_226))
      | ~ m1_subset_1(F_228,u1_struct_0(A_229))
      | ~ m1_subset_1(E_227,u1_struct_0(A_229))
      | ~ m1_yellow_0(B_226,A_229)
      | ~ v4_yellow_0(B_226,A_229)
      | ~ l1_orders_2(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_144,plain,(
    ! [B_230,B_231,F_232,A_233] :
      ( r1_orders_2(B_230,B_231,F_232)
      | ~ r1_orders_2(A_233,B_231,F_232)
      | ~ m1_subset_1(F_232,u1_struct_0(B_230))
      | ~ m1_subset_1(F_232,u1_struct_0(A_233))
      | ~ m1_subset_1(B_231,u1_struct_0(A_233))
      | ~ m1_yellow_0(B_230,A_233)
      | ~ v4_yellow_0(B_230,A_233)
      | ~ l1_orders_2(A_233)
      | ~ m1_subset_1(B_231,u1_struct_0(B_230))
      | v1_xboole_0(u1_struct_0(B_230)) ) ),
    inference(resolution,[status(thm)],[c_4,c_139])).

tff(c_146,plain,(
    ! [B_230] :
      ( r1_orders_2(B_230,'#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0(B_230))
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ m1_yellow_0(B_230,'#skF_2')
      | ~ v4_yellow_0(B_230,'#skF_2')
      | ~ l1_orders_2('#skF_2')
      | ~ m1_subset_1('#skF_4',u1_struct_0(B_230))
      | v1_xboole_0(u1_struct_0(B_230)) ) ),
    inference(resolution,[status(thm)],[c_28,c_144])).

tff(c_150,plain,(
    ! [B_234] :
      ( r1_orders_2(B_234,'#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0(B_234))
      | ~ m1_yellow_0(B_234,'#skF_2')
      | ~ v4_yellow_0(B_234,'#skF_2')
      | ~ m1_subset_1('#skF_4',u1_struct_0(B_234))
      | v1_xboole_0(u1_struct_0(B_234)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_40,c_38,c_146])).

tff(c_156,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_5')
    | ~ m1_yellow_0('#skF_3','#skF_2')
    | ~ v4_yellow_0('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_150])).

tff(c_163,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_122,c_129,c_156])).

tff(c_165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_55,c_163])).

tff(c_167,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_10,plain,(
    ! [A_3] :
      ( ~ v1_xboole_0(u1_struct_0(A_3))
      | ~ l1_struct_0(A_3)
      | v2_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_176,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_167,c_10])).

tff(c_179,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_176])).

tff(c_183,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_179])).

tff(c_191,plain,(
    ! [C_240,A_241,B_242] :
      ( l1_waybel_0(C_240,A_241)
      | ~ m1_yellow_6(C_240,A_241,B_242)
      | ~ l1_waybel_0(B_242,A_241)
      | ~ l1_struct_0(A_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_194,plain,
    ( l1_waybel_0('#skF_3','#skF_1')
    | ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_191])).

tff(c_197,plain,(
    l1_waybel_0('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_194])).

tff(c_16,plain,(
    ! [B_70,A_68] :
      ( l1_orders_2(B_70)
      | ~ l1_waybel_0(B_70,A_68)
      | ~ l1_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_200,plain,
    ( l1_orders_2('#skF_3')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_197,c_16])).

tff(c_203,plain,(
    l1_orders_2('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_200])).

tff(c_205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_203])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:08:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.27  
% 2.21/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.28  %$ v2_yellow_6 > r1_orders_2 > m1_yellow_6 > v4_yellow_0 > r2_hidden > m1_yellow_0 > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > #nlpp > u1_struct_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.21/1.28  
% 2.21/1.28  %Foreground sorts:
% 2.21/1.28  
% 2.21/1.28  
% 2.21/1.28  %Background operators:
% 2.21/1.28  
% 2.21/1.28  
% 2.21/1.28  %Foreground operators:
% 2.21/1.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.21/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.28  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.21/1.28  tff(v4_yellow_0, type, v4_yellow_0: ($i * $i) > $o).
% 2.21/1.28  tff('#skF_7', type, '#skF_7': $i).
% 2.21/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.21/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.21/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.28  tff(m1_yellow_0, type, m1_yellow_0: ($i * $i) > $o).
% 2.21/1.28  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.21/1.28  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.21/1.28  tff(m1_yellow_6, type, m1_yellow_6: ($i * $i * $i) > $o).
% 2.21/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.28  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.21/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.21/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.28  tff(v2_yellow_6, type, v2_yellow_6: ($i * $i * $i) > $o).
% 2.21/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.21/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.21/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.28  
% 2.21/1.29  tff(f_50, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.21/1.29  tff(f_146, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (((~v2_struct_0(C) & v2_yellow_6(C, A, B)) & m1_yellow_6(C, A, B)) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((((D = F) & (E = G)) & r1_orders_2(B, D, E)) => r1_orders_2(C, F, G)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_yellow_6)).
% 2.21/1.29  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.21/1.29  tff(f_100, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => (![C]: (m1_yellow_6(C, A, B) => (v2_yellow_6(C, A, B) <=> (v4_yellow_0(C, B) & m1_yellow_0(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_yellow_6)).
% 2.21/1.29  tff(f_86, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 2.21/1.29  tff(f_79, axiom, (![A]: (l1_orders_2(A) => (![B]: ((v4_yellow_0(B, A) & m1_yellow_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (((((E = C) & (F = D)) & r1_orders_2(A, C, D)) & r2_hidden(E, u1_struct_0(B))) => r1_orders_2(B, E, F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_yellow_0)).
% 2.21/1.29  tff(f_46, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.21/1.29  tff(f_109, axiom, (![A, B]: ((l1_struct_0(A) & l1_waybel_0(B, A)) => (![C]: (m1_yellow_6(C, A, B) => l1_waybel_0(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_yellow_6)).
% 2.21/1.29  tff(c_12, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_orders_2(A_4))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.21/1.29  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.21/1.29  tff(c_30, plain, ('#skF_7'='#skF_5'), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.21/1.29  tff(c_34, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.21/1.29  tff(c_54, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34])).
% 2.21/1.29  tff(c_73, plain, (![B_207, A_208]: (v1_xboole_0(B_207) | ~m1_subset_1(B_207, A_208) | ~v1_xboole_0(A_208))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.21/1.29  tff(c_90, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_73])).
% 2.21/1.29  tff(c_95, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_90])).
% 2.21/1.29  tff(c_32, plain, ('#skF_6'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.21/1.29  tff(c_26, plain, (~r1_orders_2('#skF_3', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.21/1.29  tff(c_55, plain, (~r1_orders_2('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_26])).
% 2.21/1.29  tff(c_36, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.21/1.29  tff(c_53, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_36])).
% 2.21/1.29  tff(c_52, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.21/1.29  tff(c_48, plain, (l1_waybel_0('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.21/1.29  tff(c_42, plain, (m1_yellow_6('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.21/1.29  tff(c_44, plain, (v2_yellow_6('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.21/1.29  tff(c_116, plain, (![C_217, B_218, A_219]: (v4_yellow_0(C_217, B_218) | ~v2_yellow_6(C_217, A_219, B_218) | ~m1_yellow_6(C_217, A_219, B_218) | ~l1_waybel_0(B_218, A_219) | ~l1_struct_0(A_219))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.21/1.29  tff(c_119, plain, (v4_yellow_0('#skF_3', '#skF_2') | ~m1_yellow_6('#skF_3', '#skF_1', '#skF_2') | ~l1_waybel_0('#skF_2', '#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_116])).
% 2.21/1.29  tff(c_122, plain, (v4_yellow_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_42, c_119])).
% 2.21/1.29  tff(c_123, plain, (![C_220, B_221, A_222]: (m1_yellow_0(C_220, B_221) | ~v2_yellow_6(C_220, A_222, B_221) | ~m1_yellow_6(C_220, A_222, B_221) | ~l1_waybel_0(B_221, A_222) | ~l1_struct_0(A_222))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.21/1.29  tff(c_126, plain, (m1_yellow_0('#skF_3', '#skF_2') | ~m1_yellow_6('#skF_3', '#skF_1', '#skF_2') | ~l1_waybel_0('#skF_2', '#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_123])).
% 2.21/1.29  tff(c_129, plain, (m1_yellow_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_42, c_126])).
% 2.21/1.29  tff(c_66, plain, (![B_205, A_206]: (l1_orders_2(B_205) | ~l1_waybel_0(B_205, A_206) | ~l1_struct_0(A_206))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.21/1.29  tff(c_69, plain, (l1_orders_2('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_66])).
% 2.21/1.29  tff(c_72, plain, (l1_orders_2('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_69])).
% 2.21/1.29  tff(c_40, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.21/1.29  tff(c_38, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.21/1.29  tff(c_28, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.21/1.29  tff(c_4, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.21/1.29  tff(c_139, plain, (![B_226, E_227, F_228, A_229]: (r1_orders_2(B_226, E_227, F_228) | ~r2_hidden(E_227, u1_struct_0(B_226)) | ~r1_orders_2(A_229, E_227, F_228) | ~m1_subset_1(F_228, u1_struct_0(B_226)) | ~m1_subset_1(E_227, u1_struct_0(B_226)) | ~m1_subset_1(F_228, u1_struct_0(A_229)) | ~m1_subset_1(E_227, u1_struct_0(A_229)) | ~m1_yellow_0(B_226, A_229) | ~v4_yellow_0(B_226, A_229) | ~l1_orders_2(A_229))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.21/1.29  tff(c_144, plain, (![B_230, B_231, F_232, A_233]: (r1_orders_2(B_230, B_231, F_232) | ~r1_orders_2(A_233, B_231, F_232) | ~m1_subset_1(F_232, u1_struct_0(B_230)) | ~m1_subset_1(F_232, u1_struct_0(A_233)) | ~m1_subset_1(B_231, u1_struct_0(A_233)) | ~m1_yellow_0(B_230, A_233) | ~v4_yellow_0(B_230, A_233) | ~l1_orders_2(A_233) | ~m1_subset_1(B_231, u1_struct_0(B_230)) | v1_xboole_0(u1_struct_0(B_230)))), inference(resolution, [status(thm)], [c_4, c_139])).
% 2.21/1.29  tff(c_146, plain, (![B_230]: (r1_orders_2(B_230, '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0(B_230)) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_yellow_0(B_230, '#skF_2') | ~v4_yellow_0(B_230, '#skF_2') | ~l1_orders_2('#skF_2') | ~m1_subset_1('#skF_4', u1_struct_0(B_230)) | v1_xboole_0(u1_struct_0(B_230)))), inference(resolution, [status(thm)], [c_28, c_144])).
% 2.21/1.29  tff(c_150, plain, (![B_234]: (r1_orders_2(B_234, '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0(B_234)) | ~m1_yellow_0(B_234, '#skF_2') | ~v4_yellow_0(B_234, '#skF_2') | ~m1_subset_1('#skF_4', u1_struct_0(B_234)) | v1_xboole_0(u1_struct_0(B_234)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_40, c_38, c_146])).
% 2.21/1.29  tff(c_156, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_5') | ~m1_yellow_0('#skF_3', '#skF_2') | ~v4_yellow_0('#skF_3', '#skF_2') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_150])).
% 2.21/1.29  tff(c_163, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_122, c_129, c_156])).
% 2.21/1.29  tff(c_165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_55, c_163])).
% 2.21/1.29  tff(c_167, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_90])).
% 2.21/1.29  tff(c_10, plain, (![A_3]: (~v1_xboole_0(u1_struct_0(A_3)) | ~l1_struct_0(A_3) | v2_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.21/1.29  tff(c_176, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_167, c_10])).
% 2.21/1.29  tff(c_179, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_46, c_176])).
% 2.21/1.29  tff(c_183, plain, (~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_12, c_179])).
% 2.21/1.29  tff(c_191, plain, (![C_240, A_241, B_242]: (l1_waybel_0(C_240, A_241) | ~m1_yellow_6(C_240, A_241, B_242) | ~l1_waybel_0(B_242, A_241) | ~l1_struct_0(A_241))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.21/1.29  tff(c_194, plain, (l1_waybel_0('#skF_3', '#skF_1') | ~l1_waybel_0('#skF_2', '#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_191])).
% 2.21/1.29  tff(c_197, plain, (l1_waybel_0('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_194])).
% 2.21/1.29  tff(c_16, plain, (![B_70, A_68]: (l1_orders_2(B_70) | ~l1_waybel_0(B_70, A_68) | ~l1_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.21/1.29  tff(c_200, plain, (l1_orders_2('#skF_3') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_197, c_16])).
% 2.21/1.29  tff(c_203, plain, (l1_orders_2('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_200])).
% 2.21/1.29  tff(c_205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_183, c_203])).
% 2.21/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.29  
% 2.21/1.29  Inference rules
% 2.21/1.29  ----------------------
% 2.21/1.29  #Ref     : 0
% 2.21/1.29  #Sup     : 27
% 2.21/1.29  #Fact    : 0
% 2.21/1.29  #Define  : 0
% 2.21/1.29  #Split   : 3
% 2.21/1.29  #Chain   : 0
% 2.21/1.29  #Close   : 0
% 2.21/1.29  
% 2.21/1.29  Ordering : KBO
% 2.21/1.29  
% 2.21/1.29  Simplification rules
% 2.21/1.29  ----------------------
% 2.21/1.29  #Subsume      : 2
% 2.21/1.29  #Demod        : 25
% 2.21/1.29  #Tautology    : 11
% 2.21/1.29  #SimpNegUnit  : 3
% 2.21/1.29  #BackRed      : 0
% 2.21/1.29  
% 2.21/1.29  #Partial instantiations: 0
% 2.21/1.30  #Strategies tried      : 1
% 2.21/1.30  
% 2.21/1.30  Timing (in seconds)
% 2.21/1.30  ----------------------
% 2.21/1.30  Preprocessing        : 0.33
% 2.21/1.30  Parsing              : 0.17
% 2.21/1.30  CNF conversion       : 0.03
% 2.21/1.30  Main loop            : 0.19
% 2.21/1.30  Inferencing          : 0.07
% 2.21/1.30  Reduction            : 0.06
% 2.21/1.30  Demodulation         : 0.04
% 2.21/1.30  BG Simplification    : 0.02
% 2.21/1.30  Subsumption          : 0.03
% 2.21/1.30  Abstraction          : 0.01
% 2.21/1.30  MUC search           : 0.00
% 2.21/1.30  Cooper               : 0.00
% 2.21/1.30  Total                : 0.55
% 2.21/1.30  Index Insertion      : 0.00
% 2.21/1.30  Index Deletion       : 0.00
% 2.21/1.30  Index Matching       : 0.00
% 2.21/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
