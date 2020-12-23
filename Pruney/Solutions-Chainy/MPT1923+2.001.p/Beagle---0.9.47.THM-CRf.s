%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:45 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 140 expanded)
%              Number of leaves         :   31 (  66 expanded)
%              Depth                    :    8
%              Number of atoms          :  170 ( 648 expanded)
%              Number of equality atoms :    6 (  70 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_144,negated_conjecture,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_107,axiom,(
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

tff(f_93,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_86,axiom,(
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

tff(f_46,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_yellow_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_0)).

tff(c_12,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_30,plain,(
    '#skF_7' = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_34,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34])).

tff(c_75,plain,(
    ! [B_209,A_210] :
      ( v1_xboole_0(B_209)
      | ~ m1_subset_1(B_209,A_210)
      | ~ v1_xboole_0(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_92,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_75])).

tff(c_96,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_32,plain,(
    '#skF_6' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_26,plain,(
    ~ r1_orders_2('#skF_3','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_55,plain,(
    ~ r1_orders_2('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_26])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_53,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36])).

tff(c_52,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_48,plain,(
    l1_waybel_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_42,plain,(
    m1_yellow_6('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_44,plain,(
    v2_yellow_6('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_117,plain,(
    ! [C_218,B_219,A_220] :
      ( v4_yellow_0(C_218,B_219)
      | ~ v2_yellow_6(C_218,A_220,B_219)
      | ~ m1_yellow_6(C_218,A_220,B_219)
      | ~ l1_waybel_0(B_219,A_220)
      | ~ l1_struct_0(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_120,plain,
    ( v4_yellow_0('#skF_3','#skF_2')
    | ~ m1_yellow_6('#skF_3','#skF_1','#skF_2')
    | ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_117])).

tff(c_123,plain,(
    v4_yellow_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_42,c_120])).

tff(c_104,plain,(
    ! [C_215,B_216,A_217] :
      ( m1_yellow_0(C_215,B_216)
      | ~ v2_yellow_6(C_215,A_217,B_216)
      | ~ m1_yellow_6(C_215,A_217,B_216)
      | ~ l1_waybel_0(B_216,A_217)
      | ~ l1_struct_0(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_107,plain,
    ( m1_yellow_0('#skF_3','#skF_2')
    | ~ m1_yellow_6('#skF_3','#skF_1','#skF_2')
    | ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_104])).

tff(c_110,plain,(
    m1_yellow_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_42,c_107])).

tff(c_67,plain,(
    ! [B_205,A_206] :
      ( l1_orders_2(B_205)
      | ~ l1_waybel_0(B_205,A_206)
      | ~ l1_struct_0(A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_70,plain,
    ( l1_orders_2('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_67])).

tff(c_73,plain,(
    l1_orders_2('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_70])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_28,plain,(
    r1_orders_2('#skF_2','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_133,plain,(
    ! [B_224,E_225,F_226,A_227] :
      ( r1_orders_2(B_224,E_225,F_226)
      | ~ r2_hidden(E_225,u1_struct_0(B_224))
      | ~ r1_orders_2(A_227,E_225,F_226)
      | ~ m1_subset_1(F_226,u1_struct_0(B_224))
      | ~ m1_subset_1(E_225,u1_struct_0(B_224))
      | ~ m1_subset_1(F_226,u1_struct_0(A_227))
      | ~ m1_subset_1(E_225,u1_struct_0(A_227))
      | ~ m1_yellow_0(B_224,A_227)
      | ~ v4_yellow_0(B_224,A_227)
      | ~ l1_orders_2(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_138,plain,(
    ! [B_228,B_229,F_230,A_231] :
      ( r1_orders_2(B_228,B_229,F_230)
      | ~ r1_orders_2(A_231,B_229,F_230)
      | ~ m1_subset_1(F_230,u1_struct_0(B_228))
      | ~ m1_subset_1(F_230,u1_struct_0(A_231))
      | ~ m1_subset_1(B_229,u1_struct_0(A_231))
      | ~ m1_yellow_0(B_228,A_231)
      | ~ v4_yellow_0(B_228,A_231)
      | ~ l1_orders_2(A_231)
      | ~ m1_subset_1(B_229,u1_struct_0(B_228))
      | v1_xboole_0(u1_struct_0(B_228)) ) ),
    inference(resolution,[status(thm)],[c_4,c_133])).

tff(c_140,plain,(
    ! [B_228] :
      ( r1_orders_2(B_228,'#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0(B_228))
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ m1_yellow_0(B_228,'#skF_2')
      | ~ v4_yellow_0(B_228,'#skF_2')
      | ~ l1_orders_2('#skF_2')
      | ~ m1_subset_1('#skF_4',u1_struct_0(B_228))
      | v1_xboole_0(u1_struct_0(B_228)) ) ),
    inference(resolution,[status(thm)],[c_28,c_138])).

tff(c_144,plain,(
    ! [B_232] :
      ( r1_orders_2(B_232,'#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0(B_232))
      | ~ m1_yellow_0(B_232,'#skF_2')
      | ~ v4_yellow_0(B_232,'#skF_2')
      | ~ m1_subset_1('#skF_4',u1_struct_0(B_232))
      | v1_xboole_0(u1_struct_0(B_232)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_40,c_38,c_140])).

tff(c_150,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_5')
    | ~ m1_yellow_0('#skF_3','#skF_2')
    | ~ v4_yellow_0('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_144])).

tff(c_157,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_123,c_110,c_150])).

tff(c_159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_55,c_157])).

tff(c_161,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_10,plain,(
    ! [A_3] :
      ( ~ v1_xboole_0(u1_struct_0(A_3))
      | ~ l1_struct_0(A_3)
      | v2_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_165,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_161,c_10])).

tff(c_168,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_165])).

tff(c_172,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_168])).

tff(c_182,plain,(
    ! [C_237,B_238,A_239] :
      ( m1_yellow_0(C_237,B_238)
      | ~ v2_yellow_6(C_237,A_239,B_238)
      | ~ m1_yellow_6(C_237,A_239,B_238)
      | ~ l1_waybel_0(B_238,A_239)
      | ~ l1_struct_0(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_185,plain,
    ( m1_yellow_0('#skF_3','#skF_2')
    | ~ m1_yellow_6('#skF_3','#skF_1','#skF_2')
    | ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_182])).

tff(c_188,plain,(
    m1_yellow_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_42,c_185])).

tff(c_14,plain,(
    ! [B_7,A_5] :
      ( l1_orders_2(B_7)
      | ~ m1_yellow_0(B_7,A_5)
      | ~ l1_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_191,plain,
    ( l1_orders_2('#skF_3')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_188,c_14])).

tff(c_194,plain,(
    l1_orders_2('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_191])).

tff(c_196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_194])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:24:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.27  
% 2.37/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.27  %$ v2_yellow_6 > r1_orders_2 > m1_yellow_6 > v4_yellow_0 > r2_hidden > m1_yellow_0 > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > #nlpp > u1_struct_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.37/1.27  
% 2.37/1.27  %Foreground sorts:
% 2.37/1.27  
% 2.37/1.27  
% 2.37/1.27  %Background operators:
% 2.37/1.27  
% 2.37/1.27  
% 2.37/1.27  %Foreground operators:
% 2.37/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.37/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.37/1.27  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.37/1.27  tff(v4_yellow_0, type, v4_yellow_0: ($i * $i) > $o).
% 2.37/1.27  tff('#skF_7', type, '#skF_7': $i).
% 2.37/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.37/1.27  tff('#skF_6', type, '#skF_6': $i).
% 2.37/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.37/1.27  tff(m1_yellow_0, type, m1_yellow_0: ($i * $i) > $o).
% 2.37/1.27  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.37/1.27  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.37/1.27  tff(m1_yellow_6, type, m1_yellow_6: ($i * $i * $i) > $o).
% 2.37/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.27  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.37/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.37/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.27  tff(v2_yellow_6, type, v2_yellow_6: ($i * $i * $i) > $o).
% 2.37/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.37/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.37/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.37/1.27  
% 2.37/1.29  tff(f_50, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.37/1.29  tff(f_144, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (((~v2_struct_0(C) & v2_yellow_6(C, A, B)) & m1_yellow_6(C, A, B)) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((((D = F) & (E = G)) & r1_orders_2(B, D, E)) => r1_orders_2(C, F, G)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_yellow_6)).
% 2.37/1.29  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.37/1.29  tff(f_107, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => (![C]: (m1_yellow_6(C, A, B) => (v2_yellow_6(C, A, B) <=> (v4_yellow_0(C, B) & m1_yellow_0(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_yellow_6)).
% 2.37/1.29  tff(f_93, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 2.37/1.29  tff(f_86, axiom, (![A]: (l1_orders_2(A) => (![B]: ((v4_yellow_0(B, A) & m1_yellow_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (((((E = C) & (F = D)) & r1_orders_2(A, C, D)) & r2_hidden(E, u1_struct_0(B))) => r1_orders_2(B, E, F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_yellow_0)).
% 2.37/1.29  tff(f_46, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.37/1.29  tff(f_57, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_yellow_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_yellow_0)).
% 2.37/1.29  tff(c_12, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_orders_2(A_4))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.37/1.29  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.37/1.29  tff(c_30, plain, ('#skF_7'='#skF_5'), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.37/1.29  tff(c_34, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.37/1.29  tff(c_54, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34])).
% 2.37/1.29  tff(c_75, plain, (![B_209, A_210]: (v1_xboole_0(B_209) | ~m1_subset_1(B_209, A_210) | ~v1_xboole_0(A_210))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.37/1.29  tff(c_92, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_75])).
% 2.37/1.29  tff(c_96, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_92])).
% 2.37/1.29  tff(c_32, plain, ('#skF_6'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.37/1.29  tff(c_26, plain, (~r1_orders_2('#skF_3', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.37/1.29  tff(c_55, plain, (~r1_orders_2('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_26])).
% 2.37/1.29  tff(c_36, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.37/1.29  tff(c_53, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_36])).
% 2.37/1.29  tff(c_52, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.37/1.29  tff(c_48, plain, (l1_waybel_0('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.37/1.29  tff(c_42, plain, (m1_yellow_6('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.37/1.29  tff(c_44, plain, (v2_yellow_6('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.37/1.29  tff(c_117, plain, (![C_218, B_219, A_220]: (v4_yellow_0(C_218, B_219) | ~v2_yellow_6(C_218, A_220, B_219) | ~m1_yellow_6(C_218, A_220, B_219) | ~l1_waybel_0(B_219, A_220) | ~l1_struct_0(A_220))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.37/1.29  tff(c_120, plain, (v4_yellow_0('#skF_3', '#skF_2') | ~m1_yellow_6('#skF_3', '#skF_1', '#skF_2') | ~l1_waybel_0('#skF_2', '#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_117])).
% 2.37/1.29  tff(c_123, plain, (v4_yellow_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_42, c_120])).
% 2.37/1.29  tff(c_104, plain, (![C_215, B_216, A_217]: (m1_yellow_0(C_215, B_216) | ~v2_yellow_6(C_215, A_217, B_216) | ~m1_yellow_6(C_215, A_217, B_216) | ~l1_waybel_0(B_216, A_217) | ~l1_struct_0(A_217))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.37/1.29  tff(c_107, plain, (m1_yellow_0('#skF_3', '#skF_2') | ~m1_yellow_6('#skF_3', '#skF_1', '#skF_2') | ~l1_waybel_0('#skF_2', '#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_104])).
% 2.37/1.29  tff(c_110, plain, (m1_yellow_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_42, c_107])).
% 2.37/1.29  tff(c_67, plain, (![B_205, A_206]: (l1_orders_2(B_205) | ~l1_waybel_0(B_205, A_206) | ~l1_struct_0(A_206))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.37/1.29  tff(c_70, plain, (l1_orders_2('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_67])).
% 2.37/1.29  tff(c_73, plain, (l1_orders_2('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_70])).
% 2.37/1.29  tff(c_40, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.37/1.29  tff(c_38, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.37/1.29  tff(c_28, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.37/1.29  tff(c_4, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.37/1.29  tff(c_133, plain, (![B_224, E_225, F_226, A_227]: (r1_orders_2(B_224, E_225, F_226) | ~r2_hidden(E_225, u1_struct_0(B_224)) | ~r1_orders_2(A_227, E_225, F_226) | ~m1_subset_1(F_226, u1_struct_0(B_224)) | ~m1_subset_1(E_225, u1_struct_0(B_224)) | ~m1_subset_1(F_226, u1_struct_0(A_227)) | ~m1_subset_1(E_225, u1_struct_0(A_227)) | ~m1_yellow_0(B_224, A_227) | ~v4_yellow_0(B_224, A_227) | ~l1_orders_2(A_227))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.37/1.29  tff(c_138, plain, (![B_228, B_229, F_230, A_231]: (r1_orders_2(B_228, B_229, F_230) | ~r1_orders_2(A_231, B_229, F_230) | ~m1_subset_1(F_230, u1_struct_0(B_228)) | ~m1_subset_1(F_230, u1_struct_0(A_231)) | ~m1_subset_1(B_229, u1_struct_0(A_231)) | ~m1_yellow_0(B_228, A_231) | ~v4_yellow_0(B_228, A_231) | ~l1_orders_2(A_231) | ~m1_subset_1(B_229, u1_struct_0(B_228)) | v1_xboole_0(u1_struct_0(B_228)))), inference(resolution, [status(thm)], [c_4, c_133])).
% 2.37/1.29  tff(c_140, plain, (![B_228]: (r1_orders_2(B_228, '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0(B_228)) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_yellow_0(B_228, '#skF_2') | ~v4_yellow_0(B_228, '#skF_2') | ~l1_orders_2('#skF_2') | ~m1_subset_1('#skF_4', u1_struct_0(B_228)) | v1_xboole_0(u1_struct_0(B_228)))), inference(resolution, [status(thm)], [c_28, c_138])).
% 2.37/1.29  tff(c_144, plain, (![B_232]: (r1_orders_2(B_232, '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0(B_232)) | ~m1_yellow_0(B_232, '#skF_2') | ~v4_yellow_0(B_232, '#skF_2') | ~m1_subset_1('#skF_4', u1_struct_0(B_232)) | v1_xboole_0(u1_struct_0(B_232)))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_40, c_38, c_140])).
% 2.37/1.29  tff(c_150, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_5') | ~m1_yellow_0('#skF_3', '#skF_2') | ~v4_yellow_0('#skF_3', '#skF_2') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_144])).
% 2.37/1.29  tff(c_157, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_123, c_110, c_150])).
% 2.37/1.29  tff(c_159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_55, c_157])).
% 2.37/1.29  tff(c_161, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_92])).
% 2.37/1.29  tff(c_10, plain, (![A_3]: (~v1_xboole_0(u1_struct_0(A_3)) | ~l1_struct_0(A_3) | v2_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.37/1.29  tff(c_165, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_161, c_10])).
% 2.37/1.29  tff(c_168, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_46, c_165])).
% 2.37/1.29  tff(c_172, plain, (~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_12, c_168])).
% 2.37/1.29  tff(c_182, plain, (![C_237, B_238, A_239]: (m1_yellow_0(C_237, B_238) | ~v2_yellow_6(C_237, A_239, B_238) | ~m1_yellow_6(C_237, A_239, B_238) | ~l1_waybel_0(B_238, A_239) | ~l1_struct_0(A_239))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.37/1.29  tff(c_185, plain, (m1_yellow_0('#skF_3', '#skF_2') | ~m1_yellow_6('#skF_3', '#skF_1', '#skF_2') | ~l1_waybel_0('#skF_2', '#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_182])).
% 2.37/1.29  tff(c_188, plain, (m1_yellow_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_42, c_185])).
% 2.37/1.29  tff(c_14, plain, (![B_7, A_5]: (l1_orders_2(B_7) | ~m1_yellow_0(B_7, A_5) | ~l1_orders_2(A_5))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.37/1.29  tff(c_191, plain, (l1_orders_2('#skF_3') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_188, c_14])).
% 2.37/1.29  tff(c_194, plain, (l1_orders_2('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_191])).
% 2.37/1.29  tff(c_196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_194])).
% 2.37/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.29  
% 2.37/1.29  Inference rules
% 2.37/1.29  ----------------------
% 2.37/1.29  #Ref     : 0
% 2.37/1.29  #Sup     : 26
% 2.37/1.29  #Fact    : 0
% 2.37/1.29  #Define  : 0
% 2.37/1.29  #Split   : 3
% 2.37/1.29  #Chain   : 0
% 2.37/1.29  #Close   : 0
% 2.37/1.29  
% 2.37/1.29  Ordering : KBO
% 2.37/1.29  
% 2.37/1.29  Simplification rules
% 2.37/1.29  ----------------------
% 2.37/1.29  #Subsume      : 2
% 2.37/1.29  #Demod        : 24
% 2.37/1.29  #Tautology    : 11
% 2.37/1.29  #SimpNegUnit  : 3
% 2.37/1.29  #BackRed      : 0
% 2.37/1.29  
% 2.37/1.29  #Partial instantiations: 0
% 2.37/1.29  #Strategies tried      : 1
% 2.37/1.29  
% 2.37/1.29  Timing (in seconds)
% 2.37/1.29  ----------------------
% 2.37/1.29  Preprocessing        : 0.32
% 2.37/1.29  Parsing              : 0.17
% 2.37/1.29  CNF conversion       : 0.03
% 2.37/1.29  Main loop            : 0.19
% 2.37/1.29  Inferencing          : 0.07
% 2.37/1.29  Reduction            : 0.05
% 2.37/1.29  Demodulation         : 0.04
% 2.37/1.29  BG Simplification    : 0.02
% 2.37/1.29  Subsumption          : 0.03
% 2.37/1.30  Abstraction          : 0.01
% 2.37/1.30  MUC search           : 0.00
% 2.37/1.30  Cooper               : 0.00
% 2.37/1.30  Total                : 0.55
% 2.37/1.30  Index Insertion      : 0.00
% 2.37/1.30  Index Deletion       : 0.00
% 2.37/1.30  Index Matching       : 0.00
% 2.37/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
