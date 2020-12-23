%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:45 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 128 expanded)
%              Number of leaves         :   33 (  63 expanded)
%              Depth                    :   12
%              Number of atoms          :  143 ( 474 expanded)
%              Number of equality atoms :    5 (  57 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > m1_yellow_6 > r2_hidden > r1_tarski > m1_yellow_0 > m1_subset_1 > l1_waybel_0 > l1_struct_0 > l1_orders_2 > k2_partfun1 > u1_waybel_0 > k4_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(m1_yellow_0,type,(
    m1_yellow_0: ( $i * $i ) > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(u1_waybel_0,type,(
    u1_waybel_0: ( $i * $i ) > $i )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( l1_waybel_0(B,A)
           => ! [C] :
                ( m1_yellow_6(C,A,B)
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
                                    & r1_orders_2(C,F,G) )
                                 => r1_orders_2(B,D,E) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_yellow_6)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => ! [C] :
          ( m1_yellow_6(C,A,B)
         => l1_waybel_0(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow_6)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => ! [C] :
              ( l1_waybel_0(C,A)
             => ( m1_yellow_6(C,A,B)
              <=> ( m1_yellow_0(C,B)
                  & u1_waybel_0(A,C) = k2_partfun1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B),u1_struct_0(C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_yellow_6)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ( m1_yellow_0(B,A)
          <=> ( r1_tarski(u1_struct_0(B),u1_struct_0(A))
              & r1_tarski(u1_orders_2(B),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_yellow_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_28,plain,(
    ~ r1_orders_2('#skF_2','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_48,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_46,plain,(
    l1_waybel_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_66,plain,(
    ! [B_155,A_156] :
      ( l1_orders_2(B_155)
      | ~ l1_waybel_0(B_155,A_156)
      | ~ l1_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_69,plain,
    ( l1_orders_2('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_66])).

tff(c_72,plain,(
    l1_orders_2('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_69])).

tff(c_44,plain,(
    m1_yellow_6('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_74,plain,(
    ! [C_160,A_161,B_162] :
      ( l1_waybel_0(C_160,A_161)
      | ~ m1_yellow_6(C_160,A_161,B_162)
      | ~ l1_waybel_0(B_162,A_161)
      | ~ l1_struct_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_77,plain,
    ( l1_waybel_0('#skF_3','#skF_1')
    | ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_74])).

tff(c_80,plain,(
    l1_waybel_0('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_77])).

tff(c_89,plain,(
    ! [C_167,B_168,A_169] :
      ( m1_yellow_0(C_167,B_168)
      | ~ m1_yellow_6(C_167,A_169,B_168)
      | ~ l1_waybel_0(C_167,A_169)
      | ~ l1_waybel_0(B_168,A_169)
      | ~ l1_struct_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_92,plain,
    ( m1_yellow_0('#skF_3','#skF_2')
    | ~ l1_waybel_0('#skF_3','#skF_1')
    | ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_89])).

tff(c_95,plain,(
    m1_yellow_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_80,c_92])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_18,plain,(
    ! [B_19,A_17] :
      ( l1_orders_2(B_19)
      | ~ l1_waybel_0(B_19,A_17)
      | ~ l1_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_83,plain,
    ( l1_orders_2('#skF_3')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_18])).

tff(c_86,plain,(
    l1_orders_2('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_83])).

tff(c_14,plain,(
    ! [B_16,A_14] :
      ( r1_tarski(u1_orders_2(B_16),u1_orders_2(A_14))
      | ~ m1_yellow_0(B_16,A_14)
      | ~ l1_orders_2(B_16)
      | ~ l1_orders_2(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_34,plain,(
    '#skF_6' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_49,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_38])).

tff(c_32,plain,(
    '#skF_7' = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_36,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36])).

tff(c_30,plain,(
    r1_orders_2('#skF_3','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_51,plain,(
    r1_orders_2('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_101,plain,(
    ! [B_172,C_173,A_174] :
      ( r2_hidden(k4_tarski(B_172,C_173),u1_orders_2(A_174))
      | ~ r1_orders_2(A_174,B_172,C_173)
      | ~ m1_subset_1(C_173,u1_struct_0(A_174))
      | ~ m1_subset_1(B_172,u1_struct_0(A_174))
      | ~ l1_orders_2(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_110,plain,(
    ! [B_178,C_179,A_180,A_181] :
      ( r2_hidden(k4_tarski(B_178,C_179),A_180)
      | ~ m1_subset_1(u1_orders_2(A_181),k1_zfmisc_1(A_180))
      | ~ r1_orders_2(A_181,B_178,C_179)
      | ~ m1_subset_1(C_179,u1_struct_0(A_181))
      | ~ m1_subset_1(B_178,u1_struct_0(A_181))
      | ~ l1_orders_2(A_181) ) ),
    inference(resolution,[status(thm)],[c_101,c_2])).

tff(c_115,plain,(
    ! [B_182,C_183,B_184,A_185] :
      ( r2_hidden(k4_tarski(B_182,C_183),B_184)
      | ~ r1_orders_2(A_185,B_182,C_183)
      | ~ m1_subset_1(C_183,u1_struct_0(A_185))
      | ~ m1_subset_1(B_182,u1_struct_0(A_185))
      | ~ l1_orders_2(A_185)
      | ~ r1_tarski(u1_orders_2(A_185),B_184) ) ),
    inference(resolution,[status(thm)],[c_6,c_110])).

tff(c_117,plain,(
    ! [B_184] :
      ( r2_hidden(k4_tarski('#skF_4','#skF_5'),B_184)
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r1_tarski(u1_orders_2('#skF_3'),B_184) ) ),
    inference(resolution,[status(thm)],[c_51,c_115])).

tff(c_121,plain,(
    ! [B_186] :
      ( r2_hidden(k4_tarski('#skF_4','#skF_5'),B_186)
      | ~ r1_tarski(u1_orders_2('#skF_3'),B_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_49,c_50,c_117])).

tff(c_8,plain,(
    ! [A_7,B_11,C_13] :
      ( r1_orders_2(A_7,B_11,C_13)
      | ~ r2_hidden(k4_tarski(B_11,C_13),u1_orders_2(A_7))
      | ~ m1_subset_1(C_13,u1_struct_0(A_7))
      | ~ m1_subset_1(B_11,u1_struct_0(A_7))
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_193,plain,(
    ! [A_206] :
      ( r1_orders_2(A_206,'#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_206))
      | ~ m1_subset_1('#skF_4',u1_struct_0(A_206))
      | ~ l1_orders_2(A_206)
      | ~ r1_tarski(u1_orders_2('#skF_3'),u1_orders_2(A_206)) ) ),
    inference(resolution,[status(thm)],[c_121,c_8])).

tff(c_197,plain,(
    ! [A_14] :
      ( r1_orders_2(A_14,'#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_14))
      | ~ m1_subset_1('#skF_4',u1_struct_0(A_14))
      | ~ m1_yellow_0('#skF_3',A_14)
      | ~ l1_orders_2('#skF_3')
      | ~ l1_orders_2(A_14) ) ),
    inference(resolution,[status(thm)],[c_14,c_193])).

tff(c_201,plain,(
    ! [A_207] :
      ( r1_orders_2(A_207,'#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_207))
      | ~ m1_subset_1('#skF_4',u1_struct_0(A_207))
      | ~ m1_yellow_0('#skF_3',A_207)
      | ~ l1_orders_2(A_207) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_197])).

tff(c_204,plain,
    ( r1_orders_2('#skF_2','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_yellow_0('#skF_3','#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_201])).

tff(c_210,plain,(
    r1_orders_2('#skF_2','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_95,c_42,c_204])).

tff(c_212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_210])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:50:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.29  
% 2.31/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.29  %$ r1_orders_2 > m1_yellow_6 > r2_hidden > r1_tarski > m1_yellow_0 > m1_subset_1 > l1_waybel_0 > l1_struct_0 > l1_orders_2 > k2_partfun1 > u1_waybel_0 > k4_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.31/1.29  
% 2.31/1.29  %Foreground sorts:
% 2.31/1.29  
% 2.31/1.29  
% 2.31/1.29  %Background operators:
% 2.31/1.29  
% 2.31/1.29  
% 2.31/1.29  %Foreground operators:
% 2.31/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.31/1.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.31/1.29  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.31/1.29  tff('#skF_7', type, '#skF_7': $i).
% 2.31/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.31/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.31/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.31/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.31/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.31/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.31/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.31/1.29  tff(m1_yellow_0, type, m1_yellow_0: ($i * $i) > $o).
% 2.31/1.29  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.31/1.29  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.31/1.29  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 2.31/1.29  tff(m1_yellow_6, type, m1_yellow_6: ($i * $i * $i) > $o).
% 2.31/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.29  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.31/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.31/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.29  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.31/1.29  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.31/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.31/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.31/1.29  
% 2.31/1.31  tff(f_118, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => (![C]: (m1_yellow_6(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((((D = F) & (E = G)) & r1_orders_2(C, F, G)) => r1_orders_2(B, D, E)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_yellow_6)).
% 2.31/1.31  tff(f_66, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 2.31/1.31  tff(f_89, axiom, (![A, B]: ((l1_struct_0(A) & l1_waybel_0(B, A)) => (![C]: (m1_yellow_6(C, A, B) => l1_waybel_0(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_yellow_6)).
% 2.31/1.31  tff(f_80, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => (![C]: (l1_waybel_0(C, A) => (m1_yellow_6(C, A, B) <=> (m1_yellow_0(C, B) & (u1_waybel_0(A, C) = k2_partfun1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B), u1_struct_0(C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_yellow_6)).
% 2.31/1.31  tff(f_59, axiom, (![A]: (l1_orders_2(A) => (![B]: (l1_orders_2(B) => (m1_yellow_0(B, A) <=> (r1_tarski(u1_struct_0(B), u1_struct_0(A)) & r1_tarski(u1_orders_2(B), u1_orders_2(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_yellow_0)).
% 2.31/1.31  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.31/1.31  tff(f_48, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_orders_2)).
% 2.31/1.31  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.31/1.31  tff(c_28, plain, (~r1_orders_2('#skF_2', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.31/1.31  tff(c_48, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.31/1.31  tff(c_46, plain, (l1_waybel_0('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.31/1.31  tff(c_66, plain, (![B_155, A_156]: (l1_orders_2(B_155) | ~l1_waybel_0(B_155, A_156) | ~l1_struct_0(A_156))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.31/1.31  tff(c_69, plain, (l1_orders_2('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_66])).
% 2.31/1.31  tff(c_72, plain, (l1_orders_2('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_69])).
% 2.31/1.31  tff(c_44, plain, (m1_yellow_6('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.31/1.31  tff(c_74, plain, (![C_160, A_161, B_162]: (l1_waybel_0(C_160, A_161) | ~m1_yellow_6(C_160, A_161, B_162) | ~l1_waybel_0(B_162, A_161) | ~l1_struct_0(A_161))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.31/1.31  tff(c_77, plain, (l1_waybel_0('#skF_3', '#skF_1') | ~l1_waybel_0('#skF_2', '#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_74])).
% 2.31/1.31  tff(c_80, plain, (l1_waybel_0('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_77])).
% 2.31/1.31  tff(c_89, plain, (![C_167, B_168, A_169]: (m1_yellow_0(C_167, B_168) | ~m1_yellow_6(C_167, A_169, B_168) | ~l1_waybel_0(C_167, A_169) | ~l1_waybel_0(B_168, A_169) | ~l1_struct_0(A_169))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.31/1.31  tff(c_92, plain, (m1_yellow_0('#skF_3', '#skF_2') | ~l1_waybel_0('#skF_3', '#skF_1') | ~l1_waybel_0('#skF_2', '#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_89])).
% 2.31/1.31  tff(c_95, plain, (m1_yellow_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_80, c_92])).
% 2.31/1.31  tff(c_42, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.31/1.31  tff(c_40, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.31/1.31  tff(c_18, plain, (![B_19, A_17]: (l1_orders_2(B_19) | ~l1_waybel_0(B_19, A_17) | ~l1_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.31/1.31  tff(c_83, plain, (l1_orders_2('#skF_3') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_80, c_18])).
% 2.31/1.31  tff(c_86, plain, (l1_orders_2('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_83])).
% 2.31/1.31  tff(c_14, plain, (![B_16, A_14]: (r1_tarski(u1_orders_2(B_16), u1_orders_2(A_14)) | ~m1_yellow_0(B_16, A_14) | ~l1_orders_2(B_16) | ~l1_orders_2(A_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.31/1.31  tff(c_34, plain, ('#skF_6'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.31/1.31  tff(c_38, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.31/1.31  tff(c_49, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_38])).
% 2.31/1.31  tff(c_32, plain, ('#skF_7'='#skF_5'), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.31/1.31  tff(c_36, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.31/1.31  tff(c_50, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_36])).
% 2.31/1.31  tff(c_30, plain, (r1_orders_2('#skF_3', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.31/1.31  tff(c_51, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30])).
% 2.31/1.31  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.31/1.31  tff(c_101, plain, (![B_172, C_173, A_174]: (r2_hidden(k4_tarski(B_172, C_173), u1_orders_2(A_174)) | ~r1_orders_2(A_174, B_172, C_173) | ~m1_subset_1(C_173, u1_struct_0(A_174)) | ~m1_subset_1(B_172, u1_struct_0(A_174)) | ~l1_orders_2(A_174))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.31/1.31  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.31/1.31  tff(c_110, plain, (![B_178, C_179, A_180, A_181]: (r2_hidden(k4_tarski(B_178, C_179), A_180) | ~m1_subset_1(u1_orders_2(A_181), k1_zfmisc_1(A_180)) | ~r1_orders_2(A_181, B_178, C_179) | ~m1_subset_1(C_179, u1_struct_0(A_181)) | ~m1_subset_1(B_178, u1_struct_0(A_181)) | ~l1_orders_2(A_181))), inference(resolution, [status(thm)], [c_101, c_2])).
% 2.31/1.31  tff(c_115, plain, (![B_182, C_183, B_184, A_185]: (r2_hidden(k4_tarski(B_182, C_183), B_184) | ~r1_orders_2(A_185, B_182, C_183) | ~m1_subset_1(C_183, u1_struct_0(A_185)) | ~m1_subset_1(B_182, u1_struct_0(A_185)) | ~l1_orders_2(A_185) | ~r1_tarski(u1_orders_2(A_185), B_184))), inference(resolution, [status(thm)], [c_6, c_110])).
% 2.31/1.31  tff(c_117, plain, (![B_184]: (r2_hidden(k4_tarski('#skF_4', '#skF_5'), B_184) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r1_tarski(u1_orders_2('#skF_3'), B_184))), inference(resolution, [status(thm)], [c_51, c_115])).
% 2.31/1.31  tff(c_121, plain, (![B_186]: (r2_hidden(k4_tarski('#skF_4', '#skF_5'), B_186) | ~r1_tarski(u1_orders_2('#skF_3'), B_186))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_49, c_50, c_117])).
% 2.31/1.31  tff(c_8, plain, (![A_7, B_11, C_13]: (r1_orders_2(A_7, B_11, C_13) | ~r2_hidden(k4_tarski(B_11, C_13), u1_orders_2(A_7)) | ~m1_subset_1(C_13, u1_struct_0(A_7)) | ~m1_subset_1(B_11, u1_struct_0(A_7)) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.31/1.31  tff(c_193, plain, (![A_206]: (r1_orders_2(A_206, '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0(A_206)) | ~m1_subset_1('#skF_4', u1_struct_0(A_206)) | ~l1_orders_2(A_206) | ~r1_tarski(u1_orders_2('#skF_3'), u1_orders_2(A_206)))), inference(resolution, [status(thm)], [c_121, c_8])).
% 2.31/1.31  tff(c_197, plain, (![A_14]: (r1_orders_2(A_14, '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0(A_14)) | ~m1_subset_1('#skF_4', u1_struct_0(A_14)) | ~m1_yellow_0('#skF_3', A_14) | ~l1_orders_2('#skF_3') | ~l1_orders_2(A_14))), inference(resolution, [status(thm)], [c_14, c_193])).
% 2.31/1.31  tff(c_201, plain, (![A_207]: (r1_orders_2(A_207, '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0(A_207)) | ~m1_subset_1('#skF_4', u1_struct_0(A_207)) | ~m1_yellow_0('#skF_3', A_207) | ~l1_orders_2(A_207))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_197])).
% 2.31/1.31  tff(c_204, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_yellow_0('#skF_3', '#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_40, c_201])).
% 2.31/1.31  tff(c_210, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_95, c_42, c_204])).
% 2.31/1.31  tff(c_212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_210])).
% 2.31/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.31  
% 2.31/1.31  Inference rules
% 2.31/1.31  ----------------------
% 2.31/1.31  #Ref     : 0
% 2.31/1.31  #Sup     : 31
% 2.31/1.31  #Fact    : 0
% 2.31/1.31  #Define  : 0
% 2.31/1.31  #Split   : 0
% 2.31/1.31  #Chain   : 0
% 2.31/1.31  #Close   : 0
% 2.31/1.31  
% 2.31/1.31  Ordering : KBO
% 2.31/1.31  
% 2.31/1.31  Simplification rules
% 2.31/1.31  ----------------------
% 2.31/1.31  #Subsume      : 0
% 2.31/1.31  #Demod        : 25
% 2.31/1.31  #Tautology    : 10
% 2.31/1.31  #SimpNegUnit  : 2
% 2.31/1.31  #BackRed      : 0
% 2.31/1.31  
% 2.31/1.31  #Partial instantiations: 0
% 2.31/1.31  #Strategies tried      : 1
% 2.31/1.31  
% 2.31/1.31  Timing (in seconds)
% 2.31/1.31  ----------------------
% 2.31/1.31  Preprocessing        : 0.34
% 2.31/1.31  Parsing              : 0.17
% 2.31/1.31  CNF conversion       : 0.04
% 2.31/1.31  Main loop            : 0.20
% 2.31/1.31  Inferencing          : 0.08
% 2.31/1.31  Reduction            : 0.06
% 2.31/1.31  Demodulation         : 0.04
% 2.31/1.31  BG Simplification    : 0.02
% 2.31/1.31  Subsumption          : 0.03
% 2.31/1.31  Abstraction          : 0.01
% 2.31/1.31  MUC search           : 0.00
% 2.31/1.31  Cooper               : 0.00
% 2.31/1.31  Total                : 0.58
% 2.31/1.31  Index Insertion      : 0.00
% 2.31/1.31  Index Deletion       : 0.00
% 2.31/1.31  Index Matching       : 0.00
% 2.31/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
