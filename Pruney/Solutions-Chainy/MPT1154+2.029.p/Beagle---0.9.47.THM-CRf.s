%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:36 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 115 expanded)
%              Number of leaves         :   42 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :  115 ( 238 expanded)
%              Number of equality atoms :   27 (  37 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_69,axiom,(
    ! [A,B,C,D,E,F,G,H,I] :
      ( I = k6_enumset1(A,B,C,D,E,F,G,H)
    <=> ! [J] :
          ( r2_hidden(J,I)
        <=> ~ ( J != A
              & J != B
              & J != C
              & J != D
              & J != E
              & J != F
              & J != G
              & J != H ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).

tff(f_141,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ~ r2_hidden(B,k1_orders_2(A,k6_domain_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_orders_2)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_123,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ~ ( r2_hidden(B,C)
                  & r2_hidden(B,k1_orders_2(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_orders_2)).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9,D_10] : k3_enumset1(A_7,A_7,B_8,C_9,D_10) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [D_14,E_15,B_12,A_11,C_13] : k4_enumset1(A_11,A_11,B_12,C_13,D_14,E_15) = k3_enumset1(A_11,B_12,C_13,D_14,E_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [C_18,B_17,A_16,D_19,E_20,F_21] : k5_enumset1(A_16,A_16,B_17,C_18,D_19,E_20,F_21) = k4_enumset1(A_16,B_17,C_18,D_19,E_20,F_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_217,plain,(
    ! [E_166,C_165,F_167,D_169,G_168,A_164,B_170] : k6_enumset1(A_164,A_164,B_170,C_165,D_169,E_166,F_167,G_168) = k5_enumset1(A_164,B_170,C_165,D_169,E_166,F_167,G_168) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    ! [G_35,H_36,E_33,J_40,A_29,F_34,D_32,B_30] : r2_hidden(J_40,k6_enumset1(A_29,B_30,J_40,D_32,E_33,F_34,G_35,H_36)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_257,plain,(
    ! [C_176,B_177,A_174,D_178,G_180,F_175,E_179] : r2_hidden(B_177,k5_enumset1(A_174,B_177,C_176,D_178,E_179,F_175,G_180)) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_28])).

tff(c_261,plain,(
    ! [F_181,B_182,D_185,C_186,E_183,A_184] : r2_hidden(A_184,k4_enumset1(A_184,B_182,C_186,D_185,E_183,F_181)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_257])).

tff(c_265,plain,(
    ! [C_187,E_191,B_189,A_188,D_190] : r2_hidden(A_188,k3_enumset1(A_188,B_189,C_187,D_190,E_191)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_261])).

tff(c_269,plain,(
    ! [A_192,B_193,C_194,D_195] : r2_hidden(A_192,k2_enumset1(A_192,B_193,C_194,D_195)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_265])).

tff(c_317,plain,(
    ! [A_205,B_206,C_207] : r2_hidden(A_205,k1_enumset1(A_205,B_206,C_207)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_269])).

tff(c_321,plain,(
    ! [A_208,B_209] : r2_hidden(A_208,k2_tarski(A_208,B_209)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_317])).

tff(c_324,plain,(
    ! [A_1] : r2_hidden(A_1,k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_321])).

tff(c_94,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_92,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_90,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_88,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_86,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_84,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_76,plain,(
    ! [A_47] :
      ( l1_struct_0(A_47)
      | ~ l1_orders_2(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_125,plain,(
    ! [A_69,B_70] :
      ( k6_domain_1(A_69,B_70) = k1_tarski(B_70)
      | ~ m1_subset_1(B_70,A_69)
      | v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_129,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_84,c_125])).

tff(c_130,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_72,plain,(
    ! [A_44] :
      ( ~ v1_xboole_0(u1_struct_0(A_44))
      | ~ l1_struct_0(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_134,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_130,c_72])).

tff(c_137,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_134])).

tff(c_140,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_137])).

tff(c_144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_140])).

tff(c_146,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_145,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_169,plain,(
    ! [A_147,B_148] :
      ( m1_subset_1(k6_domain_1(A_147,B_148),k1_zfmisc_1(A_147))
      | ~ m1_subset_1(B_148,A_147)
      | v1_xboole_0(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_177,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_169])).

tff(c_181,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_177])).

tff(c_182,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_181])).

tff(c_82,plain,(
    r2_hidden('#skF_4',k1_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_147,plain,(
    r2_hidden('#skF_4',k1_orders_2('#skF_3',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_82])).

tff(c_250,plain,(
    ! [B_171,A_172,C_173] :
      ( ~ r2_hidden(B_171,k1_orders_2(A_172,C_173))
      | ~ r2_hidden(B_171,C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ m1_subset_1(B_171,u1_struct_0(A_172))
      | ~ l1_orders_2(A_172)
      | ~ v5_orders_2(A_172)
      | ~ v4_orders_2(A_172)
      | ~ v3_orders_2(A_172)
      | v2_struct_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_252,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_147,c_250])).

tff(c_255,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_86,c_84,c_182,c_252])).

tff(c_256,plain,(
    ~ r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_255])).

tff(c_327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_256])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:11:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.44  
% 2.68/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.44  %$ r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.68/1.44  
% 2.68/1.44  %Foreground sorts:
% 2.68/1.44  
% 2.68/1.44  
% 2.68/1.44  %Background operators:
% 2.68/1.44  
% 2.68/1.44  
% 2.68/1.44  %Foreground operators:
% 2.68/1.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.68/1.44  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.68/1.44  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 2.68/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.68/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.68/1.44  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.68/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.68/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.68/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.68/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.68/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.44  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.68/1.44  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.68/1.44  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.68/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.68/1.44  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.68/1.44  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.68/1.44  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.68/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.68/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.44  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.68/1.44  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.68/1.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.68/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.68/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.68/1.44  
% 3.10/1.46  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.10/1.46  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.10/1.46  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.10/1.46  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.10/1.46  tff(f_35, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.10/1.46  tff(f_37, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 3.10/1.46  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 3.10/1.46  tff(f_69, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 3.10/1.46  tff(f_141, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k1_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_orders_2)).
% 3.10/1.46  tff(f_94, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.10/1.46  tff(f_101, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.10/1.46  tff(f_83, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.10/1.46  tff(f_90, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.10/1.46  tff(f_123, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k1_orders_2(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_orders_2)).
% 3.10/1.46  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.10/1.46  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.10/1.46  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.10/1.46  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (k3_enumset1(A_7, A_7, B_8, C_9, D_10)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.10/1.46  tff(c_10, plain, (![D_14, E_15, B_12, A_11, C_13]: (k4_enumset1(A_11, A_11, B_12, C_13, D_14, E_15)=k3_enumset1(A_11, B_12, C_13, D_14, E_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.10/1.46  tff(c_12, plain, (![C_18, B_17, A_16, D_19, E_20, F_21]: (k5_enumset1(A_16, A_16, B_17, C_18, D_19, E_20, F_21)=k4_enumset1(A_16, B_17, C_18, D_19, E_20, F_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.10/1.46  tff(c_217, plain, (![E_166, C_165, F_167, D_169, G_168, A_164, B_170]: (k6_enumset1(A_164, A_164, B_170, C_165, D_169, E_166, F_167, G_168)=k5_enumset1(A_164, B_170, C_165, D_169, E_166, F_167, G_168))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.10/1.46  tff(c_28, plain, (![G_35, H_36, E_33, J_40, A_29, F_34, D_32, B_30]: (r2_hidden(J_40, k6_enumset1(A_29, B_30, J_40, D_32, E_33, F_34, G_35, H_36)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.10/1.46  tff(c_257, plain, (![C_176, B_177, A_174, D_178, G_180, F_175, E_179]: (r2_hidden(B_177, k5_enumset1(A_174, B_177, C_176, D_178, E_179, F_175, G_180)))), inference(superposition, [status(thm), theory('equality')], [c_217, c_28])).
% 3.10/1.46  tff(c_261, plain, (![F_181, B_182, D_185, C_186, E_183, A_184]: (r2_hidden(A_184, k4_enumset1(A_184, B_182, C_186, D_185, E_183, F_181)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_257])).
% 3.10/1.46  tff(c_265, plain, (![C_187, E_191, B_189, A_188, D_190]: (r2_hidden(A_188, k3_enumset1(A_188, B_189, C_187, D_190, E_191)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_261])).
% 3.10/1.46  tff(c_269, plain, (![A_192, B_193, C_194, D_195]: (r2_hidden(A_192, k2_enumset1(A_192, B_193, C_194, D_195)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_265])).
% 3.10/1.46  tff(c_317, plain, (![A_205, B_206, C_207]: (r2_hidden(A_205, k1_enumset1(A_205, B_206, C_207)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_269])).
% 3.10/1.46  tff(c_321, plain, (![A_208, B_209]: (r2_hidden(A_208, k2_tarski(A_208, B_209)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_317])).
% 3.10/1.46  tff(c_324, plain, (![A_1]: (r2_hidden(A_1, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_321])).
% 3.10/1.46  tff(c_94, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.10/1.46  tff(c_92, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.10/1.46  tff(c_90, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.10/1.46  tff(c_88, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.10/1.46  tff(c_86, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.10/1.46  tff(c_84, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.10/1.46  tff(c_76, plain, (![A_47]: (l1_struct_0(A_47) | ~l1_orders_2(A_47))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.10/1.46  tff(c_125, plain, (![A_69, B_70]: (k6_domain_1(A_69, B_70)=k1_tarski(B_70) | ~m1_subset_1(B_70, A_69) | v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.10/1.46  tff(c_129, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_84, c_125])).
% 3.10/1.46  tff(c_130, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_129])).
% 3.10/1.46  tff(c_72, plain, (![A_44]: (~v1_xboole_0(u1_struct_0(A_44)) | ~l1_struct_0(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.10/1.46  tff(c_134, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_130, c_72])).
% 3.10/1.46  tff(c_137, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_94, c_134])).
% 3.10/1.46  tff(c_140, plain, (~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_76, c_137])).
% 3.10/1.46  tff(c_144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_140])).
% 3.10/1.46  tff(c_146, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_129])).
% 3.10/1.46  tff(c_145, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_129])).
% 3.10/1.46  tff(c_169, plain, (![A_147, B_148]: (m1_subset_1(k6_domain_1(A_147, B_148), k1_zfmisc_1(A_147)) | ~m1_subset_1(B_148, A_147) | v1_xboole_0(A_147))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.10/1.46  tff(c_177, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_145, c_169])).
% 3.10/1.46  tff(c_181, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_177])).
% 3.10/1.46  tff(c_182, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_146, c_181])).
% 3.10/1.46  tff(c_82, plain, (r2_hidden('#skF_4', k1_orders_2('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.10/1.46  tff(c_147, plain, (r2_hidden('#skF_4', k1_orders_2('#skF_3', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_82])).
% 3.10/1.46  tff(c_250, plain, (![B_171, A_172, C_173]: (~r2_hidden(B_171, k1_orders_2(A_172, C_173)) | ~r2_hidden(B_171, C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(u1_struct_0(A_172))) | ~m1_subset_1(B_171, u1_struct_0(A_172)) | ~l1_orders_2(A_172) | ~v5_orders_2(A_172) | ~v4_orders_2(A_172) | ~v3_orders_2(A_172) | v2_struct_0(A_172))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.10/1.46  tff(c_252, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_147, c_250])).
% 3.10/1.46  tff(c_255, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_86, c_84, c_182, c_252])).
% 3.10/1.46  tff(c_256, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_94, c_255])).
% 3.10/1.46  tff(c_327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_324, c_256])).
% 3.10/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.46  
% 3.10/1.46  Inference rules
% 3.10/1.46  ----------------------
% 3.10/1.46  #Ref     : 0
% 3.10/1.46  #Sup     : 49
% 3.10/1.46  #Fact    : 0
% 3.10/1.46  #Define  : 0
% 3.10/1.46  #Split   : 2
% 3.10/1.46  #Chain   : 0
% 3.10/1.46  #Close   : 0
% 3.10/1.46  
% 3.10/1.46  Ordering : KBO
% 3.10/1.46  
% 3.10/1.46  Simplification rules
% 3.10/1.46  ----------------------
% 3.10/1.46  #Subsume      : 1
% 3.10/1.46  #Demod        : 11
% 3.10/1.46  #Tautology    : 24
% 3.10/1.46  #SimpNegUnit  : 4
% 3.10/1.46  #BackRed      : 2
% 3.10/1.46  
% 3.10/1.46  #Partial instantiations: 0
% 3.10/1.46  #Strategies tried      : 1
% 3.10/1.46  
% 3.10/1.46  Timing (in seconds)
% 3.10/1.46  ----------------------
% 3.10/1.46  Preprocessing        : 0.35
% 3.10/1.46  Parsing              : 0.16
% 3.10/1.46  CNF conversion       : 0.03
% 3.10/1.46  Main loop            : 0.27
% 3.10/1.46  Inferencing          : 0.08
% 3.10/1.46  Reduction            : 0.07
% 3.10/1.46  Demodulation         : 0.05
% 3.10/1.46  BG Simplification    : 0.02
% 3.10/1.46  Subsumption          : 0.08
% 3.10/1.46  Abstraction          : 0.02
% 3.10/1.46  MUC search           : 0.00
% 3.10/1.46  Cooper               : 0.00
% 3.10/1.46  Total                : 0.66
% 3.10/1.46  Index Insertion      : 0.00
% 3.10/1.46  Index Deletion       : 0.00
% 3.10/1.46  Index Matching       : 0.00
% 3.10/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
