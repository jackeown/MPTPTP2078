%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:36 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 111 expanded)
%              Number of leaves         :   43 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :  117 ( 223 expanded)
%              Number of equality atoms :   27 (  33 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   1 average)

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

tff(f_144,negated_conjecture,(
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

tff(f_97,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_73,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

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

tff(f_126,axiom,(
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

tff(c_88,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_78,plain,(
    ! [A_49] :
      ( l1_struct_0(A_49)
      | ~ l1_orders_2(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_96,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_86,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_128,plain,(
    ! [A_72,B_73] :
      ( k6_domain_1(A_72,B_73) = k1_tarski(B_73)
      | ~ m1_subset_1(B_73,A_72)
      | v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_136,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_86,c_128])).

tff(c_141,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_76,plain,(
    ! [A_48] :
      ( ~ v1_xboole_0(u1_struct_0(A_48))
      | ~ l1_struct_0(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_144,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_141,c_76])).

tff(c_147,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_144])).

tff(c_150,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_147])).

tff(c_154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_150])).

tff(c_156,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_72,plain,(
    ! [A_43,B_44] :
      ( r2_hidden(A_43,B_44)
      | v1_xboole_0(B_44)
      | ~ m1_subset_1(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_70,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1(k1_tarski(A_41),k1_zfmisc_1(B_42))
      | ~ r2_hidden(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_94,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_92,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_90,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

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

tff(c_244,plain,(
    ! [F_170,A_167,D_172,E_169,G_171,C_168,B_173] : k6_enumset1(A_167,A_167,B_173,C_168,D_172,E_169,F_170,G_171) = k5_enumset1(A_167,B_173,C_168,D_172,E_169,F_170,G_171) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [G_35,H_36,E_33,J_40,A_29,D_32,C_31,B_30] : r2_hidden(J_40,k6_enumset1(A_29,B_30,C_31,D_32,E_33,J_40,G_35,H_36)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_277,plain,(
    ! [B_177,E_178,F_176,G_175,D_174,A_180,C_179] : r2_hidden(E_178,k5_enumset1(A_180,B_177,C_179,D_174,E_178,F_176,G_175)) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_22])).

tff(c_284,plain,(
    ! [F_181,B_182,D_185,C_186,E_183,A_184] : r2_hidden(D_185,k4_enumset1(A_184,B_182,C_186,D_185,E_183,F_181)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_277])).

tff(c_291,plain,(
    ! [C_187,E_191,B_189,A_188,D_190] : r2_hidden(C_187,k3_enumset1(A_188,B_189,C_187,D_190,E_191)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_284])).

tff(c_298,plain,(
    ! [B_192,A_193,C_194,D_195] : r2_hidden(B_192,k2_enumset1(A_193,B_192,C_194,D_195)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_291])).

tff(c_305,plain,(
    ! [A_196,B_197,C_198] : r2_hidden(A_196,k1_enumset1(A_196,B_197,C_198)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_298])).

tff(c_361,plain,(
    ! [A_208,B_209] : r2_hidden(A_208,k2_tarski(A_208,B_209)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_305])).

tff(c_366,plain,(
    ! [A_1] : r2_hidden(A_1,k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_361])).

tff(c_155,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_84,plain,(
    r2_hidden('#skF_4',k1_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_157,plain,(
    r2_hidden('#skF_4',k1_orders_2('#skF_3',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_84])).

tff(c_492,plain,(
    ! [B_228,A_229,C_230] :
      ( ~ r2_hidden(B_228,k1_orders_2(A_229,C_230))
      | ~ r2_hidden(B_228,C_230)
      | ~ m1_subset_1(C_230,k1_zfmisc_1(u1_struct_0(A_229)))
      | ~ m1_subset_1(B_228,u1_struct_0(A_229))
      | ~ l1_orders_2(A_229)
      | ~ v5_orders_2(A_229)
      | ~ v4_orders_2(A_229)
      | ~ v3_orders_2(A_229)
      | v2_struct_0(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_494,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_157,c_492])).

tff(c_500,plain,
    ( ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_90,c_88,c_86,c_366,c_494])).

tff(c_501,plain,(
    ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_500])).

tff(c_506,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_70,c_501])).

tff(c_509,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_72,c_506])).

tff(c_512,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_509])).

tff(c_514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_512])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:52:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.00/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.45  
% 3.00/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.45  %$ r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.00/1.45  
% 3.00/1.45  %Foreground sorts:
% 3.00/1.45  
% 3.00/1.45  
% 3.00/1.45  %Background operators:
% 3.00/1.45  
% 3.00/1.45  
% 3.00/1.45  %Foreground operators:
% 3.00/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.00/1.45  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.00/1.45  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 3.00/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.00/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.00/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.00/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.00/1.45  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.00/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.00/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.00/1.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.00/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.00/1.45  tff('#skF_3', type, '#skF_3': $i).
% 3.00/1.45  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.00/1.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.00/1.45  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.00/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.00/1.45  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.00/1.45  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.00/1.45  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.00/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.00/1.45  tff('#skF_4', type, '#skF_4': $i).
% 3.00/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.00/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.00/1.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.00/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.00/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.00/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.00/1.45  
% 3.46/1.47  tff(f_144, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k1_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_orders_2)).
% 3.46/1.47  tff(f_97, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.46/1.47  tff(f_104, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.46/1.47  tff(f_93, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.46/1.47  tff(f_79, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.46/1.47  tff(f_73, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 3.46/1.47  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.46/1.47  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.46/1.47  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.46/1.47  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.46/1.47  tff(f_35, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.46/1.47  tff(f_37, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 3.46/1.47  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 3.46/1.47  tff(f_69, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 3.46/1.47  tff(f_126, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k1_orders_2(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_orders_2)).
% 3.46/1.47  tff(c_88, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.46/1.47  tff(c_78, plain, (![A_49]: (l1_struct_0(A_49) | ~l1_orders_2(A_49))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.46/1.47  tff(c_96, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.46/1.47  tff(c_86, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.46/1.47  tff(c_128, plain, (![A_72, B_73]: (k6_domain_1(A_72, B_73)=k1_tarski(B_73) | ~m1_subset_1(B_73, A_72) | v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.46/1.47  tff(c_136, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_86, c_128])).
% 3.46/1.47  tff(c_141, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_136])).
% 3.46/1.47  tff(c_76, plain, (![A_48]: (~v1_xboole_0(u1_struct_0(A_48)) | ~l1_struct_0(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.46/1.47  tff(c_144, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_141, c_76])).
% 3.46/1.47  tff(c_147, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_96, c_144])).
% 3.46/1.47  tff(c_150, plain, (~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_78, c_147])).
% 3.46/1.47  tff(c_154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_150])).
% 3.46/1.47  tff(c_156, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_136])).
% 3.46/1.47  tff(c_72, plain, (![A_43, B_44]: (r2_hidden(A_43, B_44) | v1_xboole_0(B_44) | ~m1_subset_1(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.46/1.47  tff(c_70, plain, (![A_41, B_42]: (m1_subset_1(k1_tarski(A_41), k1_zfmisc_1(B_42)) | ~r2_hidden(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.46/1.47  tff(c_94, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.46/1.47  tff(c_92, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.46/1.47  tff(c_90, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.46/1.47  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.46/1.47  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.46/1.47  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.46/1.47  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (k3_enumset1(A_7, A_7, B_8, C_9, D_10)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.46/1.47  tff(c_10, plain, (![D_14, E_15, B_12, A_11, C_13]: (k4_enumset1(A_11, A_11, B_12, C_13, D_14, E_15)=k3_enumset1(A_11, B_12, C_13, D_14, E_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.46/1.47  tff(c_12, plain, (![C_18, B_17, A_16, D_19, E_20, F_21]: (k5_enumset1(A_16, A_16, B_17, C_18, D_19, E_20, F_21)=k4_enumset1(A_16, B_17, C_18, D_19, E_20, F_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.46/1.47  tff(c_244, plain, (![F_170, A_167, D_172, E_169, G_171, C_168, B_173]: (k6_enumset1(A_167, A_167, B_173, C_168, D_172, E_169, F_170, G_171)=k5_enumset1(A_167, B_173, C_168, D_172, E_169, F_170, G_171))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.46/1.47  tff(c_22, plain, (![G_35, H_36, E_33, J_40, A_29, D_32, C_31, B_30]: (r2_hidden(J_40, k6_enumset1(A_29, B_30, C_31, D_32, E_33, J_40, G_35, H_36)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.46/1.47  tff(c_277, plain, (![B_177, E_178, F_176, G_175, D_174, A_180, C_179]: (r2_hidden(E_178, k5_enumset1(A_180, B_177, C_179, D_174, E_178, F_176, G_175)))), inference(superposition, [status(thm), theory('equality')], [c_244, c_22])).
% 3.46/1.47  tff(c_284, plain, (![F_181, B_182, D_185, C_186, E_183, A_184]: (r2_hidden(D_185, k4_enumset1(A_184, B_182, C_186, D_185, E_183, F_181)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_277])).
% 3.46/1.47  tff(c_291, plain, (![C_187, E_191, B_189, A_188, D_190]: (r2_hidden(C_187, k3_enumset1(A_188, B_189, C_187, D_190, E_191)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_284])).
% 3.46/1.47  tff(c_298, plain, (![B_192, A_193, C_194, D_195]: (r2_hidden(B_192, k2_enumset1(A_193, B_192, C_194, D_195)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_291])).
% 3.46/1.47  tff(c_305, plain, (![A_196, B_197, C_198]: (r2_hidden(A_196, k1_enumset1(A_196, B_197, C_198)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_298])).
% 3.46/1.47  tff(c_361, plain, (![A_208, B_209]: (r2_hidden(A_208, k2_tarski(A_208, B_209)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_305])).
% 3.46/1.47  tff(c_366, plain, (![A_1]: (r2_hidden(A_1, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_361])).
% 3.46/1.47  tff(c_155, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_136])).
% 3.46/1.47  tff(c_84, plain, (r2_hidden('#skF_4', k1_orders_2('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.46/1.47  tff(c_157, plain, (r2_hidden('#skF_4', k1_orders_2('#skF_3', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_84])).
% 3.46/1.47  tff(c_492, plain, (![B_228, A_229, C_230]: (~r2_hidden(B_228, k1_orders_2(A_229, C_230)) | ~r2_hidden(B_228, C_230) | ~m1_subset_1(C_230, k1_zfmisc_1(u1_struct_0(A_229))) | ~m1_subset_1(B_228, u1_struct_0(A_229)) | ~l1_orders_2(A_229) | ~v5_orders_2(A_229) | ~v4_orders_2(A_229) | ~v3_orders_2(A_229) | v2_struct_0(A_229))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.46/1.47  tff(c_494, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_157, c_492])).
% 3.46/1.47  tff(c_500, plain, (~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_90, c_88, c_86, c_366, c_494])).
% 3.46/1.47  tff(c_501, plain, (~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_96, c_500])).
% 3.46/1.47  tff(c_506, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_70, c_501])).
% 3.46/1.47  tff(c_509, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_72, c_506])).
% 3.46/1.47  tff(c_512, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_509])).
% 3.46/1.47  tff(c_514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_156, c_512])).
% 3.46/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.47  
% 3.46/1.47  Inference rules
% 3.46/1.47  ----------------------
% 3.46/1.47  #Ref     : 0
% 3.46/1.47  #Sup     : 98
% 3.46/1.47  #Fact    : 0
% 3.46/1.47  #Define  : 0
% 3.46/1.47  #Split   : 2
% 3.46/1.47  #Chain   : 0
% 3.46/1.47  #Close   : 0
% 3.46/1.47  
% 3.46/1.47  Ordering : KBO
% 3.46/1.47  
% 3.46/1.47  Simplification rules
% 3.46/1.47  ----------------------
% 3.46/1.47  #Subsume      : 0
% 3.46/1.47  #Demod        : 13
% 3.46/1.47  #Tautology    : 33
% 3.46/1.47  #SimpNegUnit  : 3
% 3.46/1.47  #BackRed      : 1
% 3.46/1.47  
% 3.46/1.47  #Partial instantiations: 0
% 3.46/1.47  #Strategies tried      : 1
% 3.46/1.47  
% 3.46/1.47  Timing (in seconds)
% 3.46/1.47  ----------------------
% 3.46/1.47  Preprocessing        : 0.36
% 3.46/1.47  Parsing              : 0.17
% 3.46/1.47  CNF conversion       : 0.03
% 3.46/1.47  Main loop            : 0.33
% 3.46/1.47  Inferencing          : 0.10
% 3.46/1.47  Reduction            : 0.10
% 3.46/1.47  Demodulation         : 0.07
% 3.46/1.47  BG Simplification    : 0.02
% 3.46/1.47  Subsumption          : 0.09
% 3.46/1.47  Abstraction          : 0.03
% 3.46/1.47  MUC search           : 0.00
% 3.46/1.47  Cooper               : 0.00
% 3.46/1.47  Total                : 0.72
% 3.46/1.47  Index Insertion      : 0.00
% 3.46/1.47  Index Deletion       : 0.00
% 3.46/1.47  Index Matching       : 0.00
% 3.46/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
