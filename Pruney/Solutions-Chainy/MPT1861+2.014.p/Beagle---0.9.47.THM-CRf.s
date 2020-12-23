%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:11 EST 2020

% Result     : Theorem 15.91s
% Output     : CNFRefutation 15.91s
% Verified   : 
% Statistics : Number of formulae       :   62 (  95 expanded)
%              Number of leaves         :   21 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :  111 ( 211 expanded)
%              Number of equality atoms :    7 (  14 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v2_tex_2(B,A)
                    | v2_tex_2(C,A) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14532,plain,(
    ! [A_236,B_237] :
      ( r1_tarski(A_236,B_237)
      | ~ m1_subset_1(A_236,k1_zfmisc_1(B_237)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14540,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_14532])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_76,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(A_30,B_31)
      | ~ m1_subset_1(A_30,k1_zfmisc_1(B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_84,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_76])).

tff(c_18,plain,
    ( v2_tex_2('#skF_3','#skF_1')
    | v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_26,plain,(
    v2_tex_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k3_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_228,plain,(
    ! [C_57,A_58,B_59] :
      ( v2_tex_2(C_57,A_58)
      | ~ v2_tex_2(B_59,A_58)
      | ~ r1_tarski(C_57,B_59)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_742,plain,(
    ! [A_73,B_74,A_75] :
      ( v2_tex_2(k3_xboole_0(A_73,B_74),A_75)
      | ~ v2_tex_2(A_73,A_75)
      | ~ m1_subset_1(k3_xboole_0(A_73,B_74),k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ m1_subset_1(A_73,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(resolution,[status(thm)],[c_6,c_228])).

tff(c_2385,plain,(
    ! [A_129,B_130,A_131] :
      ( v2_tex_2(k3_xboole_0(A_129,B_130),A_131)
      | ~ v2_tex_2(A_129,A_131)
      | ~ m1_subset_1(A_129,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_pre_topc(A_131)
      | ~ r1_tarski(k3_xboole_0(A_129,B_130),u1_struct_0(A_131)) ) ),
    inference(resolution,[status(thm)],[c_12,c_742])).

tff(c_14414,plain,(
    ! [A_228,C_229,A_230] :
      ( v2_tex_2(k3_xboole_0(A_228,C_229),A_230)
      | ~ v2_tex_2(A_228,A_230)
      | ~ m1_subset_1(A_228,k1_zfmisc_1(u1_struct_0(A_230)))
      | ~ l1_pre_topc(A_230)
      | ~ r1_tarski(A_228,u1_struct_0(A_230)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2385])).

tff(c_14421,plain,(
    ! [C_229] :
      ( v2_tex_2(k3_xboole_0('#skF_2',C_229),'#skF_1')
      | ~ v2_tex_2('#skF_2','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_22,c_14414])).

tff(c_14429,plain,(
    ! [C_231] : v2_tex_2(k3_xboole_0('#skF_2',C_231),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_24,c_26,c_14421])).

tff(c_14465,plain,(
    ! [B_2] : v2_tex_2(k3_xboole_0(B_2,'#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_14429])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_97,plain,(
    ! [A_37,B_38,C_39] :
      ( k9_subset_1(A_37,B_38,C_39) = k3_xboole_0(B_38,C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_105,plain,(
    ! [B_38] : k9_subset_1(u1_struct_0('#skF_1'),B_38,'#skF_3') = k3_xboole_0(B_38,'#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_97])).

tff(c_16,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_123,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_16])).

tff(c_124,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_123])).

tff(c_14480,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14465,c_124])).

tff(c_14481,plain,(
    v2_tex_2('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_14546,plain,(
    ! [A_240,C_241,B_242] :
      ( r1_tarski(k3_xboole_0(A_240,C_241),B_242)
      | ~ r1_tarski(A_240,B_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14549,plain,(
    ! [B_2,A_1,B_242] :
      ( r1_tarski(k3_xboole_0(B_2,A_1),B_242)
      | ~ r1_tarski(A_1,B_242) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_14546])).

tff(c_14590,plain,(
    ! [C_251,A_252,B_253] :
      ( v2_tex_2(C_251,A_252)
      | ~ v2_tex_2(B_253,A_252)
      | ~ r1_tarski(C_251,B_253)
      | ~ m1_subset_1(C_251,k1_zfmisc_1(u1_struct_0(A_252)))
      | ~ m1_subset_1(B_253,k1_zfmisc_1(u1_struct_0(A_252)))
      | ~ l1_pre_topc(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14960,plain,(
    ! [A_276,B_277,A_278] :
      ( v2_tex_2(k3_xboole_0(A_276,B_277),A_278)
      | ~ v2_tex_2(A_276,A_278)
      | ~ m1_subset_1(k3_xboole_0(A_276,B_277),k1_zfmisc_1(u1_struct_0(A_278)))
      | ~ m1_subset_1(A_276,k1_zfmisc_1(u1_struct_0(A_278)))
      | ~ l1_pre_topc(A_278) ) ),
    inference(resolution,[status(thm)],[c_6,c_14590])).

tff(c_16513,plain,(
    ! [A_327,B_328,A_329] :
      ( v2_tex_2(k3_xboole_0(A_327,B_328),A_329)
      | ~ v2_tex_2(A_327,A_329)
      | ~ m1_subset_1(A_327,k1_zfmisc_1(u1_struct_0(A_329)))
      | ~ l1_pre_topc(A_329)
      | ~ r1_tarski(k3_xboole_0(A_327,B_328),u1_struct_0(A_329)) ) ),
    inference(resolution,[status(thm)],[c_12,c_14960])).

tff(c_24734,plain,(
    ! [B_425,A_426,A_427] :
      ( v2_tex_2(k3_xboole_0(B_425,A_426),A_427)
      | ~ v2_tex_2(B_425,A_427)
      | ~ m1_subset_1(B_425,k1_zfmisc_1(u1_struct_0(A_427)))
      | ~ l1_pre_topc(A_427)
      | ~ r1_tarski(A_426,u1_struct_0(A_427)) ) ),
    inference(resolution,[status(thm)],[c_14549,c_16513])).

tff(c_24739,plain,(
    ! [A_426] :
      ( v2_tex_2(k3_xboole_0('#skF_3',A_426),'#skF_1')
      | ~ v2_tex_2('#skF_3','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_426,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_20,c_24734])).

tff(c_24749,plain,(
    ! [A_428] :
      ( v2_tex_2(k3_xboole_0('#skF_3',A_428),'#skF_1')
      | ~ r1_tarski(A_428,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_14481,c_24739])).

tff(c_14553,plain,(
    ! [A_243,B_244,C_245] :
      ( k9_subset_1(A_243,B_244,C_245) = k3_xboole_0(B_244,C_245)
      | ~ m1_subset_1(C_245,k1_zfmisc_1(A_243)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14561,plain,(
    ! [B_244] : k9_subset_1(u1_struct_0('#skF_1'),B_244,'#skF_3') = k3_xboole_0(B_244,'#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_14553])).

tff(c_14579,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14561,c_16])).

tff(c_14580,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14579])).

tff(c_24752,plain,(
    ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24749,c_14580])).

tff(c_24796,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14540,c_24752])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:46:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.91/7.88  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.91/7.88  
% 15.91/7.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.91/7.89  %$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 15.91/7.89  
% 15.91/7.89  %Foreground sorts:
% 15.91/7.89  
% 15.91/7.89  
% 15.91/7.89  %Background operators:
% 15.91/7.89  
% 15.91/7.89  
% 15.91/7.89  %Foreground operators:
% 15.91/7.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.91/7.89  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 15.91/7.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.91/7.89  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 15.91/7.89  tff('#skF_2', type, '#skF_2': $i).
% 15.91/7.89  tff('#skF_3', type, '#skF_3': $i).
% 15.91/7.89  tff('#skF_1', type, '#skF_1': $i).
% 15.91/7.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.91/7.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.91/7.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.91/7.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.91/7.89  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 15.91/7.89  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 15.91/7.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.91/7.89  
% 15.91/7.90  tff(f_70, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tex_2)).
% 15.91/7.90  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 15.91/7.90  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 15.91/7.90  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 15.91/7.90  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 15.91/7.90  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_tex_2)).
% 15.91/7.90  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 15.91/7.90  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 15.91/7.90  tff(c_14532, plain, (![A_236, B_237]: (r1_tarski(A_236, B_237) | ~m1_subset_1(A_236, k1_zfmisc_1(B_237)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.91/7.90  tff(c_14540, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_14532])).
% 15.91/7.90  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 15.91/7.90  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 15.91/7.90  tff(c_76, plain, (![A_30, B_31]: (r1_tarski(A_30, B_31) | ~m1_subset_1(A_30, k1_zfmisc_1(B_31)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.91/7.90  tff(c_84, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_76])).
% 15.91/7.90  tff(c_18, plain, (v2_tex_2('#skF_3', '#skF_1') | v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 15.91/7.90  tff(c_26, plain, (v2_tex_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_18])).
% 15.91/7.90  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(k3_xboole_0(A_3, C_5), B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.91/7.90  tff(c_12, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.91/7.90  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 15.91/7.90  tff(c_228, plain, (![C_57, A_58, B_59]: (v2_tex_2(C_57, A_58) | ~v2_tex_2(B_59, A_58) | ~r1_tarski(C_57, B_59) | ~m1_subset_1(C_57, k1_zfmisc_1(u1_struct_0(A_58))) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_55])).
% 15.91/7.90  tff(c_742, plain, (![A_73, B_74, A_75]: (v2_tex_2(k3_xboole_0(A_73, B_74), A_75) | ~v2_tex_2(A_73, A_75) | ~m1_subset_1(k3_xboole_0(A_73, B_74), k1_zfmisc_1(u1_struct_0(A_75))) | ~m1_subset_1(A_73, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75))), inference(resolution, [status(thm)], [c_6, c_228])).
% 15.91/7.90  tff(c_2385, plain, (![A_129, B_130, A_131]: (v2_tex_2(k3_xboole_0(A_129, B_130), A_131) | ~v2_tex_2(A_129, A_131) | ~m1_subset_1(A_129, k1_zfmisc_1(u1_struct_0(A_131))) | ~l1_pre_topc(A_131) | ~r1_tarski(k3_xboole_0(A_129, B_130), u1_struct_0(A_131)))), inference(resolution, [status(thm)], [c_12, c_742])).
% 15.91/7.90  tff(c_14414, plain, (![A_228, C_229, A_230]: (v2_tex_2(k3_xboole_0(A_228, C_229), A_230) | ~v2_tex_2(A_228, A_230) | ~m1_subset_1(A_228, k1_zfmisc_1(u1_struct_0(A_230))) | ~l1_pre_topc(A_230) | ~r1_tarski(A_228, u1_struct_0(A_230)))), inference(resolution, [status(thm)], [c_4, c_2385])).
% 15.91/7.90  tff(c_14421, plain, (![C_229]: (v2_tex_2(k3_xboole_0('#skF_2', C_229), '#skF_1') | ~v2_tex_2('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~r1_tarski('#skF_2', u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_22, c_14414])).
% 15.91/7.90  tff(c_14429, plain, (![C_231]: (v2_tex_2(k3_xboole_0('#skF_2', C_231), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_24, c_26, c_14421])).
% 15.91/7.90  tff(c_14465, plain, (![B_2]: (v2_tex_2(k3_xboole_0(B_2, '#skF_2'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_14429])).
% 15.91/7.90  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 15.91/7.90  tff(c_97, plain, (![A_37, B_38, C_39]: (k9_subset_1(A_37, B_38, C_39)=k3_xboole_0(B_38, C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.91/7.90  tff(c_105, plain, (![B_38]: (k9_subset_1(u1_struct_0('#skF_1'), B_38, '#skF_3')=k3_xboole_0(B_38, '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_97])).
% 15.91/7.90  tff(c_16, plain, (~v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 15.91/7.90  tff(c_123, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_16])).
% 15.91/7.90  tff(c_124, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_123])).
% 15.91/7.90  tff(c_14480, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14465, c_124])).
% 15.91/7.90  tff(c_14481, plain, (v2_tex_2('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_18])).
% 15.91/7.90  tff(c_14546, plain, (![A_240, C_241, B_242]: (r1_tarski(k3_xboole_0(A_240, C_241), B_242) | ~r1_tarski(A_240, B_242))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.91/7.90  tff(c_14549, plain, (![B_2, A_1, B_242]: (r1_tarski(k3_xboole_0(B_2, A_1), B_242) | ~r1_tarski(A_1, B_242))), inference(superposition, [status(thm), theory('equality')], [c_2, c_14546])).
% 15.91/7.90  tff(c_14590, plain, (![C_251, A_252, B_253]: (v2_tex_2(C_251, A_252) | ~v2_tex_2(B_253, A_252) | ~r1_tarski(C_251, B_253) | ~m1_subset_1(C_251, k1_zfmisc_1(u1_struct_0(A_252))) | ~m1_subset_1(B_253, k1_zfmisc_1(u1_struct_0(A_252))) | ~l1_pre_topc(A_252))), inference(cnfTransformation, [status(thm)], [f_55])).
% 15.91/7.90  tff(c_14960, plain, (![A_276, B_277, A_278]: (v2_tex_2(k3_xboole_0(A_276, B_277), A_278) | ~v2_tex_2(A_276, A_278) | ~m1_subset_1(k3_xboole_0(A_276, B_277), k1_zfmisc_1(u1_struct_0(A_278))) | ~m1_subset_1(A_276, k1_zfmisc_1(u1_struct_0(A_278))) | ~l1_pre_topc(A_278))), inference(resolution, [status(thm)], [c_6, c_14590])).
% 15.91/7.90  tff(c_16513, plain, (![A_327, B_328, A_329]: (v2_tex_2(k3_xboole_0(A_327, B_328), A_329) | ~v2_tex_2(A_327, A_329) | ~m1_subset_1(A_327, k1_zfmisc_1(u1_struct_0(A_329))) | ~l1_pre_topc(A_329) | ~r1_tarski(k3_xboole_0(A_327, B_328), u1_struct_0(A_329)))), inference(resolution, [status(thm)], [c_12, c_14960])).
% 15.91/7.90  tff(c_24734, plain, (![B_425, A_426, A_427]: (v2_tex_2(k3_xboole_0(B_425, A_426), A_427) | ~v2_tex_2(B_425, A_427) | ~m1_subset_1(B_425, k1_zfmisc_1(u1_struct_0(A_427))) | ~l1_pre_topc(A_427) | ~r1_tarski(A_426, u1_struct_0(A_427)))), inference(resolution, [status(thm)], [c_14549, c_16513])).
% 15.91/7.90  tff(c_24739, plain, (![A_426]: (v2_tex_2(k3_xboole_0('#skF_3', A_426), '#skF_1') | ~v2_tex_2('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_426, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_20, c_24734])).
% 15.91/7.90  tff(c_24749, plain, (![A_428]: (v2_tex_2(k3_xboole_0('#skF_3', A_428), '#skF_1') | ~r1_tarski(A_428, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_14481, c_24739])).
% 15.91/7.90  tff(c_14553, plain, (![A_243, B_244, C_245]: (k9_subset_1(A_243, B_244, C_245)=k3_xboole_0(B_244, C_245) | ~m1_subset_1(C_245, k1_zfmisc_1(A_243)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.91/7.90  tff(c_14561, plain, (![B_244]: (k9_subset_1(u1_struct_0('#skF_1'), B_244, '#skF_3')=k3_xboole_0(B_244, '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_14553])).
% 15.91/7.90  tff(c_14579, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14561, c_16])).
% 15.91/7.90  tff(c_14580, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14579])).
% 15.91/7.90  tff(c_24752, plain, (~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24749, c_14580])).
% 15.91/7.90  tff(c_24796, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14540, c_24752])).
% 15.91/7.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.91/7.90  
% 15.91/7.90  Inference rules
% 15.91/7.90  ----------------------
% 15.91/7.90  #Ref     : 0
% 15.91/7.90  #Sup     : 7140
% 15.91/7.90  #Fact    : 0
% 15.91/7.90  #Define  : 0
% 15.91/7.90  #Split   : 4
% 15.91/7.90  #Chain   : 0
% 15.91/7.90  #Close   : 0
% 15.91/7.90  
% 15.91/7.90  Ordering : KBO
% 15.91/7.90  
% 15.91/7.90  Simplification rules
% 15.91/7.90  ----------------------
% 15.91/7.90  #Subsume      : 862
% 15.91/7.90  #Demod        : 878
% 15.91/7.90  #Tautology    : 1128
% 15.91/7.90  #SimpNegUnit  : 0
% 15.91/7.90  #BackRed      : 3
% 15.91/7.90  
% 15.91/7.90  #Partial instantiations: 0
% 15.91/7.90  #Strategies tried      : 1
% 15.91/7.90  
% 15.91/7.90  Timing (in seconds)
% 15.91/7.90  ----------------------
% 15.91/7.90  Preprocessing        : 0.28
% 15.91/7.90  Parsing              : 0.15
% 15.91/7.90  CNF conversion       : 0.02
% 15.91/7.90  Main loop            : 6.83
% 15.91/7.90  Inferencing          : 1.28
% 15.91/7.90  Reduction            : 4.50
% 15.91/7.90  Demodulation         : 4.30
% 15.91/7.90  BG Simplification    : 0.21
% 15.91/7.90  Subsumption          : 0.66
% 15.91/7.90  Abstraction          : 0.26
% 15.91/7.90  MUC search           : 0.00
% 15.91/7.90  Cooper               : 0.00
% 15.91/7.90  Total                : 7.13
% 15.91/7.90  Index Insertion      : 0.00
% 15.91/7.90  Index Deletion       : 0.00
% 15.91/7.90  Index Matching       : 0.00
% 15.91/7.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
