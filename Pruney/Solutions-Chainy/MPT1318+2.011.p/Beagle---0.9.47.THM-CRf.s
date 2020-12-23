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
% DateTime   : Thu Dec  3 10:23:06 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   47 (  64 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   52 (  87 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > l1_pre_topc > k9_subset_1 > k8_setfam_1 > k6_setfam_1 > k3_xboole_0 > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

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

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => m1_subset_1(k9_subset_1(u1_struct_0(A),B,C),k1_zfmisc_1(u1_struct_0(k1_pre_topc(A,C)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_tops_2)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

tff(c_6,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_8] :
      ( k8_setfam_1(A_8,k1_xboole_0) = A_8
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26,plain,(
    ! [A_8] : k8_setfam_1(A_8,k1_xboole_0) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_134,plain,(
    ! [A_52,B_53] :
      ( m1_subset_1(k8_setfam_1(A_52,B_53),k1_zfmisc_1(A_52))
      | ~ m1_subset_1(B_53,k1_zfmisc_1(k1_zfmisc_1(A_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_141,plain,(
    ! [A_8] :
      ( m1_subset_1(A_8,k1_zfmisc_1(A_8))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_8))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_134])).

tff(c_145,plain,(
    ! [A_8] : m1_subset_1(A_8,k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_141])).

tff(c_146,plain,(
    ! [A_54] : m1_subset_1(A_54,k1_zfmisc_1(A_54)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_141])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6] :
      ( k9_subset_1(A_4,B_5,C_6) = k3_xboole_0(B_5,C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_232,plain,(
    ! [A_60,B_61] : k9_subset_1(A_60,B_61,A_60) = k3_xboole_0(B_61,A_60) ),
    inference(resolution,[status(thm)],[c_146,c_4])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( m1_subset_1(k9_subset_1(A_1,B_2,C_3),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(C_3,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_238,plain,(
    ! [B_61,A_60] :
      ( m1_subset_1(k3_xboole_0(B_61,A_60),k1_zfmisc_1(A_60))
      | ~ m1_subset_1(A_60,k1_zfmisc_1(A_60)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_2])).

tff(c_252,plain,(
    ! [B_61,A_60] : m1_subset_1(k3_xboole_0(B_61,A_60),k1_zfmisc_1(A_60)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_238])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_154,plain,(
    ! [A_57,B_58] :
      ( u1_struct_0(k1_pre_topc(A_57,B_58)) = B_58
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_179,plain,
    ( u1_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_154])).

tff(c_199,plain,(
    u1_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_179])).

tff(c_50,plain,(
    ! [A_31,B_32,C_33] :
      ( k9_subset_1(A_31,B_32,C_33) = k3_xboole_0(B_32,C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_57,plain,(
    ! [B_32] : k9_subset_1(u1_struct_0('#skF_1'),B_32,'#skF_3') = k3_xboole_0(B_32,'#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_50])).

tff(c_18,plain,(
    ~ m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_78,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_18])).

tff(c_204,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_78])).

tff(c_258,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_204])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:40:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.43  
% 2.47/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.43  %$ r2_hidden > m1_subset_1 > l1_pre_topc > k9_subset_1 > k8_setfam_1 > k6_setfam_1 > k3_xboole_0 > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.47/1.43  
% 2.47/1.43  %Foreground sorts:
% 2.47/1.43  
% 2.47/1.43  
% 2.47/1.43  %Background operators:
% 2.47/1.43  
% 2.47/1.43  
% 2.47/1.43  %Foreground operators:
% 2.47/1.43  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 2.47/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.43  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.47/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.47/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.47/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.47/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.47/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.43  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.47/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.47/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.47/1.43  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.47/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.47/1.43  
% 2.47/1.44  tff(f_35, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.47/1.44  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.47/1.44  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 2.47/1.44  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.47/1.44  tff(f_29, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 2.47/1.44  tff(f_74, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => m1_subset_1(k9_subset_1(u1_struct_0(A), B, C), k1_zfmisc_1(u1_struct_0(k1_pre_topc(A, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_tops_2)).
% 2.47/1.44  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 2.47/1.44  tff(c_6, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.47/1.44  tff(c_8, plain, (![A_8]: (k8_setfam_1(A_8, k1_xboole_0)=A_8 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_8))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.47/1.44  tff(c_26, plain, (![A_8]: (k8_setfam_1(A_8, k1_xboole_0)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 2.47/1.44  tff(c_134, plain, (![A_52, B_53]: (m1_subset_1(k8_setfam_1(A_52, B_53), k1_zfmisc_1(A_52)) | ~m1_subset_1(B_53, k1_zfmisc_1(k1_zfmisc_1(A_52))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.47/1.44  tff(c_141, plain, (![A_8]: (m1_subset_1(A_8, k1_zfmisc_1(A_8)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_8))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_134])).
% 2.47/1.44  tff(c_145, plain, (![A_8]: (m1_subset_1(A_8, k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_141])).
% 2.47/1.44  tff(c_146, plain, (![A_54]: (m1_subset_1(A_54, k1_zfmisc_1(A_54)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_141])).
% 2.47/1.44  tff(c_4, plain, (![A_4, B_5, C_6]: (k9_subset_1(A_4, B_5, C_6)=k3_xboole_0(B_5, C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.47/1.44  tff(c_232, plain, (![A_60, B_61]: (k9_subset_1(A_60, B_61, A_60)=k3_xboole_0(B_61, A_60))), inference(resolution, [status(thm)], [c_146, c_4])).
% 2.47/1.44  tff(c_2, plain, (![A_1, B_2, C_3]: (m1_subset_1(k9_subset_1(A_1, B_2, C_3), k1_zfmisc_1(A_1)) | ~m1_subset_1(C_3, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.47/1.44  tff(c_238, plain, (![B_61, A_60]: (m1_subset_1(k3_xboole_0(B_61, A_60), k1_zfmisc_1(A_60)) | ~m1_subset_1(A_60, k1_zfmisc_1(A_60)))), inference(superposition, [status(thm), theory('equality')], [c_232, c_2])).
% 2.47/1.44  tff(c_252, plain, (![B_61, A_60]: (m1_subset_1(k3_xboole_0(B_61, A_60), k1_zfmisc_1(A_60)))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_238])).
% 2.47/1.44  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.47/1.44  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.47/1.44  tff(c_154, plain, (![A_57, B_58]: (u1_struct_0(k1_pre_topc(A_57, B_58))=B_58 | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.47/1.44  tff(c_179, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_154])).
% 2.47/1.44  tff(c_199, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_179])).
% 2.47/1.44  tff(c_50, plain, (![A_31, B_32, C_33]: (k9_subset_1(A_31, B_32, C_33)=k3_xboole_0(B_32, C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.47/1.44  tff(c_57, plain, (![B_32]: (k9_subset_1(u1_struct_0('#skF_1'), B_32, '#skF_3')=k3_xboole_0(B_32, '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_50])).
% 2.47/1.44  tff(c_18, plain, (~m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.47/1.44  tff(c_78, plain, (~m1_subset_1(k3_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_18])).
% 2.47/1.44  tff(c_204, plain, (~m1_subset_1(k3_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_78])).
% 2.47/1.44  tff(c_258, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_252, c_204])).
% 2.47/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.44  
% 2.47/1.44  Inference rules
% 2.47/1.44  ----------------------
% 2.47/1.44  #Ref     : 0
% 2.47/1.44  #Sup     : 53
% 2.47/1.44  #Fact    : 0
% 2.47/1.44  #Define  : 0
% 2.47/1.44  #Split   : 1
% 2.47/1.44  #Chain   : 0
% 2.47/1.44  #Close   : 0
% 2.47/1.44  
% 2.47/1.44  Ordering : KBO
% 2.47/1.44  
% 2.47/1.44  Simplification rules
% 2.47/1.44  ----------------------
% 2.47/1.44  #Subsume      : 0
% 2.47/1.44  #Demod        : 13
% 2.47/1.44  #Tautology    : 18
% 2.47/1.44  #SimpNegUnit  : 0
% 2.47/1.44  #BackRed      : 3
% 2.47/1.44  
% 2.47/1.44  #Partial instantiations: 0
% 2.47/1.44  #Strategies tried      : 1
% 2.47/1.44  
% 2.47/1.44  Timing (in seconds)
% 2.47/1.44  ----------------------
% 2.47/1.44  Preprocessing        : 0.41
% 2.47/1.44  Parsing              : 0.23
% 2.47/1.44  CNF conversion       : 0.02
% 2.47/1.45  Main loop            : 0.22
% 2.47/1.45  Inferencing          : 0.08
% 2.47/1.45  Reduction            : 0.07
% 2.47/1.45  Demodulation         : 0.06
% 2.47/1.45  BG Simplification    : 0.01
% 2.47/1.45  Subsumption          : 0.04
% 2.47/1.45  Abstraction          : 0.02
% 2.47/1.45  MUC search           : 0.00
% 2.47/1.45  Cooper               : 0.00
% 2.47/1.45  Total                : 0.66
% 2.47/1.45  Index Insertion      : 0.00
% 2.47/1.45  Index Deletion       : 0.00
% 2.47/1.45  Index Matching       : 0.00
% 2.47/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
