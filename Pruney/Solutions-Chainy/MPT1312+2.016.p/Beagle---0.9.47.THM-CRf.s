%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:59 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   46 (  51 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   60 (  76 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
               => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_2)).

tff(f_39,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_25,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_322,plain,(
    ! [C_55,A_56,B_57] :
      ( m1_subset_1(C_55,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ m1_subset_1(C_55,k1_zfmisc_1(u1_struct_0(B_57)))
      | ~ m1_pre_topc(B_57,A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_440,plain,(
    ! [B_67,A_68] :
      ( m1_subset_1(u1_struct_0(B_67),k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ m1_pre_topc(B_67,A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_25,c_322])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_448,plain,(
    ! [B_69,A_70] :
      ( r1_tarski(u1_struct_0(B_69),u1_struct_0(A_70))
      | ~ m1_pre_topc(B_69,A_70)
      | ~ l1_pre_topc(A_70) ) ),
    inference(resolution,[status(thm)],[c_440,c_12])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k1_zfmisc_1(A_6),k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_36,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(A_25,B_26)
      | ~ m1_subset_1(A_25,k1_zfmisc_1(B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_43,plain,(
    r1_tarski('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_20,c_36])).

tff(c_46,plain,(
    ! [A_28,B_29] :
      ( k2_xboole_0(A_28,B_29) = B_29
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_53,plain,(
    k2_xboole_0('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) = k1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_43,c_46])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_144,plain,(
    ! [C_44] :
      ( r1_tarski('#skF_3',C_44)
      | ~ r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_2')),C_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_2])).

tff(c_162,plain,(
    ! [B_7] :
      ( r1_tarski('#skF_3',k1_zfmisc_1(B_7))
      | ~ r1_tarski(u1_struct_0('#skF_2'),B_7) ) ),
    inference(resolution,[status(thm)],[c_6,c_144])).

tff(c_458,plain,(
    ! [A_71] :
      ( r1_tarski('#skF_3',k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ m1_pre_topc('#skF_2',A_71)
      | ~ l1_pre_topc(A_71) ) ),
    inference(resolution,[status(thm)],[c_448,c_162])).

tff(c_64,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1(A_31,k1_zfmisc_1(B_32))
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_72,plain,(
    ~ r1_tarski('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_64,c_18])).

tff(c_461,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_458,c_72])).

tff(c_468,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_461])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:00:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.27  
% 2.09/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.27  %$ r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.09/1.27  
% 2.09/1.27  %Foreground sorts:
% 2.09/1.27  
% 2.09/1.27  
% 2.09/1.27  %Background operators:
% 2.09/1.27  
% 2.09/1.27  
% 2.09/1.27  %Foreground operators:
% 2.09/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.09/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.09/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.27  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.09/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.09/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.09/1.27  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.09/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.09/1.27  
% 2.09/1.28  tff(f_66, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_tops_2)).
% 2.09/1.28  tff(f_39, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.09/1.28  tff(f_41, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.09/1.28  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 2.09/1.28  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.09/1.28  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.09/1.28  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.09/1.28  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.09/1.28  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.09/1.28  tff(c_22, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.09/1.28  tff(c_8, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.09/1.28  tff(c_10, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.09/1.28  tff(c_25, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 2.09/1.28  tff(c_322, plain, (![C_55, A_56, B_57]: (m1_subset_1(C_55, k1_zfmisc_1(u1_struct_0(A_56))) | ~m1_subset_1(C_55, k1_zfmisc_1(u1_struct_0(B_57))) | ~m1_pre_topc(B_57, A_56) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.09/1.28  tff(c_440, plain, (![B_67, A_68]: (m1_subset_1(u1_struct_0(B_67), k1_zfmisc_1(u1_struct_0(A_68))) | ~m1_pre_topc(B_67, A_68) | ~l1_pre_topc(A_68))), inference(resolution, [status(thm)], [c_25, c_322])).
% 2.09/1.28  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.09/1.28  tff(c_448, plain, (![B_69, A_70]: (r1_tarski(u1_struct_0(B_69), u1_struct_0(A_70)) | ~m1_pre_topc(B_69, A_70) | ~l1_pre_topc(A_70))), inference(resolution, [status(thm)], [c_440, c_12])).
% 2.09/1.28  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k1_zfmisc_1(A_6), k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.09/1.28  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.09/1.28  tff(c_36, plain, (![A_25, B_26]: (r1_tarski(A_25, B_26) | ~m1_subset_1(A_25, k1_zfmisc_1(B_26)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.09/1.28  tff(c_43, plain, (r1_tarski('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_20, c_36])).
% 2.09/1.28  tff(c_46, plain, (![A_28, B_29]: (k2_xboole_0(A_28, B_29)=B_29 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.09/1.28  tff(c_53, plain, (k2_xboole_0('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))=k1_zfmisc_1(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_43, c_46])).
% 2.09/1.28  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.09/1.28  tff(c_144, plain, (![C_44]: (r1_tarski('#skF_3', C_44) | ~r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_2')), C_44))), inference(superposition, [status(thm), theory('equality')], [c_53, c_2])).
% 2.09/1.28  tff(c_162, plain, (![B_7]: (r1_tarski('#skF_3', k1_zfmisc_1(B_7)) | ~r1_tarski(u1_struct_0('#skF_2'), B_7))), inference(resolution, [status(thm)], [c_6, c_144])).
% 2.09/1.28  tff(c_458, plain, (![A_71]: (r1_tarski('#skF_3', k1_zfmisc_1(u1_struct_0(A_71))) | ~m1_pre_topc('#skF_2', A_71) | ~l1_pre_topc(A_71))), inference(resolution, [status(thm)], [c_448, c_162])).
% 2.09/1.28  tff(c_64, plain, (![A_31, B_32]: (m1_subset_1(A_31, k1_zfmisc_1(B_32)) | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.09/1.28  tff(c_18, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.09/1.28  tff(c_72, plain, (~r1_tarski('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_64, c_18])).
% 2.09/1.28  tff(c_461, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_458, c_72])).
% 2.09/1.28  tff(c_468, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_461])).
% 2.09/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.28  
% 2.09/1.28  Inference rules
% 2.09/1.28  ----------------------
% 2.09/1.28  #Ref     : 0
% 2.09/1.28  #Sup     : 97
% 2.09/1.28  #Fact    : 0
% 2.09/1.28  #Define  : 0
% 2.09/1.28  #Split   : 0
% 2.09/1.28  #Chain   : 0
% 2.09/1.28  #Close   : 0
% 2.09/1.28  
% 2.09/1.28  Ordering : KBO
% 2.09/1.28  
% 2.09/1.28  Simplification rules
% 2.09/1.28  ----------------------
% 2.09/1.28  #Subsume      : 8
% 2.09/1.28  #Demod        : 42
% 2.09/1.28  #Tautology    : 48
% 2.09/1.28  #SimpNegUnit  : 0
% 2.09/1.28  #BackRed      : 0
% 2.09/1.28  
% 2.09/1.28  #Partial instantiations: 0
% 2.09/1.28  #Strategies tried      : 1
% 2.09/1.28  
% 2.09/1.28  Timing (in seconds)
% 2.09/1.28  ----------------------
% 2.09/1.29  Preprocessing        : 0.26
% 2.09/1.29  Parsing              : 0.15
% 2.09/1.29  CNF conversion       : 0.02
% 2.09/1.29  Main loop            : 0.24
% 2.09/1.29  Inferencing          : 0.10
% 2.09/1.29  Reduction            : 0.08
% 2.09/1.29  Demodulation         : 0.06
% 2.09/1.29  BG Simplification    : 0.01
% 2.09/1.29  Subsumption          : 0.05
% 2.09/1.29  Abstraction          : 0.01
% 2.09/1.29  MUC search           : 0.00
% 2.09/1.29  Cooper               : 0.00
% 2.09/1.29  Total                : 0.53
% 2.09/1.29  Index Insertion      : 0.00
% 2.09/1.29  Index Deletion       : 0.00
% 2.09/1.29  Index Matching       : 0.00
% 2.09/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
