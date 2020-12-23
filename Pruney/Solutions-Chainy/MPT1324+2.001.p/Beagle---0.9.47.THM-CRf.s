%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:07 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :   43 (  62 expanded)
%              Number of leaves         :   20 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :   63 ( 117 expanded)
%              Number of equality atoms :    7 (  13 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k1_tops_2 > k5_setfam_1 > k2_xboole_0 > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

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

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff(k1_tops_2,type,(
    k1_tops_2: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_58,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( r1_tarski(B,k5_setfam_1(u1_struct_0(k1_pre_topc(A,B)),k1_tops_2(A,B,C)))
                 => r1_tarski(B,k5_setfam_1(u1_struct_0(A),C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_tops_2)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A,B)),k1_tops_2(A,B,C)),k5_setfam_1(u1_struct_0(A),C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_10,plain,(
    ~ r1_tarski('#skF_2',k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_18,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_333,plain,(
    ! [A_45,B_46,C_47] :
      ( r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A_45,B_46)),k1_tops_2(A_45,B_46,C_47)),k5_setfam_1(u1_struct_0(A_45),C_47))
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_45))))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_338,plain,(
    ! [A_45,B_46,C_47] :
      ( k2_xboole_0(k5_setfam_1(u1_struct_0(k1_pre_topc(A_45,B_46)),k1_tops_2(A_45,B_46,C_47)),k5_setfam_1(u1_struct_0(A_45),C_47)) = k5_setfam_1(u1_struct_0(A_45),C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_45))))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(resolution,[status(thm)],[c_333,c_6])).

tff(c_795,plain,(
    ! [A_62,C_63,B_64] :
      ( k2_xboole_0(k5_setfam_1(u1_struct_0(A_62),C_63),k5_setfam_1(u1_struct_0(k1_pre_topc(A_62,B_64)),k1_tops_2(A_62,B_64,C_63))) = k5_setfam_1(u1_struct_0(A_62),C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_62))))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_338])).

tff(c_16,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [A_8,B_12,C_14] :
      ( r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A_8,B_12)),k1_tops_2(A_8,B_12,C_14)),k5_setfam_1(u1_struct_0(A_8),C_14))
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_8))))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    r1_tarski('#skF_2',k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),k1_tops_2('#skF_1','#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_53,plain,(
    ! [A_23,C_24,B_25] :
      ( r1_tarski(A_23,k2_xboole_0(C_24,B_25))
      | ~ r1_tarski(A_23,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_79,plain,(
    ! [A_29,C_30,B_31] :
      ( k2_xboole_0(A_29,k2_xboole_0(C_30,B_31)) = k2_xboole_0(C_30,B_31)
      | ~ r1_tarski(A_29,B_31) ) ),
    inference(resolution,[status(thm)],[c_53,c_6])).

tff(c_59,plain,(
    ! [A_23,B_2,A_1] :
      ( r1_tarski(A_23,k2_xboole_0(B_2,A_1))
      | ~ r1_tarski(A_23,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_53])).

tff(c_175,plain,(
    ! [A_35,C_36,B_37,A_38] :
      ( r1_tarski(A_35,k2_xboole_0(C_36,B_37))
      | ~ r1_tarski(A_35,A_38)
      | ~ r1_tarski(A_38,B_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_59])).

tff(c_342,plain,(
    ! [C_48,B_49] :
      ( r1_tarski('#skF_2',k2_xboole_0(C_48,B_49))
      | ~ r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),k1_tops_2('#skF_1','#skF_2','#skF_3')),B_49) ) ),
    inference(resolution,[status(thm)],[c_12,c_175])).

tff(c_345,plain,(
    ! [C_48] :
      ( r1_tarski('#skF_2',k2_xboole_0(C_48,k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_8,c_342])).

tff(c_357,plain,(
    ! [C_50] : r1_tarski('#skF_2',k2_xboole_0(C_50,k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_14,c_345])).

tff(c_370,plain,(
    ! [A_1] : r1_tarski('#skF_2',k2_xboole_0(k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3'),A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_357])).

tff(c_811,plain,(
    ! [B_64] :
      ( r1_tarski('#skF_2',k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_795,c_370])).

tff(c_837,plain,(
    ! [B_64] :
      ( r1_tarski('#skF_2',k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3'))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_14,c_811])).

tff(c_838,plain,(
    ! [B_64] : ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_837])).

tff(c_842,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_838,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:17:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.43  
% 2.93/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.43  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k1_tops_2 > k5_setfam_1 > k2_xboole_0 > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.93/1.43  
% 2.93/1.43  %Foreground sorts:
% 2.93/1.43  
% 2.93/1.43  
% 2.93/1.43  %Background operators:
% 2.93/1.43  
% 2.93/1.43  
% 2.93/1.43  %Foreground operators:
% 2.93/1.43  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 2.93/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.93/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.93/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.93/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.93/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.93/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.93/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.93/1.43  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.93/1.43  tff(k1_tops_2, type, k1_tops_2: ($i * $i * $i) > $i).
% 2.93/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.93/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.93/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.93/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.93/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.93/1.43  
% 2.93/1.45  tff(f_58, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, k5_setfam_1(u1_struct_0(k1_pre_topc(A, B)), k1_tops_2(A, B, C))) => r1_tarski(B, k5_setfam_1(u1_struct_0(A), C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_tops_2)).
% 2.93/1.45  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.93/1.45  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A, B)), k1_tops_2(A, B, C)), k5_setfam_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_2)).
% 2.93/1.45  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.93/1.45  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.93/1.45  tff(c_10, plain, (~r1_tarski('#skF_2', k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.93/1.45  tff(c_18, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.93/1.45  tff(c_14, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.93/1.45  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.93/1.45  tff(c_333, plain, (![A_45, B_46, C_47]: (r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A_45, B_46)), k1_tops_2(A_45, B_46, C_47)), k5_setfam_1(u1_struct_0(A_45), C_47)) | ~m1_subset_1(C_47, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_45)))) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.93/1.45  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.93/1.45  tff(c_338, plain, (![A_45, B_46, C_47]: (k2_xboole_0(k5_setfam_1(u1_struct_0(k1_pre_topc(A_45, B_46)), k1_tops_2(A_45, B_46, C_47)), k5_setfam_1(u1_struct_0(A_45), C_47))=k5_setfam_1(u1_struct_0(A_45), C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_45)))) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45))), inference(resolution, [status(thm)], [c_333, c_6])).
% 2.93/1.45  tff(c_795, plain, (![A_62, C_63, B_64]: (k2_xboole_0(k5_setfam_1(u1_struct_0(A_62), C_63), k5_setfam_1(u1_struct_0(k1_pre_topc(A_62, B_64)), k1_tops_2(A_62, B_64, C_63)))=k5_setfam_1(u1_struct_0(A_62), C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_62)))) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_338])).
% 2.93/1.45  tff(c_16, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.93/1.45  tff(c_8, plain, (![A_8, B_12, C_14]: (r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A_8, B_12)), k1_tops_2(A_8, B_12, C_14)), k5_setfam_1(u1_struct_0(A_8), C_14)) | ~m1_subset_1(C_14, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_8)))) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.93/1.45  tff(c_12, plain, (r1_tarski('#skF_2', k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), k1_tops_2('#skF_1', '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.93/1.45  tff(c_53, plain, (![A_23, C_24, B_25]: (r1_tarski(A_23, k2_xboole_0(C_24, B_25)) | ~r1_tarski(A_23, B_25))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.93/1.45  tff(c_79, plain, (![A_29, C_30, B_31]: (k2_xboole_0(A_29, k2_xboole_0(C_30, B_31))=k2_xboole_0(C_30, B_31) | ~r1_tarski(A_29, B_31))), inference(resolution, [status(thm)], [c_53, c_6])).
% 2.93/1.45  tff(c_59, plain, (![A_23, B_2, A_1]: (r1_tarski(A_23, k2_xboole_0(B_2, A_1)) | ~r1_tarski(A_23, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_53])).
% 2.93/1.45  tff(c_175, plain, (![A_35, C_36, B_37, A_38]: (r1_tarski(A_35, k2_xboole_0(C_36, B_37)) | ~r1_tarski(A_35, A_38) | ~r1_tarski(A_38, B_37))), inference(superposition, [status(thm), theory('equality')], [c_79, c_59])).
% 2.93/1.45  tff(c_342, plain, (![C_48, B_49]: (r1_tarski('#skF_2', k2_xboole_0(C_48, B_49)) | ~r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), k1_tops_2('#skF_1', '#skF_2', '#skF_3')), B_49))), inference(resolution, [status(thm)], [c_12, c_175])).
% 2.93/1.45  tff(c_345, plain, (![C_48]: (r1_tarski('#skF_2', k2_xboole_0(C_48, k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_342])).
% 2.93/1.45  tff(c_357, plain, (![C_50]: (r1_tarski('#skF_2', k2_xboole_0(C_50, k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_14, c_345])).
% 2.93/1.45  tff(c_370, plain, (![A_1]: (r1_tarski('#skF_2', k2_xboole_0(k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3'), A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_357])).
% 2.93/1.45  tff(c_811, plain, (![B_64]: (r1_tarski('#skF_2', k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_795, c_370])).
% 2.93/1.45  tff(c_837, plain, (![B_64]: (r1_tarski('#skF_2', k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_14, c_811])).
% 2.93/1.45  tff(c_838, plain, (![B_64]: (~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_10, c_837])).
% 2.93/1.45  tff(c_842, plain, $false, inference(negUnitSimplification, [status(thm)], [c_838, c_16])).
% 2.93/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.45  
% 2.93/1.45  Inference rules
% 2.93/1.45  ----------------------
% 2.93/1.45  #Ref     : 0
% 2.93/1.45  #Sup     : 232
% 2.93/1.45  #Fact    : 0
% 2.93/1.45  #Define  : 0
% 2.93/1.45  #Split   : 0
% 2.93/1.45  #Chain   : 0
% 2.93/1.45  #Close   : 0
% 2.93/1.45  
% 2.93/1.45  Ordering : KBO
% 2.93/1.45  
% 2.93/1.45  Simplification rules
% 2.93/1.45  ----------------------
% 2.93/1.45  #Subsume      : 48
% 2.93/1.45  #Demod        : 22
% 2.93/1.45  #Tautology    : 41
% 2.93/1.45  #SimpNegUnit  : 2
% 2.93/1.45  #BackRed      : 1
% 2.93/1.45  
% 2.93/1.45  #Partial instantiations: 0
% 2.93/1.45  #Strategies tried      : 1
% 2.93/1.45  
% 2.93/1.45  Timing (in seconds)
% 2.93/1.45  ----------------------
% 2.93/1.45  Preprocessing        : 0.26
% 2.93/1.45  Parsing              : 0.15
% 2.93/1.45  CNF conversion       : 0.02
% 2.93/1.45  Main loop            : 0.40
% 2.93/1.45  Inferencing          : 0.14
% 2.93/1.45  Reduction            : 0.14
% 2.93/1.45  Demodulation         : 0.11
% 2.93/1.45  BG Simplification    : 0.02
% 2.93/1.45  Subsumption          : 0.07
% 2.93/1.45  Abstraction          : 0.02
% 2.93/1.45  MUC search           : 0.00
% 2.93/1.45  Cooper               : 0.00
% 2.93/1.45  Total                : 0.68
% 2.93/1.45  Index Insertion      : 0.00
% 2.93/1.45  Index Deletion       : 0.00
% 2.93/1.45  Index Matching       : 0.00
% 2.93/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
