%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:34 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   51 (  88 expanded)
%              Number of leaves         :   26 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :   85 ( 184 expanded)
%              Number of equality atoms :    8 (  20 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k7_subset_1(u1_struct_0(A),k2_struct_0(A),k7_subset_1(u1_struct_0(A),k2_struct_0(A),B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_pre_topc)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_52,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

tff(c_18,plain,(
    ~ m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_8,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_64,plain,(
    ! [A_31,B_32] :
      ( k7_subset_1(u1_struct_0(A_31),k2_struct_0(A_31),k7_subset_1(u1_struct_0(A_31),k2_struct_0(A_31),B_32)) = B_32
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [A_6] :
      ( m1_subset_1(k2_struct_0(A_6),k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_39,plain,(
    ! [A_25,B_26,C_27] :
      ( k7_subset_1(A_25,B_26,C_27) = k4_xboole_0(B_26,C_27)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    ! [A_6,C_27] :
      ( k7_subset_1(u1_struct_0(A_6),k2_struct_0(A_6),C_27) = k4_xboole_0(k2_struct_0(A_6),C_27)
      | ~ l1_struct_0(A_6) ) ),
    inference(resolution,[status(thm)],[c_6,c_39])).

tff(c_91,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(k2_struct_0(A_33),k7_subset_1(u1_struct_0(A_33),k2_struct_0(A_33),B_34)) = B_34
      | ~ l1_struct_0(A_33)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_struct_0(A_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_44])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_109,plain,(
    ! [B_35,A_36] :
      ( r1_tarski(B_35,k2_struct_0(A_36))
      | ~ l1_struct_0(A_36)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_struct_0(A_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_2])).

tff(c_117,plain,
    ( r1_tarski('#skF_2',k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_109])).

tff(c_125,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_128,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_125])).

tff(c_132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_128])).

tff(c_134,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_24,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_133,plain,(
    r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_12,plain,(
    ! [A_11] :
      ( k1_tops_1(A_11,k2_struct_0(A_11)) = k2_struct_0(A_11)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_118,plain,(
    ! [C_37,A_38,B_39] :
      ( m2_connsp_2(C_37,A_38,B_39)
      | ~ r1_tarski(B_39,k1_tops_1(A_38,C_37))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_223,plain,(
    ! [A_56,B_57] :
      ( m2_connsp_2(k2_struct_0(A_56),A_56,B_57)
      | ~ r1_tarski(B_57,k2_struct_0(A_56))
      | ~ m1_subset_1(k2_struct_0(A_56),k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_118])).

tff(c_227,plain,(
    ! [A_58,B_59] :
      ( m2_connsp_2(k2_struct_0(A_58),A_58,B_59)
      | ~ r1_tarski(B_59,k2_struct_0(A_58))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58)
      | ~ l1_struct_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_6,c_223])).

tff(c_231,plain,
    ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2')
    | ~ r1_tarski('#skF_2',k2_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_227])).

tff(c_235,plain,(
    m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_24,c_22,c_133,c_231])).

tff(c_237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_235])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:16:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.25  
% 2.19/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.25  %$ m2_connsp_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.19/1.25  
% 2.19/1.25  %Foreground sorts:
% 2.19/1.25  
% 2.19/1.25  
% 2.19/1.25  %Background operators:
% 2.19/1.25  
% 2.19/1.25  
% 2.19/1.25  %Foreground operators:
% 2.19/1.25  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.19/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.19/1.25  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.19/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.25  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.19/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.25  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.19/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.19/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.25  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.19/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.25  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.19/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.19/1.25  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.19/1.25  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 2.19/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.25  
% 2.19/1.27  tff(f_79, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_connsp_2)).
% 2.19/1.27  tff(f_39, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.19/1.27  tff(f_46, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k7_subset_1(u1_struct_0(A), k2_struct_0(A), k7_subset_1(u1_struct_0(A), k2_struct_0(A), B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_pre_topc)).
% 2.19/1.27  tff(f_35, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 2.19/1.27  tff(f_31, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.19/1.27  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.19/1.27  tff(f_52, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tops_1)).
% 2.19/1.27  tff(f_66, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 2.19/1.27  tff(c_18, plain, (~m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.19/1.27  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.19/1.27  tff(c_8, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.19/1.27  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.19/1.27  tff(c_64, plain, (![A_31, B_32]: (k7_subset_1(u1_struct_0(A_31), k2_struct_0(A_31), k7_subset_1(u1_struct_0(A_31), k2_struct_0(A_31), B_32))=B_32 | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.19/1.27  tff(c_6, plain, (![A_6]: (m1_subset_1(k2_struct_0(A_6), k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.19/1.27  tff(c_39, plain, (![A_25, B_26, C_27]: (k7_subset_1(A_25, B_26, C_27)=k4_xboole_0(B_26, C_27) | ~m1_subset_1(B_26, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.19/1.27  tff(c_44, plain, (![A_6, C_27]: (k7_subset_1(u1_struct_0(A_6), k2_struct_0(A_6), C_27)=k4_xboole_0(k2_struct_0(A_6), C_27) | ~l1_struct_0(A_6))), inference(resolution, [status(thm)], [c_6, c_39])).
% 2.19/1.27  tff(c_91, plain, (![A_33, B_34]: (k4_xboole_0(k2_struct_0(A_33), k7_subset_1(u1_struct_0(A_33), k2_struct_0(A_33), B_34))=B_34 | ~l1_struct_0(A_33) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_struct_0(A_33))), inference(superposition, [status(thm), theory('equality')], [c_64, c_44])).
% 2.19/1.27  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.19/1.27  tff(c_109, plain, (![B_35, A_36]: (r1_tarski(B_35, k2_struct_0(A_36)) | ~l1_struct_0(A_36) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_struct_0(A_36))), inference(superposition, [status(thm), theory('equality')], [c_91, c_2])).
% 2.19/1.27  tff(c_117, plain, (r1_tarski('#skF_2', k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_109])).
% 2.19/1.27  tff(c_125, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_117])).
% 2.19/1.27  tff(c_128, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_125])).
% 2.19/1.27  tff(c_132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_128])).
% 2.19/1.27  tff(c_134, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_117])).
% 2.19/1.27  tff(c_24, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.19/1.27  tff(c_133, plain, (r1_tarski('#skF_2', k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_117])).
% 2.19/1.27  tff(c_12, plain, (![A_11]: (k1_tops_1(A_11, k2_struct_0(A_11))=k2_struct_0(A_11) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.19/1.27  tff(c_118, plain, (![C_37, A_38, B_39]: (m2_connsp_2(C_37, A_38, B_39) | ~r1_tarski(B_39, k1_tops_1(A_38, C_37)) | ~m1_subset_1(C_37, k1_zfmisc_1(u1_struct_0(A_38))) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.19/1.27  tff(c_223, plain, (![A_56, B_57]: (m2_connsp_2(k2_struct_0(A_56), A_56, B_57) | ~r1_tarski(B_57, k2_struct_0(A_56)) | ~m1_subset_1(k2_struct_0(A_56), k1_zfmisc_1(u1_struct_0(A_56))) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56))), inference(superposition, [status(thm), theory('equality')], [c_12, c_118])).
% 2.19/1.27  tff(c_227, plain, (![A_58, B_59]: (m2_connsp_2(k2_struct_0(A_58), A_58, B_59) | ~r1_tarski(B_59, k2_struct_0(A_58)) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58) | ~l1_struct_0(A_58))), inference(resolution, [status(thm)], [c_6, c_223])).
% 2.19/1.27  tff(c_231, plain, (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', '#skF_2') | ~r1_tarski('#skF_2', k2_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_227])).
% 2.19/1.27  tff(c_235, plain, (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_24, c_22, c_133, c_231])).
% 2.19/1.27  tff(c_237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_235])).
% 2.19/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.27  
% 2.19/1.27  Inference rules
% 2.19/1.27  ----------------------
% 2.19/1.27  #Ref     : 0
% 2.19/1.27  #Sup     : 49
% 2.19/1.27  #Fact    : 0
% 2.19/1.27  #Define  : 0
% 2.19/1.27  #Split   : 3
% 2.19/1.27  #Chain   : 0
% 2.19/1.27  #Close   : 0
% 2.19/1.27  
% 2.19/1.27  Ordering : KBO
% 2.19/1.27  
% 2.19/1.27  Simplification rules
% 2.19/1.27  ----------------------
% 2.19/1.27  #Subsume      : 8
% 2.19/1.27  #Demod        : 8
% 2.19/1.27  #Tautology    : 21
% 2.19/1.27  #SimpNegUnit  : 1
% 2.19/1.27  #BackRed      : 0
% 2.19/1.27  
% 2.19/1.27  #Partial instantiations: 0
% 2.19/1.27  #Strategies tried      : 1
% 2.19/1.27  
% 2.19/1.27  Timing (in seconds)
% 2.19/1.27  ----------------------
% 2.19/1.27  Preprocessing        : 0.30
% 2.19/1.27  Parsing              : 0.16
% 2.19/1.27  CNF conversion       : 0.02
% 2.19/1.27  Main loop            : 0.21
% 2.19/1.27  Inferencing          : 0.09
% 2.19/1.27  Reduction            : 0.06
% 2.19/1.27  Demodulation         : 0.04
% 2.19/1.27  BG Simplification    : 0.01
% 2.19/1.27  Subsumption          : 0.03
% 2.19/1.27  Abstraction          : 0.01
% 2.19/1.27  MUC search           : 0.00
% 2.19/1.27  Cooper               : 0.00
% 2.19/1.27  Total                : 0.54
% 2.19/1.27  Index Insertion      : 0.00
% 2.19/1.27  Index Deletion       : 0.00
% 2.19/1.27  Index Matching       : 0.00
% 2.19/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
