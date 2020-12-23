%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:48 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   42 (  50 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 (  85 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k8_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k8_subset_1,type,(
    k8_subset_1: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v1_tops_2(B,A)
                 => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_tops_2)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k8_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k8_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( ( r1_tarski(B,C)
                  & v1_tops_2(C,A) )
               => v1_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    v1_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_33,plain,(
    ! [A_29,B_30,C_31] :
      ( k8_subset_1(A_29,B_30,C_31) = k3_xboole_0(B_30,C_31)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_39,plain,(
    ! [C_31] : k8_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_31) = k3_xboole_0('#skF_2',C_31) ),
    inference(resolution,[status(thm)],[c_20,c_33])).

tff(c_58,plain,(
    ! [A_34,B_35,C_36] :
      ( m1_subset_1(k8_subset_1(A_34,B_35,C_36),k1_zfmisc_1(A_34))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_63,plain,(
    ! [C_31] :
      ( m1_subset_1(k3_xboole_0('#skF_2',C_31),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_58])).

tff(c_69,plain,(
    ! [C_31] : m1_subset_1(k3_xboole_0('#skF_2',C_31),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_63])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_106,plain,(
    ! [B_43,A_44,C_45] :
      ( v1_tops_2(B_43,A_44)
      | ~ v1_tops_2(C_45,A_44)
      | ~ r1_tarski(B_43,C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_44))))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_44))))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_306,plain,(
    ! [A_85,B_86,A_87] :
      ( v1_tops_2(k3_xboole_0(A_85,B_86),A_87)
      | ~ v1_tops_2(A_85,A_87)
      | ~ m1_subset_1(A_85,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_87))))
      | ~ m1_subset_1(k3_xboole_0(A_85,B_86),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_87))))
      | ~ l1_pre_topc(A_87) ) ),
    inference(resolution,[status(thm)],[c_2,c_106])).

tff(c_324,plain,(
    ! [C_31] :
      ( v1_tops_2(k3_xboole_0('#skF_2',C_31),'#skF_1')
      | ~ v1_tops_2('#skF_2','#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_69,c_306])).

tff(c_342,plain,(
    ! [C_31] : v1_tops_2(k3_xboole_0('#skF_2',C_31),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_16,c_324])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_80,plain,(
    ! [A_39,B_40,C_41] :
      ( k9_subset_1(A_39,B_40,C_41) = k3_xboole_0(B_40,C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_94,plain,(
    ! [B_40] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_40,'#skF_3') = k3_xboole_0(B_40,'#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_80])).

tff(c_14,plain,(
    ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_96,plain,(
    ~ v1_tops_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_14])).

tff(c_345,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_96])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:57:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.27  
% 2.37/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.27  %$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k8_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.37/1.27  
% 2.37/1.27  %Foreground sorts:
% 2.37/1.27  
% 2.37/1.27  
% 2.37/1.27  %Background operators:
% 2.37/1.27  
% 2.37/1.27  
% 2.37/1.27  %Foreground operators:
% 2.37/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.27  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 2.37/1.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.37/1.27  tff(k8_subset_1, type, k8_subset_1: ($i * $i * $i) > $i).
% 2.37/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.37/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.37/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.37/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.37/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.37/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.37/1.27  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.37/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.37/1.27  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.37/1.27  
% 2.37/1.28  tff(f_68, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_tops_2)).
% 2.37/1.28  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_subset_1)).
% 2.37/1.28  tff(f_31, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k8_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_subset_1)).
% 2.37/1.28  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.37/1.28  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v1_tops_2(C, A)) => v1_tops_2(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_tops_2)).
% 2.37/1.28  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.37/1.28  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.37/1.28  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.37/1.28  tff(c_16, plain, (v1_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.37/1.28  tff(c_33, plain, (![A_29, B_30, C_31]: (k8_subset_1(A_29, B_30, C_31)=k3_xboole_0(B_30, C_31) | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.37/1.28  tff(c_39, plain, (![C_31]: (k8_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_31)=k3_xboole_0('#skF_2', C_31))), inference(resolution, [status(thm)], [c_20, c_33])).
% 2.37/1.28  tff(c_58, plain, (![A_34, B_35, C_36]: (m1_subset_1(k8_subset_1(A_34, B_35, C_36), k1_zfmisc_1(A_34)) | ~m1_subset_1(B_35, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.37/1.28  tff(c_63, plain, (![C_31]: (m1_subset_1(k3_xboole_0('#skF_2', C_31), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_39, c_58])).
% 2.37/1.28  tff(c_69, plain, (![C_31]: (m1_subset_1(k3_xboole_0('#skF_2', C_31), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_63])).
% 2.37/1.28  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.37/1.28  tff(c_106, plain, (![B_43, A_44, C_45]: (v1_tops_2(B_43, A_44) | ~v1_tops_2(C_45, A_44) | ~r1_tarski(B_43, C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_44)))) | ~m1_subset_1(B_43, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_44)))) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.37/1.28  tff(c_306, plain, (![A_85, B_86, A_87]: (v1_tops_2(k3_xboole_0(A_85, B_86), A_87) | ~v1_tops_2(A_85, A_87) | ~m1_subset_1(A_85, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_87)))) | ~m1_subset_1(k3_xboole_0(A_85, B_86), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_87)))) | ~l1_pre_topc(A_87))), inference(resolution, [status(thm)], [c_2, c_106])).
% 2.37/1.28  tff(c_324, plain, (![C_31]: (v1_tops_2(k3_xboole_0('#skF_2', C_31), '#skF_1') | ~v1_tops_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_69, c_306])).
% 2.37/1.28  tff(c_342, plain, (![C_31]: (v1_tops_2(k3_xboole_0('#skF_2', C_31), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_16, c_324])).
% 2.37/1.28  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.37/1.28  tff(c_80, plain, (![A_39, B_40, C_41]: (k9_subset_1(A_39, B_40, C_41)=k3_xboole_0(B_40, C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.37/1.28  tff(c_94, plain, (![B_40]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_40, '#skF_3')=k3_xboole_0(B_40, '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_80])).
% 2.37/1.28  tff(c_14, plain, (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.37/1.28  tff(c_96, plain, (~v1_tops_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_14])).
% 2.37/1.28  tff(c_345, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_342, c_96])).
% 2.37/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.28  
% 2.37/1.28  Inference rules
% 2.37/1.28  ----------------------
% 2.37/1.28  #Ref     : 0
% 2.37/1.28  #Sup     : 75
% 2.37/1.28  #Fact    : 0
% 2.37/1.28  #Define  : 0
% 2.37/1.28  #Split   : 0
% 2.37/1.28  #Chain   : 0
% 2.37/1.28  #Close   : 0
% 2.37/1.28  
% 2.37/1.28  Ordering : KBO
% 2.37/1.28  
% 2.37/1.28  Simplification rules
% 2.37/1.28  ----------------------
% 2.37/1.28  #Subsume      : 0
% 2.37/1.28  #Demod        : 44
% 2.37/1.28  #Tautology    : 33
% 2.37/1.28  #SimpNegUnit  : 0
% 2.37/1.28  #BackRed      : 2
% 2.37/1.28  
% 2.37/1.28  #Partial instantiations: 0
% 2.37/1.28  #Strategies tried      : 1
% 2.37/1.28  
% 2.37/1.28  Timing (in seconds)
% 2.37/1.28  ----------------------
% 2.37/1.28  Preprocessing        : 0.29
% 2.37/1.28  Parsing              : 0.16
% 2.37/1.28  CNF conversion       : 0.02
% 2.37/1.28  Main loop            : 0.24
% 2.37/1.28  Inferencing          : 0.10
% 2.37/1.28  Reduction            : 0.08
% 2.37/1.28  Demodulation         : 0.06
% 2.37/1.28  BG Simplification    : 0.01
% 2.37/1.28  Subsumption          : 0.03
% 2.37/1.28  Abstraction          : 0.02
% 2.37/1.28  MUC search           : 0.00
% 2.37/1.29  Cooper               : 0.00
% 2.37/1.29  Total                : 0.56
% 2.37/1.29  Index Insertion      : 0.00
% 2.37/1.29  Index Deletion       : 0.00
% 2.37/1.29  Index Matching       : 0.00
% 2.37/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
