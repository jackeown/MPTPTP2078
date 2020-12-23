%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:05 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   47 (  61 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   44 (  80 expanded)
%              Number of equality atoms :   15 (  20 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_61,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => m1_subset_1(k9_subset_1(u1_struct_0(A),B,C),k1_zfmisc_1(u1_struct_0(k1_pre_topc(A,C)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_tops_2)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(c_53,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k4_xboole_0(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_62,plain,(
    ! [A_30,B_31] : r1_tarski(k3_xboole_0(A_30,B_31),A_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_2])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_89,plain,(
    ! [A_36,B_37,C_38] :
      ( k9_subset_1(A_36,B_37,C_38) = k3_xboole_0(B_37,C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_97,plain,(
    ! [B_37] : k9_subset_1(u1_struct_0('#skF_1'),B_37,'#skF_3') = k3_xboole_0(B_37,'#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_89])).

tff(c_191,plain,(
    ! [A_52,C_53,B_54] :
      ( k9_subset_1(A_52,C_53,B_54) = k9_subset_1(A_52,B_54,C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_195,plain,(
    ! [B_54] : k9_subset_1(u1_struct_0('#skF_1'),B_54,'#skF_3') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_54) ),
    inference(resolution,[status(thm)],[c_20,c_191])).

tff(c_214,plain,(
    ! [B_55] : k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_55) = k3_xboole_0(B_55,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_195])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_98,plain,(
    ! [B_37] : k9_subset_1(u1_struct_0('#skF_1'),B_37,'#skF_2') = k3_xboole_0(B_37,'#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_89])).

tff(c_229,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_98])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_164,plain,(
    ! [A_50,B_51] :
      ( u1_struct_0(k1_pre_topc(A_50,B_51)) = B_51
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_171,plain,
    ( u1_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_164])).

tff(c_178,plain,(
    u1_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_171])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ~ m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_52,plain,(
    ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),u1_struct_0(k1_pre_topc('#skF_1','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_14,c_18])).

tff(c_99,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),u1_struct_0(k1_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_52])).

tff(c_183,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_99])).

tff(c_258,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_183])).

tff(c_261,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_258])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:08:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.23  
% 2.11/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.23  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.23/1.23  
% 2.23/1.23  %Foreground sorts:
% 2.23/1.23  
% 2.23/1.23  
% 2.23/1.23  %Background operators:
% 2.23/1.23  
% 2.23/1.23  
% 2.23/1.23  %Foreground operators:
% 2.23/1.23  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 2.23/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.23/1.23  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.23/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.23/1.23  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.23/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.23/1.23  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.23/1.23  
% 2.23/1.25  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.23/1.25  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.23/1.25  tff(f_61, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => m1_subset_1(k9_subset_1(u1_struct_0(A), B, C), k1_zfmisc_1(u1_struct_0(k1_pre_topc(A, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_tops_2)).
% 2.23/1.25  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.23/1.25  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 2.23/1.25  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 2.23/1.25  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.23/1.25  tff(c_53, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k4_xboole_0(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.25  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.23/1.25  tff(c_62, plain, (![A_30, B_31]: (r1_tarski(k3_xboole_0(A_30, B_31), A_30))), inference(superposition, [status(thm), theory('equality')], [c_53, c_2])).
% 2.23/1.25  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.23/1.25  tff(c_89, plain, (![A_36, B_37, C_38]: (k9_subset_1(A_36, B_37, C_38)=k3_xboole_0(B_37, C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.23/1.25  tff(c_97, plain, (![B_37]: (k9_subset_1(u1_struct_0('#skF_1'), B_37, '#skF_3')=k3_xboole_0(B_37, '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_89])).
% 2.23/1.25  tff(c_191, plain, (![A_52, C_53, B_54]: (k9_subset_1(A_52, C_53, B_54)=k9_subset_1(A_52, B_54, C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.23/1.25  tff(c_195, plain, (![B_54]: (k9_subset_1(u1_struct_0('#skF_1'), B_54, '#skF_3')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_54))), inference(resolution, [status(thm)], [c_20, c_191])).
% 2.23/1.25  tff(c_214, plain, (![B_55]: (k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_55)=k3_xboole_0(B_55, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_195])).
% 2.23/1.25  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.23/1.25  tff(c_98, plain, (![B_37]: (k9_subset_1(u1_struct_0('#skF_1'), B_37, '#skF_2')=k3_xboole_0(B_37, '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_89])).
% 2.23/1.25  tff(c_229, plain, (k3_xboole_0('#skF_2', '#skF_3')=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_214, c_98])).
% 2.23/1.25  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.23/1.25  tff(c_164, plain, (![A_50, B_51]: (u1_struct_0(k1_pre_topc(A_50, B_51))=B_51 | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.23/1.25  tff(c_171, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_164])).
% 2.23/1.25  tff(c_178, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_171])).
% 2.23/1.25  tff(c_14, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.23/1.25  tff(c_18, plain, (~m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.23/1.25  tff(c_52, plain, (~r1_tarski(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_14, c_18])).
% 2.23/1.25  tff(c_99, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_52])).
% 2.23/1.25  tff(c_183, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_178, c_99])).
% 2.23/1.25  tff(c_258, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_229, c_183])).
% 2.23/1.25  tff(c_261, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_258])).
% 2.23/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.25  
% 2.23/1.25  Inference rules
% 2.23/1.25  ----------------------
% 2.23/1.25  #Ref     : 0
% 2.23/1.25  #Sup     : 56
% 2.23/1.25  #Fact    : 0
% 2.23/1.25  #Define  : 0
% 2.23/1.25  #Split   : 0
% 2.23/1.25  #Chain   : 0
% 2.23/1.25  #Close   : 0
% 2.23/1.25  
% 2.23/1.25  Ordering : KBO
% 2.23/1.25  
% 2.23/1.25  Simplification rules
% 2.23/1.25  ----------------------
% 2.23/1.25  #Subsume      : 2
% 2.23/1.25  #Demod        : 19
% 2.23/1.25  #Tautology    : 29
% 2.23/1.25  #SimpNegUnit  : 0
% 2.23/1.25  #BackRed      : 6
% 2.23/1.25  
% 2.23/1.25  #Partial instantiations: 0
% 2.23/1.25  #Strategies tried      : 1
% 2.23/1.25  
% 2.23/1.25  Timing (in seconds)
% 2.23/1.25  ----------------------
% 2.23/1.25  Preprocessing        : 0.29
% 2.23/1.25  Parsing              : 0.16
% 2.23/1.25  CNF conversion       : 0.02
% 2.23/1.25  Main loop            : 0.18
% 2.23/1.25  Inferencing          : 0.07
% 2.23/1.25  Reduction            : 0.06
% 2.23/1.25  Demodulation         : 0.04
% 2.23/1.25  BG Simplification    : 0.01
% 2.23/1.25  Subsumption          : 0.02
% 2.23/1.25  Abstraction          : 0.01
% 2.23/1.25  MUC search           : 0.00
% 2.23/1.25  Cooper               : 0.00
% 2.23/1.25  Total                : 0.50
% 2.23/1.25  Index Insertion      : 0.00
% 2.23/1.25  Index Deletion       : 0.00
% 2.23/1.25  Index Matching       : 0.00
% 2.23/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
