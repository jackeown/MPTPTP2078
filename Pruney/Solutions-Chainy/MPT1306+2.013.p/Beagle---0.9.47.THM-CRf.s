%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:53 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :   46 (  58 expanded)
%              Number of leaves         :   23 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   66 ( 104 expanded)
%              Number of equality atoms :    6 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

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

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v2_tops_2(B,A)
                 => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tops_2)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( ( r1_tarski(B,C)
                  & v2_tops_2(C,A) )
               => v2_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tops_2)).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_70,plain,(
    ! [A_37,B_38,C_39] :
      ( k9_subset_1(A_37,B_38,C_39) = k3_xboole_0(B_38,C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_78,plain,(
    ! [B_38] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_38,'#skF_3') = k3_xboole_0(B_38,'#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_70])).

tff(c_14,plain,(
    ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_80,plain,(
    ~ v2_tops_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_14])).

tff(c_16,plain,(
    v2_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_81,plain,(
    ! [B_40] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_40,'#skF_3') = k3_xboole_0(B_40,'#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_70])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( m1_subset_1(k9_subset_1(A_5,B_6,C_7),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(C_7,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_87,plain,(
    ! [B_40] :
      ( m1_subset_1(k3_xboole_0(B_40,'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_6])).

tff(c_93,plain,(
    ! [B_40] : m1_subset_1(k3_xboole_0(B_40,'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_87])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_95,plain,(
    ! [B_41,A_42,C_43] :
      ( v2_tops_2(B_41,A_42)
      | ~ v2_tops_2(C_43,A_42)
      | ~ r1_tarski(B_41,C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_42))))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_42))))
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_352,plain,(
    ! [A_77,B_78,A_79] :
      ( v2_tops_2(k4_xboole_0(A_77,B_78),A_79)
      | ~ v2_tops_2(A_77,A_79)
      | ~ m1_subset_1(A_77,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_79))))
      | ~ m1_subset_1(k4_xboole_0(A_77,B_78),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_79))))
      | ~ l1_pre_topc(A_79) ) ),
    inference(resolution,[status(thm)],[c_2,c_95])).

tff(c_367,plain,(
    ! [A_3,B_4,A_79] :
      ( v2_tops_2(k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)),A_79)
      | ~ v2_tops_2(A_3,A_79)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_79))))
      | ~ m1_subset_1(k3_xboole_0(A_3,B_4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_79))))
      | ~ l1_pre_topc(A_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_352])).

tff(c_692,plain,(
    ! [A_117,B_118,A_119] :
      ( v2_tops_2(k3_xboole_0(A_117,B_118),A_119)
      | ~ v2_tops_2(A_117,A_119)
      | ~ m1_subset_1(A_117,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_119))))
      | ~ m1_subset_1(k3_xboole_0(A_117,B_118),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_119))))
      | ~ l1_pre_topc(A_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_367])).

tff(c_719,plain,(
    ! [B_40] :
      ( v2_tops_2(k3_xboole_0(B_40,'#skF_3'),'#skF_1')
      | ~ v2_tops_2(B_40,'#skF_1')
      | ~ m1_subset_1(B_40,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_93,c_692])).

tff(c_802,plain,(
    ! [B_123] :
      ( v2_tops_2(k3_xboole_0(B_123,'#skF_3'),'#skF_1')
      | ~ v2_tops_2(B_123,'#skF_1')
      | ~ m1_subset_1(B_123,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_719])).

tff(c_839,plain,
    ( v2_tops_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v2_tops_2('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_802])).

tff(c_853,plain,(
    v2_tops_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_839])).

tff(c_855,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_853])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:47:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.42  
% 2.98/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.42  %$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.98/1.42  
% 2.98/1.42  %Foreground sorts:
% 2.98/1.42  
% 2.98/1.42  
% 2.98/1.42  %Background operators:
% 2.98/1.42  
% 2.98/1.42  
% 2.98/1.42  %Foreground operators:
% 2.98/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.98/1.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.98/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.98/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.98/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.98/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.98/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.98/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.98/1.42  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 2.98/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.98/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.98/1.42  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.98/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.98/1.42  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.98/1.42  
% 2.98/1.43  tff(f_66, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tops_2)).
% 2.98/1.43  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.98/1.43  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 2.98/1.43  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.98/1.43  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.98/1.43  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v2_tops_2(C, A)) => v2_tops_2(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tops_2)).
% 2.98/1.43  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.98/1.43  tff(c_70, plain, (![A_37, B_38, C_39]: (k9_subset_1(A_37, B_38, C_39)=k3_xboole_0(B_38, C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.98/1.43  tff(c_78, plain, (![B_38]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_38, '#skF_3')=k3_xboole_0(B_38, '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_70])).
% 2.98/1.43  tff(c_14, plain, (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.98/1.43  tff(c_80, plain, (~v2_tops_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_14])).
% 2.98/1.43  tff(c_16, plain, (v2_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.98/1.43  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.98/1.43  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.98/1.43  tff(c_81, plain, (![B_40]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_40, '#skF_3')=k3_xboole_0(B_40, '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_70])).
% 2.98/1.43  tff(c_6, plain, (![A_5, B_6, C_7]: (m1_subset_1(k9_subset_1(A_5, B_6, C_7), k1_zfmisc_1(A_5)) | ~m1_subset_1(C_7, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.98/1.43  tff(c_87, plain, (![B_40]: (m1_subset_1(k3_xboole_0(B_40, '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_81, c_6])).
% 2.98/1.43  tff(c_93, plain, (![B_40]: (m1_subset_1(k3_xboole_0(B_40, '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_87])).
% 2.98/1.43  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.98/1.43  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.98/1.43  tff(c_95, plain, (![B_41, A_42, C_43]: (v2_tops_2(B_41, A_42) | ~v2_tops_2(C_43, A_42) | ~r1_tarski(B_41, C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_42)))) | ~m1_subset_1(B_41, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_42)))) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.98/1.43  tff(c_352, plain, (![A_77, B_78, A_79]: (v2_tops_2(k4_xboole_0(A_77, B_78), A_79) | ~v2_tops_2(A_77, A_79) | ~m1_subset_1(A_77, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_79)))) | ~m1_subset_1(k4_xboole_0(A_77, B_78), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_79)))) | ~l1_pre_topc(A_79))), inference(resolution, [status(thm)], [c_2, c_95])).
% 2.98/1.43  tff(c_367, plain, (![A_3, B_4, A_79]: (v2_tops_2(k4_xboole_0(A_3, k4_xboole_0(A_3, B_4)), A_79) | ~v2_tops_2(A_3, A_79) | ~m1_subset_1(A_3, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_79)))) | ~m1_subset_1(k3_xboole_0(A_3, B_4), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_79)))) | ~l1_pre_topc(A_79))), inference(superposition, [status(thm), theory('equality')], [c_4, c_352])).
% 2.98/1.43  tff(c_692, plain, (![A_117, B_118, A_119]: (v2_tops_2(k3_xboole_0(A_117, B_118), A_119) | ~v2_tops_2(A_117, A_119) | ~m1_subset_1(A_117, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_119)))) | ~m1_subset_1(k3_xboole_0(A_117, B_118), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_119)))) | ~l1_pre_topc(A_119))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_367])).
% 2.98/1.43  tff(c_719, plain, (![B_40]: (v2_tops_2(k3_xboole_0(B_40, '#skF_3'), '#skF_1') | ~v2_tops_2(B_40, '#skF_1') | ~m1_subset_1(B_40, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_93, c_692])).
% 2.98/1.43  tff(c_802, plain, (![B_123]: (v2_tops_2(k3_xboole_0(B_123, '#skF_3'), '#skF_1') | ~v2_tops_2(B_123, '#skF_1') | ~m1_subset_1(B_123, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_719])).
% 2.98/1.43  tff(c_839, plain, (v2_tops_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v2_tops_2('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_20, c_802])).
% 2.98/1.43  tff(c_853, plain, (v2_tops_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_839])).
% 2.98/1.43  tff(c_855, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_853])).
% 2.98/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.43  
% 2.98/1.43  Inference rules
% 2.98/1.43  ----------------------
% 2.98/1.43  #Ref     : 0
% 2.98/1.43  #Sup     : 196
% 2.98/1.43  #Fact    : 0
% 2.98/1.43  #Define  : 0
% 2.98/1.43  #Split   : 1
% 2.98/1.43  #Chain   : 0
% 2.98/1.43  #Close   : 0
% 2.98/1.43  
% 2.98/1.43  Ordering : KBO
% 2.98/1.43  
% 2.98/1.43  Simplification rules
% 2.98/1.43  ----------------------
% 2.98/1.43  #Subsume      : 1
% 2.98/1.43  #Demod        : 145
% 2.98/1.43  #Tautology    : 88
% 2.98/1.43  #SimpNegUnit  : 1
% 2.98/1.43  #BackRed      : 1
% 2.98/1.43  
% 2.98/1.43  #Partial instantiations: 0
% 2.98/1.43  #Strategies tried      : 1
% 2.98/1.43  
% 2.98/1.43  Timing (in seconds)
% 2.98/1.43  ----------------------
% 2.98/1.43  Preprocessing        : 0.28
% 2.98/1.43  Parsing              : 0.15
% 2.98/1.43  CNF conversion       : 0.02
% 2.98/1.43  Main loop            : 0.39
% 2.98/1.43  Inferencing          : 0.15
% 2.98/1.43  Reduction            : 0.14
% 2.98/1.43  Demodulation         : 0.11
% 2.98/1.43  BG Simplification    : 0.02
% 2.98/1.43  Subsumption          : 0.06
% 2.98/1.43  Abstraction          : 0.03
% 2.98/1.43  MUC search           : 0.00
% 2.98/1.44  Cooper               : 0.00
% 2.98/1.44  Total                : 0.70
% 2.98/1.44  Index Insertion      : 0.00
% 2.98/1.44  Index Deletion       : 0.00
% 2.98/1.44  Index Matching       : 0.00
% 2.98/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
