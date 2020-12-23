%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:51 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   39 (  47 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   61 (  90 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v1_tops_2(B,A)
                 => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tops_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_31,axiom,(
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
                  & v1_tops_2(C,A) )
               => v1_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_24,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ m1_subset_1(A_24,k1_zfmisc_1(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_32,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_20,c_24])).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    v1_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(k4_xboole_0(A_1,C_3),B_2)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(k4_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ! [B_36,A_37,C_38] :
      ( v1_tops_2(B_36,A_37)
      | ~ v1_tops_2(C_38,A_37)
      | ~ r1_tarski(B_36,C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37))))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37))))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_129,plain,(
    ! [A_51,B_52,A_53] :
      ( v1_tops_2(k4_xboole_0(A_51,B_52),A_53)
      | ~ v1_tops_2(A_51,A_53)
      | ~ m1_subset_1(A_51,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_53))))
      | ~ m1_subset_1(k4_xboole_0(A_51,B_52),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_53))))
      | ~ l1_pre_topc(A_53) ) ),
    inference(resolution,[status(thm)],[c_4,c_68])).

tff(c_134,plain,(
    ! [A_54,B_55,A_56] :
      ( v1_tops_2(k4_xboole_0(A_54,B_55),A_56)
      | ~ v1_tops_2(A_54,A_56)
      | ~ m1_subset_1(A_54,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_56))))
      | ~ l1_pre_topc(A_56)
      | ~ r1_tarski(k4_xboole_0(A_54,B_55),k1_zfmisc_1(u1_struct_0(A_56))) ) ),
    inference(resolution,[status(thm)],[c_10,c_129])).

tff(c_145,plain,(
    ! [A_57,C_58,A_59] :
      ( v1_tops_2(k4_xboole_0(A_57,C_58),A_59)
      | ~ v1_tops_2(A_57,A_59)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_59))))
      | ~ l1_pre_topc(A_59)
      | ~ r1_tarski(A_57,k1_zfmisc_1(u1_struct_0(A_59))) ) ),
    inference(resolution,[status(thm)],[c_2,c_134])).

tff(c_152,plain,(
    ! [C_58] :
      ( v1_tops_2(k4_xboole_0('#skF_2',C_58),'#skF_1')
      | ~ v1_tops_2('#skF_2','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_20,c_145])).

tff(c_159,plain,(
    ! [C_58] : v1_tops_2(k4_xboole_0('#skF_2',C_58),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_22,c_16,c_152])).

tff(c_39,plain,(
    ! [A_31,B_32,C_33] :
      ( k7_subset_1(A_31,B_32,C_33) = k4_xboole_0(B_32,C_33)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_48,plain,(
    ! [C_33] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_33) = k4_xboole_0('#skF_2',C_33) ),
    inference(resolution,[status(thm)],[c_20,c_39])).

tff(c_14,plain,(
    ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_58,plain,(
    ~ v1_tops_2(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_14])).

tff(c_162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n024.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:21:51 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.22  
% 2.08/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.22  %$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.08/1.22  
% 2.08/1.22  %Foreground sorts:
% 2.08/1.22  
% 2.08/1.22  
% 2.08/1.22  %Background operators:
% 2.08/1.22  
% 2.08/1.22  
% 2.08/1.22  %Foreground operators:
% 2.08/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.08/1.22  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 2.08/1.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.08/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.22  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.08/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.08/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.08/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.08/1.22  
% 2.08/1.23  tff(f_66, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_tops_2)).
% 2.08/1.23  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.08/1.23  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 2.08/1.23  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.08/1.23  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v1_tops_2(C, A)) => v1_tops_2(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_tops_2)).
% 2.08/1.23  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.08/1.23  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.08/1.23  tff(c_24, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | ~m1_subset_1(A_24, k1_zfmisc_1(B_25)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.08/1.23  tff(c_32, plain, (r1_tarski('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_20, c_24])).
% 2.08/1.23  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.08/1.23  tff(c_16, plain, (v1_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.08/1.23  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(k4_xboole_0(A_1, C_3), B_2) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.08/1.23  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.08/1.23  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.08/1.23  tff(c_68, plain, (![B_36, A_37, C_38]: (v1_tops_2(B_36, A_37) | ~v1_tops_2(C_38, A_37) | ~r1_tarski(B_36, C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37)))) | ~m1_subset_1(B_36, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37)))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.08/1.23  tff(c_129, plain, (![A_51, B_52, A_53]: (v1_tops_2(k4_xboole_0(A_51, B_52), A_53) | ~v1_tops_2(A_51, A_53) | ~m1_subset_1(A_51, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_53)))) | ~m1_subset_1(k4_xboole_0(A_51, B_52), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_53)))) | ~l1_pre_topc(A_53))), inference(resolution, [status(thm)], [c_4, c_68])).
% 2.08/1.23  tff(c_134, plain, (![A_54, B_55, A_56]: (v1_tops_2(k4_xboole_0(A_54, B_55), A_56) | ~v1_tops_2(A_54, A_56) | ~m1_subset_1(A_54, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_56)))) | ~l1_pre_topc(A_56) | ~r1_tarski(k4_xboole_0(A_54, B_55), k1_zfmisc_1(u1_struct_0(A_56))))), inference(resolution, [status(thm)], [c_10, c_129])).
% 2.08/1.23  tff(c_145, plain, (![A_57, C_58, A_59]: (v1_tops_2(k4_xboole_0(A_57, C_58), A_59) | ~v1_tops_2(A_57, A_59) | ~m1_subset_1(A_57, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_59)))) | ~l1_pre_topc(A_59) | ~r1_tarski(A_57, k1_zfmisc_1(u1_struct_0(A_59))))), inference(resolution, [status(thm)], [c_2, c_134])).
% 2.08/1.23  tff(c_152, plain, (![C_58]: (v1_tops_2(k4_xboole_0('#skF_2', C_58), '#skF_1') | ~v1_tops_2('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~r1_tarski('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_20, c_145])).
% 2.08/1.23  tff(c_159, plain, (![C_58]: (v1_tops_2(k4_xboole_0('#skF_2', C_58), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_22, c_16, c_152])).
% 2.08/1.23  tff(c_39, plain, (![A_31, B_32, C_33]: (k7_subset_1(A_31, B_32, C_33)=k4_xboole_0(B_32, C_33) | ~m1_subset_1(B_32, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.08/1.23  tff(c_48, plain, (![C_33]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_33)=k4_xboole_0('#skF_2', C_33))), inference(resolution, [status(thm)], [c_20, c_39])).
% 2.08/1.23  tff(c_14, plain, (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.08/1.23  tff(c_58, plain, (~v1_tops_2(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_14])).
% 2.08/1.23  tff(c_162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_159, c_58])).
% 2.08/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.23  
% 2.08/1.23  Inference rules
% 2.08/1.23  ----------------------
% 2.08/1.23  #Ref     : 0
% 2.08/1.23  #Sup     : 31
% 2.08/1.23  #Fact    : 0
% 2.08/1.23  #Define  : 0
% 2.08/1.23  #Split   : 0
% 2.08/1.23  #Chain   : 0
% 2.08/1.23  #Close   : 0
% 2.08/1.23  
% 2.08/1.23  Ordering : KBO
% 2.08/1.23  
% 2.08/1.23  Simplification rules
% 2.08/1.23  ----------------------
% 2.08/1.23  #Subsume      : 0
% 2.08/1.23  #Demod        : 9
% 2.08/1.23  #Tautology    : 13
% 2.08/1.23  #SimpNegUnit  : 0
% 2.08/1.23  #BackRed      : 2
% 2.08/1.23  
% 2.08/1.23  #Partial instantiations: 0
% 2.08/1.23  #Strategies tried      : 1
% 2.08/1.23  
% 2.08/1.23  Timing (in seconds)
% 2.08/1.23  ----------------------
% 2.08/1.24  Preprocessing        : 0.30
% 2.08/1.24  Parsing              : 0.16
% 2.08/1.24  CNF conversion       : 0.02
% 2.08/1.24  Main loop            : 0.18
% 2.08/1.24  Inferencing          : 0.07
% 2.08/1.24  Reduction            : 0.05
% 2.08/1.24  Demodulation         : 0.04
% 2.08/1.24  BG Simplification    : 0.01
% 2.08/1.24  Subsumption          : 0.03
% 2.08/1.24  Abstraction          : 0.01
% 2.08/1.24  MUC search           : 0.00
% 2.08/1.24  Cooper               : 0.00
% 2.08/1.24  Total                : 0.50
% 2.08/1.24  Index Insertion      : 0.00
% 2.08/1.24  Index Deletion       : 0.00
% 2.08/1.24  Index Matching       : 0.00
% 2.08/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
