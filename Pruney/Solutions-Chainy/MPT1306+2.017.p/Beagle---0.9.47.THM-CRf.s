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
% DateTime   : Thu Dec  3 10:22:53 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   40 (  47 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   62 (  90 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

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

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

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
    v2_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(k3_xboole_0(A_1,C_3),B_2)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(k3_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ! [B_36,A_37,C_38] :
      ( v2_tops_2(B_36,A_37)
      | ~ v2_tops_2(C_38,A_37)
      | ~ r1_tarski(B_36,C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37))))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37))))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_129,plain,(
    ! [A_51,B_52,A_53] :
      ( v2_tops_2(k3_xboole_0(A_51,B_52),A_53)
      | ~ v2_tops_2(A_51,A_53)
      | ~ m1_subset_1(A_51,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_53))))
      | ~ m1_subset_1(k3_xboole_0(A_51,B_52),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_53))))
      | ~ l1_pre_topc(A_53) ) ),
    inference(resolution,[status(thm)],[c_4,c_68])).

tff(c_134,plain,(
    ! [A_54,B_55,A_56] :
      ( v2_tops_2(k3_xboole_0(A_54,B_55),A_56)
      | ~ v2_tops_2(A_54,A_56)
      | ~ m1_subset_1(A_54,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_56))))
      | ~ l1_pre_topc(A_56)
      | ~ r1_tarski(k3_xboole_0(A_54,B_55),k1_zfmisc_1(u1_struct_0(A_56))) ) ),
    inference(resolution,[status(thm)],[c_10,c_129])).

tff(c_145,plain,(
    ! [A_57,C_58,A_59] :
      ( v2_tops_2(k3_xboole_0(A_57,C_58),A_59)
      | ~ v2_tops_2(A_57,A_59)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_59))))
      | ~ l1_pre_topc(A_59)
      | ~ r1_tarski(A_57,k1_zfmisc_1(u1_struct_0(A_59))) ) ),
    inference(resolution,[status(thm)],[c_2,c_134])).

tff(c_152,plain,(
    ! [C_58] :
      ( v2_tops_2(k3_xboole_0('#skF_2',C_58),'#skF_1')
      | ~ v2_tops_2('#skF_2','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_20,c_145])).

tff(c_159,plain,(
    ! [C_58] : v2_tops_2(k3_xboole_0('#skF_2',C_58),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_22,c_16,c_152])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_39,plain,(
    ! [A_31,B_32,C_33] :
      ( k9_subset_1(A_31,B_32,C_33) = k3_xboole_0(B_32,C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_47,plain,(
    ! [B_32] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_32,'#skF_3') = k3_xboole_0(B_32,'#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_39])).

tff(c_14,plain,(
    ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_49,plain,(
    ~ v2_tops_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_14])).

tff(c_162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_49])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 13:30:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.26  
% 1.95/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.26  %$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.95/1.26  
% 1.95/1.26  %Foreground sorts:
% 1.95/1.26  
% 1.95/1.26  
% 1.95/1.26  %Background operators:
% 1.95/1.26  
% 1.95/1.26  
% 1.95/1.26  %Foreground operators:
% 1.95/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.26  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.95/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.26  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.95/1.26  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 1.95/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.95/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.95/1.26  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 1.95/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.95/1.26  
% 1.95/1.27  tff(f_66, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tops_2)).
% 1.95/1.27  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.95/1.27  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 1.95/1.27  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.95/1.27  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v2_tops_2(C, A)) => v2_tops_2(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tops_2)).
% 1.95/1.27  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 1.95/1.27  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.95/1.27  tff(c_24, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | ~m1_subset_1(A_24, k1_zfmisc_1(B_25)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.95/1.27  tff(c_32, plain, (r1_tarski('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_20, c_24])).
% 1.95/1.27  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.95/1.27  tff(c_16, plain, (v2_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.95/1.27  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(k3_xboole_0(A_1, C_3), B_2) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.95/1.27  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.95/1.27  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k3_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.95/1.27  tff(c_68, plain, (![B_36, A_37, C_38]: (v2_tops_2(B_36, A_37) | ~v2_tops_2(C_38, A_37) | ~r1_tarski(B_36, C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37)))) | ~m1_subset_1(B_36, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37)))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.95/1.27  tff(c_129, plain, (![A_51, B_52, A_53]: (v2_tops_2(k3_xboole_0(A_51, B_52), A_53) | ~v2_tops_2(A_51, A_53) | ~m1_subset_1(A_51, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_53)))) | ~m1_subset_1(k3_xboole_0(A_51, B_52), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_53)))) | ~l1_pre_topc(A_53))), inference(resolution, [status(thm)], [c_4, c_68])).
% 1.95/1.27  tff(c_134, plain, (![A_54, B_55, A_56]: (v2_tops_2(k3_xboole_0(A_54, B_55), A_56) | ~v2_tops_2(A_54, A_56) | ~m1_subset_1(A_54, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_56)))) | ~l1_pre_topc(A_56) | ~r1_tarski(k3_xboole_0(A_54, B_55), k1_zfmisc_1(u1_struct_0(A_56))))), inference(resolution, [status(thm)], [c_10, c_129])).
% 1.95/1.27  tff(c_145, plain, (![A_57, C_58, A_59]: (v2_tops_2(k3_xboole_0(A_57, C_58), A_59) | ~v2_tops_2(A_57, A_59) | ~m1_subset_1(A_57, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_59)))) | ~l1_pre_topc(A_59) | ~r1_tarski(A_57, k1_zfmisc_1(u1_struct_0(A_59))))), inference(resolution, [status(thm)], [c_2, c_134])).
% 1.95/1.27  tff(c_152, plain, (![C_58]: (v2_tops_2(k3_xboole_0('#skF_2', C_58), '#skF_1') | ~v2_tops_2('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~r1_tarski('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_20, c_145])).
% 1.95/1.27  tff(c_159, plain, (![C_58]: (v2_tops_2(k3_xboole_0('#skF_2', C_58), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_22, c_16, c_152])).
% 1.95/1.27  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.95/1.27  tff(c_39, plain, (![A_31, B_32, C_33]: (k9_subset_1(A_31, B_32, C_33)=k3_xboole_0(B_32, C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.95/1.27  tff(c_47, plain, (![B_32]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_32, '#skF_3')=k3_xboole_0(B_32, '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_39])).
% 1.95/1.27  tff(c_14, plain, (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.95/1.27  tff(c_49, plain, (~v2_tops_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_14])).
% 1.95/1.27  tff(c_162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_159, c_49])).
% 1.95/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.27  
% 1.95/1.27  Inference rules
% 1.95/1.27  ----------------------
% 1.95/1.27  #Ref     : 0
% 1.95/1.27  #Sup     : 31
% 1.95/1.27  #Fact    : 0
% 1.95/1.27  #Define  : 0
% 1.95/1.27  #Split   : 0
% 1.95/1.27  #Chain   : 0
% 1.95/1.27  #Close   : 0
% 1.95/1.27  
% 1.95/1.27  Ordering : KBO
% 1.95/1.27  
% 1.95/1.27  Simplification rules
% 1.95/1.27  ----------------------
% 1.95/1.27  #Subsume      : 0
% 1.95/1.27  #Demod        : 9
% 1.95/1.27  #Tautology    : 13
% 1.95/1.27  #SimpNegUnit  : 0
% 1.95/1.27  #BackRed      : 2
% 1.95/1.27  
% 1.95/1.27  #Partial instantiations: 0
% 1.95/1.27  #Strategies tried      : 1
% 1.95/1.27  
% 1.95/1.27  Timing (in seconds)
% 1.95/1.27  ----------------------
% 1.95/1.27  Preprocessing        : 0.30
% 1.95/1.27  Parsing              : 0.16
% 1.95/1.27  CNF conversion       : 0.02
% 1.95/1.27  Main loop            : 0.15
% 1.95/1.27  Inferencing          : 0.06
% 1.95/1.27  Reduction            : 0.04
% 1.95/1.27  Demodulation         : 0.03
% 1.95/1.27  BG Simplification    : 0.01
% 1.95/1.27  Subsumption          : 0.03
% 1.95/1.27  Abstraction          : 0.01
% 1.95/1.27  MUC search           : 0.00
% 1.95/1.27  Cooper               : 0.00
% 1.95/1.27  Total                : 0.48
% 1.95/1.27  Index Insertion      : 0.00
% 1.95/1.27  Index Deletion       : 0.00
% 1.95/1.27  Index Matching       : 0.00
% 1.95/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
