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
% DateTime   : Thu Dec  3 10:22:55 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 2.01s
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
%$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

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
               => ( v2_tops_2(B,A)
                 => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tops_2)).

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
                  & v2_tops_2(C,A) )
               => v2_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tops_2)).

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
    v2_tops_2('#skF_2','#skF_1') ),
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
      ( v2_tops_2(B_36,A_37)
      | ~ v2_tops_2(C_38,A_37)
      | ~ r1_tarski(B_36,C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37))))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37))))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_129,plain,(
    ! [A_51,B_52,A_53] :
      ( v2_tops_2(k4_xboole_0(A_51,B_52),A_53)
      | ~ v2_tops_2(A_51,A_53)
      | ~ m1_subset_1(A_51,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_53))))
      | ~ m1_subset_1(k4_xboole_0(A_51,B_52),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_53))))
      | ~ l1_pre_topc(A_53) ) ),
    inference(resolution,[status(thm)],[c_4,c_68])).

tff(c_134,plain,(
    ! [A_54,B_55,A_56] :
      ( v2_tops_2(k4_xboole_0(A_54,B_55),A_56)
      | ~ v2_tops_2(A_54,A_56)
      | ~ m1_subset_1(A_54,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_56))))
      | ~ l1_pre_topc(A_56)
      | ~ r1_tarski(k4_xboole_0(A_54,B_55),k1_zfmisc_1(u1_struct_0(A_56))) ) ),
    inference(resolution,[status(thm)],[c_10,c_129])).

tff(c_145,plain,(
    ! [A_57,C_58,A_59] :
      ( v2_tops_2(k4_xboole_0(A_57,C_58),A_59)
      | ~ v2_tops_2(A_57,A_59)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_59))))
      | ~ l1_pre_topc(A_59)
      | ~ r1_tarski(A_57,k1_zfmisc_1(u1_struct_0(A_59))) ) ),
    inference(resolution,[status(thm)],[c_2,c_134])).

tff(c_152,plain,(
    ! [C_58] :
      ( v2_tops_2(k4_xboole_0('#skF_2',C_58),'#skF_1')
      | ~ v2_tops_2('#skF_2','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_20,c_145])).

tff(c_159,plain,(
    ! [C_58] : v2_tops_2(k4_xboole_0('#skF_2',C_58),'#skF_1') ),
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
    ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_58,plain,(
    ~ v2_tops_2(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_14])).

tff(c_162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:53:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.20  
% 1.87/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.20  %$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.87/1.20  
% 1.87/1.20  %Foreground sorts:
% 1.87/1.20  
% 1.87/1.20  
% 1.87/1.20  %Background operators:
% 1.87/1.20  
% 1.87/1.20  
% 1.87/1.20  %Foreground operators:
% 1.87/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.87/1.20  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.87/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.20  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 1.87/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.87/1.20  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 1.87/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.20  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.87/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.87/1.20  
% 2.01/1.21  tff(f_66, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_tops_2)).
% 2.01/1.21  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.01/1.21  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 2.01/1.21  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.01/1.21  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v2_tops_2(C, A)) => v2_tops_2(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tops_2)).
% 2.01/1.21  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.01/1.21  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.01/1.21  tff(c_24, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | ~m1_subset_1(A_24, k1_zfmisc_1(B_25)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.01/1.21  tff(c_32, plain, (r1_tarski('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_20, c_24])).
% 2.01/1.21  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.01/1.21  tff(c_16, plain, (v2_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.01/1.21  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(k4_xboole_0(A_1, C_3), B_2) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.01/1.21  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.01/1.21  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.01/1.21  tff(c_68, plain, (![B_36, A_37, C_38]: (v2_tops_2(B_36, A_37) | ~v2_tops_2(C_38, A_37) | ~r1_tarski(B_36, C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37)))) | ~m1_subset_1(B_36, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37)))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.01/1.21  tff(c_129, plain, (![A_51, B_52, A_53]: (v2_tops_2(k4_xboole_0(A_51, B_52), A_53) | ~v2_tops_2(A_51, A_53) | ~m1_subset_1(A_51, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_53)))) | ~m1_subset_1(k4_xboole_0(A_51, B_52), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_53)))) | ~l1_pre_topc(A_53))), inference(resolution, [status(thm)], [c_4, c_68])).
% 2.01/1.21  tff(c_134, plain, (![A_54, B_55, A_56]: (v2_tops_2(k4_xboole_0(A_54, B_55), A_56) | ~v2_tops_2(A_54, A_56) | ~m1_subset_1(A_54, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_56)))) | ~l1_pre_topc(A_56) | ~r1_tarski(k4_xboole_0(A_54, B_55), k1_zfmisc_1(u1_struct_0(A_56))))), inference(resolution, [status(thm)], [c_10, c_129])).
% 2.01/1.21  tff(c_145, plain, (![A_57, C_58, A_59]: (v2_tops_2(k4_xboole_0(A_57, C_58), A_59) | ~v2_tops_2(A_57, A_59) | ~m1_subset_1(A_57, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_59)))) | ~l1_pre_topc(A_59) | ~r1_tarski(A_57, k1_zfmisc_1(u1_struct_0(A_59))))), inference(resolution, [status(thm)], [c_2, c_134])).
% 2.01/1.21  tff(c_152, plain, (![C_58]: (v2_tops_2(k4_xboole_0('#skF_2', C_58), '#skF_1') | ~v2_tops_2('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~r1_tarski('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_20, c_145])).
% 2.01/1.21  tff(c_159, plain, (![C_58]: (v2_tops_2(k4_xboole_0('#skF_2', C_58), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_22, c_16, c_152])).
% 2.01/1.21  tff(c_39, plain, (![A_31, B_32, C_33]: (k7_subset_1(A_31, B_32, C_33)=k4_xboole_0(B_32, C_33) | ~m1_subset_1(B_32, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.01/1.21  tff(c_48, plain, (![C_33]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_33)=k4_xboole_0('#skF_2', C_33))), inference(resolution, [status(thm)], [c_20, c_39])).
% 2.01/1.21  tff(c_14, plain, (~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.01/1.21  tff(c_58, plain, (~v2_tops_2(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_14])).
% 2.01/1.21  tff(c_162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_159, c_58])).
% 2.01/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.21  
% 2.01/1.21  Inference rules
% 2.01/1.21  ----------------------
% 2.01/1.21  #Ref     : 0
% 2.01/1.21  #Sup     : 31
% 2.01/1.21  #Fact    : 0
% 2.01/1.21  #Define  : 0
% 2.01/1.21  #Split   : 0
% 2.01/1.21  #Chain   : 0
% 2.01/1.21  #Close   : 0
% 2.01/1.21  
% 2.01/1.21  Ordering : KBO
% 2.01/1.21  
% 2.01/1.21  Simplification rules
% 2.01/1.21  ----------------------
% 2.01/1.21  #Subsume      : 0
% 2.01/1.21  #Demod        : 9
% 2.01/1.21  #Tautology    : 13
% 2.01/1.21  #SimpNegUnit  : 0
% 2.01/1.21  #BackRed      : 2
% 2.01/1.21  
% 2.01/1.21  #Partial instantiations: 0
% 2.01/1.21  #Strategies tried      : 1
% 2.01/1.21  
% 2.01/1.21  Timing (in seconds)
% 2.01/1.21  ----------------------
% 2.01/1.21  Preprocessing        : 0.28
% 2.01/1.21  Parsing              : 0.15
% 2.01/1.21  CNF conversion       : 0.02
% 2.01/1.21  Main loop            : 0.16
% 2.01/1.21  Inferencing          : 0.06
% 2.01/1.21  Reduction            : 0.04
% 2.01/1.21  Demodulation         : 0.03
% 2.01/1.21  BG Simplification    : 0.01
% 2.01/1.21  Subsumption          : 0.03
% 2.01/1.21  Abstraction          : 0.01
% 2.01/1.21  MUC search           : 0.00
% 2.01/1.21  Cooper               : 0.00
% 2.01/1.21  Total                : 0.46
% 2.01/1.21  Index Insertion      : 0.00
% 2.01/1.21  Index Deletion       : 0.00
% 2.01/1.21  Index Matching       : 0.00
% 2.01/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
