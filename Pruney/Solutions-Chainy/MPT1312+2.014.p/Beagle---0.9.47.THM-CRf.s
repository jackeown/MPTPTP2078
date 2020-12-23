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
% DateTime   : Thu Dec  3 10:22:58 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   51 (  67 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   77 ( 115 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
               => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_2)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_31,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( r1_tarski(C,B)
             => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_tops_2)).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_25,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_37,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,B_30)
      | ~ m1_subset_1(A_29,k1_zfmisc_1(B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_45,plain,(
    ! [A_4] : r1_tarski(A_4,A_4) ),
    inference(resolution,[status(thm)],[c_25,c_37])).

tff(c_22,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_57,plain,(
    ! [C_36,A_37,B_38] :
      ( m1_subset_1(C_36,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ m1_subset_1(C_36,k1_zfmisc_1(u1_struct_0(B_38)))
      | ~ m1_pre_topc(B_38,A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_88,plain,(
    ! [A_46,A_47,B_48] :
      ( m1_subset_1(A_46,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ m1_pre_topc(B_48,A_47)
      | ~ l1_pre_topc(A_47)
      | ~ r1_tarski(A_46,u1_struct_0(B_48)) ) ),
    inference(resolution,[status(thm)],[c_10,c_57])).

tff(c_90,plain,(
    ! [A_46] :
      ( m1_subset_1(A_46,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_46,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_22,c_88])).

tff(c_94,plain,(
    ! [A_49] :
      ( m1_subset_1(A_49,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_49,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_90])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_113,plain,(
    ! [A_51] :
      ( r1_tarski(A_51,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_51,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_94,c_8])).

tff(c_123,plain,(
    r1_tarski(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_45,c_113])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(k1_zfmisc_1(A_1),k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_74,plain,(
    ! [C_41,A_42,B_43] :
      ( m1_subset_1(C_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_42))))
      | ~ r1_tarski(C_41,B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_42))))
      | ~ l1_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_136,plain,(
    ! [A_54,A_55,B_56] :
      ( m1_subset_1(k1_zfmisc_1(A_54),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_55))))
      | ~ m1_subset_1(k1_zfmisc_1(B_56),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_55))))
      | ~ l1_struct_0(A_55)
      | ~ r1_tarski(A_54,B_56) ) ),
    inference(resolution,[status(thm)],[c_2,c_74])).

tff(c_145,plain,(
    ! [A_57,A_58] :
      ( m1_subset_1(k1_zfmisc_1(A_57),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_58))))
      | ~ l1_struct_0(A_58)
      | ~ r1_tarski(A_57,u1_struct_0(A_58)) ) ),
    inference(resolution,[status(thm)],[c_25,c_136])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_44,plain,(
    r1_tarski('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_20,c_37])).

tff(c_82,plain,(
    ! [A_42] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_42))))
      | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0('#skF_2')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_42))))
      | ~ l1_struct_0(A_42) ) ),
    inference(resolution,[status(thm)],[c_44,c_74])).

tff(c_158,plain,(
    ! [A_59] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_59))))
      | ~ l1_struct_0(A_59)
      | ~ r1_tarski(u1_struct_0('#skF_2'),u1_struct_0(A_59)) ) ),
    inference(resolution,[status(thm)],[c_145,c_82])).

tff(c_18,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_164,plain,
    ( ~ l1_struct_0('#skF_1')
    | ~ r1_tarski(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_158,c_18])).

tff(c_168,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_164])).

tff(c_171,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_168])).

tff(c_175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_171])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:52:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.22  
% 1.95/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.22  %$ r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.95/1.22  
% 1.95/1.22  %Foreground sorts:
% 1.95/1.22  
% 1.95/1.22  
% 1.95/1.22  %Background operators:
% 1.95/1.22  
% 1.95/1.22  
% 1.95/1.22  %Foreground operators:
% 1.95/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.95/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.95/1.22  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.95/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.22  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 1.95/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.95/1.22  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 1.95/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.95/1.22  
% 1.95/1.24  tff(f_72, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_tops_2)).
% 1.95/1.24  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 1.95/1.24  tff(f_31, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 1.95/1.24  tff(f_33, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 1.95/1.24  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.95/1.24  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 1.95/1.24  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 1.95/1.24  tff(f_61, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (r1_tarski(C, B) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_tops_2)).
% 1.95/1.24  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.95/1.24  tff(c_12, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.95/1.24  tff(c_4, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.95/1.24  tff(c_6, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.95/1.24  tff(c_25, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 1.95/1.24  tff(c_37, plain, (![A_29, B_30]: (r1_tarski(A_29, B_30) | ~m1_subset_1(A_29, k1_zfmisc_1(B_30)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.95/1.24  tff(c_45, plain, (![A_4]: (r1_tarski(A_4, A_4))), inference(resolution, [status(thm)], [c_25, c_37])).
% 1.95/1.24  tff(c_22, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.95/1.24  tff(c_10, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.95/1.24  tff(c_57, plain, (![C_36, A_37, B_38]: (m1_subset_1(C_36, k1_zfmisc_1(u1_struct_0(A_37))) | ~m1_subset_1(C_36, k1_zfmisc_1(u1_struct_0(B_38))) | ~m1_pre_topc(B_38, A_37) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.95/1.24  tff(c_88, plain, (![A_46, A_47, B_48]: (m1_subset_1(A_46, k1_zfmisc_1(u1_struct_0(A_47))) | ~m1_pre_topc(B_48, A_47) | ~l1_pre_topc(A_47) | ~r1_tarski(A_46, u1_struct_0(B_48)))), inference(resolution, [status(thm)], [c_10, c_57])).
% 1.95/1.24  tff(c_90, plain, (![A_46]: (m1_subset_1(A_46, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_46, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_22, c_88])).
% 1.95/1.24  tff(c_94, plain, (![A_49]: (m1_subset_1(A_49, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_49, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_90])).
% 1.95/1.24  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.95/1.24  tff(c_113, plain, (![A_51]: (r1_tarski(A_51, u1_struct_0('#skF_1')) | ~r1_tarski(A_51, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_94, c_8])).
% 1.95/1.24  tff(c_123, plain, (r1_tarski(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_45, c_113])).
% 1.95/1.24  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k1_zfmisc_1(A_1), k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.95/1.24  tff(c_74, plain, (![C_41, A_42, B_43]: (m1_subset_1(C_41, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_42)))) | ~r1_tarski(C_41, B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_42)))) | ~l1_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.95/1.24  tff(c_136, plain, (![A_54, A_55, B_56]: (m1_subset_1(k1_zfmisc_1(A_54), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_55)))) | ~m1_subset_1(k1_zfmisc_1(B_56), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_55)))) | ~l1_struct_0(A_55) | ~r1_tarski(A_54, B_56))), inference(resolution, [status(thm)], [c_2, c_74])).
% 1.95/1.24  tff(c_145, plain, (![A_57, A_58]: (m1_subset_1(k1_zfmisc_1(A_57), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_58)))) | ~l1_struct_0(A_58) | ~r1_tarski(A_57, u1_struct_0(A_58)))), inference(resolution, [status(thm)], [c_25, c_136])).
% 1.95/1.24  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.95/1.24  tff(c_44, plain, (r1_tarski('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_20, c_37])).
% 1.95/1.24  tff(c_82, plain, (![A_42]: (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_42)))) | ~m1_subset_1(k1_zfmisc_1(u1_struct_0('#skF_2')), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_42)))) | ~l1_struct_0(A_42))), inference(resolution, [status(thm)], [c_44, c_74])).
% 1.95/1.24  tff(c_158, plain, (![A_59]: (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_59)))) | ~l1_struct_0(A_59) | ~r1_tarski(u1_struct_0('#skF_2'), u1_struct_0(A_59)))), inference(resolution, [status(thm)], [c_145, c_82])).
% 1.95/1.24  tff(c_18, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.95/1.24  tff(c_164, plain, (~l1_struct_0('#skF_1') | ~r1_tarski(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_158, c_18])).
% 1.95/1.24  tff(c_168, plain, (~l1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_164])).
% 1.95/1.24  tff(c_171, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_168])).
% 1.95/1.24  tff(c_175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_171])).
% 1.95/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.24  
% 1.95/1.24  Inference rules
% 1.95/1.24  ----------------------
% 1.95/1.24  #Ref     : 0
% 1.95/1.24  #Sup     : 32
% 1.95/1.24  #Fact    : 0
% 1.95/1.24  #Define  : 0
% 1.95/1.24  #Split   : 1
% 1.95/1.24  #Chain   : 0
% 1.95/1.24  #Close   : 0
% 1.95/1.24  
% 1.95/1.24  Ordering : KBO
% 1.95/1.24  
% 1.95/1.24  Simplification rules
% 1.95/1.24  ----------------------
% 1.95/1.24  #Subsume      : 1
% 1.95/1.24  #Demod        : 5
% 1.95/1.24  #Tautology    : 5
% 1.95/1.24  #SimpNegUnit  : 0
% 1.95/1.24  #BackRed      : 0
% 1.95/1.24  
% 1.95/1.24  #Partial instantiations: 0
% 1.95/1.24  #Strategies tried      : 1
% 1.95/1.24  
% 1.95/1.24  Timing (in seconds)
% 1.95/1.24  ----------------------
% 2.17/1.24  Preprocessing        : 0.28
% 2.17/1.24  Parsing              : 0.16
% 2.17/1.24  CNF conversion       : 0.02
% 2.17/1.24  Main loop            : 0.19
% 2.17/1.24  Inferencing          : 0.07
% 2.17/1.24  Reduction            : 0.05
% 2.17/1.24  Demodulation         : 0.04
% 2.17/1.24  BG Simplification    : 0.01
% 2.17/1.24  Subsumption          : 0.05
% 2.17/1.24  Abstraction          : 0.01
% 2.17/1.24  MUC search           : 0.00
% 2.17/1.24  Cooper               : 0.00
% 2.17/1.24  Total                : 0.50
% 2.17/1.24  Index Insertion      : 0.00
% 2.17/1.24  Index Deletion       : 0.00
% 2.17/1.24  Index Matching       : 0.00
% 2.17/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
