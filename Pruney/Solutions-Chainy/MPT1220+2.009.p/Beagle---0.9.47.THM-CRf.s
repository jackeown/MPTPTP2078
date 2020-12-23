%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:22 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   43 (  70 expanded)
%              Number of leaves         :   19 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :   65 ( 114 expanded)
%              Number of equality atoms :   11 (  26 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => k2_pre_topc(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    k2_pre_topc('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [A_14] :
      ( u1_struct_0(A_14) = k2_struct_0(A_14)
      | ~ l1_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_32,plain,(
    ! [A_17] :
      ( u1_struct_0(A_17) = k2_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(resolution,[status(thm)],[c_16,c_26])).

tff(c_36,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_32])).

tff(c_76,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(k2_pre_topc(A_29,B_30),k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_84,plain,(
    ! [B_30] :
      ( m1_subset_1(k2_pre_topc('#skF_1',B_30),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_76])).

tff(c_89,plain,(
    ! [B_31] :
      ( m1_subset_1(k2_pre_topc('#skF_1',B_31),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_36,c_84])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_97,plain,(
    ! [B_32] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_32),k2_struct_0('#skF_1'))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_89,c_8])).

tff(c_53,plain,(
    ! [B_22,A_23] :
      ( r1_tarski(B_22,k2_pre_topc(A_23,B_22))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_55,plain,(
    ! [B_22] :
      ( r1_tarski(B_22,k2_pre_topc('#skF_1',B_22))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_53])).

tff(c_62,plain,(
    ! [B_24] :
      ( r1_tarski(B_24,k2_pre_topc('#skF_1',B_24))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_55])).

tff(c_67,plain,(
    ! [A_25] :
      ( r1_tarski(A_25,k2_pre_topc('#skF_1',A_25))
      | ~ r1_tarski(A_25,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_10,c_62])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    ! [A_25] :
      ( k2_pre_topc('#skF_1',A_25) = A_25
      | ~ r1_tarski(k2_pre_topc('#skF_1',A_25),A_25)
      | ~ r1_tarski(A_25,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_67,c_2])).

tff(c_101,plain,
    ( k2_pre_topc('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1')
    | ~ r1_tarski(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_97,c_70])).

tff(c_106,plain,
    ( k2_pre_topc('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_101])).

tff(c_107,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_106])).

tff(c_111,plain,(
    ~ r1_tarski(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_107])).

tff(c_115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_111])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:03:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.22  
% 1.79/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.22  %$ r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1
% 1.79/1.22  
% 1.79/1.22  %Foreground sorts:
% 1.79/1.22  
% 1.79/1.22  
% 1.79/1.22  %Background operators:
% 1.79/1.22  
% 1.79/1.22  
% 1.79/1.22  %Foreground operators:
% 1.79/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.79/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.79/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.79/1.22  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.79/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.79/1.22  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 1.79/1.22  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 1.79/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.79/1.22  
% 2.00/1.23  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.00/1.23  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.00/1.23  tff(f_61, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (k2_pre_topc(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tops_1)).
% 2.00/1.23  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.00/1.23  tff(f_39, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.00/1.23  tff(f_45, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.00/1.23  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 2.00/1.23  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.00/1.23  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.00/1.23  tff(c_20, plain, (k2_pre_topc('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.00/1.23  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.00/1.23  tff(c_16, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.00/1.23  tff(c_26, plain, (![A_14]: (u1_struct_0(A_14)=k2_struct_0(A_14) | ~l1_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.00/1.23  tff(c_32, plain, (![A_17]: (u1_struct_0(A_17)=k2_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(resolution, [status(thm)], [c_16, c_26])).
% 2.00/1.23  tff(c_36, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_32])).
% 2.00/1.23  tff(c_76, plain, (![A_29, B_30]: (m1_subset_1(k2_pre_topc(A_29, B_30), k1_zfmisc_1(u1_struct_0(A_29))) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.00/1.23  tff(c_84, plain, (![B_30]: (m1_subset_1(k2_pre_topc('#skF_1', B_30), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_76])).
% 2.00/1.23  tff(c_89, plain, (![B_31]: (m1_subset_1(k2_pre_topc('#skF_1', B_31), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_31, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_36, c_84])).
% 2.00/1.23  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.00/1.23  tff(c_97, plain, (![B_32]: (r1_tarski(k2_pre_topc('#skF_1', B_32), k2_struct_0('#skF_1')) | ~m1_subset_1(B_32, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_89, c_8])).
% 2.00/1.23  tff(c_53, plain, (![B_22, A_23]: (r1_tarski(B_22, k2_pre_topc(A_23, B_22)) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.00/1.23  tff(c_55, plain, (![B_22]: (r1_tarski(B_22, k2_pre_topc('#skF_1', B_22)) | ~m1_subset_1(B_22, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_53])).
% 2.00/1.23  tff(c_62, plain, (![B_24]: (r1_tarski(B_24, k2_pre_topc('#skF_1', B_24)) | ~m1_subset_1(B_24, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_55])).
% 2.00/1.23  tff(c_67, plain, (![A_25]: (r1_tarski(A_25, k2_pre_topc('#skF_1', A_25)) | ~r1_tarski(A_25, k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_10, c_62])).
% 2.00/1.23  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.00/1.23  tff(c_70, plain, (![A_25]: (k2_pre_topc('#skF_1', A_25)=A_25 | ~r1_tarski(k2_pre_topc('#skF_1', A_25), A_25) | ~r1_tarski(A_25, k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_67, c_2])).
% 2.00/1.23  tff(c_101, plain, (k2_pre_topc('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1') | ~r1_tarski(k2_struct_0('#skF_1'), k2_struct_0('#skF_1')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_97, c_70])).
% 2.00/1.23  tff(c_106, plain, (k2_pre_topc('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_101])).
% 2.00/1.23  tff(c_107, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_20, c_106])).
% 2.00/1.23  tff(c_111, plain, (~r1_tarski(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_107])).
% 2.00/1.23  tff(c_115, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_111])).
% 2.00/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.23  
% 2.00/1.23  Inference rules
% 2.00/1.23  ----------------------
% 2.00/1.23  #Ref     : 0
% 2.00/1.23  #Sup     : 19
% 2.00/1.23  #Fact    : 0
% 2.00/1.23  #Define  : 0
% 2.00/1.23  #Split   : 0
% 2.00/1.23  #Chain   : 0
% 2.00/1.23  #Close   : 0
% 2.00/1.23  
% 2.00/1.23  Ordering : KBO
% 2.00/1.23  
% 2.00/1.23  Simplification rules
% 2.00/1.23  ----------------------
% 2.00/1.23  #Subsume      : 0
% 2.00/1.23  #Demod        : 7
% 2.00/1.23  #Tautology    : 5
% 2.00/1.23  #SimpNegUnit  : 1
% 2.00/1.23  #BackRed      : 0
% 2.00/1.23  
% 2.00/1.23  #Partial instantiations: 0
% 2.00/1.23  #Strategies tried      : 1
% 2.00/1.23  
% 2.00/1.23  Timing (in seconds)
% 2.00/1.23  ----------------------
% 2.00/1.23  Preprocessing        : 0.30
% 2.00/1.23  Parsing              : 0.16
% 2.00/1.23  CNF conversion       : 0.02
% 2.00/1.23  Main loop            : 0.13
% 2.00/1.23  Inferencing          : 0.05
% 2.00/1.23  Reduction            : 0.04
% 2.00/1.23  Demodulation         : 0.03
% 2.00/1.23  BG Simplification    : 0.01
% 2.00/1.24  Subsumption          : 0.03
% 2.00/1.24  Abstraction          : 0.01
% 2.00/1.24  MUC search           : 0.00
% 2.00/1.24  Cooper               : 0.00
% 2.00/1.24  Total                : 0.46
% 2.00/1.24  Index Insertion      : 0.00
% 2.00/1.24  Index Deletion       : 0.00
% 2.00/1.24  Index Matching       : 0.00
% 2.00/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
