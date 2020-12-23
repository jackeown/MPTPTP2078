%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:49 EST 2020

% Result     : Theorem 4.61s
% Output     : CNFRefutation 4.61s
% Verified   : 
% Statistics : Number of formulae       :   50 (  62 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :   85 ( 120 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v1_tops_2(B,A)
                 => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tops_2)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_63,axiom,(
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

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_33,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,B_29)
      | ~ m1_subset_1(A_28,k1_zfmisc_1(B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_41,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_28,c_33])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8] :
      ( r1_tarski(k4_xboole_0(A_6,B_7),C_8)
      | ~ r1_tarski(A_6,k2_xboole_0(B_7,C_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_24,plain,(
    v1_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_12,plain,(
    ! [A_9,B_10] : k2_xboole_0(k3_xboole_0(A_9,B_10),k4_xboole_0(A_9,B_10)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_145,plain,(
    ! [B_60,A_61,C_62] :
      ( v1_tops_2(B_60,A_61)
      | ~ v1_tops_2(C_62,A_61)
      | ~ r1_tarski(B_60,C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_61))))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_61))))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_609,plain,(
    ! [A_118,A_119,C_120,B_121] :
      ( v1_tops_2(A_118,A_119)
      | ~ v1_tops_2(k2_xboole_0(C_120,B_121),A_119)
      | ~ m1_subset_1(k2_xboole_0(C_120,B_121),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_119))))
      | ~ m1_subset_1(A_118,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_119))))
      | ~ l1_pre_topc(A_119)
      | ~ r1_tarski(A_118,B_121) ) ),
    inference(resolution,[status(thm)],[c_8,c_145])).

tff(c_611,plain,(
    ! [A_118,A_119,A_9,B_10] :
      ( v1_tops_2(A_118,A_119)
      | ~ v1_tops_2(k2_xboole_0(k3_xboole_0(A_9,B_10),k4_xboole_0(A_9,B_10)),A_119)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_119))))
      | ~ m1_subset_1(A_118,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_119))))
      | ~ l1_pre_topc(A_119)
      | ~ r1_tarski(A_118,k4_xboole_0(A_9,B_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_609])).

tff(c_2278,plain,(
    ! [A_289,A_290,A_291,B_292] :
      ( v1_tops_2(A_289,A_290)
      | ~ v1_tops_2(A_291,A_290)
      | ~ m1_subset_1(A_291,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_290))))
      | ~ m1_subset_1(A_289,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_290))))
      | ~ l1_pre_topc(A_290)
      | ~ r1_tarski(A_289,k4_xboole_0(A_291,B_292)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_611])).

tff(c_2285,plain,(
    ! [A_289,B_292] :
      ( v1_tops_2(A_289,'#skF_1')
      | ~ v1_tops_2('#skF_2','#skF_1')
      | ~ m1_subset_1(A_289,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_289,k4_xboole_0('#skF_2',B_292)) ) ),
    inference(resolution,[status(thm)],[c_28,c_2278])).

tff(c_2293,plain,(
    ! [A_293,B_294] :
      ( v1_tops_2(A_293,'#skF_1')
      | ~ m1_subset_1(A_293,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ r1_tarski(A_293,k4_xboole_0('#skF_2',B_294)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_2285])).

tff(c_2308,plain,(
    ! [A_296,B_297] :
      ( v1_tops_2(A_296,'#skF_1')
      | ~ r1_tarski(A_296,k4_xboole_0('#skF_2',B_297))
      | ~ r1_tarski(A_296,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_18,c_2293])).

tff(c_2421,plain,(
    ! [B_298] :
      ( v1_tops_2(k4_xboole_0('#skF_2',B_298),'#skF_1')
      | ~ r1_tarski(k4_xboole_0('#skF_2',B_298),k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_6,c_2308])).

tff(c_2435,plain,(
    ! [B_300] :
      ( v1_tops_2(k4_xboole_0('#skF_2',B_300),'#skF_1')
      | ~ r1_tarski('#skF_2',k2_xboole_0(B_300,k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(resolution,[status(thm)],[c_10,c_2421])).

tff(c_2439,plain,(
    ! [C_5] :
      ( v1_tops_2(k4_xboole_0('#skF_2',C_5),'#skF_1')
      | ~ r1_tarski('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_8,c_2435])).

tff(c_2442,plain,(
    ! [C_5] : v1_tops_2(k4_xboole_0('#skF_2',C_5),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_2439])).

tff(c_126,plain,(
    ! [A_56,B_57,C_58] :
      ( k7_subset_1(A_56,B_57,C_58) = k4_xboole_0(B_57,C_58)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_135,plain,(
    ! [C_58] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_58) = k4_xboole_0('#skF_2',C_58) ),
    inference(resolution,[status(thm)],[c_28,c_126])).

tff(c_22,plain,(
    ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_170,plain,(
    ~ v1_tops_2(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_22])).

tff(c_2448,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2442,c_170])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:40:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.61/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.61/1.87  
% 4.61/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.61/1.87  %$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 4.61/1.87  
% 4.61/1.87  %Foreground sorts:
% 4.61/1.87  
% 4.61/1.87  
% 4.61/1.87  %Background operators:
% 4.61/1.87  
% 4.61/1.87  
% 4.61/1.87  %Foreground operators:
% 4.61/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.61/1.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.61/1.87  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 4.61/1.87  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.61/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.61/1.87  tff('#skF_2', type, '#skF_2': $i).
% 4.61/1.87  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.61/1.87  tff('#skF_3', type, '#skF_3': $i).
% 4.61/1.87  tff('#skF_1', type, '#skF_1': $i).
% 4.61/1.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.61/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.61/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.61/1.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.61/1.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.61/1.87  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.61/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.61/1.87  
% 4.61/1.88  tff(f_76, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_tops_2)).
% 4.61/1.88  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.61/1.88  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 4.61/1.88  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 4.61/1.88  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.61/1.88  tff(f_41, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 4.61/1.88  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v1_tops_2(C, A)) => v1_tops_2(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_tops_2)).
% 4.61/1.88  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.61/1.88  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.61/1.88  tff(c_33, plain, (![A_28, B_29]: (r1_tarski(A_28, B_29) | ~m1_subset_1(A_28, k1_zfmisc_1(B_29)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.61/1.88  tff(c_41, plain, (r1_tarski('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_28, c_33])).
% 4.61/1.88  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.61/1.88  tff(c_10, plain, (![A_6, B_7, C_8]: (r1_tarski(k4_xboole_0(A_6, B_7), C_8) | ~r1_tarski(A_6, k2_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.61/1.88  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.61/1.88  tff(c_18, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.61/1.88  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.61/1.88  tff(c_24, plain, (v1_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.61/1.88  tff(c_12, plain, (![A_9, B_10]: (k2_xboole_0(k3_xboole_0(A_9, B_10), k4_xboole_0(A_9, B_10))=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.61/1.88  tff(c_145, plain, (![B_60, A_61, C_62]: (v1_tops_2(B_60, A_61) | ~v1_tops_2(C_62, A_61) | ~r1_tarski(B_60, C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_61)))) | ~m1_subset_1(B_60, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_61)))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.61/1.88  tff(c_609, plain, (![A_118, A_119, C_120, B_121]: (v1_tops_2(A_118, A_119) | ~v1_tops_2(k2_xboole_0(C_120, B_121), A_119) | ~m1_subset_1(k2_xboole_0(C_120, B_121), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_119)))) | ~m1_subset_1(A_118, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_119)))) | ~l1_pre_topc(A_119) | ~r1_tarski(A_118, B_121))), inference(resolution, [status(thm)], [c_8, c_145])).
% 4.61/1.88  tff(c_611, plain, (![A_118, A_119, A_9, B_10]: (v1_tops_2(A_118, A_119) | ~v1_tops_2(k2_xboole_0(k3_xboole_0(A_9, B_10), k4_xboole_0(A_9, B_10)), A_119) | ~m1_subset_1(A_9, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_119)))) | ~m1_subset_1(A_118, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_119)))) | ~l1_pre_topc(A_119) | ~r1_tarski(A_118, k4_xboole_0(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_609])).
% 4.61/1.88  tff(c_2278, plain, (![A_289, A_290, A_291, B_292]: (v1_tops_2(A_289, A_290) | ~v1_tops_2(A_291, A_290) | ~m1_subset_1(A_291, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_290)))) | ~m1_subset_1(A_289, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_290)))) | ~l1_pre_topc(A_290) | ~r1_tarski(A_289, k4_xboole_0(A_291, B_292)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_611])).
% 4.61/1.88  tff(c_2285, plain, (![A_289, B_292]: (v1_tops_2(A_289, '#skF_1') | ~v1_tops_2('#skF_2', '#skF_1') | ~m1_subset_1(A_289, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_289, k4_xboole_0('#skF_2', B_292)))), inference(resolution, [status(thm)], [c_28, c_2278])).
% 4.61/1.88  tff(c_2293, plain, (![A_293, B_294]: (v1_tops_2(A_293, '#skF_1') | ~m1_subset_1(A_293, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~r1_tarski(A_293, k4_xboole_0('#skF_2', B_294)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_24, c_2285])).
% 4.61/1.88  tff(c_2308, plain, (![A_296, B_297]: (v1_tops_2(A_296, '#skF_1') | ~r1_tarski(A_296, k4_xboole_0('#skF_2', B_297)) | ~r1_tarski(A_296, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_18, c_2293])).
% 4.61/1.88  tff(c_2421, plain, (![B_298]: (v1_tops_2(k4_xboole_0('#skF_2', B_298), '#skF_1') | ~r1_tarski(k4_xboole_0('#skF_2', B_298), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_6, c_2308])).
% 4.61/1.88  tff(c_2435, plain, (![B_300]: (v1_tops_2(k4_xboole_0('#skF_2', B_300), '#skF_1') | ~r1_tarski('#skF_2', k2_xboole_0(B_300, k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(resolution, [status(thm)], [c_10, c_2421])).
% 4.61/1.88  tff(c_2439, plain, (![C_5]: (v1_tops_2(k4_xboole_0('#skF_2', C_5), '#skF_1') | ~r1_tarski('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_8, c_2435])).
% 4.61/1.88  tff(c_2442, plain, (![C_5]: (v1_tops_2(k4_xboole_0('#skF_2', C_5), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_2439])).
% 4.61/1.88  tff(c_126, plain, (![A_56, B_57, C_58]: (k7_subset_1(A_56, B_57, C_58)=k4_xboole_0(B_57, C_58) | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.61/1.88  tff(c_135, plain, (![C_58]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_58)=k4_xboole_0('#skF_2', C_58))), inference(resolution, [status(thm)], [c_28, c_126])).
% 4.61/1.88  tff(c_22, plain, (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.61/1.88  tff(c_170, plain, (~v1_tops_2(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_22])).
% 4.61/1.88  tff(c_2448, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2442, c_170])).
% 4.61/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.61/1.88  
% 4.61/1.88  Inference rules
% 4.61/1.88  ----------------------
% 4.61/1.88  #Ref     : 0
% 4.61/1.88  #Sup     : 561
% 4.61/1.88  #Fact    : 0
% 4.61/1.88  #Define  : 0
% 4.61/1.88  #Split   : 4
% 4.61/1.88  #Chain   : 0
% 4.61/1.88  #Close   : 0
% 4.61/1.88  
% 4.61/1.88  Ordering : KBO
% 4.61/1.88  
% 4.61/1.88  Simplification rules
% 4.61/1.88  ----------------------
% 4.61/1.88  #Subsume      : 7
% 4.61/1.88  #Demod        : 66
% 4.61/1.88  #Tautology    : 79
% 4.61/1.88  #SimpNegUnit  : 1
% 4.61/1.88  #BackRed      : 2
% 4.61/1.88  
% 4.61/1.88  #Partial instantiations: 0
% 4.61/1.88  #Strategies tried      : 1
% 4.61/1.88  
% 4.61/1.88  Timing (in seconds)
% 4.61/1.88  ----------------------
% 4.61/1.88  Preprocessing        : 0.31
% 4.61/1.88  Parsing              : 0.17
% 4.61/1.88  CNF conversion       : 0.02
% 4.61/1.88  Main loop            : 0.81
% 4.61/1.88  Inferencing          : 0.26
% 4.61/1.88  Reduction            : 0.24
% 4.61/1.88  Demodulation         : 0.18
% 4.61/1.88  BG Simplification    : 0.05
% 4.61/1.88  Subsumption          : 0.19
% 4.61/1.88  Abstraction          : 0.08
% 4.61/1.88  MUC search           : 0.00
% 4.61/1.88  Cooper               : 0.00
% 4.61/1.88  Total                : 1.15
% 4.61/1.88  Index Insertion      : 0.00
% 4.61/1.88  Index Deletion       : 0.00
% 4.61/1.88  Index Matching       : 0.00
% 4.61/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
