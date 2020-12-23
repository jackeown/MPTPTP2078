%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:59 EST 2020

% Result     : Theorem 5.32s
% Output     : CNFRefutation 5.32s
% Verified   : 
% Statistics : Number of formulae       :   41 (  53 expanded)
%              Number of leaves         :   19 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 (  82 expanded)
%              Number of equality atoms :    6 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => ( ( r1_tarski(A,B)
            & r1_tarski(C,D) )
         => m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_18,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_22,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_92,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_96,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_92])).

tff(c_172,plain,(
    ! [C_31,A_32,B_33] :
      ( r1_tarski(k2_zfmisc_1(C_31,A_32),k2_zfmisc_1(C_31,B_33))
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_734,plain,(
    ! [C_64,A_65,B_66] :
      ( k2_xboole_0(k2_zfmisc_1(C_64,A_65),k2_zfmisc_1(C_64,B_66)) = k2_zfmisc_1(C_64,B_66)
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_172,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_110,plain,(
    ! [A_21,C_22,B_23] :
      ( r1_tarski(A_21,k2_xboole_0(C_22,B_23))
      | ~ r1_tarski(A_21,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    ! [A_21,A_1,B_2] :
      ( r1_tarski(A_21,k2_xboole_0(A_1,B_2))
      | ~ r1_tarski(A_21,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_110])).

tff(c_1196,plain,(
    ! [A_84,C_85,B_86,A_87] :
      ( r1_tarski(A_84,k2_zfmisc_1(C_85,B_86))
      | ~ r1_tarski(A_84,k2_zfmisc_1(C_85,A_87))
      | ~ r1_tarski(A_87,B_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_734,c_128])).

tff(c_1208,plain,(
    ! [B_86] :
      ( r1_tarski('#skF_5',k2_zfmisc_1('#skF_1',B_86))
      | ~ r1_tarski('#skF_3',B_86) ) ),
    inference(resolution,[status(thm)],[c_96,c_1196])).

tff(c_177,plain,(
    ! [A_34,C_35,B_36] :
      ( r1_tarski(k2_zfmisc_1(A_34,C_35),k2_zfmisc_1(B_36,C_35))
      | ~ r1_tarski(A_34,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_362,plain,(
    ! [A_48,C_49,B_50] :
      ( k2_xboole_0(k2_zfmisc_1(A_48,C_49),k2_zfmisc_1(B_50,C_49)) = k2_zfmisc_1(B_50,C_49)
      | ~ r1_tarski(A_48,B_50) ) ),
    inference(resolution,[status(thm)],[c_177,c_6])).

tff(c_3315,plain,(
    ! [A_145,B_146,C_147,A_148] :
      ( r1_tarski(A_145,k2_zfmisc_1(B_146,C_147))
      | ~ r1_tarski(A_145,k2_zfmisc_1(A_148,C_147))
      | ~ r1_tarski(A_148,B_146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_128])).

tff(c_3660,plain,(
    ! [B_159,B_160] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(B_159,B_160))
      | ~ r1_tarski('#skF_1',B_159)
      | ~ r1_tarski('#skF_3',B_160) ) ),
    inference(resolution,[status(thm)],[c_1208,c_3315])).

tff(c_101,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_109,plain,(
    ~ r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_101,c_16])).

tff(c_3677,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_3660,c_109])).

tff(c_3692,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_3677])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n006.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 13:07:22 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.32/2.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.32/2.02  
% 5.32/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.32/2.02  %$ r1_tarski > m1_subset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.32/2.02  
% 5.32/2.02  %Foreground sorts:
% 5.32/2.02  
% 5.32/2.02  
% 5.32/2.02  %Background operators:
% 5.32/2.02  
% 5.32/2.02  
% 5.32/2.02  %Foreground operators:
% 5.32/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.32/2.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.32/2.02  tff('#skF_5', type, '#skF_5': $i).
% 5.32/2.02  tff('#skF_2', type, '#skF_2': $i).
% 5.32/2.02  tff('#skF_3', type, '#skF_3': $i).
% 5.32/2.02  tff('#skF_1', type, '#skF_1': $i).
% 5.32/2.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.32/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.32/2.02  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.32/2.02  tff('#skF_4', type, '#skF_4': $i).
% 5.32/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.32/2.02  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.32/2.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.32/2.02  
% 5.32/2.04  tff(f_54, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C))) => ((r1_tarski(A, B) & r1_tarski(C, D)) => m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_relset_1)).
% 5.32/2.04  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.32/2.04  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 5.32/2.04  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.32/2.04  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.32/2.04  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 5.32/2.04  tff(c_18, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.32/2.04  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.32/2.04  tff(c_22, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.32/2.04  tff(c_92, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~m1_subset_1(A_17, k1_zfmisc_1(B_18)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.32/2.04  tff(c_96, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_92])).
% 5.32/2.04  tff(c_172, plain, (![C_31, A_32, B_33]: (r1_tarski(k2_zfmisc_1(C_31, A_32), k2_zfmisc_1(C_31, B_33)) | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.32/2.04  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.32/2.04  tff(c_734, plain, (![C_64, A_65, B_66]: (k2_xboole_0(k2_zfmisc_1(C_64, A_65), k2_zfmisc_1(C_64, B_66))=k2_zfmisc_1(C_64, B_66) | ~r1_tarski(A_65, B_66))), inference(resolution, [status(thm)], [c_172, c_6])).
% 5.32/2.04  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.32/2.04  tff(c_110, plain, (![A_21, C_22, B_23]: (r1_tarski(A_21, k2_xboole_0(C_22, B_23)) | ~r1_tarski(A_21, B_23))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.32/2.04  tff(c_128, plain, (![A_21, A_1, B_2]: (r1_tarski(A_21, k2_xboole_0(A_1, B_2)) | ~r1_tarski(A_21, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_110])).
% 5.32/2.04  tff(c_1196, plain, (![A_84, C_85, B_86, A_87]: (r1_tarski(A_84, k2_zfmisc_1(C_85, B_86)) | ~r1_tarski(A_84, k2_zfmisc_1(C_85, A_87)) | ~r1_tarski(A_87, B_86))), inference(superposition, [status(thm), theory('equality')], [c_734, c_128])).
% 5.32/2.04  tff(c_1208, plain, (![B_86]: (r1_tarski('#skF_5', k2_zfmisc_1('#skF_1', B_86)) | ~r1_tarski('#skF_3', B_86))), inference(resolution, [status(thm)], [c_96, c_1196])).
% 5.32/2.04  tff(c_177, plain, (![A_34, C_35, B_36]: (r1_tarski(k2_zfmisc_1(A_34, C_35), k2_zfmisc_1(B_36, C_35)) | ~r1_tarski(A_34, B_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.32/2.04  tff(c_362, plain, (![A_48, C_49, B_50]: (k2_xboole_0(k2_zfmisc_1(A_48, C_49), k2_zfmisc_1(B_50, C_49))=k2_zfmisc_1(B_50, C_49) | ~r1_tarski(A_48, B_50))), inference(resolution, [status(thm)], [c_177, c_6])).
% 5.32/2.04  tff(c_3315, plain, (![A_145, B_146, C_147, A_148]: (r1_tarski(A_145, k2_zfmisc_1(B_146, C_147)) | ~r1_tarski(A_145, k2_zfmisc_1(A_148, C_147)) | ~r1_tarski(A_148, B_146))), inference(superposition, [status(thm), theory('equality')], [c_362, c_128])).
% 5.32/2.04  tff(c_3660, plain, (![B_159, B_160]: (r1_tarski('#skF_5', k2_zfmisc_1(B_159, B_160)) | ~r1_tarski('#skF_1', B_159) | ~r1_tarski('#skF_3', B_160))), inference(resolution, [status(thm)], [c_1208, c_3315])).
% 5.32/2.04  tff(c_101, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.32/2.04  tff(c_16, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.32/2.04  tff(c_109, plain, (~r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_101, c_16])).
% 5.32/2.04  tff(c_3677, plain, (~r1_tarski('#skF_1', '#skF_2') | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_3660, c_109])).
% 5.32/2.04  tff(c_3692, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_3677])).
% 5.32/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.32/2.04  
% 5.32/2.04  Inference rules
% 5.32/2.04  ----------------------
% 5.32/2.04  #Ref     : 0
% 5.32/2.04  #Sup     : 1056
% 5.32/2.04  #Fact    : 0
% 5.32/2.04  #Define  : 0
% 5.32/2.04  #Split   : 16
% 5.32/2.04  #Chain   : 0
% 5.32/2.04  #Close   : 0
% 5.32/2.04  
% 5.32/2.04  Ordering : KBO
% 5.32/2.04  
% 5.32/2.04  Simplification rules
% 5.32/2.04  ----------------------
% 5.32/2.04  #Subsume      : 296
% 5.32/2.04  #Demod        : 125
% 5.32/2.04  #Tautology    : 154
% 5.32/2.04  #SimpNegUnit  : 0
% 5.32/2.04  #BackRed      : 0
% 5.32/2.04  
% 5.32/2.04  #Partial instantiations: 0
% 5.32/2.04  #Strategies tried      : 1
% 5.32/2.04  
% 5.32/2.04  Timing (in seconds)
% 5.32/2.04  ----------------------
% 5.32/2.04  Preprocessing        : 0.26
% 5.32/2.04  Parsing              : 0.14
% 5.32/2.04  CNF conversion       : 0.02
% 5.32/2.04  Main loop            : 1.03
% 5.32/2.04  Inferencing          : 0.31
% 5.32/2.04  Reduction            : 0.32
% 5.32/2.04  Demodulation         : 0.24
% 5.32/2.04  BG Simplification    : 0.04
% 5.32/2.04  Subsumption          : 0.28
% 5.32/2.04  Abstraction          : 0.04
% 5.32/2.04  MUC search           : 0.00
% 5.32/2.04  Cooper               : 0.00
% 5.32/2.04  Total                : 1.32
% 5.32/2.04  Index Insertion      : 0.00
% 5.32/2.04  Index Deletion       : 0.00
% 5.32/2.04  Index Matching       : 0.00
% 5.32/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
