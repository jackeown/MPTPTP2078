%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:39 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   55 (  57 expanded)
%              Number of leaves         :   32 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   55 (  61 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_setfam_1(B,k1_tarski(A))
       => ! [C] :
            ( r2_hidden(C,B)
           => r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_setfam_1)).

tff(f_34,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_setfam_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_38,plain,(
    ~ r1_tarski('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_42,plain,(
    r1_setfam_1('#skF_3',k1_tarski('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8,plain,(
    ! [A_6] : k2_xboole_0(A_6,A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ! [A_11] : k2_tarski(A_11,A_11) = k1_tarski(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_82,plain,(
    ! [A_60,B_61] : k3_tarski(k2_tarski(A_60,B_61)) = k2_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_94,plain,(
    ! [A_11] : k3_tarski(k1_tarski(A_11)) = k2_xboole_0(A_11,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_82])).

tff(c_97,plain,(
    ! [A_11] : k3_tarski(k1_tarski(A_11)) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_94])).

tff(c_28,plain,(
    ! [A_41] : r1_tarski(A_41,k1_zfmisc_1(k3_tarski(A_41))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_40,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_201,plain,(
    ! [C_86,B_87,A_88] :
      ( r2_hidden(C_86,B_87)
      | ~ r2_hidden(C_86,A_88)
      | ~ r1_tarski(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_208,plain,(
    ! [B_89] :
      ( r2_hidden('#skF_4',B_89)
      | ~ r1_tarski('#skF_3',B_89) ) ),
    inference(resolution,[status(thm)],[c_40,c_201])).

tff(c_32,plain,(
    ! [A_44,B_45] :
      ( m1_subset_1(A_44,B_45)
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_216,plain,(
    ! [B_90] :
      ( m1_subset_1('#skF_4',B_90)
      | ~ r1_tarski('#skF_3',B_90) ) ),
    inference(resolution,[status(thm)],[c_208,c_32])).

tff(c_242,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k3_tarski('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_28,c_216])).

tff(c_34,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_246,plain,(
    r1_tarski('#skF_4',k3_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_242,c_34])).

tff(c_30,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(k3_tarski(A_42),k3_tarski(B_43))
      | ~ r1_setfam_1(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_145,plain,(
    ! [A_73,C_74,B_75] :
      ( r1_tarski(A_73,C_74)
      | ~ r1_tarski(B_75,C_74)
      | ~ r1_tarski(A_73,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_769,plain,(
    ! [A_165,B_166,A_167] :
      ( r1_tarski(A_165,k3_tarski(B_166))
      | ~ r1_tarski(A_165,k3_tarski(A_167))
      | ~ r1_setfam_1(A_167,B_166) ) ),
    inference(resolution,[status(thm)],[c_30,c_145])).

tff(c_819,plain,(
    ! [B_168] :
      ( r1_tarski('#skF_4',k3_tarski(B_168))
      | ~ r1_setfam_1('#skF_3',B_168) ) ),
    inference(resolution,[status(thm)],[c_246,c_769])).

tff(c_839,plain,(
    ! [A_169] :
      ( r1_tarski('#skF_4',A_169)
      | ~ r1_setfam_1('#skF_3',k1_tarski(A_169)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_819])).

tff(c_842,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_839])).

tff(c_846,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_842])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:18:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.46  
% 3.21/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.47  %$ r2_hidden > r1_tarski > r1_setfam_1 > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.21/1.47  
% 3.21/1.47  %Foreground sorts:
% 3.21/1.47  
% 3.21/1.47  
% 3.21/1.47  %Background operators:
% 3.21/1.47  
% 3.21/1.47  
% 3.21/1.47  %Foreground operators:
% 3.21/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.47  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 3.21/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.21/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.21/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.21/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.21/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.21/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.21/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.21/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.21/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.21/1.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.21/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.21/1.47  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.21/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.47  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.21/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.21/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.21/1.47  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.21/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.21/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.21/1.47  
% 3.21/1.48  tff(f_78, negated_conjecture, ~(![A, B]: (r1_setfam_1(B, k1_tarski(A)) => (![C]: (r2_hidden(C, B) => r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_setfam_1)).
% 3.21/1.48  tff(f_34, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.21/1.48  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.21/1.48  tff(f_56, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.21/1.48  tff(f_58, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 3.21/1.48  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.21/1.48  tff(f_66, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.21/1.48  tff(f_70, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.21/1.48  tff(f_62, axiom, (![A, B]: (r1_setfam_1(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_setfam_1)).
% 3.21/1.48  tff(f_40, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.21/1.48  tff(c_38, plain, (~r1_tarski('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.21/1.48  tff(c_42, plain, (r1_setfam_1('#skF_3', k1_tarski('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.21/1.48  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.21/1.48  tff(c_12, plain, (![A_11]: (k2_tarski(A_11, A_11)=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.21/1.48  tff(c_82, plain, (![A_60, B_61]: (k3_tarski(k2_tarski(A_60, B_61))=k2_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.21/1.48  tff(c_94, plain, (![A_11]: (k3_tarski(k1_tarski(A_11))=k2_xboole_0(A_11, A_11))), inference(superposition, [status(thm), theory('equality')], [c_12, c_82])).
% 3.21/1.48  tff(c_97, plain, (![A_11]: (k3_tarski(k1_tarski(A_11))=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_94])).
% 3.21/1.48  tff(c_28, plain, (![A_41]: (r1_tarski(A_41, k1_zfmisc_1(k3_tarski(A_41))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.21/1.48  tff(c_40, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.21/1.48  tff(c_201, plain, (![C_86, B_87, A_88]: (r2_hidden(C_86, B_87) | ~r2_hidden(C_86, A_88) | ~r1_tarski(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.21/1.48  tff(c_208, plain, (![B_89]: (r2_hidden('#skF_4', B_89) | ~r1_tarski('#skF_3', B_89))), inference(resolution, [status(thm)], [c_40, c_201])).
% 3.21/1.48  tff(c_32, plain, (![A_44, B_45]: (m1_subset_1(A_44, B_45) | ~r2_hidden(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.21/1.48  tff(c_216, plain, (![B_90]: (m1_subset_1('#skF_4', B_90) | ~r1_tarski('#skF_3', B_90))), inference(resolution, [status(thm)], [c_208, c_32])).
% 3.21/1.48  tff(c_242, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k3_tarski('#skF_3')))), inference(resolution, [status(thm)], [c_28, c_216])).
% 3.21/1.48  tff(c_34, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~m1_subset_1(A_46, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.21/1.48  tff(c_246, plain, (r1_tarski('#skF_4', k3_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_242, c_34])).
% 3.21/1.48  tff(c_30, plain, (![A_42, B_43]: (r1_tarski(k3_tarski(A_42), k3_tarski(B_43)) | ~r1_setfam_1(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.21/1.48  tff(c_145, plain, (![A_73, C_74, B_75]: (r1_tarski(A_73, C_74) | ~r1_tarski(B_75, C_74) | ~r1_tarski(A_73, B_75))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.21/1.48  tff(c_769, plain, (![A_165, B_166, A_167]: (r1_tarski(A_165, k3_tarski(B_166)) | ~r1_tarski(A_165, k3_tarski(A_167)) | ~r1_setfam_1(A_167, B_166))), inference(resolution, [status(thm)], [c_30, c_145])).
% 3.21/1.48  tff(c_819, plain, (![B_168]: (r1_tarski('#skF_4', k3_tarski(B_168)) | ~r1_setfam_1('#skF_3', B_168))), inference(resolution, [status(thm)], [c_246, c_769])).
% 3.21/1.48  tff(c_839, plain, (![A_169]: (r1_tarski('#skF_4', A_169) | ~r1_setfam_1('#skF_3', k1_tarski(A_169)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_819])).
% 3.21/1.48  tff(c_842, plain, (r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_839])).
% 3.21/1.48  tff(c_846, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_842])).
% 3.21/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.48  
% 3.21/1.48  Inference rules
% 3.21/1.48  ----------------------
% 3.21/1.48  #Ref     : 0
% 3.21/1.48  #Sup     : 208
% 3.21/1.48  #Fact    : 0
% 3.21/1.48  #Define  : 0
% 3.21/1.48  #Split   : 2
% 3.21/1.48  #Chain   : 0
% 3.21/1.48  #Close   : 0
% 3.21/1.48  
% 3.21/1.48  Ordering : KBO
% 3.21/1.48  
% 3.21/1.48  Simplification rules
% 3.21/1.48  ----------------------
% 3.21/1.48  #Subsume      : 44
% 3.21/1.48  #Demod        : 14
% 3.21/1.48  #Tautology    : 31
% 3.21/1.48  #SimpNegUnit  : 1
% 3.21/1.48  #BackRed      : 0
% 3.21/1.48  
% 3.21/1.48  #Partial instantiations: 0
% 3.21/1.48  #Strategies tried      : 1
% 3.21/1.48  
% 3.21/1.48  Timing (in seconds)
% 3.21/1.48  ----------------------
% 3.21/1.48  Preprocessing        : 0.32
% 3.21/1.48  Parsing              : 0.17
% 3.21/1.48  CNF conversion       : 0.02
% 3.21/1.48  Main loop            : 0.41
% 3.21/1.48  Inferencing          : 0.15
% 3.21/1.48  Reduction            : 0.12
% 3.21/1.48  Demodulation         : 0.08
% 3.21/1.48  BG Simplification    : 0.02
% 3.21/1.48  Subsumption          : 0.09
% 3.21/1.48  Abstraction          : 0.02
% 3.21/1.48  MUC search           : 0.00
% 3.21/1.48  Cooper               : 0.00
% 3.21/1.48  Total                : 0.76
% 3.21/1.48  Index Insertion      : 0.00
% 3.21/1.48  Index Deletion       : 0.00
% 3.21/1.48  Index Matching       : 0.00
% 3.21/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
