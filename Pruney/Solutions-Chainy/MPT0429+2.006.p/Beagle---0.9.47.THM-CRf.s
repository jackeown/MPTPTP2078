%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:06 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   38 (  38 expanded)
%              Number of leaves         :   25 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  33 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k4_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_67,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ! [A_21] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_77,plain,(
    ! [A_44,B_45] :
      ( r2_hidden(A_44,B_45)
      | v1_xboole_0(B_45)
      | ~ m1_subset_1(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_68,plain,(
    ! [A_42,B_43] :
      ( m1_subset_1(k1_tarski(A_42),k1_zfmisc_1(B_43))
      | ~ r2_hidden(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_34,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_72,plain,(
    ~ r2_hidden(k1_xboole_0,k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_68,c_34])).

tff(c_80,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_77,c_72])).

tff(c_90,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_80])).

tff(c_58,plain,(
    ! [C_38,A_39] :
      ( r2_hidden(C_38,k1_zfmisc_1(A_39))
      | ~ r1_tarski(C_38,A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ! [A_39,C_38] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_39))
      | ~ r1_tarski(C_38,A_39) ) ),
    inference(resolution,[status(thm)],[c_58,c_2])).

tff(c_96,plain,(
    ! [C_46] : ~ r1_tarski(C_46,'#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_66])).

tff(c_101,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_96])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n006.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 19:03:37 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.20  
% 1.86/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.20  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k4_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.86/1.20  
% 1.86/1.20  %Foreground sorts:
% 1.86/1.20  
% 1.86/1.20  
% 1.86/1.20  %Background operators:
% 1.86/1.20  
% 1.86/1.20  
% 1.86/1.20  %Foreground operators:
% 1.86/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.86/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.86/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.86/1.20  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.86/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.86/1.20  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.86/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.86/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.86/1.20  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.86/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.86/1.20  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.86/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.86/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.20  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.86/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.86/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.86/1.20  
% 1.86/1.21  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.86/1.21  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 1.86/1.21  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 1.86/1.21  tff(f_52, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 1.86/1.21  tff(f_67, negated_conjecture, ~(![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_setfam_1)).
% 1.86/1.21  tff(f_46, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.86/1.21  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.86/1.21  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.86/1.21  tff(c_26, plain, (![A_21]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.86/1.21  tff(c_77, plain, (![A_44, B_45]: (r2_hidden(A_44, B_45) | v1_xboole_0(B_45) | ~m1_subset_1(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.86/1.21  tff(c_68, plain, (![A_42, B_43]: (m1_subset_1(k1_tarski(A_42), k1_zfmisc_1(B_43)) | ~r2_hidden(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.86/1.21  tff(c_34, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.86/1.21  tff(c_72, plain, (~r2_hidden(k1_xboole_0, k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_34])).
% 1.86/1.21  tff(c_80, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_77, c_72])).
% 1.86/1.21  tff(c_90, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_80])).
% 1.86/1.21  tff(c_58, plain, (![C_38, A_39]: (r2_hidden(C_38, k1_zfmisc_1(A_39)) | ~r1_tarski(C_38, A_39))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.86/1.21  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.86/1.21  tff(c_66, plain, (![A_39, C_38]: (~v1_xboole_0(k1_zfmisc_1(A_39)) | ~r1_tarski(C_38, A_39))), inference(resolution, [status(thm)], [c_58, c_2])).
% 1.86/1.21  tff(c_96, plain, (![C_46]: (~r1_tarski(C_46, '#skF_4'))), inference(resolution, [status(thm)], [c_90, c_66])).
% 1.86/1.21  tff(c_101, plain, $false, inference(resolution, [status(thm)], [c_6, c_96])).
% 1.86/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.21  
% 1.86/1.21  Inference rules
% 1.86/1.21  ----------------------
% 1.86/1.21  #Ref     : 0
% 1.86/1.21  #Sup     : 13
% 1.86/1.21  #Fact    : 0
% 1.86/1.21  #Define  : 0
% 1.86/1.21  #Split   : 0
% 1.86/1.21  #Chain   : 0
% 1.86/1.21  #Close   : 0
% 1.86/1.21  
% 1.86/1.21  Ordering : KBO
% 1.86/1.21  
% 1.86/1.21  Simplification rules
% 1.86/1.21  ----------------------
% 1.86/1.21  #Subsume      : 1
% 1.86/1.21  #Demod        : 1
% 1.86/1.21  #Tautology    : 5
% 1.86/1.21  #SimpNegUnit  : 0
% 1.86/1.21  #BackRed      : 0
% 1.86/1.21  
% 1.86/1.21  #Partial instantiations: 0
% 1.86/1.21  #Strategies tried      : 1
% 1.86/1.21  
% 1.86/1.21  Timing (in seconds)
% 1.86/1.21  ----------------------
% 1.86/1.21  Preprocessing        : 0.32
% 1.86/1.21  Parsing              : 0.16
% 1.86/1.21  CNF conversion       : 0.02
% 1.86/1.21  Main loop            : 0.14
% 1.86/1.21  Inferencing          : 0.05
% 1.86/1.21  Reduction            : 0.05
% 1.86/1.21  Demodulation         : 0.04
% 1.86/1.21  BG Simplification    : 0.01
% 1.86/1.21  Subsumption          : 0.02
% 1.86/1.21  Abstraction          : 0.01
% 1.86/1.21  MUC search           : 0.00
% 1.86/1.21  Cooper               : 0.00
% 1.86/1.21  Total                : 0.49
% 1.86/1.21  Index Insertion      : 0.00
% 1.86/1.21  Index Deletion       : 0.00
% 1.86/1.21  Index Matching       : 0.00
% 1.86/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
