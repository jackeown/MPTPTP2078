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
% DateTime   : Thu Dec  3 09:56:59 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   63 (  78 expanded)
%              Number of leaves         :   31 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :   83 ( 131 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,A)
       => ( A != k1_xboole_0
         => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_85,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_80,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_82,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_52,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_90,plain,(
    ! [B_58,A_59] :
      ( v1_xboole_0(B_58)
      | ~ m1_subset_1(B_58,A_59)
      | ~ v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_102,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_90])).

tff(c_103,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_36,plain,(
    ! [B_43,A_42] :
      ( r2_hidden(B_43,A_42)
      | ~ m1_subset_1(B_43,A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_280,plain,(
    ! [A_110,B_111,C_112] :
      ( r1_tarski(k2_tarski(A_110,B_111),C_112)
      | ~ r2_hidden(B_111,C_112)
      | ~ r2_hidden(A_110,C_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_289,plain,(
    ! [A_9,C_112] :
      ( r1_tarski(k1_tarski(A_9),C_112)
      | ~ r2_hidden(A_9,C_112)
      | ~ r2_hidden(A_9,C_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_280])).

tff(c_46,plain,(
    ! [A_46] : ~ v1_xboole_0(k1_zfmisc_1(A_46)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_42,plain,(
    ! [A_44] : k2_subset_1(A_44) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_44,plain,(
    ! [A_45] : m1_subset_1(k2_subset_1(A_45),k1_zfmisc_1(A_45)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_53,plain,(
    ! [A_45] : m1_subset_1(A_45,k1_zfmisc_1(A_45)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44])).

tff(c_32,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(k1_zfmisc_1(A_40),k1_zfmisc_1(B_41))
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_246,plain,(
    ! [C_103,B_104,A_105] :
      ( r2_hidden(C_103,B_104)
      | ~ r2_hidden(C_103,A_105)
      | ~ r1_tarski(A_105,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_317,plain,(
    ! [B_121,B_122,A_123] :
      ( r2_hidden(B_121,B_122)
      | ~ r1_tarski(A_123,B_122)
      | ~ m1_subset_1(B_121,A_123)
      | v1_xboole_0(A_123) ) ),
    inference(resolution,[status(thm)],[c_36,c_246])).

tff(c_327,plain,(
    ! [B_121,B_41,A_40] :
      ( r2_hidden(B_121,k1_zfmisc_1(B_41))
      | ~ m1_subset_1(B_121,k1_zfmisc_1(A_40))
      | v1_xboole_0(k1_zfmisc_1(A_40))
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(resolution,[status(thm)],[c_32,c_317])).

tff(c_395,plain,(
    ! [B_138,B_139,A_140] :
      ( r2_hidden(B_138,k1_zfmisc_1(B_139))
      | ~ m1_subset_1(B_138,k1_zfmisc_1(A_140))
      | ~ r1_tarski(A_140,B_139) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_327])).

tff(c_418,plain,(
    ! [A_147,B_148] :
      ( r2_hidden(A_147,k1_zfmisc_1(B_148))
      | ~ r1_tarski(A_147,B_148) ) ),
    inference(resolution,[status(thm)],[c_53,c_395])).

tff(c_34,plain,(
    ! [B_43,A_42] :
      ( m1_subset_1(B_43,A_42)
      | ~ r2_hidden(B_43,A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_427,plain,(
    ! [A_147,B_148] :
      ( m1_subset_1(A_147,k1_zfmisc_1(B_148))
      | v1_xboole_0(k1_zfmisc_1(B_148))
      | ~ r1_tarski(A_147,B_148) ) ),
    inference(resolution,[status(thm)],[c_418,c_34])).

tff(c_437,plain,(
    ! [A_149,B_150] :
      ( m1_subset_1(A_149,k1_zfmisc_1(B_150))
      | ~ r1_tarski(A_149,B_150) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_427])).

tff(c_48,plain,(
    ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_455,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_437,c_48])).

tff(c_462,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_289,c_455])).

tff(c_466,plain,
    ( ~ m1_subset_1('#skF_3','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_462])).

tff(c_469,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_466])).

tff(c_471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_469])).

tff(c_473,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_484,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_473,c_8])).

tff(c_488,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_484])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:33:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.49  
% 2.71/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.49  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.71/1.49  
% 2.71/1.49  %Foreground sorts:
% 2.71/1.49  
% 2.71/1.49  
% 2.71/1.49  %Background operators:
% 2.71/1.49  
% 2.71/1.49  
% 2.71/1.49  %Foreground operators:
% 2.71/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.71/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.71/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.71/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.71/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.71/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.71/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.71/1.49  tff('#skF_2', type, '#skF_2': $i).
% 2.71/1.49  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.71/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.71/1.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.71/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.71/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.71/1.49  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.71/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.71/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.71/1.49  
% 2.71/1.50  tff(f_93, negated_conjecture, ~(![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 2.71/1.50  tff(f_78, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.71/1.50  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.71/1.50  tff(f_61, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.71/1.50  tff(f_85, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.71/1.50  tff(f_80, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.71/1.50  tff(f_82, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.71/1.50  tff(f_65, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.71/1.50  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.71/1.50  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.71/1.50  tff(c_50, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.71/1.50  tff(c_52, plain, (m1_subset_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.71/1.50  tff(c_90, plain, (![B_58, A_59]: (v1_xboole_0(B_58) | ~m1_subset_1(B_58, A_59) | ~v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.71/1.50  tff(c_102, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_90])).
% 2.71/1.50  tff(c_103, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_102])).
% 2.71/1.50  tff(c_36, plain, (![B_43, A_42]: (r2_hidden(B_43, A_42) | ~m1_subset_1(B_43, A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.71/1.50  tff(c_12, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.71/1.50  tff(c_280, plain, (![A_110, B_111, C_112]: (r1_tarski(k2_tarski(A_110, B_111), C_112) | ~r2_hidden(B_111, C_112) | ~r2_hidden(A_110, C_112))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.71/1.50  tff(c_289, plain, (![A_9, C_112]: (r1_tarski(k1_tarski(A_9), C_112) | ~r2_hidden(A_9, C_112) | ~r2_hidden(A_9, C_112))), inference(superposition, [status(thm), theory('equality')], [c_12, c_280])).
% 2.71/1.50  tff(c_46, plain, (![A_46]: (~v1_xboole_0(k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.71/1.50  tff(c_42, plain, (![A_44]: (k2_subset_1(A_44)=A_44)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.71/1.50  tff(c_44, plain, (![A_45]: (m1_subset_1(k2_subset_1(A_45), k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.71/1.50  tff(c_53, plain, (![A_45]: (m1_subset_1(A_45, k1_zfmisc_1(A_45)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44])).
% 2.71/1.50  tff(c_32, plain, (![A_40, B_41]: (r1_tarski(k1_zfmisc_1(A_40), k1_zfmisc_1(B_41)) | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.71/1.50  tff(c_246, plain, (![C_103, B_104, A_105]: (r2_hidden(C_103, B_104) | ~r2_hidden(C_103, A_105) | ~r1_tarski(A_105, B_104))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.71/1.50  tff(c_317, plain, (![B_121, B_122, A_123]: (r2_hidden(B_121, B_122) | ~r1_tarski(A_123, B_122) | ~m1_subset_1(B_121, A_123) | v1_xboole_0(A_123))), inference(resolution, [status(thm)], [c_36, c_246])).
% 2.71/1.50  tff(c_327, plain, (![B_121, B_41, A_40]: (r2_hidden(B_121, k1_zfmisc_1(B_41)) | ~m1_subset_1(B_121, k1_zfmisc_1(A_40)) | v1_xboole_0(k1_zfmisc_1(A_40)) | ~r1_tarski(A_40, B_41))), inference(resolution, [status(thm)], [c_32, c_317])).
% 2.71/1.50  tff(c_395, plain, (![B_138, B_139, A_140]: (r2_hidden(B_138, k1_zfmisc_1(B_139)) | ~m1_subset_1(B_138, k1_zfmisc_1(A_140)) | ~r1_tarski(A_140, B_139))), inference(negUnitSimplification, [status(thm)], [c_46, c_327])).
% 2.71/1.50  tff(c_418, plain, (![A_147, B_148]: (r2_hidden(A_147, k1_zfmisc_1(B_148)) | ~r1_tarski(A_147, B_148))), inference(resolution, [status(thm)], [c_53, c_395])).
% 2.71/1.50  tff(c_34, plain, (![B_43, A_42]: (m1_subset_1(B_43, A_42) | ~r2_hidden(B_43, A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.71/1.50  tff(c_427, plain, (![A_147, B_148]: (m1_subset_1(A_147, k1_zfmisc_1(B_148)) | v1_xboole_0(k1_zfmisc_1(B_148)) | ~r1_tarski(A_147, B_148))), inference(resolution, [status(thm)], [c_418, c_34])).
% 2.71/1.50  tff(c_437, plain, (![A_149, B_150]: (m1_subset_1(A_149, k1_zfmisc_1(B_150)) | ~r1_tarski(A_149, B_150))), inference(negUnitSimplification, [status(thm)], [c_46, c_427])).
% 2.71/1.50  tff(c_48, plain, (~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.71/1.50  tff(c_455, plain, (~r1_tarski(k1_tarski('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_437, c_48])).
% 2.71/1.50  tff(c_462, plain, (~r2_hidden('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_289, c_455])).
% 2.71/1.50  tff(c_466, plain, (~m1_subset_1('#skF_3', '#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_462])).
% 2.71/1.50  tff(c_469, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_466])).
% 2.71/1.50  tff(c_471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_469])).
% 2.71/1.50  tff(c_473, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_102])).
% 2.71/1.50  tff(c_8, plain, (![A_6]: (k1_xboole_0=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.71/1.50  tff(c_484, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_473, c_8])).
% 2.71/1.50  tff(c_488, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_484])).
% 2.71/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.50  
% 2.71/1.50  Inference rules
% 2.71/1.50  ----------------------
% 2.71/1.50  #Ref     : 0
% 2.71/1.50  #Sup     : 94
% 2.71/1.50  #Fact    : 0
% 2.71/1.50  #Define  : 0
% 2.71/1.50  #Split   : 1
% 2.71/1.50  #Chain   : 0
% 2.71/1.50  #Close   : 0
% 2.71/1.50  
% 2.71/1.50  Ordering : KBO
% 2.71/1.50  
% 2.71/1.50  Simplification rules
% 2.71/1.50  ----------------------
% 2.71/1.50  #Subsume      : 28
% 2.71/1.50  #Demod        : 7
% 2.71/1.50  #Tautology    : 29
% 2.71/1.50  #SimpNegUnit  : 12
% 2.71/1.50  #BackRed      : 0
% 2.71/1.50  
% 2.71/1.50  #Partial instantiations: 0
% 2.71/1.50  #Strategies tried      : 1
% 2.71/1.50  
% 2.71/1.50  Timing (in seconds)
% 2.71/1.50  ----------------------
% 2.71/1.50  Preprocessing        : 0.41
% 2.71/1.50  Parsing              : 0.23
% 2.71/1.51  CNF conversion       : 0.03
% 2.71/1.51  Main loop            : 0.27
% 2.71/1.51  Inferencing          : 0.10
% 2.71/1.51  Reduction            : 0.08
% 2.71/1.51  Demodulation         : 0.05
% 2.71/1.51  BG Simplification    : 0.02
% 2.71/1.51  Subsumption          : 0.05
% 2.71/1.51  Abstraction          : 0.01
% 2.71/1.51  MUC search           : 0.00
% 2.71/1.51  Cooper               : 0.00
% 2.71/1.51  Total                : 0.71
% 2.71/1.51  Index Insertion      : 0.00
% 2.71/1.51  Index Deletion       : 0.00
% 2.71/1.51  Index Matching       : 0.00
% 2.71/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
