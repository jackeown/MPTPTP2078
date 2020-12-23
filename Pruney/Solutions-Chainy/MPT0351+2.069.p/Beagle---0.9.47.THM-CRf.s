%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:46 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   61 (  69 expanded)
%              Number of leaves         :   36 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 (  82 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_77,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_79,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_82,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_62,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_62,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_52,plain,(
    ! [A_59] : k2_subset_1(A_59) = A_59 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_54,plain,(
    ! [A_60] : m1_subset_1(k2_subset_1(A_60),k1_zfmisc_1(A_60)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_64,plain,(
    ! [A_60] : m1_subset_1(A_60,k1_zfmisc_1(A_60)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_54])).

tff(c_380,plain,(
    ! [A_137,B_138,C_139] :
      ( k4_subset_1(A_137,B_138,C_139) = k2_xboole_0(B_138,C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(A_137))
      | ~ m1_subset_1(B_138,k1_zfmisc_1(A_137)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_400,plain,(
    ! [A_140,B_141] :
      ( k4_subset_1(A_140,B_141,A_140) = k2_xboole_0(B_141,A_140)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(A_140)) ) ),
    inference(resolution,[status(thm)],[c_64,c_380])).

tff(c_420,plain,(
    k4_subset_1('#skF_6','#skF_7','#skF_6') = k2_xboole_0('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_400])).

tff(c_60,plain,(
    k4_subset_1('#skF_6','#skF_7',k2_subset_1('#skF_6')) != k2_subset_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_63,plain,(
    k4_subset_1('#skF_6','#skF_7','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_60])).

tff(c_430,plain,(
    k2_xboole_0('#skF_7','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_63])).

tff(c_56,plain,(
    ! [A_61] : ~ v1_xboole_0(k1_zfmisc_1(A_61)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_42,plain,(
    ! [A_56] : k3_tarski(k1_zfmisc_1(A_56)) = A_56 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_46,plain,(
    ! [B_58,A_57] :
      ( r2_hidden(B_58,A_57)
      | ~ m1_subset_1(B_58,A_57)
      | v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_170,plain,(
    ! [C_95,A_96,D_97] :
      ( r2_hidden(C_95,k3_tarski(A_96))
      | ~ r2_hidden(D_97,A_96)
      | ~ r2_hidden(C_95,D_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_300,plain,(
    ! [C_127,A_128,B_129] :
      ( r2_hidden(C_127,k3_tarski(A_128))
      | ~ r2_hidden(C_127,B_129)
      | ~ m1_subset_1(B_129,A_128)
      | v1_xboole_0(A_128) ) ),
    inference(resolution,[status(thm)],[c_46,c_170])).

tff(c_708,plain,(
    ! [A_180,B_181,A_182] :
      ( r2_hidden('#skF_1'(A_180,B_181),k3_tarski(A_182))
      | ~ m1_subset_1(A_180,A_182)
      | v1_xboole_0(A_182)
      | r1_tarski(A_180,B_181) ) ),
    inference(resolution,[status(thm)],[c_6,c_300])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_734,plain,(
    ! [A_183,A_184] :
      ( ~ m1_subset_1(A_183,A_184)
      | v1_xboole_0(A_184)
      | r1_tarski(A_183,k3_tarski(A_184)) ) ),
    inference(resolution,[status(thm)],[c_708,c_4])).

tff(c_755,plain,(
    ! [A_183,A_56] :
      ( ~ m1_subset_1(A_183,k1_zfmisc_1(A_56))
      | v1_xboole_0(k1_zfmisc_1(A_56))
      | r1_tarski(A_183,A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_734])).

tff(c_771,plain,(
    ! [A_186,A_187] :
      ( ~ m1_subset_1(A_186,k1_zfmisc_1(A_187))
      | r1_tarski(A_186,A_187) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_755])).

tff(c_810,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_771])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_817,plain,(
    k2_xboole_0('#skF_7','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_810,c_8])).

tff(c_824,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_430,c_817])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:36:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.78  
% 3.31/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.78  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 3.31/1.78  
% 3.31/1.78  %Foreground sorts:
% 3.31/1.78  
% 3.31/1.78  
% 3.31/1.78  %Background operators:
% 3.31/1.78  
% 3.31/1.78  
% 3.31/1.78  %Foreground operators:
% 3.31/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.31/1.78  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.31/1.78  tff('#skF_7', type, '#skF_7': $i).
% 3.31/1.78  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.31/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.31/1.78  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.31/1.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.31/1.78  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.31/1.78  tff('#skF_6', type, '#skF_6': $i).
% 3.31/1.78  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.31/1.78  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.31/1.78  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.31/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.31/1.78  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.31/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.78  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.31/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.78  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.31/1.78  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.31/1.78  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.31/1.78  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.31/1.78  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.31/1.78  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.31/1.78  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.31/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.31/1.78  
% 3.31/1.79  tff(f_93, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 3.31/1.79  tff(f_77, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.31/1.79  tff(f_79, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.31/1.79  tff(f_88, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.31/1.79  tff(f_82, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.31/1.79  tff(f_62, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 3.31/1.79  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.31/1.79  tff(f_75, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.31/1.79  tff(f_58, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 3.31/1.79  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.31/1.79  tff(c_62, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.31/1.79  tff(c_52, plain, (![A_59]: (k2_subset_1(A_59)=A_59)), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.31/1.79  tff(c_54, plain, (![A_60]: (m1_subset_1(k2_subset_1(A_60), k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.31/1.79  tff(c_64, plain, (![A_60]: (m1_subset_1(A_60, k1_zfmisc_1(A_60)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_54])).
% 3.31/1.79  tff(c_380, plain, (![A_137, B_138, C_139]: (k4_subset_1(A_137, B_138, C_139)=k2_xboole_0(B_138, C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(A_137)) | ~m1_subset_1(B_138, k1_zfmisc_1(A_137)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.31/1.79  tff(c_400, plain, (![A_140, B_141]: (k4_subset_1(A_140, B_141, A_140)=k2_xboole_0(B_141, A_140) | ~m1_subset_1(B_141, k1_zfmisc_1(A_140)))), inference(resolution, [status(thm)], [c_64, c_380])).
% 3.31/1.79  tff(c_420, plain, (k4_subset_1('#skF_6', '#skF_7', '#skF_6')=k2_xboole_0('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_62, c_400])).
% 3.31/1.79  tff(c_60, plain, (k4_subset_1('#skF_6', '#skF_7', k2_subset_1('#skF_6'))!=k2_subset_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.31/1.79  tff(c_63, plain, (k4_subset_1('#skF_6', '#skF_7', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_60])).
% 3.31/1.79  tff(c_430, plain, (k2_xboole_0('#skF_7', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_420, c_63])).
% 3.31/1.79  tff(c_56, plain, (![A_61]: (~v1_xboole_0(k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.31/1.79  tff(c_42, plain, (![A_56]: (k3_tarski(k1_zfmisc_1(A_56))=A_56)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.31/1.79  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.31/1.79  tff(c_46, plain, (![B_58, A_57]: (r2_hidden(B_58, A_57) | ~m1_subset_1(B_58, A_57) | v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.31/1.79  tff(c_170, plain, (![C_95, A_96, D_97]: (r2_hidden(C_95, k3_tarski(A_96)) | ~r2_hidden(D_97, A_96) | ~r2_hidden(C_95, D_97))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.31/1.79  tff(c_300, plain, (![C_127, A_128, B_129]: (r2_hidden(C_127, k3_tarski(A_128)) | ~r2_hidden(C_127, B_129) | ~m1_subset_1(B_129, A_128) | v1_xboole_0(A_128))), inference(resolution, [status(thm)], [c_46, c_170])).
% 3.31/1.79  tff(c_708, plain, (![A_180, B_181, A_182]: (r2_hidden('#skF_1'(A_180, B_181), k3_tarski(A_182)) | ~m1_subset_1(A_180, A_182) | v1_xboole_0(A_182) | r1_tarski(A_180, B_181))), inference(resolution, [status(thm)], [c_6, c_300])).
% 3.31/1.79  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.31/1.79  tff(c_734, plain, (![A_183, A_184]: (~m1_subset_1(A_183, A_184) | v1_xboole_0(A_184) | r1_tarski(A_183, k3_tarski(A_184)))), inference(resolution, [status(thm)], [c_708, c_4])).
% 3.31/1.79  tff(c_755, plain, (![A_183, A_56]: (~m1_subset_1(A_183, k1_zfmisc_1(A_56)) | v1_xboole_0(k1_zfmisc_1(A_56)) | r1_tarski(A_183, A_56))), inference(superposition, [status(thm), theory('equality')], [c_42, c_734])).
% 3.31/1.79  tff(c_771, plain, (![A_186, A_187]: (~m1_subset_1(A_186, k1_zfmisc_1(A_187)) | r1_tarski(A_186, A_187))), inference(negUnitSimplification, [status(thm)], [c_56, c_755])).
% 3.31/1.79  tff(c_810, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_62, c_771])).
% 3.31/1.79  tff(c_8, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.31/1.79  tff(c_817, plain, (k2_xboole_0('#skF_7', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_810, c_8])).
% 3.31/1.79  tff(c_824, plain, $false, inference(negUnitSimplification, [status(thm)], [c_430, c_817])).
% 3.31/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.79  
% 3.31/1.79  Inference rules
% 3.31/1.79  ----------------------
% 3.31/1.79  #Ref     : 0
% 3.31/1.79  #Sup     : 176
% 3.31/1.79  #Fact    : 0
% 3.31/1.79  #Define  : 0
% 3.31/1.79  #Split   : 1
% 3.31/1.79  #Chain   : 0
% 3.31/1.79  #Close   : 0
% 3.31/1.79  
% 3.31/1.79  Ordering : KBO
% 3.31/1.79  
% 3.31/1.79  Simplification rules
% 3.31/1.79  ----------------------
% 3.31/1.79  #Subsume      : 15
% 3.31/1.79  #Demod        : 34
% 3.31/1.79  #Tautology    : 43
% 3.31/1.79  #SimpNegUnit  : 20
% 3.31/1.79  #BackRed      : 1
% 3.31/1.79  
% 3.31/1.79  #Partial instantiations: 0
% 3.31/1.79  #Strategies tried      : 1
% 3.31/1.79  
% 3.31/1.79  Timing (in seconds)
% 3.31/1.79  ----------------------
% 3.31/1.80  Preprocessing        : 0.51
% 3.31/1.80  Parsing              : 0.27
% 3.31/1.80  CNF conversion       : 0.04
% 3.31/1.80  Main loop            : 0.41
% 3.31/1.80  Inferencing          : 0.15
% 3.31/1.80  Reduction            : 0.11
% 3.31/1.80  Demodulation         : 0.08
% 3.31/1.80  BG Simplification    : 0.03
% 3.31/1.80  Subsumption          : 0.09
% 3.31/1.80  Abstraction          : 0.03
% 3.31/1.80  MUC search           : 0.00
% 3.31/1.80  Cooper               : 0.00
% 3.31/1.80  Total                : 0.95
% 3.31/1.80  Index Insertion      : 0.00
% 3.31/1.80  Index Deletion       : 0.00
% 3.31/1.80  Index Matching       : 0.00
% 3.31/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
