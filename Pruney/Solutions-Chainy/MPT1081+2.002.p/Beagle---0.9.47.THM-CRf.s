%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:16 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   40 (  84 expanded)
%              Number of leaves         :   23 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   57 ( 170 expanded)
%              Number of equality atoms :    8 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(m1_funct_2,type,(
    m1_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => m1_funct_2(k1_tarski(C),A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ( m1_funct_2(C,A,B)
      <=> ! [D] :
            ( m1_subset_1(D,C)
           => ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_2)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_14,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_tarski(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,(
    ~ m1_funct_2(k1_tarski('#skF_6'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_40,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_121,plain,(
    ! [A_41,B_42,C_43] :
      ( m1_subset_1('#skF_3'(A_41,B_42,C_43),C_43)
      | m1_funct_2(C_43,A_41,B_42)
      | v1_xboole_0(C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_60,plain,(
    ! [B_23,A_24] :
      ( r2_hidden(B_23,A_24)
      | ~ m1_subset_1(B_23,A_24)
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_64,plain,(
    ! [B_23,A_1] :
      ( B_23 = A_1
      | ~ m1_subset_1(B_23,k1_tarski(A_1))
      | v1_xboole_0(k1_tarski(A_1)) ) ),
    inference(resolution,[status(thm)],[c_60,c_2])).

tff(c_67,plain,(
    ! [B_23,A_1] :
      ( B_23 = A_1
      | ~ m1_subset_1(B_23,k1_tarski(A_1)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_64])).

tff(c_127,plain,(
    ! [A_41,B_42,A_1] :
      ( '#skF_3'(A_41,B_42,k1_tarski(A_1)) = A_1
      | m1_funct_2(k1_tarski(A_1),A_41,B_42)
      | v1_xboole_0(k1_tarski(A_1)) ) ),
    inference(resolution,[status(thm)],[c_121,c_67])).

tff(c_136,plain,(
    ! [A_44,B_45,A_46] :
      ( '#skF_3'(A_44,B_45,k1_tarski(A_46)) = A_46
      | m1_funct_2(k1_tarski(A_46),A_44,B_45) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_127])).

tff(c_144,plain,(
    '#skF_3'('#skF_4','#skF_5',k1_tarski('#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_136,c_34])).

tff(c_38,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_331,plain,(
    ! [A_82,B_83,C_84] :
      ( ~ m1_subset_1('#skF_3'(A_82,B_83,C_84),k1_zfmisc_1(k2_zfmisc_1(A_82,B_83)))
      | ~ v1_funct_2('#skF_3'(A_82,B_83,C_84),A_82,B_83)
      | ~ v1_funct_1('#skF_3'(A_82,B_83,C_84))
      | m1_funct_2(C_84,A_82,B_83)
      | v1_xboole_0(C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_344,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_3'('#skF_4','#skF_5',k1_tarski('#skF_6')),'#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_3'('#skF_4','#skF_5',k1_tarski('#skF_6')))
    | m1_funct_2(k1_tarski('#skF_6'),'#skF_4','#skF_5')
    | v1_xboole_0(k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_331])).

tff(c_356,plain,
    ( m1_funct_2(k1_tarski('#skF_6'),'#skF_4','#skF_5')
    | v1_xboole_0(k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_144,c_38,c_144,c_36,c_344])).

tff(c_358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_34,c_356])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:18:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.36  
% 2.36/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.36  %$ v1_funct_2 > m1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.36/1.36  
% 2.36/1.36  %Foreground sorts:
% 2.36/1.36  
% 2.36/1.36  
% 2.36/1.36  %Background operators:
% 2.36/1.36  
% 2.36/1.36  
% 2.36/1.36  %Foreground operators:
% 2.36/1.36  tff(m1_funct_2, type, m1_funct_2: ($i * $i * $i) > $o).
% 2.36/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.36/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.36/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.36/1.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.36/1.36  tff('#skF_6', type, '#skF_6': $i).
% 2.36/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.36/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.36/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.36/1.36  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.36/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.36/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.36/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.36/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.36  
% 2.36/1.38  tff(f_35, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.36/1.38  tff(f_71, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => m1_funct_2(k1_tarski(C), A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t198_funct_2)).
% 2.36/1.38  tff(f_62, axiom, (![A, B, C]: (~v1_xboole_0(C) => (m1_funct_2(C, A, B) <=> (![D]: (m1_subset_1(D, C) => ((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_funct_2)).
% 2.36/1.38  tff(f_48, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.36/1.38  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.36/1.38  tff(c_14, plain, (![A_6]: (~v1_xboole_0(k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.36/1.38  tff(c_34, plain, (~m1_funct_2(k1_tarski('#skF_6'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.36/1.38  tff(c_40, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.36/1.38  tff(c_121, plain, (![A_41, B_42, C_43]: (m1_subset_1('#skF_3'(A_41, B_42, C_43), C_43) | m1_funct_2(C_43, A_41, B_42) | v1_xboole_0(C_43))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.36/1.38  tff(c_60, plain, (![B_23, A_24]: (r2_hidden(B_23, A_24) | ~m1_subset_1(B_23, A_24) | v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.36/1.38  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.36/1.38  tff(c_64, plain, (![B_23, A_1]: (B_23=A_1 | ~m1_subset_1(B_23, k1_tarski(A_1)) | v1_xboole_0(k1_tarski(A_1)))), inference(resolution, [status(thm)], [c_60, c_2])).
% 2.36/1.38  tff(c_67, plain, (![B_23, A_1]: (B_23=A_1 | ~m1_subset_1(B_23, k1_tarski(A_1)))), inference(negUnitSimplification, [status(thm)], [c_14, c_64])).
% 2.36/1.38  tff(c_127, plain, (![A_41, B_42, A_1]: ('#skF_3'(A_41, B_42, k1_tarski(A_1))=A_1 | m1_funct_2(k1_tarski(A_1), A_41, B_42) | v1_xboole_0(k1_tarski(A_1)))), inference(resolution, [status(thm)], [c_121, c_67])).
% 2.36/1.38  tff(c_136, plain, (![A_44, B_45, A_46]: ('#skF_3'(A_44, B_45, k1_tarski(A_46))=A_46 | m1_funct_2(k1_tarski(A_46), A_44, B_45))), inference(negUnitSimplification, [status(thm)], [c_14, c_127])).
% 2.36/1.38  tff(c_144, plain, ('#skF_3'('#skF_4', '#skF_5', k1_tarski('#skF_6'))='#skF_6'), inference(resolution, [status(thm)], [c_136, c_34])).
% 2.36/1.38  tff(c_38, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.36/1.38  tff(c_36, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.36/1.38  tff(c_331, plain, (![A_82, B_83, C_84]: (~m1_subset_1('#skF_3'(A_82, B_83, C_84), k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))) | ~v1_funct_2('#skF_3'(A_82, B_83, C_84), A_82, B_83) | ~v1_funct_1('#skF_3'(A_82, B_83, C_84)) | m1_funct_2(C_84, A_82, B_83) | v1_xboole_0(C_84))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.36/1.38  tff(c_344, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_3'('#skF_4', '#skF_5', k1_tarski('#skF_6')), '#skF_4', '#skF_5') | ~v1_funct_1('#skF_3'('#skF_4', '#skF_5', k1_tarski('#skF_6'))) | m1_funct_2(k1_tarski('#skF_6'), '#skF_4', '#skF_5') | v1_xboole_0(k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_144, c_331])).
% 2.36/1.38  tff(c_356, plain, (m1_funct_2(k1_tarski('#skF_6'), '#skF_4', '#skF_5') | v1_xboole_0(k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_144, c_38, c_144, c_36, c_344])).
% 2.36/1.38  tff(c_358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_34, c_356])).
% 2.36/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.38  
% 2.36/1.38  Inference rules
% 2.36/1.38  ----------------------
% 2.36/1.38  #Ref     : 0
% 2.36/1.38  #Sup     : 67
% 2.36/1.38  #Fact    : 0
% 2.36/1.38  #Define  : 0
% 2.36/1.38  #Split   : 1
% 2.36/1.38  #Chain   : 0
% 2.36/1.38  #Close   : 0
% 2.36/1.38  
% 2.36/1.38  Ordering : KBO
% 2.36/1.38  
% 2.36/1.38  Simplification rules
% 2.36/1.38  ----------------------
% 2.36/1.38  #Subsume      : 3
% 2.36/1.38  #Demod        : 16
% 2.36/1.38  #Tautology    : 31
% 2.36/1.38  #SimpNegUnit  : 17
% 2.36/1.38  #BackRed      : 0
% 2.36/1.38  
% 2.36/1.38  #Partial instantiations: 0
% 2.36/1.38  #Strategies tried      : 1
% 2.36/1.38  
% 2.36/1.38  Timing (in seconds)
% 2.36/1.38  ----------------------
% 2.36/1.38  Preprocessing        : 0.30
% 2.36/1.38  Parsing              : 0.17
% 2.36/1.38  CNF conversion       : 0.02
% 2.36/1.38  Main loop            : 0.25
% 2.36/1.38  Inferencing          : 0.10
% 2.36/1.38  Reduction            : 0.07
% 2.36/1.38  Demodulation         : 0.04
% 2.36/1.38  BG Simplification    : 0.02
% 2.36/1.38  Subsumption          : 0.05
% 2.36/1.38  Abstraction          : 0.01
% 2.36/1.38  MUC search           : 0.00
% 2.36/1.38  Cooper               : 0.00
% 2.36/1.38  Total                : 0.58
% 2.36/1.38  Index Insertion      : 0.00
% 2.36/1.38  Index Deletion       : 0.00
% 2.36/1.38  Index Matching       : 0.00
% 2.36/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
