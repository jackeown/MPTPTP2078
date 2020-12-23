%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:16 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   40 (  84 expanded)
%              Number of leaves         :   23 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   54 ( 161 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => m1_funct_2(k1_tarski(C),A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ( m1_funct_2(C,A,B)
      <=> ! [D] :
            ( m1_subset_1(D,C)
           => ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_14,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_tarski(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    ~ m1_funct_2(k1_tarski('#skF_6'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_34,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_58,plain,(
    ! [A_29,B_30,C_31] :
      ( m1_subset_1('#skF_3'(A_29,B_30,C_31),C_31)
      | m1_funct_2(C_31,A_29,B_30)
      | v1_xboole_0(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_43,plain,(
    ! [A_19,B_20] :
      ( r2_hidden(A_19,B_20)
      | v1_xboole_0(B_20)
      | ~ m1_subset_1(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_47,plain,(
    ! [A_19,A_1] :
      ( A_19 = A_1
      | v1_xboole_0(k1_tarski(A_1))
      | ~ m1_subset_1(A_19,k1_tarski(A_1)) ) ),
    inference(resolution,[status(thm)],[c_43,c_2])).

tff(c_50,plain,(
    ! [A_19,A_1] :
      ( A_19 = A_1
      | ~ m1_subset_1(A_19,k1_tarski(A_1)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_47])).

tff(c_64,plain,(
    ! [A_29,B_30,A_1] :
      ( '#skF_3'(A_29,B_30,k1_tarski(A_1)) = A_1
      | m1_funct_2(k1_tarski(A_1),A_29,B_30)
      | v1_xboole_0(k1_tarski(A_1)) ) ),
    inference(resolution,[status(thm)],[c_58,c_50])).

tff(c_69,plain,(
    ! [A_32,B_33,A_34] :
      ( '#skF_3'(A_32,B_33,k1_tarski(A_34)) = A_34
      | m1_funct_2(k1_tarski(A_34),A_32,B_33) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_64])).

tff(c_73,plain,(
    '#skF_3'('#skF_4','#skF_5',k1_tarski('#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_69,c_28])).

tff(c_32,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_30,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_335,plain,(
    ! [A_92,B_93,C_94] :
      ( ~ m1_subset_1('#skF_3'(A_92,B_93,C_94),k1_zfmisc_1(k2_zfmisc_1(A_92,B_93)))
      | ~ v1_funct_2('#skF_3'(A_92,B_93,C_94),A_92,B_93)
      | ~ v1_funct_1('#skF_3'(A_92,B_93,C_94))
      | m1_funct_2(C_94,A_92,B_93)
      | v1_xboole_0(C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_348,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_3'('#skF_4','#skF_5',k1_tarski('#skF_6')),'#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_3'('#skF_4','#skF_5',k1_tarski('#skF_6')))
    | m1_funct_2(k1_tarski('#skF_6'),'#skF_4','#skF_5')
    | v1_xboole_0(k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_335])).

tff(c_357,plain,
    ( m1_funct_2(k1_tarski('#skF_6'),'#skF_4','#skF_5')
    | v1_xboole_0(k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_73,c_32,c_73,c_30,c_348])).

tff(c_359,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_28,c_357])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:18:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.27  
% 2.06/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.28  %$ v1_funct_2 > m1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.06/1.28  
% 2.06/1.28  %Foreground sorts:
% 2.06/1.28  
% 2.06/1.28  
% 2.06/1.28  %Background operators:
% 2.06/1.28  
% 2.06/1.28  
% 2.06/1.28  %Foreground operators:
% 2.06/1.28  tff(m1_funct_2, type, m1_funct_2: ($i * $i * $i) > $o).
% 2.06/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.06/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.06/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.06/1.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.06/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.06/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.06/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.06/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.06/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.06/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.06/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.06/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.06/1.28  
% 2.06/1.28  tff(f_35, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.06/1.28  tff(f_64, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => m1_funct_2(k1_tarski(C), A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t198_funct_2)).
% 2.06/1.28  tff(f_55, axiom, (![A, B, C]: (~v1_xboole_0(C) => (m1_funct_2(C, A, B) <=> (![D]: (m1_subset_1(D, C) => ((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_funct_2)).
% 2.06/1.28  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.06/1.28  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.06/1.28  tff(c_14, plain, (![A_6]: (~v1_xboole_0(k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.06/1.29  tff(c_28, plain, (~m1_funct_2(k1_tarski('#skF_6'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.06/1.29  tff(c_34, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.06/1.29  tff(c_58, plain, (![A_29, B_30, C_31]: (m1_subset_1('#skF_3'(A_29, B_30, C_31), C_31) | m1_funct_2(C_31, A_29, B_30) | v1_xboole_0(C_31))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.06/1.29  tff(c_43, plain, (![A_19, B_20]: (r2_hidden(A_19, B_20) | v1_xboole_0(B_20) | ~m1_subset_1(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.06/1.29  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.06/1.29  tff(c_47, plain, (![A_19, A_1]: (A_19=A_1 | v1_xboole_0(k1_tarski(A_1)) | ~m1_subset_1(A_19, k1_tarski(A_1)))), inference(resolution, [status(thm)], [c_43, c_2])).
% 2.06/1.29  tff(c_50, plain, (![A_19, A_1]: (A_19=A_1 | ~m1_subset_1(A_19, k1_tarski(A_1)))), inference(negUnitSimplification, [status(thm)], [c_14, c_47])).
% 2.06/1.29  tff(c_64, plain, (![A_29, B_30, A_1]: ('#skF_3'(A_29, B_30, k1_tarski(A_1))=A_1 | m1_funct_2(k1_tarski(A_1), A_29, B_30) | v1_xboole_0(k1_tarski(A_1)))), inference(resolution, [status(thm)], [c_58, c_50])).
% 2.06/1.29  tff(c_69, plain, (![A_32, B_33, A_34]: ('#skF_3'(A_32, B_33, k1_tarski(A_34))=A_34 | m1_funct_2(k1_tarski(A_34), A_32, B_33))), inference(negUnitSimplification, [status(thm)], [c_14, c_64])).
% 2.06/1.29  tff(c_73, plain, ('#skF_3'('#skF_4', '#skF_5', k1_tarski('#skF_6'))='#skF_6'), inference(resolution, [status(thm)], [c_69, c_28])).
% 2.06/1.29  tff(c_32, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.06/1.29  tff(c_30, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.06/1.29  tff(c_335, plain, (![A_92, B_93, C_94]: (~m1_subset_1('#skF_3'(A_92, B_93, C_94), k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))) | ~v1_funct_2('#skF_3'(A_92, B_93, C_94), A_92, B_93) | ~v1_funct_1('#skF_3'(A_92, B_93, C_94)) | m1_funct_2(C_94, A_92, B_93) | v1_xboole_0(C_94))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.06/1.29  tff(c_348, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_3'('#skF_4', '#skF_5', k1_tarski('#skF_6')), '#skF_4', '#skF_5') | ~v1_funct_1('#skF_3'('#skF_4', '#skF_5', k1_tarski('#skF_6'))) | m1_funct_2(k1_tarski('#skF_6'), '#skF_4', '#skF_5') | v1_xboole_0(k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_335])).
% 2.06/1.29  tff(c_357, plain, (m1_funct_2(k1_tarski('#skF_6'), '#skF_4', '#skF_5') | v1_xboole_0(k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_73, c_32, c_73, c_30, c_348])).
% 2.06/1.29  tff(c_359, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_28, c_357])).
% 2.06/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.29  
% 2.06/1.29  Inference rules
% 2.06/1.29  ----------------------
% 2.06/1.29  #Ref     : 0
% 2.06/1.29  #Sup     : 68
% 2.06/1.29  #Fact    : 0
% 2.06/1.29  #Define  : 0
% 2.06/1.29  #Split   : 1
% 2.06/1.29  #Chain   : 0
% 2.06/1.29  #Close   : 0
% 2.06/1.29  
% 2.06/1.29  Ordering : KBO
% 2.06/1.29  
% 2.06/1.29  Simplification rules
% 2.06/1.29  ----------------------
% 2.06/1.29  #Subsume      : 9
% 2.06/1.29  #Demod        : 21
% 2.06/1.29  #Tautology    : 29
% 2.06/1.29  #SimpNegUnit  : 25
% 2.06/1.29  #BackRed      : 0
% 2.06/1.29  
% 2.06/1.29  #Partial instantiations: 0
% 2.06/1.29  #Strategies tried      : 1
% 2.06/1.29  
% 2.06/1.29  Timing (in seconds)
% 2.06/1.29  ----------------------
% 2.06/1.29  Preprocessing        : 0.28
% 2.06/1.29  Parsing              : 0.15
% 2.06/1.29  CNF conversion       : 0.02
% 2.06/1.29  Main loop            : 0.25
% 2.06/1.29  Inferencing          : 0.10
% 2.06/1.29  Reduction            : 0.07
% 2.06/1.29  Demodulation         : 0.04
% 2.06/1.29  BG Simplification    : 0.01
% 2.06/1.29  Subsumption          : 0.05
% 2.06/1.29  Abstraction          : 0.01
% 2.06/1.29  MUC search           : 0.00
% 2.06/1.29  Cooper               : 0.00
% 2.06/1.29  Total                : 0.56
% 2.06/1.29  Index Insertion      : 0.00
% 2.06/1.29  Index Deletion       : 0.00
% 2.06/1.29  Index Matching       : 0.00
% 2.06/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
