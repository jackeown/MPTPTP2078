%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:16 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 106 expanded)
%              Number of leaves         :   24 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :   58 ( 210 expanded)
%              Number of equality atoms :    8 (  38 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => m1_funct_2(k1_tarski(C),A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_funct_2)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ( m1_funct_2(C,A,B)
      <=> ! [D] :
            ( m1_subset_1(D,C)
           => ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(c_8,plain,(
    ! [C_9] : r2_hidden(C_9,k1_tarski(C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_38,plain,(
    ! [B_19,A_20] :
      ( ~ r2_hidden(B_19,A_20)
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ! [C_9] : ~ v1_xboole_0(k1_tarski(C_9)) ),
    inference(resolution,[status(thm)],[c_8,c_38])).

tff(c_30,plain,(
    ~ m1_funct_2(k1_tarski('#skF_7'),'#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_36,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_95,plain,(
    ! [A_36,B_37,C_38] :
      ( m1_subset_1('#skF_4'(A_36,B_37,C_38),C_38)
      | m1_funct_2(C_38,A_36,B_37)
      | v1_xboole_0(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_62,plain,(
    ! [A_25,B_26] :
      ( r2_hidden(A_25,B_26)
      | v1_xboole_0(B_26)
      | ~ m1_subset_1(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    ! [C_9,A_5] :
      ( C_9 = A_5
      | ~ r2_hidden(C_9,k1_tarski(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_66,plain,(
    ! [A_5,A_25] :
      ( A_5 = A_25
      | v1_xboole_0(k1_tarski(A_5))
      | ~ m1_subset_1(A_25,k1_tarski(A_5)) ) ),
    inference(resolution,[status(thm)],[c_62,c_6])).

tff(c_72,plain,(
    ! [A_5,A_25] :
      ( A_5 = A_25
      | ~ m1_subset_1(A_25,k1_tarski(A_5)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_66])).

tff(c_101,plain,(
    ! [A_36,B_37,A_5] :
      ( '#skF_4'(A_36,B_37,k1_tarski(A_5)) = A_5
      | m1_funct_2(k1_tarski(A_5),A_36,B_37)
      | v1_xboole_0(k1_tarski(A_5)) ) ),
    inference(resolution,[status(thm)],[c_95,c_72])).

tff(c_117,plain,(
    ! [A_43,B_44,A_45] :
      ( '#skF_4'(A_43,B_44,k1_tarski(A_45)) = A_45
      | m1_funct_2(k1_tarski(A_45),A_43,B_44) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_101])).

tff(c_121,plain,(
    '#skF_4'('#skF_5','#skF_6',k1_tarski('#skF_7')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_117,c_30])).

tff(c_34,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_32,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_280,plain,(
    ! [A_78,B_79,C_80] :
      ( ~ m1_subset_1('#skF_4'(A_78,B_79,C_80),k1_zfmisc_1(k2_zfmisc_1(A_78,B_79)))
      | ~ v1_funct_2('#skF_4'(A_78,B_79,C_80),A_78,B_79)
      | ~ v1_funct_1('#skF_4'(A_78,B_79,C_80))
      | m1_funct_2(C_80,A_78,B_79)
      | v1_xboole_0(C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_286,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ v1_funct_2('#skF_4'('#skF_5','#skF_6',k1_tarski('#skF_7')),'#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_4'('#skF_5','#skF_6',k1_tarski('#skF_7')))
    | m1_funct_2(k1_tarski('#skF_7'),'#skF_5','#skF_6')
    | v1_xboole_0(k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_280])).

tff(c_293,plain,
    ( m1_funct_2(k1_tarski('#skF_7'),'#skF_5','#skF_6')
    | v1_xboole_0(k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_121,c_34,c_121,c_32,c_286])).

tff(c_295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_30,c_293])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:02:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.33  
% 2.26/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.33  %$ v1_funct_2 > m1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2
% 2.26/1.33  
% 2.26/1.33  %Foreground sorts:
% 2.26/1.33  
% 2.26/1.33  
% 2.26/1.33  %Background operators:
% 2.26/1.33  
% 2.26/1.33  
% 2.26/1.33  %Foreground operators:
% 2.26/1.33  tff(m1_funct_2, type, m1_funct_2: ($i * $i * $i) > $o).
% 2.26/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.26/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.26/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.26/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.26/1.33  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.26/1.33  tff('#skF_7', type, '#skF_7': $i).
% 2.26/1.33  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.26/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.26/1.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.26/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.26/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.26/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.26/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.26/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.26/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.26/1.33  
% 2.26/1.34  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.26/1.34  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.26/1.34  tff(f_67, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => m1_funct_2(k1_tarski(C), A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t198_funct_2)).
% 2.26/1.34  tff(f_58, axiom, (![A, B, C]: (~v1_xboole_0(C) => (m1_funct_2(C, A, B) <=> (![D]: (m1_subset_1(D, C) => ((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_funct_2)).
% 2.26/1.34  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.26/1.34  tff(c_8, plain, (![C_9]: (r2_hidden(C_9, k1_tarski(C_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.26/1.34  tff(c_38, plain, (![B_19, A_20]: (~r2_hidden(B_19, A_20) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.26/1.34  tff(c_42, plain, (![C_9]: (~v1_xboole_0(k1_tarski(C_9)))), inference(resolution, [status(thm)], [c_8, c_38])).
% 2.26/1.34  tff(c_30, plain, (~m1_funct_2(k1_tarski('#skF_7'), '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.26/1.34  tff(c_36, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.26/1.34  tff(c_95, plain, (![A_36, B_37, C_38]: (m1_subset_1('#skF_4'(A_36, B_37, C_38), C_38) | m1_funct_2(C_38, A_36, B_37) | v1_xboole_0(C_38))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.26/1.34  tff(c_62, plain, (![A_25, B_26]: (r2_hidden(A_25, B_26) | v1_xboole_0(B_26) | ~m1_subset_1(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.26/1.34  tff(c_6, plain, (![C_9, A_5]: (C_9=A_5 | ~r2_hidden(C_9, k1_tarski(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.26/1.34  tff(c_66, plain, (![A_5, A_25]: (A_5=A_25 | v1_xboole_0(k1_tarski(A_5)) | ~m1_subset_1(A_25, k1_tarski(A_5)))), inference(resolution, [status(thm)], [c_62, c_6])).
% 2.26/1.34  tff(c_72, plain, (![A_5, A_25]: (A_5=A_25 | ~m1_subset_1(A_25, k1_tarski(A_5)))), inference(negUnitSimplification, [status(thm)], [c_42, c_66])).
% 2.26/1.34  tff(c_101, plain, (![A_36, B_37, A_5]: ('#skF_4'(A_36, B_37, k1_tarski(A_5))=A_5 | m1_funct_2(k1_tarski(A_5), A_36, B_37) | v1_xboole_0(k1_tarski(A_5)))), inference(resolution, [status(thm)], [c_95, c_72])).
% 2.26/1.34  tff(c_117, plain, (![A_43, B_44, A_45]: ('#skF_4'(A_43, B_44, k1_tarski(A_45))=A_45 | m1_funct_2(k1_tarski(A_45), A_43, B_44))), inference(negUnitSimplification, [status(thm)], [c_42, c_101])).
% 2.26/1.34  tff(c_121, plain, ('#skF_4'('#skF_5', '#skF_6', k1_tarski('#skF_7'))='#skF_7'), inference(resolution, [status(thm)], [c_117, c_30])).
% 2.26/1.34  tff(c_34, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.26/1.34  tff(c_32, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.26/1.34  tff(c_280, plain, (![A_78, B_79, C_80]: (~m1_subset_1('#skF_4'(A_78, B_79, C_80), k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))) | ~v1_funct_2('#skF_4'(A_78, B_79, C_80), A_78, B_79) | ~v1_funct_1('#skF_4'(A_78, B_79, C_80)) | m1_funct_2(C_80, A_78, B_79) | v1_xboole_0(C_80))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.26/1.34  tff(c_286, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_2('#skF_4'('#skF_5', '#skF_6', k1_tarski('#skF_7')), '#skF_5', '#skF_6') | ~v1_funct_1('#skF_4'('#skF_5', '#skF_6', k1_tarski('#skF_7'))) | m1_funct_2(k1_tarski('#skF_7'), '#skF_5', '#skF_6') | v1_xboole_0(k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_121, c_280])).
% 2.26/1.34  tff(c_293, plain, (m1_funct_2(k1_tarski('#skF_7'), '#skF_5', '#skF_6') | v1_xboole_0(k1_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_121, c_34, c_121, c_32, c_286])).
% 2.26/1.34  tff(c_295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_30, c_293])).
% 2.26/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.34  
% 2.26/1.34  Inference rules
% 2.26/1.34  ----------------------
% 2.26/1.34  #Ref     : 0
% 2.26/1.34  #Sup     : 53
% 2.26/1.34  #Fact    : 0
% 2.26/1.34  #Define  : 0
% 2.26/1.34  #Split   : 1
% 2.26/1.34  #Chain   : 0
% 2.26/1.34  #Close   : 0
% 2.26/1.34  
% 2.26/1.34  Ordering : KBO
% 2.26/1.34  
% 2.26/1.34  Simplification rules
% 2.26/1.34  ----------------------
% 2.26/1.34  #Subsume      : 1
% 2.26/1.34  #Demod        : 15
% 2.26/1.34  #Tautology    : 25
% 2.26/1.34  #SimpNegUnit  : 13
% 2.26/1.34  #BackRed      : 0
% 2.26/1.34  
% 2.26/1.34  #Partial instantiations: 0
% 2.26/1.34  #Strategies tried      : 1
% 2.26/1.34  
% 2.26/1.34  Timing (in seconds)
% 2.26/1.34  ----------------------
% 2.26/1.34  Preprocessing        : 0.31
% 2.26/1.34  Parsing              : 0.16
% 2.26/1.34  CNF conversion       : 0.03
% 2.26/1.34  Main loop            : 0.23
% 2.26/1.34  Inferencing          : 0.09
% 2.26/1.34  Reduction            : 0.06
% 2.26/1.34  Demodulation         : 0.04
% 2.26/1.34  BG Simplification    : 0.02
% 2.26/1.34  Subsumption          : 0.05
% 2.26/1.34  Abstraction          : 0.01
% 2.26/1.34  MUC search           : 0.00
% 2.26/1.35  Cooper               : 0.00
% 2.26/1.35  Total                : 0.57
% 2.26/1.35  Index Insertion      : 0.00
% 2.26/1.35  Index Deletion       : 0.00
% 2.26/1.35  Index Matching       : 0.00
% 2.26/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
