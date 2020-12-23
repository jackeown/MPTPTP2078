%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:53 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   43 (  64 expanded)
%              Number of leaves         :   19 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   76 ( 154 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v5_relat_1(C,A)
          & v1_funct_1(C) )
       => ( r2_hidden(B,k1_relat_1(C))
         => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_35,plain,(
    ! [B_14,A_15] :
      ( m1_subset_1(B_14,A_15)
      | ~ v1_xboole_0(B_14)
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_16,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_39,plain,
    ( ~ v1_xboole_0(k1_funct_1('#skF_4','#skF_3'))
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_35,c_16])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_39])).

tff(c_22,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_24,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_75,plain,(
    ! [B_23,C_24,A_25] :
      ( r2_hidden(k1_funct_1(B_23,C_24),A_25)
      | ~ r2_hidden(C_24,k1_relat_1(B_23))
      | ~ v1_funct_1(B_23)
      | ~ v5_relat_1(B_23,A_25)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ r2_hidden(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_114,plain,(
    ! [B_32,C_33,A_34] :
      ( m1_subset_1(k1_funct_1(B_32,C_33),A_34)
      | v1_xboole_0(A_34)
      | ~ r2_hidden(C_33,k1_relat_1(B_32))
      | ~ v1_funct_1(B_32)
      | ~ v5_relat_1(B_32,A_34)
      | ~ v1_relat_1(B_32) ) ),
    inference(resolution,[status(thm)],[c_75,c_6])).

tff(c_125,plain,(
    ! [A_34] :
      ( m1_subset_1(k1_funct_1('#skF_4','#skF_3'),A_34)
      | v1_xboole_0(A_34)
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4',A_34)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_114])).

tff(c_132,plain,(
    ! [A_35] :
      ( m1_subset_1(k1_funct_1('#skF_4','#skF_3'),A_35)
      | v1_xboole_0(A_35)
      | ~ v5_relat_1('#skF_4',A_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_125])).

tff(c_138,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_132,c_16])).

tff(c_142,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_138])).

tff(c_144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_142])).

tff(c_146,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_39])).

tff(c_176,plain,(
    ! [B_42,C_43,A_44] :
      ( r2_hidden(k1_funct_1(B_42,C_43),A_44)
      | ~ r2_hidden(C_43,k1_relat_1(B_42))
      | ~ v1_funct_1(B_42)
      | ~ v5_relat_1(B_42,A_44)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_190,plain,(
    ! [A_46,C_47,B_48] :
      ( ~ v1_xboole_0(A_46)
      | ~ r2_hidden(C_47,k1_relat_1(B_48))
      | ~ v1_funct_1(B_48)
      | ~ v5_relat_1(B_48,A_46)
      | ~ v1_relat_1(B_48) ) ),
    inference(resolution,[status(thm)],[c_176,c_2])).

tff(c_201,plain,(
    ! [A_46] :
      ( ~ v1_xboole_0(A_46)
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4',A_46)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_190])).

tff(c_208,plain,(
    ! [A_49] :
      ( ~ v1_xboole_0(A_49)
      | ~ v5_relat_1('#skF_4',A_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_201])).

tff(c_211,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_208])).

tff(c_215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_211])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:33:23 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.60  
% 2.29/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.61  %$ v5_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.29/1.61  
% 2.29/1.61  %Foreground sorts:
% 2.29/1.61  
% 2.29/1.61  
% 2.29/1.61  %Background operators:
% 2.29/1.61  
% 2.29/1.61  
% 2.29/1.61  %Foreground operators:
% 2.29/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.29/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.29/1.61  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.29/1.61  tff('#skF_2', type, '#skF_2': $i).
% 2.29/1.61  tff('#skF_3', type, '#skF_3': $i).
% 2.29/1.61  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.29/1.61  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.29/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.29/1.61  tff('#skF_4', type, '#skF_4': $i).
% 2.29/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.29/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.29/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.29/1.61  
% 2.29/1.63  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.29/1.63  tff(f_66, negated_conjecture, ~(![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_1)).
% 2.29/1.63  tff(f_55, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 2.29/1.63  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.29/1.63  tff(c_35, plain, (![B_14, A_15]: (m1_subset_1(B_14, A_15) | ~v1_xboole_0(B_14) | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.29/1.63  tff(c_16, plain, (~m1_subset_1(k1_funct_1('#skF_4', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.29/1.63  tff(c_39, plain, (~v1_xboole_0(k1_funct_1('#skF_4', '#skF_3')) | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_35, c_16])).
% 2.29/1.63  tff(c_40, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_39])).
% 2.29/1.63  tff(c_22, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.29/1.63  tff(c_24, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.29/1.63  tff(c_20, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.29/1.63  tff(c_18, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.29/1.63  tff(c_75, plain, (![B_23, C_24, A_25]: (r2_hidden(k1_funct_1(B_23, C_24), A_25) | ~r2_hidden(C_24, k1_relat_1(B_23)) | ~v1_funct_1(B_23) | ~v5_relat_1(B_23, A_25) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.29/1.63  tff(c_6, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~r2_hidden(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.29/1.63  tff(c_114, plain, (![B_32, C_33, A_34]: (m1_subset_1(k1_funct_1(B_32, C_33), A_34) | v1_xboole_0(A_34) | ~r2_hidden(C_33, k1_relat_1(B_32)) | ~v1_funct_1(B_32) | ~v5_relat_1(B_32, A_34) | ~v1_relat_1(B_32))), inference(resolution, [status(thm)], [c_75, c_6])).
% 2.29/1.63  tff(c_125, plain, (![A_34]: (m1_subset_1(k1_funct_1('#skF_4', '#skF_3'), A_34) | v1_xboole_0(A_34) | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', A_34) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_114])).
% 2.29/1.63  tff(c_132, plain, (![A_35]: (m1_subset_1(k1_funct_1('#skF_4', '#skF_3'), A_35) | v1_xboole_0(A_35) | ~v5_relat_1('#skF_4', A_35))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_125])).
% 2.29/1.63  tff(c_138, plain, (v1_xboole_0('#skF_2') | ~v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_132, c_16])).
% 2.29/1.63  tff(c_142, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_138])).
% 2.29/1.63  tff(c_144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_142])).
% 2.29/1.63  tff(c_146, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_39])).
% 2.29/1.63  tff(c_176, plain, (![B_42, C_43, A_44]: (r2_hidden(k1_funct_1(B_42, C_43), A_44) | ~r2_hidden(C_43, k1_relat_1(B_42)) | ~v1_funct_1(B_42) | ~v5_relat_1(B_42, A_44) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.29/1.63  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.29/1.63  tff(c_190, plain, (![A_46, C_47, B_48]: (~v1_xboole_0(A_46) | ~r2_hidden(C_47, k1_relat_1(B_48)) | ~v1_funct_1(B_48) | ~v5_relat_1(B_48, A_46) | ~v1_relat_1(B_48))), inference(resolution, [status(thm)], [c_176, c_2])).
% 2.29/1.63  tff(c_201, plain, (![A_46]: (~v1_xboole_0(A_46) | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', A_46) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_190])).
% 2.29/1.63  tff(c_208, plain, (![A_49]: (~v1_xboole_0(A_49) | ~v5_relat_1('#skF_4', A_49))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_201])).
% 2.29/1.63  tff(c_211, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_22, c_208])).
% 2.29/1.63  tff(c_215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_146, c_211])).
% 2.29/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.63  
% 2.29/1.63  Inference rules
% 2.29/1.63  ----------------------
% 2.29/1.63  #Ref     : 0
% 2.29/1.63  #Sup     : 38
% 2.29/1.63  #Fact    : 0
% 2.29/1.63  #Define  : 0
% 2.29/1.63  #Split   : 1
% 2.29/1.63  #Chain   : 0
% 2.29/1.63  #Close   : 0
% 2.29/1.63  
% 2.29/1.63  Ordering : KBO
% 2.29/1.63  
% 2.29/1.63  Simplification rules
% 2.29/1.63  ----------------------
% 2.29/1.63  #Subsume      : 6
% 2.29/1.63  #Demod        : 10
% 2.29/1.63  #Tautology    : 9
% 2.29/1.63  #SimpNegUnit  : 4
% 2.29/1.63  #BackRed      : 0
% 2.29/1.63  
% 2.29/1.63  #Partial instantiations: 0
% 2.29/1.63  #Strategies tried      : 1
% 2.29/1.63  
% 2.29/1.63  Timing (in seconds)
% 2.29/1.63  ----------------------
% 2.52/1.63  Preprocessing        : 0.41
% 2.52/1.63  Parsing              : 0.22
% 2.52/1.63  CNF conversion       : 0.03
% 2.52/1.63  Main loop            : 0.32
% 2.52/1.63  Inferencing          : 0.13
% 2.52/1.64  Reduction            : 0.07
% 2.52/1.64  Demodulation         : 0.04
% 2.52/1.64  BG Simplification    : 0.02
% 2.52/1.64  Subsumption          : 0.06
% 2.52/1.64  Abstraction          : 0.01
% 2.52/1.64  MUC search           : 0.00
% 2.52/1.64  Cooper               : 0.00
% 2.52/1.64  Total                : 0.78
% 2.52/1.64  Index Insertion      : 0.00
% 2.52/1.64  Index Deletion       : 0.00
% 2.52/1.64  Index Matching       : 0.00
% 2.52/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
