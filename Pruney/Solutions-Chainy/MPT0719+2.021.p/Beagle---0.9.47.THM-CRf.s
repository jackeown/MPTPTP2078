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
% DateTime   : Thu Dec  3 10:05:45 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   41 (  45 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   57 (  65 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_42,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( v5_funct_1(B,A)
          <=> ! [C] :
                ( r2_hidden(C,k1_relat_1(B))
               => r2_hidden(k1_funct_1(B,C),k1_funct_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_28,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_71,plain,(
    ! [A_21,B_22] : ~ r2_hidden(A_21,k2_zfmisc_1(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_74,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_71])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_66,plain,(
    ! [A_20] :
      ( v1_relat_1(A_20)
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_70,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_66])).

tff(c_46,plain,(
    ! [A_18] :
      ( v1_funct_1(A_18)
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_50,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_46])).

tff(c_16,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_90,plain,(
    ! [A_26,B_27] :
      ( r2_hidden('#skF_1'(A_26,B_27),k1_relat_1(B_27))
      | v5_funct_1(B_27,A_26)
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_93,plain,(
    ! [A_26] :
      ( r2_hidden('#skF_1'(A_26,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_26)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_90])).

tff(c_95,plain,(
    ! [A_26] :
      ( r2_hidden('#skF_1'(A_26,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_26)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_50,c_93])).

tff(c_97,plain,(
    ! [A_28] :
      ( v5_funct_1(k1_xboole_0,A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_95])).

tff(c_26,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_100,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_97,c_26])).

tff(c_104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_100])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:24:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.22  
% 1.87/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.23  %$ v5_funct_1 > r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.87/1.23  
% 1.87/1.23  %Foreground sorts:
% 1.87/1.23  
% 1.87/1.23  
% 1.87/1.23  %Background operators:
% 1.87/1.23  
% 1.87/1.23  
% 1.87/1.23  %Foreground operators:
% 1.87/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.87/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.87/1.23  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 1.87/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.87/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.23  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.87/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.87/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.87/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.87/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.87/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.87/1.23  
% 1.87/1.24  tff(f_69, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_1)).
% 1.87/1.24  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.87/1.24  tff(f_35, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.87/1.24  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.87/1.24  tff(f_39, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.87/1.24  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 1.87/1.24  tff(f_42, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.87/1.24  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 1.87/1.24  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.87/1.24  tff(c_28, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.87/1.24  tff(c_6, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.87/1.24  tff(c_71, plain, (![A_21, B_22]: (~r2_hidden(A_21, k2_zfmisc_1(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.87/1.24  tff(c_74, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_71])).
% 1.87/1.24  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.87/1.24  tff(c_66, plain, (![A_20]: (v1_relat_1(A_20) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.87/1.24  tff(c_70, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_66])).
% 1.87/1.24  tff(c_46, plain, (![A_18]: (v1_funct_1(A_18) | ~v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.87/1.24  tff(c_50, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_46])).
% 1.87/1.24  tff(c_16, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.87/1.24  tff(c_90, plain, (![A_26, B_27]: (r2_hidden('#skF_1'(A_26, B_27), k1_relat_1(B_27)) | v5_funct_1(B_27, A_26) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.87/1.24  tff(c_93, plain, (![A_26]: (r2_hidden('#skF_1'(A_26, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_26) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(superposition, [status(thm), theory('equality')], [c_16, c_90])).
% 1.87/1.24  tff(c_95, plain, (![A_26]: (r2_hidden('#skF_1'(A_26, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_26) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_50, c_93])).
% 1.87/1.24  tff(c_97, plain, (![A_28]: (v5_funct_1(k1_xboole_0, A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(negUnitSimplification, [status(thm)], [c_74, c_95])).
% 1.87/1.24  tff(c_26, plain, (~v5_funct_1(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.87/1.24  tff(c_100, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_97, c_26])).
% 1.87/1.24  tff(c_104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_100])).
% 1.87/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.24  
% 1.87/1.24  Inference rules
% 1.87/1.24  ----------------------
% 1.87/1.24  #Ref     : 0
% 1.87/1.24  #Sup     : 18
% 1.87/1.24  #Fact    : 0
% 1.87/1.24  #Define  : 0
% 1.87/1.24  #Split   : 0
% 1.87/1.24  #Chain   : 0
% 1.87/1.24  #Close   : 0
% 1.87/1.24  
% 1.87/1.24  Ordering : KBO
% 1.87/1.24  
% 1.87/1.24  Simplification rules
% 1.87/1.24  ----------------------
% 1.87/1.24  #Subsume      : 1
% 1.87/1.24  #Demod        : 4
% 1.87/1.24  #Tautology    : 12
% 1.87/1.24  #SimpNegUnit  : 1
% 1.87/1.24  #BackRed      : 0
% 1.87/1.24  
% 1.87/1.24  #Partial instantiations: 0
% 1.87/1.24  #Strategies tried      : 1
% 1.87/1.24  
% 1.87/1.24  Timing (in seconds)
% 1.87/1.24  ----------------------
% 1.87/1.24  Preprocessing        : 0.30
% 1.87/1.24  Parsing              : 0.16
% 1.87/1.24  CNF conversion       : 0.02
% 1.87/1.24  Main loop            : 0.12
% 1.87/1.24  Inferencing          : 0.05
% 1.87/1.24  Reduction            : 0.03
% 1.87/1.24  Demodulation         : 0.03
% 1.87/1.24  BG Simplification    : 0.01
% 1.87/1.24  Subsumption          : 0.02
% 1.87/1.24  Abstraction          : 0.00
% 1.87/1.24  MUC search           : 0.00
% 1.87/1.24  Cooper               : 0.00
% 1.87/1.24  Total                : 0.44
% 1.87/1.24  Index Insertion      : 0.00
% 1.94/1.24  Index Deletion       : 0.00
% 1.94/1.24  Index Matching       : 0.00
% 1.94/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
