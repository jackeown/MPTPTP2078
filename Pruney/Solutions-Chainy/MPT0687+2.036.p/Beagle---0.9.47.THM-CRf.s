%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:38 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   50 (  66 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :    6
%              Number of atoms          :   65 ( 100 expanded)
%              Number of equality atoms :   24 (  36 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_32,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_107,plain,(
    ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_38,plain,
    ( r2_hidden('#skF_1',k2_relat_1('#skF_2'))
    | k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_165,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_38])).

tff(c_108,plain,(
    ! [A_39,B_40] :
      ( r1_xboole_0(k1_tarski(A_39),B_40)
      | r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_115,plain,(
    ! [B_40,A_39] :
      ( r1_xboole_0(B_40,k1_tarski(A_39))
      | r2_hidden(A_39,B_40) ) ),
    inference(resolution,[status(thm)],[c_108,c_2])).

tff(c_266,plain,(
    ! [B_56,A_57] :
      ( k10_relat_1(B_56,A_57) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_56),A_57)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_606,plain,(
    ! [B_105,A_106] :
      ( k10_relat_1(B_105,k1_tarski(A_106)) = k1_xboole_0
      | ~ v1_relat_1(B_105)
      | r2_hidden(A_106,k2_relat_1(B_105)) ) ),
    inference(resolution,[status(thm)],[c_115,c_266])).

tff(c_609,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_606,c_107])).

tff(c_612,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_609])).

tff(c_614,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_612])).

tff(c_615,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_616,plain,(
    r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_733,plain,(
    ! [B_122,A_123] :
      ( r1_xboole_0(k2_relat_1(B_122),A_123)
      | k10_relat_1(B_122,A_123) != k1_xboole_0
      | ~ v1_relat_1(B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_838,plain,(
    ! [A_134,B_135] :
      ( r1_xboole_0(A_134,k2_relat_1(B_135))
      | k10_relat_1(B_135,A_134) != k1_xboole_0
      | ~ v1_relat_1(B_135) ) ),
    inference(resolution,[status(thm)],[c_733,c_2])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = A_5
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1037,plain,(
    ! [A_169,B_170] :
      ( k4_xboole_0(A_169,k2_relat_1(B_170)) = A_169
      | k10_relat_1(B_170,A_169) != k1_xboole_0
      | ~ v1_relat_1(B_170) ) ),
    inference(resolution,[status(thm)],[c_838,c_6])).

tff(c_10,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_851,plain,(
    ! [A_136,C_137,B_138] :
      ( ~ r2_hidden(A_136,C_137)
      | k4_xboole_0(k2_tarski(A_136,B_138),C_137) != k2_tarski(A_136,B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_862,plain,(
    ! [A_7,C_137] :
      ( ~ r2_hidden(A_7,C_137)
      | k4_xboole_0(k1_tarski(A_7),C_137) != k2_tarski(A_7,A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_851])).

tff(c_865,plain,(
    ! [A_7,C_137] :
      ( ~ r2_hidden(A_7,C_137)
      | k4_xboole_0(k1_tarski(A_7),C_137) != k1_tarski(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_862])).

tff(c_1207,plain,(
    ! [A_177,B_178] :
      ( ~ r2_hidden(A_177,k2_relat_1(B_178))
      | k10_relat_1(B_178,k1_tarski(A_177)) != k1_xboole_0
      | ~ v1_relat_1(B_178) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1037,c_865])).

tff(c_1213,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_616,c_1207])).

tff(c_1218,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_615,c_1213])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:32:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.40  
% 2.69/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.40  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.69/1.40  
% 2.69/1.40  %Foreground sorts:
% 2.69/1.40  
% 2.69/1.40  
% 2.69/1.40  %Background operators:
% 2.69/1.40  
% 2.69/1.40  
% 2.69/1.40  %Foreground operators:
% 2.69/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.69/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.69/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.69/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.69/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.69/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.69/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.69/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.69/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.69/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.69/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.40  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.69/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.69/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.40  
% 2.69/1.41  tff(f_70, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 2.69/1.41  tff(f_48, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.69/1.41  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.69/1.41  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 2.69/1.41  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.69/1.41  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.69/1.41  tff(f_56, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 2.69/1.41  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.69/1.41  tff(c_32, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.69/1.41  tff(c_107, plain, (~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_32])).
% 2.69/1.41  tff(c_38, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2')) | k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.69/1.41  tff(c_165, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_107, c_38])).
% 2.69/1.41  tff(c_108, plain, (![A_39, B_40]: (r1_xboole_0(k1_tarski(A_39), B_40) | r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.69/1.41  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.69/1.41  tff(c_115, plain, (![B_40, A_39]: (r1_xboole_0(B_40, k1_tarski(A_39)) | r2_hidden(A_39, B_40))), inference(resolution, [status(thm)], [c_108, c_2])).
% 2.69/1.41  tff(c_266, plain, (![B_56, A_57]: (k10_relat_1(B_56, A_57)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_56), A_57) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.69/1.41  tff(c_606, plain, (![B_105, A_106]: (k10_relat_1(B_105, k1_tarski(A_106))=k1_xboole_0 | ~v1_relat_1(B_105) | r2_hidden(A_106, k2_relat_1(B_105)))), inference(resolution, [status(thm)], [c_115, c_266])).
% 2.69/1.41  tff(c_609, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_606, c_107])).
% 2.69/1.41  tff(c_612, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_609])).
% 2.69/1.41  tff(c_614, plain, $false, inference(negUnitSimplification, [status(thm)], [c_165, c_612])).
% 2.69/1.41  tff(c_615, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 2.69/1.41  tff(c_616, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_32])).
% 2.69/1.41  tff(c_733, plain, (![B_122, A_123]: (r1_xboole_0(k2_relat_1(B_122), A_123) | k10_relat_1(B_122, A_123)!=k1_xboole_0 | ~v1_relat_1(B_122))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.69/1.41  tff(c_838, plain, (![A_134, B_135]: (r1_xboole_0(A_134, k2_relat_1(B_135)) | k10_relat_1(B_135, A_134)!=k1_xboole_0 | ~v1_relat_1(B_135))), inference(resolution, [status(thm)], [c_733, c_2])).
% 2.69/1.41  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=A_5 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.69/1.41  tff(c_1037, plain, (![A_169, B_170]: (k4_xboole_0(A_169, k2_relat_1(B_170))=A_169 | k10_relat_1(B_170, A_169)!=k1_xboole_0 | ~v1_relat_1(B_170))), inference(resolution, [status(thm)], [c_838, c_6])).
% 2.69/1.41  tff(c_10, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.69/1.41  tff(c_851, plain, (![A_136, C_137, B_138]: (~r2_hidden(A_136, C_137) | k4_xboole_0(k2_tarski(A_136, B_138), C_137)!=k2_tarski(A_136, B_138))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.69/1.41  tff(c_862, plain, (![A_7, C_137]: (~r2_hidden(A_7, C_137) | k4_xboole_0(k1_tarski(A_7), C_137)!=k2_tarski(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_851])).
% 2.69/1.41  tff(c_865, plain, (![A_7, C_137]: (~r2_hidden(A_7, C_137) | k4_xboole_0(k1_tarski(A_7), C_137)!=k1_tarski(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_862])).
% 2.69/1.41  tff(c_1207, plain, (![A_177, B_178]: (~r2_hidden(A_177, k2_relat_1(B_178)) | k10_relat_1(B_178, k1_tarski(A_177))!=k1_xboole_0 | ~v1_relat_1(B_178))), inference(superposition, [status(thm), theory('equality')], [c_1037, c_865])).
% 2.69/1.41  tff(c_1213, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_616, c_1207])).
% 2.69/1.41  tff(c_1218, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_615, c_1213])).
% 2.69/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.41  
% 2.69/1.41  Inference rules
% 2.69/1.41  ----------------------
% 2.69/1.41  #Ref     : 0
% 2.69/1.41  #Sup     : 273
% 2.69/1.41  #Fact    : 0
% 2.69/1.41  #Define  : 0
% 2.69/1.41  #Split   : 1
% 2.69/1.41  #Chain   : 0
% 2.69/1.41  #Close   : 0
% 2.69/1.41  
% 2.69/1.41  Ordering : KBO
% 2.69/1.41  
% 2.69/1.41  Simplification rules
% 2.69/1.41  ----------------------
% 2.69/1.41  #Subsume      : 65
% 2.69/1.41  #Demod        : 39
% 2.69/1.41  #Tautology    : 127
% 2.69/1.41  #SimpNegUnit  : 6
% 2.69/1.41  #BackRed      : 0
% 2.69/1.41  
% 2.69/1.41  #Partial instantiations: 0
% 2.69/1.41  #Strategies tried      : 1
% 2.69/1.41  
% 2.69/1.41  Timing (in seconds)
% 2.69/1.41  ----------------------
% 2.69/1.42  Preprocessing        : 0.30
% 2.69/1.42  Parsing              : 0.16
% 2.69/1.42  CNF conversion       : 0.02
% 2.69/1.42  Main loop            : 0.37
% 2.69/1.42  Inferencing          : 0.16
% 2.69/1.42  Reduction            : 0.10
% 2.69/1.42  Demodulation         : 0.07
% 2.69/1.42  BG Simplification    : 0.02
% 2.69/1.42  Subsumption          : 0.06
% 2.69/1.42  Abstraction          : 0.02
% 2.69/1.42  MUC search           : 0.00
% 2.69/1.42  Cooper               : 0.00
% 2.69/1.42  Total                : 0.69
% 2.69/1.42  Index Insertion      : 0.00
% 2.69/1.42  Index Deletion       : 0.00
% 2.69/1.42  Index Matching       : 0.00
% 2.69/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
