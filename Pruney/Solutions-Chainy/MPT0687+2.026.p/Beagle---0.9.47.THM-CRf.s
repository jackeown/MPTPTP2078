%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:36 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   61 (  73 expanded)
%              Number of leaves         :   33 (  40 expanded)
%              Depth                    :    6
%              Number of atoms          :   67 (  96 expanded)
%              Number of equality atoms :   25 (  35 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_67,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_42,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_85,plain,(
    ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_48,plain,
    ( r2_hidden('#skF_1',k2_relat_1('#skF_2'))
    | k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_141,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_48])).

tff(c_95,plain,(
    ! [A_63,B_64] :
      ( r1_xboole_0(k1_tarski(A_63),B_64)
      | r2_hidden(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_102,plain,(
    ! [B_64,A_63] :
      ( r1_xboole_0(B_64,k1_tarski(A_63))
      | r2_hidden(A_63,B_64) ) ),
    inference(resolution,[status(thm)],[c_95,c_2])).

tff(c_201,plain,(
    ! [B_86,A_87] :
      ( k10_relat_1(B_86,A_87) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_86),A_87)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_258,plain,(
    ! [B_98,A_99] :
      ( k10_relat_1(B_98,k1_tarski(A_99)) = k1_xboole_0
      | ~ v1_relat_1(B_98)
      | r2_hidden(A_99,k2_relat_1(B_98)) ) ),
    inference(resolution,[status(thm)],[c_102,c_201])).

tff(c_261,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_258,c_85])).

tff(c_264,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_261])).

tff(c_266,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_264])).

tff(c_267,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_268,plain,(
    r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_396,plain,(
    ! [B_129,A_130] :
      ( r1_xboole_0(k2_relat_1(B_129),A_130)
      | k10_relat_1(B_129,A_130) != k1_xboole_0
      | ~ v1_relat_1(B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = A_8
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_500,plain,(
    ! [B_156,A_157] :
      ( k4_xboole_0(k2_relat_1(B_156),A_157) = k2_relat_1(B_156)
      | k10_relat_1(B_156,A_157) != k1_xboole_0
      | ~ v1_relat_1(B_156) ) ),
    inference(resolution,[status(thm)],[c_396,c_10])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_67,plain,(
    ! [A_48,B_49] : k2_xboole_0(k1_tarski(A_48),B_49) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_71,plain,(
    ! [A_48] : k1_tarski(A_48) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_67])).

tff(c_281,plain,(
    ! [A_102,B_103] :
      ( r1_tarski(k1_tarski(A_102),B_103)
      | ~ r2_hidden(A_102,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k4_xboole_0(B_7,A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_285,plain,(
    ! [A_102,B_7] :
      ( k1_tarski(A_102) = k1_xboole_0
      | ~ r2_hidden(A_102,k4_xboole_0(B_7,k1_tarski(A_102))) ) ),
    inference(resolution,[status(thm)],[c_281,c_8])).

tff(c_288,plain,(
    ! [A_102,B_7] : ~ r2_hidden(A_102,k4_xboole_0(B_7,k1_tarski(A_102))) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_285])).

tff(c_544,plain,(
    ! [A_158,B_159] :
      ( ~ r2_hidden(A_158,k2_relat_1(B_159))
      | k10_relat_1(B_159,k1_tarski(A_158)) != k1_xboole_0
      | ~ v1_relat_1(B_159) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_500,c_288])).

tff(c_550,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_268,c_544])).

tff(c_555,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_267,c_550])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:14:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.30  
% 2.30/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.30  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.30/1.30  
% 2.30/1.30  %Foreground sorts:
% 2.30/1.30  
% 2.30/1.30  
% 2.30/1.30  %Background operators:
% 2.30/1.30  
% 2.30/1.30  
% 2.30/1.30  %Foreground operators:
% 2.30/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.30/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.30/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.30/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.30/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.30/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.30/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.30/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.30/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.30/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.30/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.30/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.30/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.30/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.30/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.30/1.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.30/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.30  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.30/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.30/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.30/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.30/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.30/1.30  
% 2.30/1.31  tff(f_81, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 2.30/1.31  tff(f_64, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.30/1.31  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.30/1.31  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 2.30/1.31  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.30/1.31  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.30/1.31  tff(f_67, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.30/1.31  tff(f_59, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.30/1.31  tff(f_37, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.30/1.31  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.30/1.31  tff(c_42, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.30/1.31  tff(c_85, plain, (~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_42])).
% 2.30/1.31  tff(c_48, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2')) | k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.30/1.31  tff(c_141, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_85, c_48])).
% 2.30/1.31  tff(c_95, plain, (![A_63, B_64]: (r1_xboole_0(k1_tarski(A_63), B_64) | r2_hidden(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.30/1.31  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.30/1.31  tff(c_102, plain, (![B_64, A_63]: (r1_xboole_0(B_64, k1_tarski(A_63)) | r2_hidden(A_63, B_64))), inference(resolution, [status(thm)], [c_95, c_2])).
% 2.30/1.31  tff(c_201, plain, (![B_86, A_87]: (k10_relat_1(B_86, A_87)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_86), A_87) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.30/1.31  tff(c_258, plain, (![B_98, A_99]: (k10_relat_1(B_98, k1_tarski(A_99))=k1_xboole_0 | ~v1_relat_1(B_98) | r2_hidden(A_99, k2_relat_1(B_98)))), inference(resolution, [status(thm)], [c_102, c_201])).
% 2.30/1.31  tff(c_261, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_258, c_85])).
% 2.30/1.31  tff(c_264, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_261])).
% 2.30/1.31  tff(c_266, plain, $false, inference(negUnitSimplification, [status(thm)], [c_141, c_264])).
% 2.30/1.31  tff(c_267, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 2.30/1.31  tff(c_268, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_42])).
% 2.30/1.31  tff(c_396, plain, (![B_129, A_130]: (r1_xboole_0(k2_relat_1(B_129), A_130) | k10_relat_1(B_129, A_130)!=k1_xboole_0 | ~v1_relat_1(B_129))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.30/1.31  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=A_8 | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.30/1.31  tff(c_500, plain, (![B_156, A_157]: (k4_xboole_0(k2_relat_1(B_156), A_157)=k2_relat_1(B_156) | k10_relat_1(B_156, A_157)!=k1_xboole_0 | ~v1_relat_1(B_156))), inference(resolution, [status(thm)], [c_396, c_10])).
% 2.30/1.31  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.30/1.31  tff(c_67, plain, (![A_48, B_49]: (k2_xboole_0(k1_tarski(A_48), B_49)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.30/1.31  tff(c_71, plain, (![A_48]: (k1_tarski(A_48)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_67])).
% 2.30/1.31  tff(c_281, plain, (![A_102, B_103]: (r1_tarski(k1_tarski(A_102), B_103) | ~r2_hidden(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.30/1.31  tff(c_8, plain, (![A_6, B_7]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k4_xboole_0(B_7, A_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.30/1.31  tff(c_285, plain, (![A_102, B_7]: (k1_tarski(A_102)=k1_xboole_0 | ~r2_hidden(A_102, k4_xboole_0(B_7, k1_tarski(A_102))))), inference(resolution, [status(thm)], [c_281, c_8])).
% 2.30/1.31  tff(c_288, plain, (![A_102, B_7]: (~r2_hidden(A_102, k4_xboole_0(B_7, k1_tarski(A_102))))), inference(negUnitSimplification, [status(thm)], [c_71, c_285])).
% 2.30/1.31  tff(c_544, plain, (![A_158, B_159]: (~r2_hidden(A_158, k2_relat_1(B_159)) | k10_relat_1(B_159, k1_tarski(A_158))!=k1_xboole_0 | ~v1_relat_1(B_159))), inference(superposition, [status(thm), theory('equality')], [c_500, c_288])).
% 2.30/1.31  tff(c_550, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_268, c_544])).
% 2.30/1.31  tff(c_555, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_267, c_550])).
% 2.30/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.31  
% 2.30/1.31  Inference rules
% 2.30/1.31  ----------------------
% 2.30/1.31  #Ref     : 0
% 2.30/1.31  #Sup     : 110
% 2.30/1.31  #Fact    : 0
% 2.30/1.31  #Define  : 0
% 2.30/1.31  #Split   : 1
% 2.30/1.31  #Chain   : 0
% 2.30/1.31  #Close   : 0
% 2.30/1.31  
% 2.30/1.31  Ordering : KBO
% 2.30/1.31  
% 2.30/1.31  Simplification rules
% 2.30/1.31  ----------------------
% 2.30/1.31  #Subsume      : 16
% 2.30/1.31  #Demod        : 5
% 2.30/1.31  #Tautology    : 59
% 2.30/1.31  #SimpNegUnit  : 8
% 2.30/1.31  #BackRed      : 0
% 2.30/1.31  
% 2.30/1.31  #Partial instantiations: 0
% 2.30/1.31  #Strategies tried      : 1
% 2.30/1.31  
% 2.30/1.31  Timing (in seconds)
% 2.30/1.31  ----------------------
% 2.30/1.31  Preprocessing        : 0.31
% 2.30/1.31  Parsing              : 0.17
% 2.30/1.31  CNF conversion       : 0.02
% 2.30/1.31  Main loop            : 0.25
% 2.30/1.31  Inferencing          : 0.11
% 2.30/1.31  Reduction            : 0.06
% 2.30/1.31  Demodulation         : 0.04
% 2.30/1.31  BG Simplification    : 0.02
% 2.30/1.31  Subsumption          : 0.05
% 2.30/1.31  Abstraction          : 0.02
% 2.30/1.31  MUC search           : 0.00
% 2.30/1.31  Cooper               : 0.00
% 2.30/1.31  Total                : 0.58
% 2.30/1.32  Index Insertion      : 0.00
% 2.30/1.32  Index Deletion       : 0.00
% 2.30/1.32  Index Matching       : 0.00
% 2.30/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
