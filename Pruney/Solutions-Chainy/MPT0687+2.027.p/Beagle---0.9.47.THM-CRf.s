%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:36 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   52 (  67 expanded)
%              Number of leaves         :   25 (  33 expanded)
%              Depth                    :    6
%              Number of atoms          :   65 ( 101 expanded)
%              Number of equality atoms :   25 (  38 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k2_relat_1(B))
          & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_28,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_75,plain,(
    ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_34,plain,
    ( r2_hidden('#skF_1',k2_relat_1('#skF_2'))
    | k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_84,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_34])).

tff(c_76,plain,(
    ! [A_33,B_34] :
      ( r1_xboole_0(k1_tarski(A_33),B_34)
      | r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_79,plain,(
    ! [B_34,A_33] :
      ( r1_xboole_0(B_34,k1_tarski(A_33))
      | r2_hidden(A_33,B_34) ) ),
    inference(resolution,[status(thm)],[c_76,c_2])).

tff(c_94,plain,(
    ! [B_40,A_41] :
      ( k10_relat_1(B_40,A_41) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_40),A_41)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_117,plain,(
    ! [B_46,A_47] :
      ( k10_relat_1(B_46,k1_tarski(A_47)) = k1_xboole_0
      | ~ v1_relat_1(B_46)
      | r2_hidden(A_47,k2_relat_1(B_46)) ) ),
    inference(resolution,[status(thm)],[c_79,c_94])).

tff(c_120,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_117,c_75])).

tff(c_123,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_120])).

tff(c_125,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_123])).

tff(c_126,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_128,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_134,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_128])).

tff(c_136,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_127,plain,(
    r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    ! [A_22,B_23] : k2_xboole_0(k1_tarski(A_22),B_23) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_57,plain,(
    ! [A_22] : k1_tarski(A_22) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_53])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(k1_tarski(A_10),B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_184,plain,(
    ! [B_63,A_64] :
      ( k10_relat_1(B_63,A_64) != k1_xboole_0
      | ~ r1_tarski(A_64,k2_relat_1(B_63))
      | k1_xboole_0 = A_64
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_188,plain,(
    ! [B_63,A_10] :
      ( k10_relat_1(B_63,k1_tarski(A_10)) != k1_xboole_0
      | k1_tarski(A_10) = k1_xboole_0
      | ~ v1_relat_1(B_63)
      | ~ r2_hidden(A_10,k2_relat_1(B_63)) ) ),
    inference(resolution,[status(thm)],[c_14,c_184])).

tff(c_192,plain,(
    ! [B_65,A_66] :
      ( k10_relat_1(B_65,k1_tarski(A_66)) != k1_xboole_0
      | ~ v1_relat_1(B_65)
      | ~ r2_hidden(A_66,k2_relat_1(B_65)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_188])).

tff(c_198,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_127,c_192])).

tff(c_203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_136,c_198])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:39:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.25  
% 2.01/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.25  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.01/1.25  
% 2.01/1.25  %Foreground sorts:
% 2.01/1.25  
% 2.01/1.25  
% 2.01/1.25  %Background operators:
% 2.01/1.25  
% 2.01/1.25  
% 2.01/1.25  %Foreground operators:
% 2.01/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.01/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.01/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.01/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.01/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.01/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.01/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.01/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.01/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.01/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.01/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.01/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.25  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.01/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.01/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.01/1.25  
% 2.01/1.26  tff(f_73, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 2.01/1.26  tff(f_46, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.01/1.26  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.01/1.26  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 2.01/1.26  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.01/1.26  tff(f_49, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.01/1.26  tff(f_41, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.01/1.26  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 2.01/1.26  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.01/1.26  tff(c_28, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.01/1.26  tff(c_75, plain, (~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_28])).
% 2.01/1.26  tff(c_34, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2')) | k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.01/1.26  tff(c_84, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_75, c_34])).
% 2.01/1.26  tff(c_76, plain, (![A_33, B_34]: (r1_xboole_0(k1_tarski(A_33), B_34) | r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.01/1.26  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.01/1.26  tff(c_79, plain, (![B_34, A_33]: (r1_xboole_0(B_34, k1_tarski(A_33)) | r2_hidden(A_33, B_34))), inference(resolution, [status(thm)], [c_76, c_2])).
% 2.01/1.26  tff(c_94, plain, (![B_40, A_41]: (k10_relat_1(B_40, A_41)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_40), A_41) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.01/1.26  tff(c_117, plain, (![B_46, A_47]: (k10_relat_1(B_46, k1_tarski(A_47))=k1_xboole_0 | ~v1_relat_1(B_46) | r2_hidden(A_47, k2_relat_1(B_46)))), inference(resolution, [status(thm)], [c_79, c_94])).
% 2.01/1.26  tff(c_120, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_117, c_75])).
% 2.01/1.26  tff(c_123, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_120])).
% 2.01/1.26  tff(c_125, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_123])).
% 2.01/1.26  tff(c_126, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_28])).
% 2.01/1.26  tff(c_128, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_34])).
% 2.01/1.26  tff(c_134, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_128])).
% 2.01/1.26  tff(c_136, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 2.01/1.26  tff(c_127, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_28])).
% 2.01/1.26  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.01/1.26  tff(c_53, plain, (![A_22, B_23]: (k2_xboole_0(k1_tarski(A_22), B_23)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.01/1.26  tff(c_57, plain, (![A_22]: (k1_tarski(A_22)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_53])).
% 2.01/1.26  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(k1_tarski(A_10), B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.01/1.26  tff(c_184, plain, (![B_63, A_64]: (k10_relat_1(B_63, A_64)!=k1_xboole_0 | ~r1_tarski(A_64, k2_relat_1(B_63)) | k1_xboole_0=A_64 | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.01/1.26  tff(c_188, plain, (![B_63, A_10]: (k10_relat_1(B_63, k1_tarski(A_10))!=k1_xboole_0 | k1_tarski(A_10)=k1_xboole_0 | ~v1_relat_1(B_63) | ~r2_hidden(A_10, k2_relat_1(B_63)))), inference(resolution, [status(thm)], [c_14, c_184])).
% 2.01/1.26  tff(c_192, plain, (![B_65, A_66]: (k10_relat_1(B_65, k1_tarski(A_66))!=k1_xboole_0 | ~v1_relat_1(B_65) | ~r2_hidden(A_66, k2_relat_1(B_65)))), inference(negUnitSimplification, [status(thm)], [c_57, c_188])).
% 2.01/1.26  tff(c_198, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_127, c_192])).
% 2.01/1.26  tff(c_203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_136, c_198])).
% 2.01/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.26  
% 2.01/1.26  Inference rules
% 2.01/1.26  ----------------------
% 2.01/1.26  #Ref     : 0
% 2.01/1.26  #Sup     : 34
% 2.01/1.26  #Fact    : 0
% 2.01/1.26  #Define  : 0
% 2.01/1.26  #Split   : 2
% 2.01/1.26  #Chain   : 0
% 2.01/1.26  #Close   : 0
% 2.01/1.26  
% 2.01/1.26  Ordering : KBO
% 2.01/1.26  
% 2.01/1.26  Simplification rules
% 2.01/1.26  ----------------------
% 2.01/1.26  #Subsume      : 4
% 2.01/1.26  #Demod        : 6
% 2.01/1.26  #Tautology    : 22
% 2.01/1.26  #SimpNegUnit  : 3
% 2.01/1.26  #BackRed      : 0
% 2.01/1.26  
% 2.01/1.26  #Partial instantiations: 0
% 2.01/1.26  #Strategies tried      : 1
% 2.01/1.26  
% 2.01/1.26  Timing (in seconds)
% 2.01/1.26  ----------------------
% 2.01/1.27  Preprocessing        : 0.30
% 2.01/1.27  Parsing              : 0.17
% 2.01/1.27  CNF conversion       : 0.02
% 2.01/1.27  Main loop            : 0.15
% 2.01/1.27  Inferencing          : 0.06
% 2.01/1.27  Reduction            : 0.04
% 2.01/1.27  Demodulation         : 0.02
% 2.01/1.27  BG Simplification    : 0.01
% 2.01/1.27  Subsumption          : 0.03
% 2.01/1.27  Abstraction          : 0.01
% 2.01/1.27  MUC search           : 0.00
% 2.01/1.27  Cooper               : 0.00
% 2.01/1.27  Total                : 0.48
% 2.01/1.27  Index Insertion      : 0.00
% 2.01/1.27  Index Deletion       : 0.00
% 2.01/1.27  Index Matching       : 0.00
% 2.01/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
