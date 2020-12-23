%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:36 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   54 (  65 expanded)
%              Number of leaves         :   26 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   73 (  99 expanded)
%              Number of equality atoms :   27 (  37 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_81,negated_conjecture,(
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

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k2_relat_1(B))
          & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_42,plain,
    ( r2_hidden('#skF_1',k2_relat_1('#skF_2'))
    | k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_89,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_85,plain,(
    ! [A_31,B_32] :
      ( r1_xboole_0(k1_tarski(A_31),B_32)
      | r2_hidden(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_88,plain,(
    ! [B_32,A_31] :
      ( r1_xboole_0(B_32,k1_tarski(A_31))
      | r2_hidden(A_31,B_32) ) ),
    inference(resolution,[status(thm)],[c_85,c_2])).

tff(c_151,plain,(
    ! [B_47,A_48] :
      ( k10_relat_1(B_47,A_48) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_47),A_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_196,plain,(
    ! [B_59,A_60] :
      ( k10_relat_1(B_59,k1_tarski(A_60)) = k1_xboole_0
      | ~ v1_relat_1(B_59)
      | r2_hidden(A_60,k2_relat_1(B_59)) ) ),
    inference(resolution,[status(thm)],[c_88,c_151])).

tff(c_36,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_140,plain,(
    ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_36])).

tff(c_199,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_196,c_140])).

tff(c_202,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_199])).

tff(c_204,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_202])).

tff(c_206,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_205,plain,(
    r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_6,plain,(
    ! [A_4] : k4_xboole_0(k1_xboole_0,A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_78,plain,(
    ! [C_24,B_25] : ~ r2_hidden(C_24,k4_xboole_0(B_25,k1_tarski(C_24))) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_81,plain,(
    ! [C_24] : ~ r2_hidden(C_24,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_78])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_231,plain,(
    ! [A_67,B_68] :
      ( r2_hidden(A_67,B_68)
      | k4_xboole_0(k1_tarski(A_67),B_68) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_235,plain,(
    ! [A_67] :
      ( r2_hidden(A_67,k1_xboole_0)
      | k1_tarski(A_67) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_231])).

tff(c_236,plain,(
    ! [A_67] : k1_tarski(A_67) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_235])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k1_tarski(A_8),B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_319,plain,(
    ! [B_84,A_85] :
      ( k10_relat_1(B_84,A_85) != k1_xboole_0
      | ~ r1_tarski(A_85,k2_relat_1(B_84))
      | k1_xboole_0 = A_85
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_323,plain,(
    ! [B_84,A_8] :
      ( k10_relat_1(B_84,k1_tarski(A_8)) != k1_xboole_0
      | k1_tarski(A_8) = k1_xboole_0
      | ~ v1_relat_1(B_84)
      | ~ r2_hidden(A_8,k2_relat_1(B_84)) ) ),
    inference(resolution,[status(thm)],[c_14,c_319])).

tff(c_328,plain,(
    ! [B_89,A_90] :
      ( k10_relat_1(B_89,k1_tarski(A_90)) != k1_xboole_0
      | ~ v1_relat_1(B_89)
      | ~ r2_hidden(A_90,k2_relat_1(B_89)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_323])).

tff(c_331,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_205,c_328])).

tff(c_335,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_206,c_331])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:58:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.24  
% 2.13/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.25  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.13/1.25  
% 2.13/1.25  %Foreground sorts:
% 2.13/1.25  
% 2.13/1.25  
% 2.13/1.25  %Background operators:
% 2.13/1.25  
% 2.13/1.25  
% 2.13/1.25  %Foreground operators:
% 2.13/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.13/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.13/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.13/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.13/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.13/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.13/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.25  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.13/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.13/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.25  
% 2.13/1.26  tff(f_81, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 2.13/1.26  tff(f_46, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.13/1.26  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.13/1.26  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 2.13/1.26  tff(f_33, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.13/1.26  tff(f_57, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.13/1.26  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.13/1.26  tff(f_50, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 2.13/1.26  tff(f_41, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.13/1.26  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 2.13/1.26  tff(c_34, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.13/1.26  tff(c_42, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2')) | k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.13/1.26  tff(c_89, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_42])).
% 2.13/1.26  tff(c_85, plain, (![A_31, B_32]: (r1_xboole_0(k1_tarski(A_31), B_32) | r2_hidden(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.13/1.26  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.13/1.26  tff(c_88, plain, (![B_32, A_31]: (r1_xboole_0(B_32, k1_tarski(A_31)) | r2_hidden(A_31, B_32))), inference(resolution, [status(thm)], [c_85, c_2])).
% 2.13/1.26  tff(c_151, plain, (![B_47, A_48]: (k10_relat_1(B_47, A_48)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_47), A_48) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.13/1.26  tff(c_196, plain, (![B_59, A_60]: (k10_relat_1(B_59, k1_tarski(A_60))=k1_xboole_0 | ~v1_relat_1(B_59) | r2_hidden(A_60, k2_relat_1(B_59)))), inference(resolution, [status(thm)], [c_88, c_151])).
% 2.13/1.26  tff(c_36, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.13/1.26  tff(c_140, plain, (~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_89, c_36])).
% 2.13/1.26  tff(c_199, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_196, c_140])).
% 2.13/1.26  tff(c_202, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_199])).
% 2.13/1.26  tff(c_204, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_202])).
% 2.13/1.26  tff(c_206, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 2.13/1.26  tff(c_205, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_42])).
% 2.13/1.26  tff(c_6, plain, (![A_4]: (k4_xboole_0(k1_xboole_0, A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.13/1.26  tff(c_78, plain, (![C_24, B_25]: (~r2_hidden(C_24, k4_xboole_0(B_25, k1_tarski(C_24))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.13/1.26  tff(c_81, plain, (![C_24]: (~r2_hidden(C_24, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_78])).
% 2.13/1.26  tff(c_4, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.26  tff(c_231, plain, (![A_67, B_68]: (r2_hidden(A_67, B_68) | k4_xboole_0(k1_tarski(A_67), B_68)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.13/1.26  tff(c_235, plain, (![A_67]: (r2_hidden(A_67, k1_xboole_0) | k1_tarski(A_67)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_231])).
% 2.13/1.26  tff(c_236, plain, (![A_67]: (k1_tarski(A_67)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_81, c_235])).
% 2.13/1.26  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(k1_tarski(A_8), B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.13/1.26  tff(c_319, plain, (![B_84, A_85]: (k10_relat_1(B_84, A_85)!=k1_xboole_0 | ~r1_tarski(A_85, k2_relat_1(B_84)) | k1_xboole_0=A_85 | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.13/1.26  tff(c_323, plain, (![B_84, A_8]: (k10_relat_1(B_84, k1_tarski(A_8))!=k1_xboole_0 | k1_tarski(A_8)=k1_xboole_0 | ~v1_relat_1(B_84) | ~r2_hidden(A_8, k2_relat_1(B_84)))), inference(resolution, [status(thm)], [c_14, c_319])).
% 2.13/1.26  tff(c_328, plain, (![B_89, A_90]: (k10_relat_1(B_89, k1_tarski(A_90))!=k1_xboole_0 | ~v1_relat_1(B_89) | ~r2_hidden(A_90, k2_relat_1(B_89)))), inference(negUnitSimplification, [status(thm)], [c_236, c_323])).
% 2.13/1.26  tff(c_331, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_205, c_328])).
% 2.13/1.26  tff(c_335, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_206, c_331])).
% 2.13/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.26  
% 2.13/1.26  Inference rules
% 2.13/1.26  ----------------------
% 2.13/1.26  #Ref     : 0
% 2.13/1.26  #Sup     : 59
% 2.13/1.26  #Fact    : 0
% 2.13/1.26  #Define  : 0
% 2.13/1.26  #Split   : 1
% 2.13/1.26  #Chain   : 0
% 2.13/1.26  #Close   : 0
% 2.13/1.26  
% 2.13/1.26  Ordering : KBO
% 2.13/1.26  
% 2.13/1.26  Simplification rules
% 2.13/1.26  ----------------------
% 2.13/1.26  #Subsume      : 16
% 2.13/1.26  #Demod        : 5
% 2.13/1.26  #Tautology    : 31
% 2.13/1.26  #SimpNegUnit  : 13
% 2.13/1.26  #BackRed      : 0
% 2.13/1.26  
% 2.13/1.26  #Partial instantiations: 0
% 2.13/1.26  #Strategies tried      : 1
% 2.13/1.26  
% 2.13/1.26  Timing (in seconds)
% 2.13/1.26  ----------------------
% 2.13/1.26  Preprocessing        : 0.30
% 2.13/1.26  Parsing              : 0.16
% 2.13/1.26  CNF conversion       : 0.02
% 2.13/1.26  Main loop            : 0.20
% 2.13/1.26  Inferencing          : 0.08
% 2.13/1.26  Reduction            : 0.05
% 2.13/1.26  Demodulation         : 0.03
% 2.13/1.26  BG Simplification    : 0.01
% 2.13/1.26  Subsumption          : 0.04
% 2.13/1.26  Abstraction          : 0.01
% 2.13/1.26  MUC search           : 0.00
% 2.13/1.26  Cooper               : 0.00
% 2.13/1.26  Total                : 0.53
% 2.13/1.26  Index Insertion      : 0.00
% 2.13/1.26  Index Deletion       : 0.00
% 2.13/1.26  Index Matching       : 0.00
% 2.13/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
