%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:37 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   47 (  60 expanded)
%              Number of leaves         :   23 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   56 (  87 expanded)
%              Number of equality atoms :   17 (  27 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

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

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_26,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_69,plain,(
    ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_32,plain,
    ( r2_hidden('#skF_1',k2_relat_1('#skF_2'))
    | k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_119,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_32])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(k1_tarski(A_17),B_18) = k1_tarski(A_17)
      | r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_xboole_0(k4_xboole_0(A_3,B_4),B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_43,plain,(
    ! [B_24,A_25] :
      ( r1_xboole_0(B_24,A_25)
      | ~ r1_xboole_0(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_46,plain,(
    ! [B_4,A_3] : r1_xboole_0(B_4,k4_xboole_0(A_3,B_4)) ),
    inference(resolution,[status(thm)],[c_4,c_43])).

tff(c_125,plain,(
    ! [B_49,A_50] :
      ( k10_relat_1(B_49,A_50) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_49),A_50)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_140,plain,(
    ! [B_51,A_52] :
      ( k10_relat_1(B_51,k4_xboole_0(A_52,k2_relat_1(B_51))) = k1_xboole_0
      | ~ v1_relat_1(B_51) ) ),
    inference(resolution,[status(thm)],[c_46,c_125])).

tff(c_178,plain,(
    ! [B_63,A_64] :
      ( k10_relat_1(B_63,k1_tarski(A_64)) = k1_xboole_0
      | ~ v1_relat_1(B_63)
      | r2_hidden(A_64,k2_relat_1(B_63)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_140])).

tff(c_184,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_178,c_69])).

tff(c_188,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_184])).

tff(c_190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_188])).

tff(c_191,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_192,plain,(
    r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_248,plain,(
    ! [B_74,A_75] :
      ( r1_xboole_0(k2_relat_1(B_74),A_75)
      | k10_relat_1(B_74,A_75) != k1_xboole_0
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_290,plain,(
    ! [A_86,B_87] :
      ( r1_xboole_0(A_86,k2_relat_1(B_87))
      | k10_relat_1(B_87,A_86) != k1_xboole_0
      | ~ v1_relat_1(B_87) ) ),
    inference(resolution,[status(thm)],[c_248,c_2])).

tff(c_14,plain,(
    ! [A_15,B_16] :
      ( ~ r2_hidden(A_15,B_16)
      | ~ r1_xboole_0(k1_tarski(A_15),B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_304,plain,(
    ! [A_88,B_89] :
      ( ~ r2_hidden(A_88,k2_relat_1(B_89))
      | k10_relat_1(B_89,k1_tarski(A_88)) != k1_xboole_0
      | ~ v1_relat_1(B_89) ) ),
    inference(resolution,[status(thm)],[c_290,c_14])).

tff(c_307,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_192,c_304])).

tff(c_311,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_191,c_307])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:24:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.30  
% 1.97/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.30  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.97/1.30  
% 1.97/1.30  %Foreground sorts:
% 1.97/1.30  
% 1.97/1.30  
% 1.97/1.30  %Background operators:
% 1.97/1.30  
% 1.97/1.30  
% 1.97/1.30  %Foreground operators:
% 1.97/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.97/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.97/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.97/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.97/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.97/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.97/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.97/1.30  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.30  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.30  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.97/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.97/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.30  
% 2.22/1.31  tff(f_63, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 2.22/1.31  tff(f_49, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 2.22/1.31  tff(f_31, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.22/1.31  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.22/1.31  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 2.22/1.31  tff(f_44, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.22/1.31  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.22/1.31  tff(c_26, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.22/1.31  tff(c_69, plain, (~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_26])).
% 2.22/1.31  tff(c_32, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2')) | k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.22/1.31  tff(c_119, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_69, c_32])).
% 2.22/1.31  tff(c_18, plain, (![A_17, B_18]: (k4_xboole_0(k1_tarski(A_17), B_18)=k1_tarski(A_17) | r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.22/1.31  tff(c_4, plain, (![A_3, B_4]: (r1_xboole_0(k4_xboole_0(A_3, B_4), B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.22/1.31  tff(c_43, plain, (![B_24, A_25]: (r1_xboole_0(B_24, A_25) | ~r1_xboole_0(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.22/1.31  tff(c_46, plain, (![B_4, A_3]: (r1_xboole_0(B_4, k4_xboole_0(A_3, B_4)))), inference(resolution, [status(thm)], [c_4, c_43])).
% 2.22/1.31  tff(c_125, plain, (![B_49, A_50]: (k10_relat_1(B_49, A_50)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_49), A_50) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.22/1.31  tff(c_140, plain, (![B_51, A_52]: (k10_relat_1(B_51, k4_xboole_0(A_52, k2_relat_1(B_51)))=k1_xboole_0 | ~v1_relat_1(B_51))), inference(resolution, [status(thm)], [c_46, c_125])).
% 2.22/1.31  tff(c_178, plain, (![B_63, A_64]: (k10_relat_1(B_63, k1_tarski(A_64))=k1_xboole_0 | ~v1_relat_1(B_63) | r2_hidden(A_64, k2_relat_1(B_63)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_140])).
% 2.22/1.31  tff(c_184, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_178, c_69])).
% 2.22/1.31  tff(c_188, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_184])).
% 2.22/1.31  tff(c_190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119, c_188])).
% 2.22/1.31  tff(c_191, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_26])).
% 2.22/1.31  tff(c_192, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_26])).
% 2.22/1.31  tff(c_248, plain, (![B_74, A_75]: (r1_xboole_0(k2_relat_1(B_74), A_75) | k10_relat_1(B_74, A_75)!=k1_xboole_0 | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.22/1.31  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.22/1.31  tff(c_290, plain, (![A_86, B_87]: (r1_xboole_0(A_86, k2_relat_1(B_87)) | k10_relat_1(B_87, A_86)!=k1_xboole_0 | ~v1_relat_1(B_87))), inference(resolution, [status(thm)], [c_248, c_2])).
% 2.22/1.31  tff(c_14, plain, (![A_15, B_16]: (~r2_hidden(A_15, B_16) | ~r1_xboole_0(k1_tarski(A_15), B_16))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.22/1.31  tff(c_304, plain, (![A_88, B_89]: (~r2_hidden(A_88, k2_relat_1(B_89)) | k10_relat_1(B_89, k1_tarski(A_88))!=k1_xboole_0 | ~v1_relat_1(B_89))), inference(resolution, [status(thm)], [c_290, c_14])).
% 2.22/1.31  tff(c_307, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_192, c_304])).
% 2.22/1.31  tff(c_311, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_191, c_307])).
% 2.22/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.31  
% 2.22/1.31  Inference rules
% 2.22/1.31  ----------------------
% 2.22/1.31  #Ref     : 0
% 2.22/1.31  #Sup     : 60
% 2.22/1.31  #Fact    : 0
% 2.22/1.31  #Define  : 0
% 2.22/1.31  #Split   : 1
% 2.22/1.31  #Chain   : 0
% 2.22/1.31  #Close   : 0
% 2.22/1.31  
% 2.22/1.31  Ordering : KBO
% 2.22/1.31  
% 2.22/1.31  Simplification rules
% 2.22/1.31  ----------------------
% 2.22/1.31  #Subsume      : 8
% 2.22/1.31  #Demod        : 6
% 2.22/1.31  #Tautology    : 33
% 2.22/1.31  #SimpNegUnit  : 2
% 2.22/1.31  #BackRed      : 0
% 2.22/1.31  
% 2.22/1.31  #Partial instantiations: 0
% 2.22/1.31  #Strategies tried      : 1
% 2.22/1.31  
% 2.22/1.31  Timing (in seconds)
% 2.22/1.31  ----------------------
% 2.22/1.31  Preprocessing        : 0.35
% 2.22/1.31  Parsing              : 0.22
% 2.22/1.31  CNF conversion       : 0.02
% 2.22/1.31  Main loop            : 0.19
% 2.22/1.31  Inferencing          : 0.08
% 2.22/1.31  Reduction            : 0.05
% 2.22/1.31  Demodulation         : 0.03
% 2.22/1.31  BG Simplification    : 0.01
% 2.22/1.31  Subsumption          : 0.03
% 2.22/1.31  Abstraction          : 0.01
% 2.22/1.31  MUC search           : 0.00
% 2.22/1.31  Cooper               : 0.00
% 2.22/1.31  Total                : 0.57
% 2.22/1.31  Index Insertion      : 0.00
% 2.22/1.31  Index Deletion       : 0.00
% 2.22/1.31  Index Matching       : 0.00
% 2.22/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
