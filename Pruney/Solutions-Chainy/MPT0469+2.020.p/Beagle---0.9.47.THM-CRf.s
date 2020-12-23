%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:54 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   52 (  73 expanded)
%              Number of leaves         :   27 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :   55 (  89 expanded)
%              Number of equality atoms :   15 (  29 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_64,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_28,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

tff(c_30,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_46,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_136,plain,(
    ! [A_59,B_60] :
      ( r2_hidden(k4_tarski('#skF_1'(A_59,B_60),'#skF_2'(A_59,B_60)),A_59)
      | r2_hidden('#skF_3'(A_59,B_60),B_60)
      | k1_relat_1(A_59) = B_60 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_56,plain,(
    ! [A_38,B_39] :
      ( ~ r2_hidden(A_38,B_39)
      | ~ r1_xboole_0(k1_tarski(A_38),B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_61,plain,(
    ! [A_38] : ~ r2_hidden(A_38,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_56])).

tff(c_271,plain,(
    ! [B_69] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_69),B_69)
      | k1_relat_1(k1_xboole_0) = B_69 ) ),
    inference(resolution,[status(thm)],[c_136,c_61])).

tff(c_307,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_271,c_61])).

tff(c_320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_307])).

tff(c_321,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_322,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_591,plain,(
    ! [A_103,B_104] :
      ( r2_hidden(k4_tarski('#skF_1'(A_103,B_104),'#skF_2'(A_103,B_104)),A_103)
      | r2_hidden('#skF_3'(A_103,B_104),B_104)
      | k1_relat_1(A_103) = B_104 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_336,plain,(
    ! [A_72,B_73] :
      ( ~ r2_hidden(A_72,B_73)
      | ~ r1_xboole_0(k1_tarski(A_72),B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_341,plain,(
    ! [A_72] : ~ r2_hidden(A_72,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_336])).

tff(c_650,plain,(
    ! [B_104] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_104),B_104)
      | k1_relat_1(k1_xboole_0) = B_104 ) ),
    inference(resolution,[status(thm)],[c_591,c_341])).

tff(c_667,plain,(
    ! [B_105] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_105),B_105)
      | k1_xboole_0 = B_105 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_650])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_32,plain,(
    ! [A_34] :
      ( v1_relat_1(A_34)
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_36,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_32])).

tff(c_353,plain,(
    ! [A_81,B_82] :
      ( r2_hidden('#skF_5'(A_81,B_82),k1_relat_1(B_82))
      | ~ r2_hidden(A_81,k2_relat_1(B_82))
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_356,plain,(
    ! [A_81] :
      ( r2_hidden('#skF_5'(A_81,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_81,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_353])).

tff(c_358,plain,(
    ! [A_81] :
      ( r2_hidden('#skF_5'(A_81,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_81,k2_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_356])).

tff(c_359,plain,(
    ! [A_81] : ~ r2_hidden(A_81,k2_relat_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_341,c_358])).

tff(c_719,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_667,c_359])).

tff(c_739,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_321,c_719])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:05:40 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.41  
% 2.38/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.41  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1 > #skF_5
% 2.38/1.41  
% 2.38/1.41  %Foreground sorts:
% 2.38/1.41  
% 2.38/1.41  
% 2.38/1.41  %Background operators:
% 2.38/1.41  
% 2.38/1.41  
% 2.38/1.41  %Foreground operators:
% 2.38/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.38/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.38/1.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.38/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.38/1.41  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.38/1.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.38/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.38/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.38/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.38/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.38/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.38/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.38/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.38/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.38/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.38/1.41  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.38/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.38/1.41  
% 2.38/1.42  tff(f_64, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.38/1.42  tff(f_51, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 2.38/1.42  tff(f_28, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.38/1.42  tff(f_39, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.38/1.42  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.38/1.42  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.38/1.42  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relat_1)).
% 2.38/1.42  tff(c_30, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.38/1.42  tff(c_46, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_30])).
% 2.38/1.42  tff(c_136, plain, (![A_59, B_60]: (r2_hidden(k4_tarski('#skF_1'(A_59, B_60), '#skF_2'(A_59, B_60)), A_59) | r2_hidden('#skF_3'(A_59, B_60), B_60) | k1_relat_1(A_59)=B_60)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.38/1.42  tff(c_4, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.38/1.42  tff(c_56, plain, (![A_38, B_39]: (~r2_hidden(A_38, B_39) | ~r1_xboole_0(k1_tarski(A_38), B_39))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.38/1.42  tff(c_61, plain, (![A_38]: (~r2_hidden(A_38, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_56])).
% 2.38/1.42  tff(c_271, plain, (![B_69]: (r2_hidden('#skF_3'(k1_xboole_0, B_69), B_69) | k1_relat_1(k1_xboole_0)=B_69)), inference(resolution, [status(thm)], [c_136, c_61])).
% 2.38/1.42  tff(c_307, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_271, c_61])).
% 2.38/1.42  tff(c_320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_307])).
% 2.38/1.42  tff(c_321, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_30])).
% 2.38/1.42  tff(c_322, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_30])).
% 2.38/1.42  tff(c_591, plain, (![A_103, B_104]: (r2_hidden(k4_tarski('#skF_1'(A_103, B_104), '#skF_2'(A_103, B_104)), A_103) | r2_hidden('#skF_3'(A_103, B_104), B_104) | k1_relat_1(A_103)=B_104)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.38/1.42  tff(c_336, plain, (![A_72, B_73]: (~r2_hidden(A_72, B_73) | ~r1_xboole_0(k1_tarski(A_72), B_73))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.38/1.42  tff(c_341, plain, (![A_72]: (~r2_hidden(A_72, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_336])).
% 2.38/1.42  tff(c_650, plain, (![B_104]: (r2_hidden('#skF_3'(k1_xboole_0, B_104), B_104) | k1_relat_1(k1_xboole_0)=B_104)), inference(resolution, [status(thm)], [c_591, c_341])).
% 2.38/1.42  tff(c_667, plain, (![B_105]: (r2_hidden('#skF_3'(k1_xboole_0, B_105), B_105) | k1_xboole_0=B_105)), inference(demodulation, [status(thm), theory('equality')], [c_322, c_650])).
% 2.38/1.42  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.38/1.42  tff(c_32, plain, (![A_34]: (v1_relat_1(A_34) | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.38/1.42  tff(c_36, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_32])).
% 2.38/1.42  tff(c_353, plain, (![A_81, B_82]: (r2_hidden('#skF_5'(A_81, B_82), k1_relat_1(B_82)) | ~r2_hidden(A_81, k2_relat_1(B_82)) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.38/1.42  tff(c_356, plain, (![A_81]: (r2_hidden('#skF_5'(A_81, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_81, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_322, c_353])).
% 2.38/1.42  tff(c_358, plain, (![A_81]: (r2_hidden('#skF_5'(A_81, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_81, k2_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_356])).
% 2.38/1.42  tff(c_359, plain, (![A_81]: (~r2_hidden(A_81, k2_relat_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_341, c_358])).
% 2.38/1.42  tff(c_719, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_667, c_359])).
% 2.38/1.42  tff(c_739, plain, $false, inference(negUnitSimplification, [status(thm)], [c_321, c_719])).
% 2.38/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.42  
% 2.38/1.42  Inference rules
% 2.38/1.42  ----------------------
% 2.38/1.42  #Ref     : 0
% 2.38/1.42  #Sup     : 133
% 2.38/1.42  #Fact    : 0
% 2.38/1.42  #Define  : 0
% 2.38/1.42  #Split   : 6
% 2.38/1.42  #Chain   : 0
% 2.38/1.42  #Close   : 0
% 2.38/1.42  
% 2.38/1.42  Ordering : KBO
% 2.38/1.42  
% 2.38/1.42  Simplification rules
% 2.38/1.42  ----------------------
% 2.38/1.42  #Subsume      : 25
% 2.38/1.42  #Demod        : 5
% 2.38/1.42  #Tautology    : 15
% 2.38/1.42  #SimpNegUnit  : 4
% 2.38/1.42  #BackRed      : 0
% 2.38/1.42  
% 2.38/1.42  #Partial instantiations: 0
% 2.38/1.42  #Strategies tried      : 1
% 2.38/1.42  
% 2.38/1.42  Timing (in seconds)
% 2.38/1.42  ----------------------
% 2.38/1.43  Preprocessing        : 0.31
% 2.38/1.43  Parsing              : 0.16
% 2.38/1.43  CNF conversion       : 0.02
% 2.38/1.43  Main loop            : 0.29
% 2.38/1.43  Inferencing          : 0.11
% 2.38/1.43  Reduction            : 0.08
% 2.38/1.43  Demodulation         : 0.05
% 2.38/1.43  BG Simplification    : 0.02
% 2.38/1.43  Subsumption          : 0.06
% 2.38/1.43  Abstraction          : 0.02
% 2.38/1.43  MUC search           : 0.00
% 2.38/1.43  Cooper               : 0.00
% 2.38/1.43  Total                : 0.63
% 2.38/1.43  Index Insertion      : 0.00
% 2.38/1.43  Index Deletion       : 0.00
% 2.38/1.43  Index Matching       : 0.00
% 2.38/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
