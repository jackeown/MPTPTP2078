%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:56 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 122 expanded)
%              Number of leaves         :   29 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :   55 ( 172 expanded)
%              Number of equality atoms :   17 (  41 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_8 > #skF_7 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).

tff(c_34,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_45,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_236,plain,(
    ! [A_92,B_93] :
      ( r2_hidden(k4_tarski('#skF_4'(A_92,B_93),'#skF_5'(A_92,B_93)),A_92)
      | r2_hidden('#skF_6'(A_92,B_93),B_93)
      | k1_relat_1(A_92) = B_93 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_48,plain,(
    ! [A_60,B_61] :
      ( ~ r2_hidden(A_60,B_61)
      | ~ r1_xboole_0(k1_tarski(A_60),B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_53,plain,(
    ! [A_60] : ~ r2_hidden(A_60,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_48])).

tff(c_1344,plain,(
    ! [B_133] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_133),B_133)
      | k1_relat_1(k1_xboole_0) = B_133 ) ),
    inference(resolution,[status(thm)],[c_236,c_53])).

tff(c_1468,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1344,c_53])).

tff(c_1503,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_1468])).

tff(c_1504,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1722,plain,(
    ! [A_175,B_176] :
      ( r2_hidden(k4_tarski('#skF_4'(A_175,B_176),'#skF_5'(A_175,B_176)),A_175)
      | r2_hidden('#skF_6'(A_175,B_176),B_176)
      | k1_relat_1(A_175) = B_176 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1512,plain,(
    ! [A_138,B_139] :
      ( ~ r2_hidden(A_138,B_139)
      | ~ r1_xboole_0(k1_tarski(A_138),B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1517,plain,(
    ! [A_138] : ~ r2_hidden(A_138,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_1512])).

tff(c_18,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_1'(A_14),A_14)
      | v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1518,plain,(
    ! [A_140] : ~ r2_hidden(A_140,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_1512])).

tff(c_1523,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_1518])).

tff(c_1505,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1552,plain,(
    ! [A_153,B_154] :
      ( r2_hidden('#skF_8'(A_153,B_154),k1_relat_1(B_154))
      | ~ r2_hidden(A_153,k2_relat_1(B_154))
      | ~ v1_relat_1(B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1555,plain,(
    ! [A_153] :
      ( r2_hidden('#skF_8'(A_153,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_153,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1505,c_1552])).

tff(c_1557,plain,(
    ! [A_153] :
      ( r2_hidden('#skF_8'(A_153,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_153,k2_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1523,c_1555])).

tff(c_1558,plain,(
    ! [A_153] : ~ r2_hidden(A_153,k2_relat_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_1517,c_1557])).

tff(c_1784,plain,(
    ! [B_178] :
      ( r2_hidden('#skF_6'(k2_relat_1(k1_xboole_0),B_178),B_178)
      | k1_relat_1(k2_relat_1(k1_xboole_0)) = B_178 ) ),
    inference(resolution,[status(thm)],[c_1722,c_1558])).

tff(c_1825,plain,(
    k1_relat_1(k2_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1784,c_1517])).

tff(c_1824,plain,(
    k1_relat_1(k2_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1784,c_1558])).

tff(c_1852,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1825,c_1824])).

tff(c_1853,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1504,c_1852])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:56:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.60  
% 3.24/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.60  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_8 > #skF_7 > #skF_2 > #skF_5 > #skF_4
% 3.24/1.60  
% 3.24/1.60  %Foreground sorts:
% 3.24/1.60  
% 3.24/1.60  
% 3.24/1.60  %Background operators:
% 3.24/1.60  
% 3.24/1.60  
% 3.24/1.60  %Foreground operators:
% 3.24/1.60  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.24/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.24/1.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.24/1.60  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.24/1.60  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.24/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.24/1.60  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.24/1.60  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.24/1.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.24/1.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.24/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.24/1.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.24/1.60  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.24/1.60  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 3.24/1.60  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.24/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.24/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.60  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.24/1.60  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.24/1.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.24/1.60  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.24/1.60  
% 3.24/1.61  tff(f_71, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.24/1.61  tff(f_58, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 3.24/1.61  tff(f_27, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.24/1.61  tff(f_40, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 3.24/1.61  tff(f_50, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 3.24/1.61  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relat_1)).
% 3.24/1.61  tff(c_34, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.24/1.61  tff(c_45, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_34])).
% 3.24/1.61  tff(c_236, plain, (![A_92, B_93]: (r2_hidden(k4_tarski('#skF_4'(A_92, B_93), '#skF_5'(A_92, B_93)), A_92) | r2_hidden('#skF_6'(A_92, B_93), B_93) | k1_relat_1(A_92)=B_93)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.24/1.61  tff(c_2, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.24/1.61  tff(c_48, plain, (![A_60, B_61]: (~r2_hidden(A_60, B_61) | ~r1_xboole_0(k1_tarski(A_60), B_61))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.24/1.61  tff(c_53, plain, (![A_60]: (~r2_hidden(A_60, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_48])).
% 3.24/1.61  tff(c_1344, plain, (![B_133]: (r2_hidden('#skF_6'(k1_xboole_0, B_133), B_133) | k1_relat_1(k1_xboole_0)=B_133)), inference(resolution, [status(thm)], [c_236, c_53])).
% 3.24/1.61  tff(c_1468, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1344, c_53])).
% 3.24/1.61  tff(c_1503, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_1468])).
% 3.24/1.61  tff(c_1504, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 3.24/1.61  tff(c_1722, plain, (![A_175, B_176]: (r2_hidden(k4_tarski('#skF_4'(A_175, B_176), '#skF_5'(A_175, B_176)), A_175) | r2_hidden('#skF_6'(A_175, B_176), B_176) | k1_relat_1(A_175)=B_176)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.24/1.61  tff(c_1512, plain, (![A_138, B_139]: (~r2_hidden(A_138, B_139) | ~r1_xboole_0(k1_tarski(A_138), B_139))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.24/1.61  tff(c_1517, plain, (![A_138]: (~r2_hidden(A_138, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_1512])).
% 3.24/1.61  tff(c_18, plain, (![A_14]: (r2_hidden('#skF_1'(A_14), A_14) | v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.24/1.61  tff(c_1518, plain, (![A_140]: (~r2_hidden(A_140, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_1512])).
% 3.24/1.61  tff(c_1523, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_1518])).
% 3.24/1.61  tff(c_1505, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 3.24/1.61  tff(c_1552, plain, (![A_153, B_154]: (r2_hidden('#skF_8'(A_153, B_154), k1_relat_1(B_154)) | ~r2_hidden(A_153, k2_relat_1(B_154)) | ~v1_relat_1(B_154))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.24/1.61  tff(c_1555, plain, (![A_153]: (r2_hidden('#skF_8'(A_153, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_153, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1505, c_1552])).
% 3.24/1.61  tff(c_1557, plain, (![A_153]: (r2_hidden('#skF_8'(A_153, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_153, k2_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1523, c_1555])).
% 3.24/1.61  tff(c_1558, plain, (![A_153]: (~r2_hidden(A_153, k2_relat_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_1517, c_1557])).
% 3.24/1.61  tff(c_1784, plain, (![B_178]: (r2_hidden('#skF_6'(k2_relat_1(k1_xboole_0), B_178), B_178) | k1_relat_1(k2_relat_1(k1_xboole_0))=B_178)), inference(resolution, [status(thm)], [c_1722, c_1558])).
% 3.24/1.61  tff(c_1825, plain, (k1_relat_1(k2_relat_1(k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_1784, c_1517])).
% 3.24/1.61  tff(c_1824, plain, (k1_relat_1(k2_relat_1(k1_xboole_0))=k2_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_1784, c_1558])).
% 3.24/1.61  tff(c_1852, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1825, c_1824])).
% 3.24/1.61  tff(c_1853, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1504, c_1852])).
% 3.24/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.61  
% 3.24/1.61  Inference rules
% 3.24/1.61  ----------------------
% 3.24/1.61  #Ref     : 2
% 3.24/1.61  #Sup     : 344
% 3.24/1.61  #Fact    : 0
% 3.24/1.61  #Define  : 0
% 3.24/1.61  #Split   : 1
% 3.24/1.61  #Chain   : 0
% 3.24/1.61  #Close   : 0
% 3.24/1.61  
% 3.24/1.61  Ordering : KBO
% 3.24/1.61  
% 3.24/1.61  Simplification rules
% 3.24/1.61  ----------------------
% 3.24/1.61  #Subsume      : 76
% 3.24/1.61  #Demod        : 37
% 3.24/1.61  #Tautology    : 31
% 3.24/1.61  #SimpNegUnit  : 6
% 3.24/1.61  #BackRed      : 7
% 3.24/1.61  
% 3.24/1.61  #Partial instantiations: 0
% 3.24/1.61  #Strategies tried      : 1
% 3.24/1.61  
% 3.24/1.61  Timing (in seconds)
% 3.24/1.61  ----------------------
% 3.24/1.62  Preprocessing        : 0.31
% 3.24/1.62  Parsing              : 0.17
% 3.24/1.62  CNF conversion       : 0.02
% 3.24/1.62  Main loop            : 0.50
% 3.24/1.62  Inferencing          : 0.17
% 3.24/1.62  Reduction            : 0.15
% 3.24/1.62  Demodulation         : 0.08
% 3.24/1.62  BG Simplification    : 0.02
% 3.24/1.62  Subsumption          : 0.11
% 3.24/1.62  Abstraction          : 0.03
% 3.24/1.62  MUC search           : 0.00
% 3.24/1.62  Cooper               : 0.00
% 3.24/1.62  Total                : 0.84
% 3.24/1.62  Index Insertion      : 0.00
% 3.24/1.62  Index Deletion       : 0.00
% 3.24/1.62  Index Matching       : 0.00
% 3.24/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
